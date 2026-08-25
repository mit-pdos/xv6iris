(* HartSKpt.v -- the SHARED KERNEL TABLE, reached one node at a time.

   [SRegime.sr_absorb] opens [kptN] ONCE around a whole [translateAddr] and
   hands back the finished translation.  That shape is unavailable at the
   [swp] layer for a structural reason: a translation there spans many nodes,
   another hart steps between them, and no fupd survives a node boundary.

   So the invariant is opened PER READ NODE instead -- and it closes again
   before the node's own mask shift, because everything the walk needs out of
   it is PURE ([pt_slot_mem] is a fact about [σ.(mem)], not a resource).  The
   whole seam is therefore an open/extract/close with nothing held across.

   WHAT THAT COSTS, and it is the one real semantic difference: the three
   PTE reads now happen at three SEPARATE openings, so they see three
   possibly-different live trees.  [kpt_lb] + [kpt_lb_agree] reconcile them
   only up to [ptree_canon], and [PtTree.ptree_maps_canon] is exact on the
   two upper levels but canonicalises the LEAF.  So:

     - the level-2 and level-1 PTEs are pinned across openings;
     - the LEAF's A/D BITS ARE NOT.  Another hart may set them between this
       walk's reads.

   That is not a gap in the reconciliation, it is the machine.  The
   PERMISSION check tolerates it -- [KptShare.tlb_res_pt_translateAddr_at]'s
   premise is [forall (a d : mword 1) …, pte_check_ok … (pte_set_ad … a d)],
   already A/D-quantified because the exec walk could not pin them either.
   The READ and the write-back condition do NOT tolerate it; both are
   answered by reading the leaf at a PREDICATE rather than at a value
   ([HartSTrans]'s [_ex] rules), which is what [swp_translate_kpt] does. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap relations bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
From iris.program_logic Require Import language weakestpre.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvExtras
        RiscvFetchExec.
Require Import SmodePte PtAdBits Pt4kWalk PtTree PtTreeAdue KptPt KMap KptTree.
Require Import KptGoodb.
Require Import KptGhost KptShare.
Require Import HartSwp HartLift HartSpan HartMStore.
Require Import WpDecodeBridge.
Require Import CommonWalk HartSTrans.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* THE A/D-PRESET LEAF NEEDS NO WRITE-BACK.                              *)
(*                                                                       *)
(* [kperm_flags pc] IS [kperm_flags_ad pc (true, true)] -- the two real   *)
(* kvmmake flag bytes 0xCB / 0xC7 -- so A and D are both set and          *)
(* [update_PTE_Bits] declines for EVERY access kind.  This is the fact    *)
(* KptTree §2c names -- no write-back is needed exactly when A (and D,    *)
(* for stores) is already set in the variant -- and leaves unproved; it   *)
(* is what the walk's no-write-back arms need, and it is the ONLY A/D     *)
(* shape for which they hold: see the note at the end of this file.       *)
(* ===================================================================== *)
Lemma kpt_noupd (ppn : mword 44) (pc : kperm)
    (acc : MemoryAccessType mem_payload) :
  update_PTE_Bits (mk_pte ppn (kperm_flags pc) : mword 64) acc = None.
Proof.
  unfold update_PTE_Bits. cbv zeta.
  rewrite (mk_pte_flags ppn (kperm_flags pc)
             (kperm_flags_ad_bound pc (true, true))).
  assert (HD : eq_vec (_get_PTE_Flags_D
                 (Mk_PTE_Flags (mword_of_int (kperm_flags pc) : mword 8)))
                 ('b"0") = false)
    by (destruct pc; vm_compute; reflexivity).
  assert (HA : eq_vec (_get_PTE_Flags_A
                 (Mk_PTE_Flags (mword_of_int (kperm_flags pc) : mword 8)))
                 ('b"0") = false)
    by (destruct pc; vm_compute; reflexivity).
  rewrite HD HA. cbn [andb orb]. reflexivity.
Qed.

(* the same, as the A/D VARIANT the tree layer actually speaks of *)
Lemma kpt_noupd_variant (ppn : mword 44) (pc : kperm) (a d : mword 1)
    (acc : MemoryAccessType mem_payload) :
  eq_vec a ('b"1") = true -> eq_vec d ('b"1") = true ->
  update_PTE_Bits
    (pte_set_ad (mk_pte ppn (kperm_flags pc)) a d : mword 64) acc = None.
Proof.
  intros Ha Hd.
  rewrite kperm_set_ad_leaf. unfold ad_of. rewrite Ha Hd.
  apply kpt_noupd.
Qed.

Section kptnode.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* THE RECONCILIATION, pure: a live tree canonically equal to the snapshot
     maps the same vpn through the same two upper PTEs, and through a leaf
     that agrees with the snapshot's leaf up to [pte_canon] (i.e. up to A/D). *)
  Lemma kpt_maps_across (t0 t' : ptree) (vpn : mword 27) (p2 p1 p0 : mword 64) :
    ptree_canon t0 = ptree_canon t' ->
    ptree_maps t0 vpn p2 p1 p0 ->
    exists q0, ptree_maps t' vpn p2 p1 q0 /\ pte_canon q0 = pte_canon p0.
  Proof.
    intros Hcan Hmaps.
    pose proof (ptree_maps_canon t0 vpn p2 p1 p0 Hmaps) as Hc0.
    rewrite Hcan in Hc0.
    destruct (ptree_maps_canon_inv t' vpn p2 p1 _ Hc0) as (q0 & Hm' & Heq).
    exists q0. split; [exact Hm' | symmetry; exact Heq].
  Qed.

  (* ONE OPENING: the three slots of [vpn]'s path as pure memory facts about
     [σ], with the invariant closed again before returning.  Used once per
     read node; nothing is held across. *)
  Lemma kpt_open_slots (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) (σ : mstate) (E : coPset) :
    ↑kptN ⊆ E ->
    ptree_maps t0 vpn p2 p1 p0 ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗ gen_heap_interp σ.(mem) ={E}=∗
      (∃ q0 : mword 64,
         ⌜ pt_slot_mem σ (pt_addr2 t0 vpn) p2 /\
           pt_slot_mem σ (pt_addr1 p2 vpn) p1 /\
           pt_slot_mem σ (pt_addr0 p1 vpn) q0 /\
           pte_canon q0 = pte_canon p0 ⌝) ∗
      gen_heap_interp σ.(mem).
  Proof.
    intros HE Hmaps. iIntros "#Hlb0 #Hkinv Hgh".
    iMod (inv_acc E kptN with "Hkinv") as "[>Hbody Hclose]"; [ exact HE | ].
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan.
    destruct (kpt_maps_across t0 t vpn p2 p1 p0 Hcan Hmaps) as (q0 & Hm' & Hq).
    iDestruct (ptree_own_path_mem σ (DfracOwn 1) t vpn p2 p1 q0 Hm'
                 with "Hgh Ht") as %(H2 & H1 & H0).
    (* the addresses are the SNAPSHOT's, and they agree: [ptree_canon]
       preserves [pt_base], so the roots coincide. *)
    assert (Hbase : pt_base t0 = pt_base t).
    { change (pt_base (ptree_canon t0) = pt_base (ptree_canon t)).
      rewrite Hcan. reflexivity. }
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
    iModIntro. iFrame "Hgh". iExists q0. iPureIntro.
    unfold pt_addr2. rewrite Hbase.
    split; [exact H2 |]. split; [exact H1 |]. split; [exact H0 | exact Hq].
  Qed.

  (* [pt_slot_mem] is exactly the per-byte form [read_bytes_of_bytes] wants. *)
  Lemma read_bytes_of_slot (σ : mstate) (a w : mword 64) :
    pt_slot_mem σ a w -> read_bytes σ.(mem) a 8 = Some w.
  Proof.
    intros (Hbytes & _ & _ & _). exact (read_bytes_of_bytes σ.(mem) a 8 w Hbytes).
  Qed.

  (* THE READ NODE, for a slot whose value is PINNED across openings -- i.e.
     levels 2 and 1, which [ptree_maps_canon] preserves exactly.  The
     selector premise says which of the path's three slots this is; it is
     [tauto] at both call sites. *)
  Lemma kpt_slot_node (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) (a w : mword 64) :
    ptree_maps t0 vpn p2 p1 p0 ->
    (forall σ q0,
       pt_slot_mem σ (pt_addr2 t0 vpn) p2 ->
       pt_slot_mem σ (pt_addr1 p2 vpn) p1 ->
       pt_slot_mem σ (pt_addr0 p1 vpn) q0 ->
       pte_canon q0 = pte_canon p0 ->
       pt_slot_mem σ a w) ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) a 8 = Some w⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hmaps Hsel. iIntros "#Hlb0 #Hkinv" (σ) "(Hreg & Hgh & Hdev)".
    iMod (kpt_open_slots root_ppn t0 vpn p2 p1 p0 σ ⊤ ltac:(solve_ndisj) Hmaps
            with "Hlb0 Hkinv Hgh") as "[%Hslots Hgh]".
    destruct Hslots as (q0 & H2 & H1 & H0 & Hq).
    (* the invariant is already closed: everything taken out of it was pure *)
    iMod (fupd_mask_subseteq (∅ : coPset)) as "Hback"; [ set_solver | ].
    iModIntro. iSplitR.
    { iPureIntro. exact (read_bytes_of_slot σ a w (Hsel σ q0 H2 H1 H0 Hq)). }
    iNext. iMod "Hback" as "_". iModIntro. iFrame "Hreg Hgh Hdev".
  Qed.

  (* the two PINNED levels *)
  Lemma kpt_pte2_node (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) :
    ptree_maps t0 vpn p2 p1 p0 ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (pt_addr2 t0 vpn) 8 = Some p2⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hmaps.
    exact (kpt_slot_node root_ppn t0 vpn p2 p1 p0 _ _ Hmaps
             (fun _ _ H2 _ _ _ => H2)).
  Qed.

  Lemma kpt_pte1_node (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) :
    ptree_maps t0 vpn p2 p1 p0 ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) (pt_addr1 p2 vpn) 8 = Some p1⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hmaps.
    exact (kpt_slot_node root_ppn t0 vpn p2 p1 p0 _ _ Hmaps
             (fun _ _ _ H1 _ _ => H1)).
  Qed.

  (* THE LEAF, and it is NOT of the pinned shape.  What comes back is the
     LIVE leaf, which agrees with the snapshot's only up to [pte_canon] --
     another hart may have set A/D between this walk's earlier reads and this
     one.  Stating it any tighter would be false of the machine.

     This is the one place the per-node port changes what a walk lemma can
     say, and it is why [CommonWalk.swp_translate_miss]'s leaf obligation has
     to be relaxed from a pinned [pte0] to this existential before the walk
     can be assembled.  Its downstream premises are ALREADY A/D-quantified
     (the [forall a d, pte_check_ok … (pte_set_ad … a d)] shape that
     [KptShare.tlb_res_pt_translateAddr_at] takes), so the relaxation costs
     the consumers nothing. *)
  Lemma kpt_leaf_node (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 p0 : mword 64) :
    ptree_maps t0 vpn p2 p1 p0 ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        (∃ q0 : mword 64,
           ⌜read_bytes σ.(mem) (pt_addr0 p1 vpn) 8 = Some q0⌝ ∗
           ⌜pte_canon q0 = pte_canon p0⌝) ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hmaps. iIntros "#Hlb0 #Hkinv" (σ) "(Hreg & Hgh & Hdev)".
    iMod (kpt_open_slots root_ppn t0 vpn p2 p1 p0 σ ⊤ ltac:(solve_ndisj) Hmaps
            with "Hlb0 Hkinv Hgh") as "[%Hslots Hgh]".
    destruct Hslots as (q0 & H2 & H1 & H0 & Hq).
    iMod (fupd_mask_subseteq (∅ : coPset)) as "Hback"; [ set_solver | ].
    iModIntro. iSplitR.
    { iExists q0. iPureIntro. split; [exact (read_bytes_of_slot σ _ q0 H0) | exact Hq]. }
    iNext. iMod "Hback" as "_". iModIntro. iFrame "Hreg Hgh Hdev".
  Qed.


  (* ================================================================== *)
  (* THE PATH, OFF THE CLAIM.  A walk has to know [p2] and [p1] BEFORE   *)
  (* it starts (they are the walk's own level-1 and level-0 slot         *)
  (* addresses), and it has to know that all three slots are aligned     *)
  (* in-RAM words before it can discharge the read node's PMA/PMP        *)
  (* premises.  All of that is pinned across openings, so it comes out   *)
  (* of ONE fupd, ahead of the walk:                                     *)
  (*                                                                     *)
  (*   - [pt_base t0], [p2] and [p1] are exact ([ptree_maps_canon]);      *)
  (*   - the three addresses' RAM/alignment facts are state-free (they    *)
  (*     fall out of the slot POINTS-TO, not out of [gen_heap_interp]);   *)
  (*   - the LEAF is delivered only as an A/D variant of the claim's      *)
  (*     word, which is all the invariant knows.                         *)
  (* ================================================================== *)

  (* the address-only half of [pt_slot_mem]: what the PTE read node's
     PMA/PMP premises need, and the half that does not mention a state *)
  Definition kpt_addr_ok (a : mword 64) : Prop :=
    addr_is_ram a /\ addr_is_ram (pa_add a 7) /\
    is_aligned_paddr (Physaddr a) 8 = true.

  Lemma kpt_addr_ok_of_slot (σ : mstate) (a w : mword 64) :
    pt_slot_mem σ a w -> kpt_addr_ok a.
  Proof. intros (_ & H1 & H2 & H3). exact (conj H1 (conj H2 H3)). Qed.

  (* STATE-FREE: the slot's own points-to already carries both ends'
     RAM-ness and the alignment ([slot_mem_of_own] takes the heap only for
     the BYTES).  This is what lets the walk's PMA/PMP premises be settled
     before the first node instead of inside it. *)
  Lemma kpt_addr_ok_own (dq : dfrac) (a w : mword 64) :
    a ↦ₚ₈{dq} w -∗ ⌜kpt_addr_ok a⌝.
  Proof.
    iIntros "Hw".
    iDestruct (phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (phys_word_pointsto_bytes with "Hw") as "Hb".
    iAssert (⌜addr_is_ram (pa_add a 0)⌝)%I as %Hr0.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "Hb0";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (phys_ram with "Hb0"). }
    iAssert (⌜addr_is_ram (pa_add a 7)⌝)%I as %Hr7.
    { iDestruct (big_sepL_lookup _ _ 7%nat 7%nat with "Hb") as "Hb7";
        [rewrite lookup_seq_lt; [reflexivity | lia]|].
      iApply (phys_ram with "Hb7"). }
    iPureIntro. split; [exact (addr_is_ram_pa0 a Hr0) |].
    split; [exact Hr7 | exact Hal].
  Qed.

  Lemma kpt_path_at (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (ppn : mword 44) (kp : kperm) (E : coPset) :
    ↑kptN ⊆ E ->
    kmap_at vpn ppn kp -∗ kpt_lb t0 -∗ kpt_inv root_ppn ={E}=∗
    ∃ (p2 p1 : mword 64) (a d : mword 1),
      ⌜ pt_base t0 = root_ppn /\
        ptree_maps t0 vpn p2 p1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) /\
        kpt_addr_ok (pt_addr2 t0 vpn) /\
        kpt_addr_ok (pt_addr1 p2 vpn) /\
        kpt_addr_ok (pt_addr0 p1 vpn) ⌝.
  Proof.
    intros HE. iIntros "#Hat #Hlb0 #Hkinv".
    iMod (inv_acc E kptN with "Hkinv") as "[>Hbody Hclose]"; [ exact HE | ].
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan.
    pose proof Hspec as Hsp. destruct Hsp as (Hbase & Hall).
    pose proof (Hall vpn) as Hv. rewrite HMlk in Hv.
    destruct Hv as (q2 & q1 & a0 & d0 & Hmaps).
    assert (Hlf : kpt_leaf_pte_of vpn (ppn, kp) = mk_pte ppn (kperm_flags kp))
      by reflexivity.
    rewrite Hlf in Hmaps.
    (* levels 2 and 1 survive the snapshot exactly; the leaf up to A/D *)
    destruct (kpt_maps_across t t0 vpn q2 q1 _ (eq_sym Hcan) Hmaps)
      as (r0 & Hm0 & Hcr).
    destruct (pte_canon_inv _ _ Hcr) as (a1 & d1 & Hr0).
    rewrite pte_set_ad_absorb in Hr0.
    (* the three slots' address facts, off the tree's own points-to *)
    iDestruct (ptree_own_path_ro (DfracOwn 1) t vpn q2 q1 _ Hmaps with "Ht")
      as "(Hs2 & Hs1 & Hs0 & Hrest)".
    iDestruct (kpt_addr_ok_own with "Hs2") as %Ha2.
    iDestruct (kpt_addr_ok_own with "Hs1") as %Ha1.
    iDestruct (kpt_addr_ok_own with "Hs0") as %Ha0.
    iDestruct ("Hrest" with "Hs2 Hs1 Hs0") as "Ht".
    assert (Hb0 : pt_base t0 = pt_base t).
    { change (pt_base (ptree_canon t0) = pt_base (ptree_canon t)).
      rewrite Hcan. reflexivity. }
    assert (Hbt0 : pt_base t0 = root_ppn) by (rewrite Hb0; exact Hbase).
    assert (Ha2' : kpt_addr_ok (pt_addr2 t0 vpn))
      by (unfold pt_addr2; rewrite Hb0; exact Ha2).
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists t, M. iFrame "Ht HM Hlbt". iPureIntro. exact Hspec. }
    iModIntro. iExists q2, q1, a1, d1. iPureIntro. rewrite <- Hr0.
    exact (conj Hbt0 (conj Hm0 (conj Ha2' (conj Ha1 Ha0)))).
  Qed.

  (* ================================================================== *)
  (* THE PTE READ NODE AT THE FRAME.  [PtTreeAdue.swp_checked_mem_read_  *)
  (* pte8] wants exactly what [kpt_slot_node] produces (the atomic-step   *)
  (* fupd) plus the slot's PMA/PMP premises, and                          *)
  (* [PtTreeAdue.swp_read_pte_S] wraps [read_pte] around it.  This is the *)
  (* whole glue: feed it [kpt_pte2_node] / [kpt_pte1_node] and it IS the  *)
  (* level-2 / level-1 read obligation [HartSTrans.swp_translate_miss]     *)
  (* takes.  (The LEAF does not fit -- see the note at the end.)          *)
  (* ================================================================== *)

  Lemma kpt_addr_ok_ram (a : mword 64) : kpt_addr_ok a -> pma_ram_access a 8.
  Proof.
    intros (Hlo & Hhi & _).
    exact (pma_access_ram a 8 7 Hlo Hhi (pma_width_ok 8 eq_refl eq_refl)
             eq_refl eq_refl).
  Qed.

  Lemma kpt_addr_ok_pmp (a paddr0 : mword 64) :
    kpt_addr_ok a ->
    (ram_base + ram_size <= uint paddr0 * 4)%Z ->
    pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4) (Z.mul (uint paddr0) 4)
      (uint a) (uint (to_bits 64 8)) = PMP_Match.
  Proof.
    intros (Hram & Hram7 & _) Hcov.
    assert (Hnw : (uint a + Z.of_nat 7 < 18446744073709551616)%Z).
    { destruct Hram as [_ Hh]. unfold ram_base, ram_size in Hh.
      change (Z.of_nat 7) with 7. lia. }
    assert (Hfit : (uint a + 8 <= ram_base + ram_size)%Z).
    { pose proof (uint_pa_add a 7 Hnw) as Heq.
      destruct Hram7 as [_ Hhi7]. rewrite Heq in Hhi7.
      change (Z.of_nat 7) with 7 in Hhi7.
      unfold ram_base, ram_size in *. lia. }
    apply (ram_pmp_match_w a _ 8);
      [lia | vm_compute; reflexivity | | exact Hfit | exact Hcov].
    destruct Hram as [Hlo _]. exact Hlo.
  Qed.

  Lemma swp_read_pte_kpt (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (a w : mword 64) (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    kpt_addr_ok a ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        ⌜read_bytes σ.(mem) a 8 = Some w⌝ ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (read_pte (Physaddr a) 8)
      (fun r => ⌜r = Values.Ok w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord HR
      Hcov Hallow Hok.
    iIntros "#Hcert Hrw Hro Hmem".
    iApply (swp_read_pte_S Drw Dro Df rs a w with "Hcert Hrw Hro").
    iIntros "Hrw Hro".
    iApply (swp_checked_mem_read_pte8 Drw Dro Df rs a pmar0 pcfg paddr w
              Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
              (kpt_addr_ok_pmp a (vec_access_dec paddr 0) Hok Hcov)
              HR Hallow (kpt_addr_ok_ram a Hok)
              (proj1 Hok) (proj2 (proj2 Hok))
              with "Hcert Hrw Hro Hmem").
  Qed.

  (* the [tlb] cell's read-after-write, which the tree did not have (only the
     idempotence/collapse laws) and which the landing snapshot needs *)
  Lemma register_lookup_set_tlb (rs : regstate) (v : type_of_register tlb) :
    register_lookup tlb (register_set tlb v rs) = v.
  Proof.
    destruct rs. unfold register_set, register_lookup. cbn. reflexivity.
  Qed.

  (* the LEAF seam, re-keyed on the CLAIM's word.  [kpt_leaf_node] states the
     variance against the SNAPSHOT's leaf (an A/D variant of the claim's);
     [pte_canon_set_ad] collapses that to the claim's own word, which is the
     predicate every [_ex] lemma above is indexed by. *)
  Lemma kpt_leaf_node_canon (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (p2 p1 leaf0 : mword 64) (a0 d0 : mword 1) :
    ptree_maps t0 vpn p2 p1 (pte_set_ad leaf0 a0 d0) ->
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        (∃ w : mword 64, ⌜read_bytes σ.(mem) (pt_addr0 p1 vpn) 8 = Some w⌝ ∗
                         ⌜pte_canon w = pte_canon leaf0⌝) ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)).
  Proof.
    intros Hmaps. iIntros "#Hlb0 #Hkinv" (σ) "Hσ".
    iPoseProof (kpt_leaf_node root_ppn t0 vpn p2 p1 _ Hmaps with "Hlb0 Hkinv")
      as "H".
    iMod ("H" $! σ with "Hσ") as "[Hex Hcl]".
    iDestruct "Hex" as (w) "[%Hrb %Hc]".
    iModIntro. iFrame "Hcl". iExists w. iPureIntro.
    split; [exact Hrb |]. rewrite Hc. apply pte_canon_set_ad.
  Qed.

  (* the LEAF READ at the frame, predicate-indexed: [swp_read_pte_kpt]'s twin
     over [PtTreeAdue.swp_checked_mem_read_pte8_ex]. *)
  Lemma swp_read_pte_kpt_ex (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (a : mword 64) (P : mword 64 -> Prop)
      (pmar0 : list PMA_Region)
      (pcfg : type_of_register pmpcfg_n) (paddr : type_of_register pmpaddr_n) :
    Drw ## Dro ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    kpt_addr_ok a ->
    gen_cert -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    (∀ σ, mstate_interp σ ={⊤,∅}=∗
        (∃ w, ⌜read_bytes σ.(mem) a 8 = Some w⌝ ∗ ⌜P w⌝) ∗
        ▷ (|={∅,⊤}=> mstate_interp σ)) -∗
    swp (read_pte (Physaddr a) 8)
      (fun r => ∃ w, ⌜r = Values.Ok w⌝ ∗ ⌜P w⌝ ∗
                hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro).
  Proof.
    intros Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord HR
      Hcov Hallow Hok.
    iIntros "#Hcert Hrw Hro Hmem".
    iApply (swp_read_pte_S_ex Drw Dro Df rs a P with "Hcert Hrw Hro").
    iIntros "Hrw Hro".
    iApply (swp_checked_mem_read_pte8_ex Drw Dro Df rs a pmar0 pcfg paddr P
              Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
              (kpt_addr_ok_pmp a (vec_access_dec paddr 0) Hok Hcov)
              HR Hallow (kpt_addr_ok_ram a Hok)
              (proj1 Hok) (proj2 (proj2 Hok))
              with "Hcert Hrw Hro Hmem").
  Qed.

  (* ================================================================== *)
  (* THE WRITE SEAM.  A read seam is PURE -- [pt_slot_mem] is a fact      *)
  (* about [σ.(mem)] -- so it opens and closes the invariant with          *)
  (* nothing held.  A WRITE is not: it must take [ptree_own] out of        *)
  (* [kptN], update the leaf slot, and put a DIFFERENT tree back, all      *)
  (* inside the one node.  What makes that sound is exactly what makes     *)
  (* the exec-side absorption sound: the Svadu write-back only ever sets   *)
  (* A/D, so the CANONICAL table does not move                            *)
  (* ([PtTree.ptree_canon_set_leaf]) -- the snapshot is re-derived by a    *)
  (* rewrite, with no ghost update -- and the mapping spec survives        *)
  (* ([KptTree.kpt_tree_spec_gen_set_leaf]).                               *)
  (*                                                                      *)
  (* The node is told the word MEMORY holds (the conditional-write rule    *)
  (* learns it from the reservation); it does not need it -- the tree's    *)
  (* own [↦ₚ₈] names the live leaf -- but the obligation's shape carries   *)
  (* it, so it is taken and dropped.                                      *)
  (* ================================================================== *)
  Lemma kpt_leaf_write_node (root_ppn : mword 44) (t0 : ptree) (vpn : mword 27)
      (ppn : mword 44) (kp : kperm) (p2 p1 : mword 64) (a0 d0 : mword 1)
      (m0 m0' : mword 64) :
    ptree_maps t0 vpn p2 p1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0) ->
    (exists a d : mword 1,
       m0' = pte_set_ad (mk_pte ppn (kperm_flags kp)) a d) ->
    kmap_at vpn ppn kp -∗ kpt_lb t0 -∗ kpt_inv root_ppn -∗
    (∀ σ, ⌜read_bytes σ.(mem) (pt_addr0 p1 vpn) 8 = Some m0⌝ -∗
        mstate_interp σ ={⊤,∅}=∗
        ▷ (|={∅,⊤}=> mstate_interp
             (MState σ.(sregs)
                (write_bytes σ.(mem) (pt_addr0 p1 vpn) 8
                   (Interface.WriteReq.value
                      (mwrite_req8_con (pt_addr0 p1 vpn)
                         (autocast (T := mword) m0'))))
                σ.(mdev)) ∗ True)).
  Proof.
    intros Hmaps Hvar.
    iIntros "#Hat #Hlb0 #Hkinv" (σ) "%Hrb (Hreg & Hgh & Hdev)".
    iMod (inv_acc ⊤ kptN with "Hkinv") as "[>Hbody Hclose]"; [ solve_ndisj | ].
    iEval (rewrite /kpt_body) in "Hbody".
    iDestruct "Hbody" as (t M) "(Ht & #Hlbt & HM & %Hspec)".
    iDestruct (kmap_at_lookup with "HM Hat") as %HMlk.
    iDestruct (kpt_lb_agree t0 t with "Hlb0 Hlbt") as %Hcan.
    destruct (kpt_maps_across t0 t vpn p2 p1 _ Hcan Hmaps) as (q0 & Hm' & Hq).
    destruct (pte_canon_inv (mk_pte ppn (kperm_flags kp)) q0
                ltac:(rewrite Hq; apply pte_canon_set_ad)) as (a1 & d1 & Hq0).
    destruct Hvar as (a & d & Hm0').
    assert (Hset : m0' = pte_set_ad q0 a d)
      by (rewrite Hq0 pte_set_ad_absorb; exact Hm0').
    (* the live leaf slot, at full ownership *)
    iDestruct (ptree_own_path_upd (DfracOwn 1) t vpn p2 p1 q0 Hm' with "Ht")
      as "(Hs2 & Hs1 & Hs0 & Hback)".
    iMod (phys_word_pointsto_write σ.(mem) (pt_addr0 p1 vpn) q0 m0'
            with "Hgh Hs0") as "[Hgh Hs0]".
    iDestruct ("Hback" $! m0' with "Hs2 Hs1 Hs0") as "Ht".
    (* the canonical table does not move, so the snapshot is a rewrite *)
    assert (Hcan' : ptree_canon (ptree_set_leaf t vpn m0') = ptree_canon t).
    { rewrite Hset. exact (ptree_canon_set_leaf t vpn p2 p1 q0 a d Hm'). }
    iDestruct (kpt_lb_canon t (ptree_set_leaf t vpn m0') (eq_sym Hcan')
                 with "Hlbt") as "#Hlb'".
    assert (Hspec' : kpt_tree_spec_gen root_ppn M (ptree_set_leaf t vpn m0')).
    { rewrite Hset.
      apply (kpt_tree_spec_gen_set_leaf root_ppn M t vpn (ppn, kp) p2 p1 q0 a d
               Hspec Hm' HMlk).
      exists a1, d1. exact Hq0. }
    iMod ("Hclose" with "[Ht HM]") as "_".
    { iNext. iExists (ptree_set_leaf t vpn m0'), M.
      iFrame "Ht HM Hlb'". iPureIntro. exact Hspec'. }
    iMod (fupd_mask_subseteq (∅ : coPset)) as "Hback2"; [ set_solver | ].
    iModIntro. iNext. iMod "Hback2" as "_". iModIntro.
    iSplitL; [| done].
    cbn [Interface.WriteReq.value mwrite_req8_con].
    rewrite TypeCasts.cast_N_refl autocast_id.
    iFrame "Hreg Hgh Hdev".
  Qed.

  (* ================================================================== *)
  (* [swp_translate_kpt] -- THE SHARED KERNEL TABLE'S TRANSLATION, one    *)
  (* node at a time.  This is [KptShare.tlb_res_pt_translateAddr_at]'s     *)
  (* swp twin: same claim-keyed interface, same three outcomes, but the    *)
  (* invariant is opened PER NODE instead of once around the whole         *)
  (* translation, and the walk's leaf is therefore EXISTENTIAL at every    *)
  (* opening ([HartSTrans.swp_translate_hit_ex] / [_miss_ex]).             *)
  (*                                                                      *)
  (* Everything the walk needs off the claim comes out of ONE fupd ahead   *)
  (* of it ([kpt_path_at]): the two upper words, the leaf's A/D variance,   *)
  (* and the three slots' RAM/alignment facts.  The reads are then the      *)
  (* pinned seams at levels 2/1 and the canon-keyed one at level 0; the     *)
  (* write-back's re-read is the same canon-keyed seam and its conditional  *)
  (* write is [kpt_leaf_write_node].                                        *)
  (*                                                                      *)
  (* THE FOOTPRINT COMPANIONS ARE PROVED, NOT TAKEN.  The swp layer needs   *)
  (* [goodb] certificates for the two PTE tests that the exec layer never   *)
  (* did.  They live in [KptGoodb]: at the claim's LEAF off the canonical   *)
  (* class, at the two INTERNAL levels off [ptree_maps]' own [pte_valid] +  *)
  (* [pte_ptr] pair -- and NOT off [pte_ptr] alone, which is false.          *)
  (* ================================================================== *)
  Lemma swp_translate_kpt
      (acc : MemoryAccessType mem_payload)
      (Drw Dro : gset register) (Df : register -> dfrac)
      (rs : regstate) (dst : mstate) (Db : register -> bool)
      (root_ppn : mword 44) (va pa satp0 menvcfg0 : mword 64)
      (ppn : mword 44) (kp : kperm)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pmar0 : list PMA_Region) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (rr : option resv) :
    Drw ## Dro ->
    (mstatus : register) ∈ Drw ∪ Dro ->
    (cur_privilege : register) ∈ Drw ∪ Dro ->
    (satp : register) ∈ Drw ∪ Dro ->
    (tlb : register) ∈ Drw ->
    (pma_regions : register) ∈ Drw ∪ Dro ->
    (pmpcfg_n : register) ∈ Drw ∪ Dro ->
    (pmpaddr_n : register) ∈ Drw ∪ Dro ->
    (htif_tohost_base : register) ∈ Drw ∪ Dro ->
    (forall r : register, Db r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, Db r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    (forall r : register, D_leafchk r = true -> r ∈ Drw ∪ Dro) ->
    (forall r : register, D_leafchk r = true ->
       register_lookup r rs = register_lookup r dst.(sregs)) ->
    register_lookup cur_privilege rs = Supervisor ->
    register_lookup satp rs = satp0 ->
    register_lookup tlb rs = tlbvec ->
    register_lookup htif_tohost_base rs = None ->
    register_lookup pma_regions rs = pmar0 ->
    register_lookup pmpcfg_n rs = pcfg ->
    register_lookup pmpaddr_n rs = paddr ->
    register_lookup mstatus rs = register_lookup mstatus dst.(sregs) ->
    register_lookup misa dst.(sregs) = MISA_C ->
    register_lookup menvcfg dst.(sregs) = menvcfg0 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_ADUE menvcfg0) ('b"1") = true ->
    exec (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor) dst
      = Some (Supervisor, dst) ->
    goodb Db (effectivePrivilege acc (register_lookup mstatus dst.(sregs)) Supervisor)
      dst = true ->
    exec (is_shadow_stack_access acc) dst = Some (false, dst) ->
    goodb Db (is_shadow_stack_access acc) dst = true ->
    exec (translationMode Supervisor) dst = Some (Sv39, dst) ->
    goodb Db (translationMode Supervisor) dst = true ->
    autocast (T := mword) (satp_to_ppn (autocast (T := mword) satp0 : mword 64))
      = root_ppn ->
    zero_extend' 16 (satp_to_asid (autocast (T := mword) satp0 : mword 64))
      = (mword_of_int 0 : mword 16) ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
      (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
                          (Z.sub 39 1) 0)) = false ->
    zero_extend' 64 (concat_vec ppn
      (subrange_vec_dec (bits_of_virtaddr (Virtaddr va))
         (Z.sub pagesize_bits 1) 0)) = pa ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_R (vec_access_dec pcfg 0)) ('b"1") = true ->
    eq_vec (_get_Pmpcfg_ent_W (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    pma_allows_ram pmar0 ->
    (* the claim's permission check, A/D-quantified (KptShare's premise) *)
    (forall (a d : mword 1) (mxr do_sum : bool),
       pte_check_ok acc Supervisor mxr do_sum
         (pte_set_ad (mk_pte ppn (kperm_flags kp)) a d)) ->
    kmap_at (svpn_of va) ppn kp -∗
    kpt_inv root_ppn -∗
    tlb_snap_ok tlbvec -∗
    gen_cert -∗
    resv_frag cpu_id rr -∗
    hreg_frame rs Drw -∗
    hreg_frame_ro Df rs Dro -∗
    swp (translateAddr (Virtaddr va) acc)
      (fun r => ⌜r = Values.Ok (Physaddr pa, PBMT_PMA, init_ext_ptw)⌝ ∗
                ∃ rsf : regstate,
                  ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                  hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                  tlb_snap_ok (register_lookup tlb rsf) ∗
                  resv_any cpu_id).
  Proof.
    intros Hdisj HDmst HDpriv HDsatp HWtlb HDpma HDcfg HDaddr HDhtif
      HDb Hag HDlc Haglc Hcp Hsatp Htlb Hhtif Hpma Hpcfg Hpaddr Hmstag
      Hmisa Hmenv HPBMTE HADUE Heff Heffg Hss Hssg Htm Htmg Hppn Hasid
      Hcanon Hident HA Hord HR HW Hcov Hpallow Hchk.
    iIntros "#Hat #Hkinv Hsnap #Hcert Hfrag Hrw Hro".
    (* NOT [set_solver] (optimization.md): a single membership in a union of
       two [gset register] VARIABLES costs ~24 s whatever the override does --
       it was the sixth most expensive statement in the tree.  [HWtlb] is
       already [tlb ∈ Drw], so the union step is one lemma. *)
    assert (HDtlb : (tlb : register) ∈ Drw ∪ Dro)
      by (apply elem_of_union_l; exact HWtlb).
    iDestruct "Hsnap" as (t0) "(%Htlbok0 & #Hlb0)".
    iApply swp_fupd.
    iMod (kpt_path_at root_ppn t0 (svpn_of va) ppn kp ⊤ ltac:(solve_ndisj)
            with "Hat Hlb0 Hkinv") as (p2 p1 a0 d0) "%Hpath".
    destruct Hpath as (Hbase & Hmaps & Hok2 & Hok1 & Hok0).
    iModIntro.
    (* the two internal levels' pure facts, off [ptree_maps] *)
    pose proof Hmaps as Hmapsd.
    destruct Hmapsd as (c1 & c0 & _ & _ & _ & _ & _ & _ & _ &
                        Hv2 & Hn2 & Hv1 & Hn1 & _ & _ & _ & _).
    (* the swp layer's footprint companions, which the exec layer never
       needed.  At the two INTERNAL levels they come off [ptree_maps]'
       own [pte_valid] + [pte_ptr] pair ([KptGoodb.pte_ptr_goodb_invalid];
       [pte_ptr] alone would be FALSE -- see that file's header), and at
       the claim's LEAF off the canonical class, with the shadow-stack
       tail taken from the caller's own [Hssg]. *)
    pose proof (pte_ptr_goodb_invalid p2 Hv2 Hn2) as Higptr2.
    pose proof (pte_ptr_goodb_invalid p1 Hv1 Hn1) as Higptr1.
    pose proof (kperm_canon_goodb_invalid ppn kp) as Higleaf.
    pose proof (fun w Hc => kperm_canon_goodb_check ppn kp w acc Db dst Hssg Hc)
      as Hchkgleaf.
    (* the leaf predicate, and its three closure facts *)
    assert (HP0i : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall s, exec (pte_is_invalid (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                                (ext_bits_of_PTE w)) s = Some (false, s)).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_valid. }
    assert (HP0nl : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_is_non_leaf (Mk_PTE_Flags (subrange_vec_dec w 7 0)) = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_leaf. }
    assert (HP0chk : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              forall (mxr do_sum : bool) s,
                exec (check_PTE_permission acc Supervisor mxr do_sum
                        (Mk_PTE_Flags (subrange_vec_dec w 7 0))
                        (ext_bits_of_PTE w) tt) s
                = Some (PTE_Check_Success tt, s)).
    { intros w Hc mxr do_sum. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply (Hchk a d mxr do_sum). }
    assert (HP0N : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              eq_vec (_get_PTE_Ext_N (ext_bits_of_PTE w)) ('b"1") = false).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_no_napot. }
    assert (HP0pb : forall w : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_pbmt0 w).
    { intros w Hc. destruct (pte_canon_inv _ _ Hc) as (a & d & ->).
      apply kperm_variant_pbmt0. }
    assert (HPvar : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              exists a d : mword 1, w = pte_set_ad w' a d).
    { intros w w' Hw Hw'.
      destruct (pte_canon_inv _ _ Hw) as (a & d & ->).
      destruct (pte_canon_inv _ _ Hw') as (a' & d' & ->).
      exists a, d. symmetry. apply pte_set_ad_absorb. }
    assert (HPupd : forall w w' : mword 64,
              pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)) ->
              update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w' ->
              pte_canon w' = pte_canon (mk_pte ppn (kperm_flags kp))).
    { intros w w' Hw Hu. rewrite autocast_id in Hu.
      destruct (update_PTE_Bits_set_ad _ _ _ Hu) as (a & d & ->).
      rewrite pte_canon_set_ad. exact Hw. }
    (* [P0] admits the claim's own A/D variant, which is the tree's leaf *)
    assert (HP0leaf : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a0 d0)
                      = pte_canon (mk_pte ppn (kperm_flags kp)))
      by apply pte_canon_set_ad.
    (* the three slot addresses, in the walk's spelling *)
    assert (Ha2 : pt_addr2 t0 (svpn_of va)
                  = u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18))
      by (unfold pt_addr2; rewrite Hbase; reflexivity).
    (* the head *)
    iApply (swp_translateAddr_pt_front_ex acc Supervisor Drw Dro Df rs dst
              (∃ rsf : regstate,
                 ⌜ rsf = rs \/ exists tv, rsf = register_set tlb tv rs ⌝ ∗
                 hreg_frame rsf Drw ∗ hreg_frame_ro Df rsf Dro ∗
                 tlb_snap_ok (register_lookup tlb rsf) ∗ resv_any cpu_id)%I
              Db (svpn_of va) root_ppn ppn satp0 va pa
              Hdisj HDmst HDpriv HDsatp HDb Hag Hcp Hsatp Hmstag
              Heff Heffg Hss Hssg Htm Htmg Hppn Hasid Hcanon eq_refl Hident
              with "Hcert Hrw Hro [Hfrag]").
    iIntros (mxr do_sum) "Hrw Hro".
    (* the read seams *)
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               ⌜read_bytes σ.(mem)
                  (u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18)) 8
                  = Some p2⌝ ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrd2".
    { rewrite <- Ha2.
      iApply (kpt_pte2_node root_ppn t0 (svpn_of va) p2 p1 _ Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               ⌜read_bytes σ.(mem)
                  (u_pte_addr (u_next_base p2) (subrange_vec_dec (svpn_of va) 17 9)) 8
                  = Some p1⌝ ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrd1".
    { iApply (kpt_pte1_node root_ppn t0 (svpn_of va) p2 p1 _ Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               (∃ w : mword 64,
                  ⌜read_bytes σ.(mem)
                     (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                     = Some w⌝ ∗
                  ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝) ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrdl".
    { iApply (kpt_leaf_node_canon root_ppn t0 (svpn_of va) p2 p1 _ a0 d0 Hmaps
                with "Hlb0 Hkinv"). }
    iAssert (∀ σ, mstate_interp σ ={⊤,∅}=∗
               (∃ w : mword 64,
                  ⌜read_bytes σ.(mem)
                     (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                     = Some w⌝ ∗
                  ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝) ∗
               ▷ (|={∅,⊤}=> mstate_interp σ))%I as "Hrdx".
    { iApply (kpt_leaf_node_canon root_ppn t0 (svpn_of va) p2 p1 _ a0 d0 Hmaps
                with "Hlb0 Hkinv"). }
    (* the WRITE seam, in the shape the [_ex] write-back takes *)
    iAssert (∀ (w w' : mword 64),
               ⌜pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp))⌝ -∗
               ⌜update_PTE_Bits (autocast (T := mword) w : mword 64) acc = Some w'⌝ -∗
               ∀ σ, ⌜read_bytes σ.(mem)
                       (u_pte_addr (u_next_base p1) (subrange_vec_dec (svpn_of va) 8 0)) 8
                       = Some w⌝ -∗
                   mstate_interp σ ={⊤,∅}=∗
                   ▷ (|={∅,⊤}=> mstate_interp
                        (MState σ.(sregs)
                           (write_bytes σ.(mem)
                              (u_pte_addr (u_next_base p1)
                                 (subrange_vec_dec (svpn_of va) 8 0)) 8
                              (Interface.WriteReq.value
                                 (mwrite_req8_con
                                    (u_pte_addr (u_next_base p1)
                                       (subrange_vec_dec (svpn_of va) 8 0))
                                    (autocast (T := mword) w'))))
                           σ.(mdev)) ∗ True))%I as "Hwr".
    { iIntros (w w') "%HPw %Hu".
      iApply (kpt_leaf_write_node root_ppn t0 (svpn_of va) ppn kp p2 p1 a0 d0
                w w' Hmaps
                ltac:(destruct (pte_canon_inv _ _ (HPupd w w' HPw Hu))
                        as (a & d & Hw'); exists a, d; exact Hw')
                with "Hat Hlb0 Hkinv"). }
    (* the three read obligations, in the shape the walk takes *)
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr root_ppn
                                (subrange_vec_dec (svpn_of va) 26 18))) 8)
                 (fun r => ⌜r = Values.Ok p2⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrd2]" as "Hob2".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt Drw Dro Df rs
                (u_pte_addr root_ppn (subrange_vec_dec (svpn_of va) 26 18)) p2
                pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow
                ltac:(rewrite <- Ha2; exact Hok2)
                with "Hcert Hrw Hro Hrd2"). }
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr (u_next_base p2)
                                (subrange_vec_dec (svpn_of va) 17 9))) 8)
                 (fun r => ⌜r = Values.Ok p1⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrd1]" as "Hob1".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt Drw Dro Df rs _ p1 pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow Hok1
                with "Hcert Hrw Hro Hrd1"). }
    iAssert (hreg_frame rs Drw -∗ hreg_frame_ro Df rs Dro -∗
               swp (read_pte (Physaddr (u_pte_addr (u_next_base p1)
                                (subrange_vec_dec (svpn_of va) 8 0))) 8)
                 (fun r => ∃ q0, ⌜r = Values.Ok q0⌝ ∗
                           ⌜pte_canon q0 = pte_canon (mk_pte ppn (kperm_flags kp))⌝ ∗
                           hreg_frame rs Drw ∗ hreg_frame_ro Df rs Dro))%I
      with "[Hrdl]" as "Hob0".
    { iIntros "Hrw Hro".
      iApply (swp_read_pte_kpt_ex Drw Dro Df rs _ _ pmar0 pcfg paddr
                Hdisj HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr
                HA Hord HR Hcov Hpallow Hok0
                with "Hcert Hrw Hro Hrdl"). }
    (* the dispatch: hit or miss, off the caller's own TLB vector *)
    destruct (vec_access_dec tlbvec (tlb_hash (__id 39) (svpn_of va)))
      as [ent |] eqn:Hslot.
    - destruct (Htlbok0 (svpn_of va) ent Hslot)
        as (vpn0 & q2 & q1 & qp0 & a' & d' & Hm0 & Hh & Hent).
      destruct (decide (vpn0 = svpn_of va)) as [-> | Hne].
      + (* HIT on this vpn's own (A/D-stale) entry *)
        destruct (ptree_maps_det t0 (svpn_of va) q2 q1 qp0 p2 p1 _ Hm0 Hmaps)
          as (-> & -> & ->).
        rewrite pte_set_ad_absorb in Hent. subst ent.
        assert (HPq0 : pte_canon (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                       = pte_canon (mk_pte ppn (kperm_flags kp)))
          by apply pte_canon_set_ad.
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_translate_hit_ex acc Supervisor mxr do_sum
                      Drw Dro Df rs dst Db (svpn_of va) (mword_of_int 0) root_ppn
                      tlbvec p2 p1 (pte_set_ad (mk_pte ppn (kperm_flags kp)) a' d')
                      menvcfg0
                      (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                      pmar0 pcfg paddr rr
                      Hdisj HWtlb Htlb Hslot
                      (uwe_match_self (svpn_of va) p2 p1 _)
                      HDb Hag HDlc Haglc
                      (Hchk a' d' mxr do_sum) (Hchkgleaf _ HPq0 mxr do_sum Db)
                      (HP0pb _ HPq0) HPq0 HPvar HPupd
                      HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                      Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                      Hmisa Hmenv HPBMTE HADUE
                      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                      (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                      HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                      (proj1 Hok0) (proj2 (proj2 Hok0))
                      with "Hcert Hfrag Hrw Hro Hrdx Hwr"). }
        iIntros (v) "(%rsf & -> & %Hshape & Hrw & Hro & Hany)".
        rewrite (kperm_variant_ppn' ppn kp a' d').
        iSplitR; [done |]. iExists rsf. iFrame "Hrw Hro Hany".
        destruct Hshape as [-> | (q0f & HPf & ->)].
        * iSplitR; [iPureIntro; left; reflexivity |].
          rewrite Htlb. iExists t0. by iFrame "Hlb0".
        * iSplitR; [iPureIntro; right; eexists; reflexivity |].
          rewrite register_lookup_set_tlb. iExists t0. iFrame "Hlb0". iPureIntro.
          apply (tlb_ok_pt_fill (mword_of_int 0) t0 tlbvec (svpn_of va) p2 p1 _ q0f
                   Hmaps (HPvar q0f _ HPf HP0leaf) Htlbok0).
      + (* a FOREIGN entry in the slot: the tag rejects it, so the walk runs *)
        iApply (swp_mono with "[] [-]").
        2:{ iApply (swp_translate_miss_ex acc Supervisor mxr do_sum
                      Drw Dro Df rs dst (svpn_of va) root_ppn (mword_of_int 0)
                      p2 p1 menvcfg0
                      (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                      tlbvec (Some ent) pmar0 pcfg paddr rr
                      Hv2 Hn2 Hv1 Hn1 Higptr1 Higptr2
                      HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                      Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                      HPvar HPupd
                      Hdisj HDtlb HWtlb Htlb Hslot
                      ltac:(rewrite Hent;
                            exact (uwe_match_other vpn0 (svpn_of va) q2 q1 _
                                     (mword_of_int 0) Hne))
                      HDlc Haglc Hmisa Hmenv HPBMTE HADUE
                      HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                      (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                      HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                      (proj1 Hok0) (proj2 (proj2 Hok0))
                      with "Hcert Hfrag Hrw Hro Hob2 Hob1 Hob0 Hrdx Hwr"). }
        iIntros (v) "(%q0 & %q0f & %HPq0 & %HPq0f & -> & Hrw & Hro & Hany)".
        destruct (pte_canon_inv _ _ HPq0) as (aq & dq & Hq0).
        rewrite Hq0. rewrite (kperm_variant_ppn' ppn kp aq dq).
        iSplitR; [done |].
        iExists _. iFrame "Hrw Hro Hany".
        iSplitR; [iPureIntro; right; eexists; reflexivity |].
        rewrite register_lookup_set_tlb. iExists t0. iFrame "Hlb0". iPureIntro.
        rewrite Htlb.
        apply (tlb_ok_pt_fill (mword_of_int 0) t0 tlbvec (svpn_of va) p2 p1 _ _
                 Hmaps (HPvar _ _ HPq0f HP0leaf) Htlbok0).
    - (* an EMPTY slot: the walk runs *)
      iApply (swp_mono with "[] [-]").
      2:{ iApply (swp_translate_miss_ex acc Supervisor mxr do_sum
                    Drw Dro Df rs dst (svpn_of va) root_ppn (mword_of_int 0)
                    p2 p1 menvcfg0
                    (fun w => pte_canon w = pte_canon (mk_pte ppn (kperm_flags kp)))
                    tlbvec None pmar0 pcfg paddr rr
                    Hv2 Hn2 Hv1 Hn1 Higptr1 Higptr2
                    HP0i HP0nl (fun w Hw => HP0chk w Hw mxr do_sum) HP0N
                    Higleaf (fun w Hw => Hchkgleaf w Hw mxr do_sum)
                    HPvar HPupd
                    Hdisj HDtlb HWtlb Htlb Hslot I
                    HDlc Haglc Hmisa Hmenv HPBMTE HADUE
                    HDpma HDcfg HDaddr HDhtif Hhtif Hpma Hpcfg Hpaddr HA Hord
                    (kpt_addr_ok_pmp _ (vec_access_dec paddr 0) Hok0 Hcov)
                    HR HW Hpallow (kpt_addr_ok_ram _ Hok0)
                    (proj1 Hok0) (proj2 (proj2 Hok0))
                    with "Hcert Hfrag Hrw Hro Hob2 Hob1 Hob0 Hrdx Hwr"). }
      iIntros (v) "(%q0 & %q0f & %HPq0 & %HPq0f & -> & Hrw & Hro & Hany)".
      destruct (pte_canon_inv _ _ HPq0) as (aq & dq & Hq0).
      rewrite Hq0. rewrite (kperm_variant_ppn' ppn kp aq dq).
      iSplitR; [done |].
      iExists _. iFrame "Hrw Hro Hany".
      iSplitR; [iPureIntro; right; eexists; reflexivity |].
      rewrite register_lookup_set_tlb. iExists t0. iFrame "Hlb0". iPureIntro.
      rewrite Htlb.
      apply (tlb_ok_pt_fill (mword_of_int 0) t0 tlbvec (svpn_of va) p2 p1 _ _
               Hmaps (HPvar _ _ HPq0f HP0leaf) Htlbok0).
  Qed.

End kptnode.

(* =====================================================================
   WHAT [swp_translate_kpt] USED TO TAKE AS A PREMISE, AND WHERE IT WENT.

   Two [goodb] certificates -- one for [pte_is_invalid], one for
   [check_PTE_permission] -- used to be premises here, and travelled up
   through [SRegime.kpt_swp_side] to the caller.  They are the FOOTPRINT
   companions of the two PTE tests: the exec layer never needed them (it
   evaluates against a reference state), the swp layer does (a stretch may
   only read registers in its frame).  Both tests DO read [menvcfg] --
   [pte_is_invalid] on the reserved-encoding branch (V=1, R=0, W=1, X=0)
   and [check_PTE_permission] on the shadow-stack branch (R=0, W=1, X=0) --
   and [pte_is_invalid] reads [misa] on the [not (pbmt matches)] branch, so
   neither is register-free in general.

   They are now PROVED, in [KptGoodb], and discharged inside the proof
   below.  The INTERNAL-LEVEL one is the interesting case: the premise
   used to be conditioned on [pte_is_non_leaf] alone, and in that shape it
   is FALSE -- a non-leaf word with PBMT = 'b"11" really does reach the
   Svpbmt probe and read [misa].  What kills that branch is VALIDITY, not
   pointer-ness: [PtTree.pte_ptr_ext_zero] reads the whole 10-bit
   extension field off [pte_valid] + [pte_ptr], and [ptree_maps] carries
   both at every internal level.  So the premise did not need weakening,
   it needed deleting.

   Everything else the note that used to stand here called missing is
   built: the leaf read is PREDICATE-indexed all the way down
   ([PtTreeAdue]'s [_ex] nodes, [CommonWalk.UserWalkEx],
   [HartSTrans.swp_translate_{hit,miss}_ex]), and the write-back arm has
   its [kptN] seam ([kpt_leaf_write_node]).  The A/D-monotone snapshot the
   note proposed as "one change kills both" was NOT needed and was not
   made: [ptree_canon] agreement plus a predicate-indexed read is enough,
   and it keeps the tree layer's existing A/D-quantified interface. *)
