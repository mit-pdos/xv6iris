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
   The READ and the write-back condition do NOT tolerate it, and that is
   what stands between this file and [swp_translate_kpt]: see the note at
   the end. *)
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
Require Import KptGhost KptShare.
Require Import HartSwp HartLift HartRegNode HartSpan HartGoodb HartEvents HartMStore.
Require Import CommonWalk HartSTrans.
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
  Context `{GEN : GenId} `{CID : CpuId}.

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

End kptnode.

(* =====================================================================
   WHAT IS STILL MISSING FOR [swp_translate_kpt], AND WHY IT IS NOT A
   PROOF PROBLEM.

   The assembly is [PtTreeAdue.swp_translateAddr_pt_front] over
   [HartSTrans.swp_translate_hit] (a cached leaf) or [swp_translate_miss]
   (the walk), with the three read obligations supplied by
   [swp_read_pte_kpt] over the seams above.  Levels 2 and 1 fit exactly.
   The LEAF does not, and neither does the CHOICE OF ARM, and both are the
   same gap:

   THE SNAPSHOT PINS ONLY [ptree_canon], SO THE LIVE LEAF'S A/D BITS ARE
   UNKNOWN.  [KptGhost.kpt_lb] is a one-shot agreement on the A/D-CANONICAL
   table, and [KptTree.kpt_tree_spec_gen] maps an entry as "an A/D variant
   of its class-keyed PTE, for SOME a d".  Neither says which.  Two
   consequences, and no amount of proof effort removes either:

   (a) THE LEAF READ CANNOT BE STATED AT A VALUE.  [kpt_leaf_node] delivers
       [∃ q0, read_bytes … = Some q0 ∗ ⌜pte_canon q0 = pte_canon p0⌝], and
       that is the sharpest TRUE statement.  [PtTreeAdue.swp_checked_mem_
       read_pte8] / [swp_read_pte_S] and, above them, [CommonWalk.swp_rec_
       walk_leaf] all take the read at a FIXED word, and the leaf read node
       is CONSUMED INSIDE [swp_rec_walk_leaf] -- so there is no point at
       which a caller can learn [q0] and only then instantiate.  Hoisting
       the existential to the front of the translation is unsound (each
       opening sees its own live tree, and nothing orders them), and the
       four-way split over [(a, d)] cannot be decided before the node runs.
       The minimal fix is to make the PTE read node PREDICATE-indexed
       instead of value-indexed -- obligation [∃ w, read_bytes … = Some w
       ∧ P w], conclusion [λ r, ∃ w, ⌜r = Ok w ∧ P w⌝ ∗ frames] -- in
       [swp_checked_mem_read_pte8] and [swp_read_pte_S], and then through
       [swp_rec_walk_leaf] / [swp_rec_walk_l1] / [swp_pt_walk_user] /
       [swp_translate_TLB_miss_user] / [HartSTrans.swp_translate_miss].
       The walk's OUTPUT ppn is A/D-stable ([PtAdBits.pte_set_ad_ppn]), so
       only the INSTALLED TLB ENTRY has to carry the word that was read.

   (b) THE NO-WRITE-BACK ARM IS NOT THE ONLY REACHABLE ONE.  [kpt_noupd] is
       true of the A/D-PRESET word and of NO other variant: [update_PTE_
       Bits] fires exactly when A is clear (or, for a store, D).  With the
       bits unpinned the [_upd] arms of [swp_translate_hit] /
       [swp_translate_miss] are live, and they need the [kptN] WRITE seam,
       which does not exist (the read seam is pure -- a write is not).

   ONE CHANGE KILLS BOTH: make the kernel table's snapshot A/D-MONOTONE (a
   lower bound in the A/D order) rather than canonical-only.  The write-back
   only ever SETS bits, and kvmmake presets them ([kperm_flags] IS
   [kperm_flags_ad pc (true, true)] -- 0xCB / 0xC7), so a snapshot taken at
   the boot table pins the live leaf EXACTLY: the leaf read becomes an
   ordinary pinned read (a), [kpt_noupd] discharges the no-write-back
   premise (b), and the shared kernel table needs no write seam at all.
   That is a change to [KptGhost] / [KptShare] / [KptTree], not to this
   file.

   AND THE REGIME FIELD [SRegime.sr_swp_translate] NEEDS ONE MORE THING
   than its recorded shape: the regime's NON-CELL RESIDUE.
   [WpSFrames.s_frames_intro] opens [tlb_res_pt] into the two frames PLUS
   [tlb_snap_ok tlbv ∗ kpt_inv root_ppn], and the kpt instance cannot open
   the table without them -- while [bare_regime] has no such residue.  So
   the record needs a companion field [sr_swp_res : regstate -> iProp Σ]
   ([True] for Bare), taken by [sr_swp_translate] at [rs] and RETURNED AT
   THE LANDING FILE [rsf]: a TLB fill moves [tlbv], and the S-mode wrapper
   cannot rebuild [tlb_res_pt] unless the walk re-establishes
   [tlb_snap_ok] at the new vector (which is exactly what
   [PtTree.tlb_ok_pt_fill] proves).                                    *)
