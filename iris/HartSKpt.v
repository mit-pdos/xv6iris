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

   That is not a gap in the reconciliation, it is the machine.  And the
   existing page-table machinery already has the right shape for it:
   [KptShare.tlb_res_pt_translateAddr_at]'s permission premise is
   [forall (a d : mword 1) …, pte_check_ok … (pte_set_ad … a d)] -- already
   quantified over the A/D bits, because the exec walk could not pin them
   either.  Nothing downstream has to change to tolerate the per-node
   version; the leaf is simply delivered up to [pte_canon]. *)
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
Require Import HartSTrans.
Local Open Scope Z_scope.

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

End kptnode.
