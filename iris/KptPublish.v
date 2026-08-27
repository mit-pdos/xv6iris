(* KptPublish.v -- THE CANON PIN'S PUBLICATION GATE, at the TREE
   (tso-machine-flip.md A6.70's ruling; tso-pin-memo.md §5.6(b)).

   [KptShare.kpt_inv_alloc] wants [kptree_own B 2 (DfracOwn 1) t], i.e.
   [PtTree.ptree_own_at (KTier B)], whose slots are
   [TsoCtx.phys_ledger_word_pin] -- elements with the option arm SET.  A
   table under construction is [ptree_own_at (UTier xi)], whose slots are
   [ctx_phys_word_pointsto] -- elements pinned to [None] BY DEFINITION.
   A6.70 measured that NOTHING in the tree moves one to the other, and this
   file is that move: [CtxPinMint]'s word gate, folded over the 512 slots of
   a node and then over the node's children.

   THE BOUND IS THE PUBLISHER'S OWN VIEW, which is what makes the receipt
   free by construction: hart 0 reaches [__sync_synchronize] -- a
   [Barrier_RISCV_rw_rw], which [RiscvLang.fence_drains] DRAINS -- so its
   view sits at the log top, [length glog <= gtv cpu_id] holds, and
   [TsoCtx.hart_view_lb_get] hands back both the [hart_view_lb] the pin's
   readers compare against and (through [TsoGhost.view_lb_llb]) the [llb]
   that makes [B] a legal log position.  This is the interp-side dual of
   [TsoCtxAbsorbLb.ctx_absorb_lb].

   THE TOKEN IS THREADED, NOT CONSUMED.  A6.70's statement carries
   [own_context xi] and it is kept here for the recorded shape, but the
   update does not need it: a slot's clean/dirty bit is a ghost-map
   FRAGMENT, and abandoning one leaves [own_context]'s dirty-watermark arm
   (a statement about the AUTHORITY's domain) untouched.  The token in and
   out is therefore documentation of WHOSE table is being published, not a
   resource cost -- and [kptree_publish_bare] below is the same gate
   without it, for a publisher that has parked.

   >>> THE SITE EXISTS NOW (A6.72).  [HartBarrier.wp_hart_barrier] is A6.5's
   ratified barrier leaf and [WpSconfFencePub.wp_fence_pub_s_sconf] lifts it
   to the sconf tier; [kptree_publish] below is stated in exactly
   [HartBarrier.pub_step]'s shape, so `fence rw,rw` runs it.  What A6.71
   recorded as "no site" was true of the tree as it stood and is no longer.

   THE PREMISE IS THE DRAIN, NOT THE LOG TOP, and that is what makes the
   fence enough: [own_pub h glog <= gtv cpu_id].  A6.70's recorded statement
   asked for [length glog <= gtv cpu_id], which only an AMO delivers; the
   token's own dirty-set justification ([TsoGhost.dirty_ok]) closes the gap,
   because every byte of the publisher's context is either clean under its
   bound or its own message.  See [CtxPinMint.ctx_phys_ts_own]. <<< *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap ghost_map mono_nat.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost TsoCtx.
Require Import PtreeType CommonWalk PtAdBits PtTree.
Require Import CtxPinMint.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* §0 A WORD IS IN ITS OWN FAMILY -- the mint's per-byte obligation, and    *)
(* the reason the publication needs no premise about the table's CONTENT.  *)
(* At an interior slot the family is eight singletons; at a leaf, byte 0's *)
(* is the four-element A/D class, which contains the leaf's own byte by    *)
(* [PtAdBits.pte_set_ad_refl] ("every word is an A/D variant of itself").  *)
(* ---------------------------------------------------------------------- *)
Lemma pte_slot_set_self (w : mword 64) (j : nat) :
  nth_byte w j ∈ pte_slot_set w j.
Proof.
  rewrite /pte_slot_set. destruct j as [|j'].
  - cbn [Nat.eqb]. destruct (pte_nonleafb w).
    + apply TsoMemPa.byteset_sing_in.
    + destruct (pte_set_ad_refl w) as (a & d & Hw).
      rewrite {1}Hw. apply pte_ad_byte0_set_ad.
  - cbn [Nat.eqb]. apply TsoMemPa.byteset_sing_in.
Qed.

Section KptPublish.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* THE DRAIN PREMISE, named once: "this hart's view has passed its own
     last publication".  [HartBarrier]'s leaf establishes it at a draining
     fence ([TsoMemPa.fence_post]) and nothing else in the tree does. *)
  Local Notation drained g :=
    (own_pub (hart_agent cpu_id) g.(glog) <= g.(gtv) cpu_id)%nat.

  (* ------------------------------------------------------------------ *)
  (* §1 THE SLOT RUN.  Left-to-right, so the interp and the TOKEN thread;  *)
  (* the list is generic because a node's slots and a node's children are  *)
  (* indexed the same way ([seqZ 0 512]) and the tree recursion below      *)
  (* reuses the shape.                                                    *)
  (* ------------------------------------------------------------------ *)
  Lemma pt_slots_publish (g : gstate) (xi : CtxId)
      (l : list Z) (F : Z -> Arch.pa) (W : Z -> mword 64) :
    drained g ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] i ∈ l, pt_slot_own (UTier xi) (F i) (DfracOwn 1) (W i)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] i ∈ l, pt_slot_own (KTier (g.(gtv) cpu_id)) (F i) (DfracOwn 1) (W i)).
  Proof.
    intros Hdr. induction l as [|i l IH].
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hs Hl]".
      rewrite (pt_slot_own_ctx (UTier xi) xi (F i) (DfracOwn 1) (W i) eq_refl).
      iMod (ctx_phys_word_pin_mint g xi (F i) (W i) (pte_slot_set (W i)) Hdr
              (fun j (_ : (j < 8)%nat) => pte_slot_set_self (W i) j)
              with "Hgh Hint Hrun Hs") as "(Hgh & Hint & Hrun & Hs)".
      iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
      iModIntro. iFrame "Hgh Hint Hrun Hl".
      rewrite (pt_slot_own_ker (KTier (g.(gtv) cpu_id)) (g.(gtv) cpu_id)
                 (F i) (DfracOwn 1) (W i) eq_refl).
      iExact "Hs".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 ONE NODE.  The identity claim ([pt_node_claim]) does not mention  *)
  (* the tier at all -- Coq does not even generalize the section's [PTT]  *)
  (* over it -- so it crosses for nothing, which is the same fact that    *)
  (* makes [pt_slot_own_forget] a one-liner at both arms.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma pt_page_publish (g : gstate) (xi : CtxId) (t : ptree) :
    drained g ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    pt_page_own_at (UTier xi) (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    pt_page_own_at (KTier (g.(gtv) cpu_id)) (DfracOwn 1) t.
  Proof.
    intros Hdr. iIntros "Hgh Hint Hrun [#Hcl Hs]".
    iMod (pt_slots_publish g xi (seqZ 0 512)
            (fun i => u_pte_addr (pt_base t) (mword_of_int i))
            (fun i => pt_ents t (mword_of_int i)) Hdr with "Hgh Hint Hrun Hs")
      as "(Hgh & Hint & Hrun & Hs)".
    iModIntro. iFrame "Hgh Hint Hrun". rewrite /pt_page_own_at.
    iFrame "Hcl Hs".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §3 THE CHILDREN, with the level's induction hypothesis handed in as  *)
  (* a Coq-level premise -- the tree's recursion is on the LEVEL and the  *)
  (* big-op's on the LIST, so the two inductions cannot be one.           *)
  (* ------------------------------------------------------------------ *)
  Lemma pt_kids_publish (g : gstate) (xi : CtxId) (P Q : ptree -> iProp Σ)
      (l : list Z) (K : Z -> option ptree) :
    (forall c : ptree,
       ⊢ gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
         tso_interp_at riscv_eraGS g -∗ own_context xi -∗ P c ==∗
         gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
         tso_interp_at riscv_eraGS g ∗ own_context xi ∗ Q c) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] i ∈ l, match K i with Some c => P c | None => emp end) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] i ∈ l, match K i with Some c => Q c | None => emp end).
  Proof.
    intros Hstep. induction l as [|i l IH].
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hc Hl]".
      destruct (K i) as [c|].
      + iMod (Hstep c with "Hgh Hint Hrun Hc") as "(Hgh & Hint & Hrun & Hc)".
        iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hc Hl".
      + iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hl".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4 THE WHOLE TREE.                                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma ptree_own_publish (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    drained g ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) t.
  Proof.
    intros Hdr. revert t. induction lvl as [|lvl IH]; intros t.
    - iIntros "Hgh Hint Hrun [Hp _]".
      iMod (pt_page_publish g xi t Hdr with "Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iModIntro. iFrame "Hgh Hint Hrun Hp".
    - iIntros "Hgh Hint Hrun [Hp Hk]".
      iMod (pt_page_publish g xi t Hdr with "Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iMod (pt_kids_publish g xi
              (fun c => ptree_own_at (UTier xi) lvl (DfracOwn 1) c)
              (fun c => ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) c)
              (seqZ 0 512) (fun i => pt_kids t (mword_of_int i)) IH
              with "Hgh Hint Hrun Hk") as "(Hgh & Hint & Hrun & Hk)".
      iModIntro. iFrame "Hgh Hint Hrun Hp Hk".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §5 THE GATE, in the shape [HartBarrier.pub_step] runs.  Its premise   *)
  (* is EXACTLY what the barrier leaf establishes, its bound is the        *)
  (* publisher's own view, and both receipts come out of the interp the    *)
  (* leaf already handed over -- so nothing is invented and nothing is     *)
  (* assumed.  [gen_heap_interp] is the one addition to A6.70's recorded   *)
  (* statement and it is forced: [TsoCtx.ledger_pin_mint] needs the FLAT   *)
  (* cell's value to discharge [v ∈ Sv] against the map the interp's tie   *)
  (* speaks about (A6.71 amendment 1).                                     *)
  (* ------------------------------------------------------------------ *)
  Lemma kptree_publish (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    drained g ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) t ∗
    llb loglen_name (g.(gtv) cpu_id) ∗ hart_view_lb (g.(gtv) cpu_id).
  Proof.
    intros Hdr. iIntros "Hgh Hint Hrun Ht".
    iDestruct (hart_view_lb_now g with "Hint") as "[Hint #Hvlb]".
    iMod (ptree_own_publish g xi lvl t Hdr with "Hgh Hint Hrun Ht")
      as "(Hgh & Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun Ht Hvlb".
    iEval (rewrite hart_view_lb_unseal /hart_view_lb_def) in "Hvlb".
    by iApply view_lb_llb.
  Qed.

End KptPublish.
