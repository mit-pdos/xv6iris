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
   [TsoCtxLedger.hart_view_lb_get] hands back both the [hart_view_lb] the pin's
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
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import TsoMemPa TsoGhost TsoCtx.
Require Import PtreeType CommonWalk PtAdBits PtTree.
Require Import CtxValues.
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
  (* A6.135: the slot's per-byte credential can be a recorded view
     receipt of the boot hart -- what a DRAINED hart-0 publisher has.
     This wraps a common-bound word pin into the anchored slot form. *)
  Lemma kpt_slot_pin_of_word_pin (a : Arch.pa) (w : mword 64) (B : nat) :
    view_lb view_name loglen_name 0%nat B -∗
    phys_ledger_word_pin a (DfracOwn 1) w B (pte_slot_set w) -∗
    kpt_slot_pin a (DfracOwn 1) w B.
  Proof.
    iIntros "#Hv [%Hal Hb]". rewrite /kpt_slot_pin.
    iSplitR; [by iPureIntro |].
    iApply (big_sepL_impl with "Hb").
    iIntros "!>" (k j Hkj) "(%t & Hp)".
    iExists B, t. iFrame "Hp".
    iSplitR; [by iPureIntro |]. iRight. iRight. iExact "Hv".
  Qed.

  Lemma pt_slots_publish (g : gstate) (xi : CtxId)
      (l : list Z) (F : Z -> Arch.pa) (W : Z -> mword 64) :
    drained g ->
    view_lb view_name loglen_name 0%nat (g.(gtv) cpu_id) -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] i ∈ l, pt_slot_own (UTier xi) (F i) (DfracOwn 1) (W i)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] i ∈ l, pt_slot_own (KTier (g.(gtv) cpu_id)) (F i) (DfracOwn 1) (W i)).
  Proof.
    intros Hdr. induction l as [|i l IH].
    - iIntros "#Hv0 Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "#Hv0 Hgh Hint Hrun [Hs Hl]".
      rewrite (pt_slot_own_ctx (UTier xi) xi (F i) (DfracOwn 1) (W i) eq_refl).
      iMod (ctx_phys_word_pin_mint g xi (F i) (W i) (pte_slot_set (W i)) Hdr
              (fun j (_ : (j < 8)%nat) => pte_slot_set_self (W i) j)
              with "Hgh Hint Hrun Hs") as "(Hgh & Hint & Hrun & Hs)".
      iMod (IH with "Hv0 Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
      iModIntro. iFrame "Hgh Hint Hrun Hl".
      rewrite (pt_slot_own_ker (KTier (g.(gtv) cpu_id)) (g.(gtv) cpu_id)
                 (F i) (DfracOwn 1) (W i) eq_refl).
      iApply (kpt_slot_pin_of_word_pin (F i) (W i) (g.(gtv) cpu_id)
                with "Hv0 Hs").
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §2 ONE NODE.  The identity claim ([pt_node_claim]) does not mention  *)
  (* the tier at all -- Coq does not even generalize the section's [PTT]  *)
  (* over it -- so it crosses for nothing, which is the same fact that    *)
  (* makes [pt_slot_own_forget] a one-liner at both arms.                 *)
  (* ------------------------------------------------------------------ *)
  Lemma pt_page_publish (g : gstate) (xi : CtxId) (t : ptree) :
    drained g ->
    view_lb view_name loglen_name 0%nat (g.(gtv) cpu_id) -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    pt_page_own_at (UTier xi) (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    pt_page_own_at (KTier (g.(gtv) cpu_id)) (DfracOwn 1) t.
  Proof.
    intros Hdr. iIntros "#Hv0 Hgh Hint Hrun [#Hcl Hs]".
    iMod (pt_slots_publish g xi (seqZ 0 512)
            (fun i => u_pte_addr (pt_base t) (mword_of_int i))
            (fun i => pt_ents t (mword_of_int i)) Hdr
            with "Hv0 Hgh Hint Hrun Hs")
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

  (* the same fold with the per-child step as a PERSISTENT WAND, for a
     caller whose step closes over resources of its own (A6.135: the
     drained telescope's recorded receipt, the boot telescope's hart
     identity). *)
  Lemma pt_kids_publish_w (g : gstate) (xi : CtxId) (P Q : ptree -> iProp Σ)
      (l : list Z) (K : Z -> option ptree) :
    □ (∀ c : ptree,
         gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
         tso_interp_at riscv_eraGS g -∗ own_context xi -∗ P c ==∗
         gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
         tso_interp_at riscv_eraGS g ∗ own_context xi ∗ Q c) -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] i ∈ l, match K i with Some c => P c | None => emp end) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] i ∈ l, match K i with Some c => Q c | None => emp end).
  Proof.
    iIntros "#Hstep". iInduction l as [|i l] "IHl".
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hc Hl]".
      destruct (K i) as [c|].
      + iMod ("Hstep" $! c with "Hgh Hint Hrun Hc")
          as "(Hgh & Hint & Hrun & Hc)".
        iMod ("IHl" with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hc Hl".
      + iMod ("IHl" with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
        iModIntro. iFrame "Hgh Hint Hrun Hl".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* §4 THE WHOLE TREE.                                                   *)
  (* ------------------------------------------------------------------ *)
  Lemma ptree_own_publish (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    drained g ->
    view_lb view_name loglen_name 0%nat (g.(gtv) cpu_id) -∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) t.
  Proof.
    intros Hdr. revert t. induction lvl as [|lvl IH]; intros t.
    - iIntros "#Hv0 Hgh Hint Hrun [Hp _]".
      iMod (pt_page_publish g xi t Hdr with "Hv0 Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iModIntro. iFrame "Hgh Hint Hrun Hp".
    - iIntros "#Hv0 Hgh Hint Hrun [Hp Hk]".
      iMod (pt_page_publish g xi t Hdr with "Hv0 Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iAssert (□ ∀ c : ptree,
                 gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
                 tso_interp_at riscv_eraGS g -∗ own_context xi -∗
                 ptree_own_at (UTier xi) lvl (DfracOwn 1) c ==∗
                 gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
                 tso_interp_at riscv_eraGS g ∗ own_context xi ∗
                 ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) c)%I
        as "#Hstep".
      { iIntros "!>" (c). iApply (IH c with "Hv0"). }
      iMod (pt_kids_publish_w g xi
              (fun c => ptree_own_at (UTier xi) lvl (DfracOwn 1) c)
              (fun c => ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) c)
              (seqZ 0 512) (fun i => pt_kids t (mword_of_int i))
              with "Hstep Hgh Hint Hrun Hk") as "(Hgh & Hint & Hrun & Hk)".
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
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (g.(gtv) cpu_id)) lvl (DfracOwn 1) t ∗
    llb loglen_name (g.(gtv) cpu_id) ∗ hart_view_lb (g.(gtv) cpu_id).
  Proof.
    intros Hdr H0. iIntros "Hgh Hint Hrun Ht".
    iDestruct (hart_view_lb_now g with "Hint") as "[Hint #Hvlb]".
    iAssert (view_lb view_name loglen_name 0%nat (g.(gtv) cpu_id))%I
      as "#Hv0".
    { rewrite -H0.
      iEval (rewrite hart_view_lb_unseal /hart_view_lb_def) in "Hvlb".
      iExact "Hvlb". }
    iMod (ptree_own_publish g xi lvl t Hdr with "Hv0 Hgh Hint Hrun Ht")
      as "(Hgh & Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun Ht Hvlb".
    iEval (rewrite hart_view_lb_unseal /hart_view_lb_def) in "Hvlb".
    by iApply view_lb_llb.
  Qed.

  (* ================================================================== *)
  (* §6 THE DRAIN-FREE GATE, AT THE LOG TOP (A6.106).                     *)
  (*                                                                     *)
  (* §5's premise has no site: [main]'s only barrier is `fence rw,w`      *)
  (* ([Barrier_RISCV_rw_w], [fence_drains] FALSE) -- see                  *)
  (* [CtxPinMint]'s §3b for the measurement.  This arm publishes at the   *)
  (* LOG TOP instead, which the mint obligation is happy with and which   *)
  (* costs no premise at all.                                            *)
  (*                                                                     *)
  (* WHAT IT DOES NOT HAND BACK is [hart_view_lb]: the publisher's own    *)
  (* view is behind its own buffered stores and no fence moves it.  The   *)
  (* [llb] still comes out ([TsoCtx.tso_interp_loglen_llb], A6.105), so   *)
  (* [KptShare.kpt_inv_alloc]'s premise is met and [kpt_bound B] is shot; *)
  (* what defers is the [view_lb] half of [KptShare.kpt_creds].          *)
  (*                                                                     *)
  (* [pt_kids_publish] is REUSED VERBATIM -- it is P/Q-generic and its     *)
  (* [own_context] thread is inert, which is why this arm keeps the token *)
  (* in its telescope even though the byte mint no longer wants it.       *)
  (* ================================================================== *)
  (* ================================================================== *)
  (* §6 THE BOOT GATE, AT THE SLOTS' OWN STAMPS (A6.135).                 *)
  (*                                                                     *)
  (* §5's drain premise has no site on hart 0's boot path (`fence rw,w`  *)
  (* does not drain -- CtxPinMint §3b), and A6.106's log-top arm gave     *)
  (* hart 0 no read credential at all (A6.134).  This arm mints every     *)
  (* byte at ITS OWN WRITE STAMP, so the mint obligation is [t <= t] --   *)
  (* UNCONDITIONAL: no drain, no log top -- and the slot records, per     *)
  (* byte, the boot hart's own-message anchor ([CtxValues.cv_own], off    *)
  (* the token's dirty registry) or its bound/view receipt.  Every floor  *)
  (* is under [length glog], which becomes the tree's global bound and    *)
  (* the [llb] that [KptShare.kpt_inv_alloc] wants.  Hart 0 then reads    *)
  (* through [CtxValues.cv_boot_cred]'s boot arm with NO view receipt.    *)
  (* ================================================================== *)
  Lemma ctx_phys_byte_publish_boot (g : gstate) (xi : CtxId)
      (a : Arch.pa) (v : bv 8) (Sv : TsoMemPa.byteset) :
    hart_agent cpu_id = 0%nat ->
    v ∈ Sv ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ctx_phys_pointsto xi a (DfracOwn 1) v ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    (∃ Ba t : nat, ⌜(Ba <= length g.(glog))%nat⌝ ∗
       phys_ledger_pin a (DfracOwn 1) v t Ba Sv ∗
       (⌜Ba = 0%nat⌝ ∨ CtxValues.cv_own 0%nat a Ba ∨
        view_lb view_name loglen_name 0%nat Ba)).
  Proof.
    intros H0 Hv. iIntros "Hgh Hint Hrun Hb".
    rewrite ctx_phys_pointsto_unseal /ctx_phys_pointsto_def.
    iDestruct "Hb" as (t) "(Hpt & Hts & Hbit)".
    iDestruct (tso_interp_ts_le g a (DfracOwn 1)
                 ((t, TsoMemPa.ts_pay_none) : TsoMemPa.ts_elem)
                 with "Hint Hts") as %Htlen.
    cbn in Htlen.
    iDestruct (CtxValues.cv_latest g a (DfracOwn 1) v t
                 with "Hint Hgh Hpt Hts") as %Hlat.
    iMod (ledger_pin_mint g a v t t Sv (Nat.le_refl t) Hv
            with "Hgh Hint [Hpt Hts]") as "(Hgh & Hint & Hpin)".
    { rewrite /phys_ledger_at. iFrame "Hpt Hts". }
    destruct t as [|i].
    - iModIntro. iFrame "Hgh Hint Hrun".
      iExists 0%nat, 0%nat. iFrame "Hpin".
      iSplitR; [iPureIntro; lia |]. iLeft. by iPureIntro.
    - destruct Hlat as [Hbyte _].
      rewrite /TsoMemPa.log_byte in Hbyte.
      destruct (g.(glog) !! i) as [m|] eqn:Hlog; last done.
      rewrite own_context_unseal /own_context_def.
      iDestruct "Hrun"
        as (Btok K W D) "(Hat & #HK & %HBK & #HW & %HDW & #Hoks)".
      iDestruct "Hbit" as "[#Hcln | #Hdirty]".
      + (* CLEAN under the token's bound: the hart's own view receipt *)
        iDestruct "Hat" as "[Hbnd Hd]".
        iDestruct (TsoGhost.llb_valid with "Hbnd Hcln") as %HtB.
        iDestruct (TsoGhost.view_lb_le view_name loglen_name
                     (hart_agent cpu_id) K (S i) ltac:(lia) with "HK")
          as "#HvSi".
        iModIntro. iFrame "Hgh Hint".
        iSplitL "Hbnd Hd".
        { iExists Btok, K, W, D. iFrame "Hbnd Hd HK HW Hoks".
          iSplit; by iPureIntro. }
        iExists (S i), (S i). iFrame "Hpin".
        iSplitR; [by iPureIntro |].
        iRight. iRight. iEval (rewrite -H0). iExact "HvSi".
      + (* DIRTY: the token's registry decides *)
        iDestruct (TsoGhost.dset_lookup with "[Hat] [Hdirty]") as %HinD.
        { iDestruct "Hat" as "[_ $]". }
        { iExact "Hdirty". }
        iDestruct (big_sepS_elem_of _ _ _ HinD with "Hoks") as "#Hok".
        iDestruct "Hok" as "[%Hle | Hown]".
        * (* under the bound: view receipt again *)
          cbn in Hle.
          iDestruct (TsoGhost.view_lb_le view_name loglen_name
                       (hart_agent cpu_id) K (S i) ltac:(lia) with "HK")
            as "#HvSi".
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hat".
          { iExists Btok, K, W, D. iFrame "Hat HK HW Hoks".
            iSplit; by iPureIntro. }
          iExists (S i), (S i). iFrame "Hpin".
          iSplitR; [by iPureIntro |].
          iRight. iRight. iEval (rewrite -H0). iExact "HvSi".
        * (* the hart's OWN MESSAGE: the anchor *)
          iDestruct "Hown" as (i' m') "(%Hii & #Hm & %Htid)".
          cbn in Hii. injection Hii as <-.
          iAssert (⌜g.(glog) !! i = Some m'⌝)%I as %Hlog'.
          { iApply (CtxValues.cv_msg_lookup with "Hint Hm"). }
          rewrite Hlog in Hlog'. injection Hlog' as <-.
          iModIntro. iFrame "Hgh Hint".
          iSplitL "Hat".
          { iExists Btok, K, W, D. iFrame "Hat HK HW Hoks".
            iSplit; by iPureIntro. }
          iExists (S i), (S i). iFrame "Hpin".
          iSplitR; [by iPureIntro |].
          iRight. iLeft. iExists i, m, v.
          iSplitR; [by iPureIntro |].
          iSplitR; [iExact "Hm" |].
          iSplit; iPureIntro; [exact Hbyte | rewrite Htid; exact H0].
  Qed.

  Lemma ctx_phys_bytes_publish_boot (g : gstate) (xi : CtxId)
      (a : Arch.pa) (n : nat) (f : nat -> bv 8)
      (Sf : nat -> TsoMemPa.byteset) :
    hart_agent cpu_id = 0%nat ->
    (forall j : nat, (j < n)%nat -> f j ∈ Sf j) ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] j ∈ seq 0 n, ctx_phys_pointsto xi (pa_add a j) (DfracOwn 1) (f j))
    ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] j ∈ seq 0 n, ∃ Ba t : nat, ⌜(Ba <= length g.(glog))%nat⌝ ∗
       phys_ledger_pin (pa_add a j) (DfracOwn 1) (f j) t Ba (Sf j) ∗
       (⌜Ba = 0%nat⌝ ∨ CtxValues.cv_own 0%nat (pa_add a j) Ba ∨
        view_lb view_name loglen_name 0%nat Ba)).
  Proof.
    intros H0. induction n as [|n IH]; intros Hf.
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite seq_S !big_sepL_app /=.
      iIntros "Hgh Hint Hrun [Hb [Hlast _]]".
      iMod (IH ltac:(intros j Hj; apply Hf; lia) with "Hgh Hint Hrun Hb")
        as "(Hgh & Hint & Hrun & Hb)".
      iMod (ctx_phys_byte_publish_boot g xi (pa_add a n) (f n) (Sf n) H0
              (Hf n ltac:(lia)) with "Hgh Hint Hrun Hlast")
        as "(Hgh & Hint & Hrun & Hlast)".
      iModIntro. iFrame "Hgh Hint Hrun Hb Hlast".
  Qed.

  Lemma kpt_slot_publish_boot (g : gstate) (xi : CtxId)
      (a : Arch.pa) (w : bv 64) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ctx_phys_word_pointsto xi a (DfracOwn 1) w ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    kpt_slot_pin a (DfracOwn 1) w (length g.(glog)).
  Proof.
    intros H0. iIntros "Hgh Hint Hrun Hw".
    iDestruct (ctx_phys_word_pointsto_aligned_p with "Hw") as %Hal.
    iDestruct (ctx_phys_word_pointsto_bytes with "Hw") as "Hb".
    iMod (ctx_phys_bytes_publish_boot g xi a 8 (nth_byte w)
            (pte_slot_set w) H0
            (fun j (_ : (j < 8)%nat) => pte_slot_set_self w j)
            with "Hgh Hint Hrun Hb") as "(Hgh & Hint & Hrun & Hb)".
    iModIntro. iFrame "Hgh Hint Hrun".
    rewrite /kpt_slot_pin. iSplitR; [by iPureIntro |]. iExact "Hb".
  Qed.

  Lemma pt_slots_publish_boot (g : gstate) (xi : CtxId)
      (l : list Z) (F : Z -> Arch.pa) (W : Z -> mword 64) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ([∗ list] i ∈ l, pt_slot_own (UTier xi) (F i) (DfracOwn 1) (W i)) ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ([∗ list] i ∈ l, pt_slot_own (KTier (length g.(glog))) (F i) (DfracOwn 1) (W i)).
  Proof.
    intros H0. induction l as [|i l IH].
    - iIntros "Hgh Hint Hrun Hl". iModIntro. iFrame "Hgh Hint Hrun".
      iExact "Hl".
    - rewrite !big_sepL_cons.
      iIntros "Hgh Hint Hrun [Hs Hl]".
      rewrite (pt_slot_own_ctx (UTier xi) xi (F i) (DfracOwn 1) (W i) eq_refl).
      iMod (kpt_slot_publish_boot g xi (F i) (W i) H0
              with "Hgh Hint Hrun Hs") as "(Hgh & Hint & Hrun & Hs)".
      iMod (IH with "Hgh Hint Hrun Hl") as "(Hgh & Hint & Hrun & Hl)".
      iModIntro. iFrame "Hgh Hint Hrun Hl".
      rewrite (pt_slot_own_ker (KTier (length g.(glog))) (length g.(glog))
                 (F i) (DfracOwn 1) (W i) eq_refl).
      iExact "Hs".
  Qed.

  Lemma pt_page_publish_boot (g : gstate) (xi : CtxId) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    pt_page_own_at (UTier xi) (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    pt_page_own_at (KTier (length g.(glog))) (DfracOwn 1) t.
  Proof.
    intros H0. iIntros "Hgh Hint Hrun [#Hcl Hs]".
    iMod (pt_slots_publish_boot g xi (seqZ 0 512)
            (fun i => u_pte_addr (pt_base t) (mword_of_int i))
            (fun i => pt_ents t (mword_of_int i)) H0 with "Hgh Hint Hrun Hs")
      as "(Hgh & Hint & Hrun & Hs)".
    iModIntro. iFrame "Hgh Hint Hrun". rewrite /pt_page_own_at.
    iFrame "Hcl Hs".
  Qed.

  Lemma ptree_own_publish_boot (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) t.
  Proof.
    intros H0. revert t. induction lvl as [|lvl IH]; intros t.
    - iIntros "Hgh Hint Hrun [Hp _]".
      iMod (pt_page_publish_boot g xi t H0 with "Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iModIntro. iFrame "Hgh Hint Hrun Hp".
    - iIntros "Hgh Hint Hrun [Hp Hk]".
      iMod (pt_page_publish_boot g xi t H0 with "Hgh Hint Hrun Hp")
        as "(Hgh & Hint & Hrun & Hp)".
      iMod (pt_kids_publish g xi
              (fun c => ptree_own_at (UTier xi) lvl (DfracOwn 1) c)
              (fun c => ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) c)
              (seqZ 0 512) (fun i => pt_kids t (mword_of_int i)) IH
              with "Hgh Hint Hrun Hk") as "(Hgh & Hint & Hrun & Hk)".
      iModIntro. iFrame "Hgh Hint Hrun Hp Hk".
  Qed.

  Lemma kptree_publish_boot (g : gstate) (xi : CtxId) (lvl : nat) (t : ptree) :
    hart_agent cpu_id = 0%nat ->
    gen_heap_interp (hG := riscv_memGS) g.(gmem) -∗
    tso_interp_at riscv_eraGS g -∗ own_context xi -∗
    ptree_own_at (UTier xi) lvl (DfracOwn 1) t ==∗
    gen_heap_interp (hG := riscv_memGS) g.(gmem) ∗
    tso_interp_at riscv_eraGS g ∗ own_context xi ∗
    ptree_own_at (KTier (length g.(glog))) lvl (DfracOwn 1) t ∗
    llb loglen_name (length g.(glog)).
  Proof.
    intros H0. iIntros "Hgh Hint Hrun Ht".
    iDestruct (tso_interp_loglen_llb g with "Hint") as "[Hint #Hllb]".
    iMod (ptree_own_publish_boot g xi lvl t H0 with "Hgh Hint Hrun Ht")
      as "(Hgh & Hint & Hrun & Ht)".
    iModIntro. iFrame "Hgh Hint Hrun Ht Hllb".
  Qed.

End KptPublish.
