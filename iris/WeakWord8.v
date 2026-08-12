(** * WeakWord8.v — the [↦w₈] tower (M4-prep)

    THE EIGHT-BYTE TWIN of [WeakInstr]'s [↦w₄] tower and of [WeakStore]'s
    store-window update.  Everything the weak layer owns today is FOUR bytes
    wide — the lock word, the [started] flag — but the kernel's own data is
    mostly eight ([lk->cpu], [lk->name], every pointer, every [uint64]), and
    [WeakLock]'s header names the missing [↦w₈] tower as the reason its
    [lock_state] can only take two of its three values.  This file supplies
    it.

    WHERE THE WIDTH-GENERIC PIECES LIVE.  M4-prep discovered them here; they
    have since MOVED DOWN to the files whose width-4 statements they
    generalise, so that both widths are instances of one statement rather than
    the 8 being an instance of something stated inside the 8's own file:

      - [WeakStore.winsw] / [winsw_lookup_in] / [winsw_lookup_out] /
        [wlat_agree_store_w] — the [n]-fold window insert and the store
        window's pure part at every width.  §4 below is its [n := 8]
        instance; [WeakStore.wins4] is the [n := 4] one.
      - [WeakInstr.wpt_byte_flat_pin] / [wlat_byte_flat_gen] — the one-byte
        flat/pinned bridges.  Every eight-fold lemma below is eight one-line
        applications of one of these, and so are [WeakInstr.wpt4_flat_pin]
        and [WeakLock.wlat4_flat_gen].
      - [WeakInstr.wP_load_w] / [wP_mem_w] / [wV_store_w] / [wV_amo_aq_w] /
        [wV_load_w] / [wQ_load_w] / [wQ_store_w] / [wQ_amo_aq_w] — the whole
        [P]/[V]/[Q] family.  §5 below names the [n := 8] instances; the
        [_w_4] lemmas here check the width-4 ones are the [n := 4] instances.

    ===================== WHAT IS IN HERE =====================

      §2  [wlat8] — the bare objective element bundle (the [wlat4] twin), and
          [wpt8] / [↦w₈] — the owned eight-byte points-to, carrying
          8-alignment and wrap-freedom exactly as [wpt4] carries them.
          Eight explicit [∗]s, NOT a [big_sepL]: extraction is then
          [destruct j as [|[|…]]] with no [Φ] to elaborate (the reason
          [WeakInstr] §1b gives, unchanged at width 8).
      §3  the algebra: [wpt8_facts], [wpt8_split], [wpt8_agree], [wpt8_flat],
          [wpt8_pinned], [wpt8_mono], plus the two seam lemmas
          [wpt8_at_elems] / [wlat8_wpt8] and [wlat8_flat_gen].
      §4  THE STORE WINDOW AT WIDTH 8: [wins8], [wlat_agree_store8],
          [wlat8_store_prim] / [wlat8_store_gen] / [wlat8_store], [wpt8_store].
      §5  THE LEAVES: [wP_load8] / [wP_mem8] and the load-side [wwp_ld8] /
          [wwp_ld8_carry]; the store-side [wV_store8] / [wQ_store8] /
          [wwp_sw8_post]; and the acquire-shaped [wwp_amoswap_d_aq_inv], the
          eight-byte twin of [WeakInstr.wwp_amoswap_w_aq_inv].

    NOTHING HERE MENTIONS [riscv_step], so the whole file is expected to be
    closed under the global context (§6). *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
(* [rv64d] is needed for [is_aligned_paddr], which the bundle carries.  It
   SHADOWS [filter] and [not] (durable notes): write [¬], never [not]. *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakFence.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import WeakStore.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 2. The two eight-byte bundles *)

Section word8.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE BARE ELEMENT BUNDLE — an [iProp], hence OBJECTIVE, hence admissible
      inside an invariant with no receipt.  The [wlat4] twin. *)
  Definition wlat8 (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 64) : iProp Σ :=
    (wlat_pointsto (acc_addr a 0) dq t (nth_byte w 0) ∗
     wlat_pointsto (acc_addr a 1) dq t (nth_byte w 1) ∗
     wlat_pointsto (acc_addr a 2) dq t (nth_byte w 2) ∗
     wlat_pointsto (acc_addr a 3) dq t (nth_byte w 3) ∗
     wlat_pointsto (acc_addr a 4) dq t (nth_byte w 4) ∗
     wlat_pointsto (acc_addr a 5) dq t (nth_byte w 5) ∗
     wlat_pointsto (acc_addr a 6) dq t (nth_byte w 6) ∗
     wlat_pointsto (acc_addr a 7) dq t (nth_byte w 7))%I.

  (** THE OWNED EIGHT-BYTE BUNDLES (φ-upgrade §1) — the [WeakStore.wlat4_own]
      / [WeakStore.wpt4_own] twins. *)
  Definition wlat8_own (c : CPU) (a : Arch.pa) (t : nat) (w : bv 64) : iProp Σ :=
    (wlat_elem (acc_addr a 0) (DfracOwn 1) t (nth_byte w 0) ∗
       wown_st c (acc_addr a 0) ∗
     wlat_elem (acc_addr a 1) (DfracOwn 1) t (nth_byte w 1) ∗
       wown_st c (acc_addr a 1) ∗
     wlat_elem (acc_addr a 2) (DfracOwn 1) t (nth_byte w 2) ∗
       wown_st c (acc_addr a 2) ∗
     wlat_elem (acc_addr a 3) (DfracOwn 1) t (nth_byte w 3) ∗
       wown_st c (acc_addr a 3) ∗
     wlat_elem (acc_addr a 4) (DfracOwn 1) t (nth_byte w 4) ∗
       wown_st c (acc_addr a 4) ∗
     wlat_elem (acc_addr a 5) (DfracOwn 1) t (nth_byte w 5) ∗
       wown_st c (acc_addr a 5) ∗
     wlat_elem (acc_addr a 6) (DfracOwn 1) t (nth_byte w 6) ∗
       wown_st c (acc_addr a 6) ∗
     wlat_elem (acc_addr a 7) (DfracOwn 1) t (nth_byte w 7) ∗
       wown_st c (acc_addr a 7))%I.

  Global Instance wlat8_objective a dq t w :
    Objective (⎡wlat8 a dq t w⎤ : vProp Σ).
  Proof. apply _. Qed.

  Global Instance wlat8_timeless a dq t w : Timeless (wlat8 a dq t w).
  Proof. rewrite /wlat8. apply _. Qed.

  (** THE OWNED EIGHT-BYTE POINTS-TO.  Same shape as [wpt4]: 8-alignment (the
      model's access check) and WRAP-FREEDOM of the eight-byte range, then
      eight explicit weak bytes at the log's own keys. *)
  Definition wpt8 (a : Arch.pa) (dq : dfrac) (w : bv 64) : vProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗ ⌜acc_wf a 8⌝ ∗
     (acc_addr a 0) ↦w{dq} nth_byte w 0 ∗
     (acc_addr a 1) ↦w{dq} nth_byte w 1 ∗
     (acc_addr a 2) ↦w{dq} nth_byte w 2 ∗
     (acc_addr a 3) ↦w{dq} nth_byte w 3 ∗
     (acc_addr a 4) ↦w{dq} nth_byte w 4 ∗
     (acc_addr a 5) ↦w{dq} nth_byte w 5 ∗
     (acc_addr a 6) ↦w{dq} nth_byte w 6 ∗
     (acc_addr a 7) ↦w{dq} nth_byte w 7)%I.

  Definition wpt8_own (c : CPU) (a : Arch.pa) (w : bv 64) : vProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗ ⌜acc_wf a 8⌝ ∗
     wpt_own_h c (acc_addr a 0) (nth_byte w 0) ∗
     wpt_own_h c (acc_addr a 1) (nth_byte w 1) ∗
     wpt_own_h c (acc_addr a 2) (nth_byte w 2) ∗
     wpt_own_h c (acc_addr a 3) (nth_byte w 3) ∗
     wpt_own_h c (acc_addr a 4) (nth_byte w 4) ∗
     wpt_own_h c (acc_addr a 5) (nth_byte w 5) ∗
     wpt_own_h c (acc_addr a 6) (nth_byte w 6) ∗
     wpt_own_h c (acc_addr a 7) (nth_byte w 7))%I.

  Lemma wpt8_own_of_wpt8 c a w : wpt8 a (DfracOwn 1) w ⊢ wpt8_own c a w.
  Proof. rewrite /wpt8 /wpt8_own !wpt_own_h_of_wpt. iIntros "$". Qed.

  Lemma wpt8_own_facts c a w :
    wpt8_own c a w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true /\ acc_wf a 8⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

  Lemma wpt8_own_mono c a w ws ws' :
    ws_le ws ws' ->
    vwp_hold (wpt8_own c a w) ws ⊢ vwp_hold (wpt8_own c a w) ws'.
  Proof. apply vwp_hold_mono. Qed.

  Global Instance wpt8_persistent a w : Persistent (wpt8 a DfracDiscarded w).
  Proof. rewrite /wpt8. apply _. Qed.
  Global Instance wpt8_timeless a q w : Timeless (wpt8 a (DfracOwn q) w).
  Proof. rewrite /wpt8. apply _. Qed.

(* ====================================================================== *)
(** ** 3. The algebra *)

  Lemma wpt8_facts a dq w :
    wpt8 a dq w ⊢ ⌜is_aligned_paddr (Physaddr a) 8 = true /\ acc_wf a 8⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

  (** FRACTION SPLIT / JOIN — inherited byte by byte from [wpt_split]. *)
  Lemma wpt8_split a q1 q2 w :
    wpt8 a (DfracOwn (q1 + q2)) w
    ⊣⊢ wpt8 a (DfracOwn q1) w ∗ wpt8 a (DfracOwn q2) w.
  Proof.
    rewrite /wpt8 !wpt_split. iSplit.
    - iIntros "(%Hal & %Hwf & [A0 B0] & [A1 B1] & [A2 B2] & [A3 B3] & [A4 B4] & [A5 B5] & [A6 B6] & [A7 B7])".
      iSplitL "A0 A1 A2 A3 A4 A5 A6 A7";
        (iSplitR; [by iPureIntro|]); (iSplitR; [by iPureIntro|]); iFrame.
    - iIntros "[(%Hal & %Hwf & A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7) (_ & _ & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7)]".
      iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|]. iFrame.
  Qed.

  Lemma wpt8_agree a dq1 w1 dq2 w2 :
    wpt8 a dq1 w1 ∗ wpt8 a dq2 w2 ⊢ ⌜w1 = w2⌝.
  Proof.
    rewrite /wpt8.
    iIntros "[(_ & _ & A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7) (_ & _ & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7)]".
    iDestruct (wpt_agree with "[$A0 $B0]") as %E0.
    iDestruct (wpt_agree with "[$A1 $B1]") as %E1.
    iDestruct (wpt_agree with "[$A2 $B2]") as %E2.
    iDestruct (wpt_agree with "[$A3 $B3]") as %E3.
    iDestruct (wpt_agree with "[$A4 $B4]") as %E4.
    iDestruct (wpt_agree with "[$A5 $B5]") as %E5.
    iDestruct (wpt_agree with "[$A6 $B6]") as %E6.
    iDestruct (wpt_agree with "[$A7 $B7]") as %E7.
    iPureIntro. apply (bv_eq_of_bytes (n := 8%N)). intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  (** THE FLAT + PINNED FACTS over the window, in one pass — eight
      applications of [wpt_byte_flat_pin] and nothing else. *)
  Lemma wpt8_flat_pin (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8 a dq w) (wm_ws σ) -∗
    ⌜acc_wf a 8 /\
     forall j : nat, (j < 8)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j) /\
       pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. rewrite /wpt8 !vwp_hold_sep !vwp_hold_pure.
    iIntros "Hi (%Hal & %Hacc & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 0) 0 Hwf Hacc
                 ltac:(lia) with "Hi H0") as %E0.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 1) 1 Hwf Hacc
                 ltac:(lia) with "Hi H1") as %E1.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 2) 2 Hwf Hacc
                 ltac:(lia) with "Hi H2") as %E2.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 3) 3 Hwf Hacc
                 ltac:(lia) with "Hi H3") as %E3.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 4) 4 Hwf Hacc
                 ltac:(lia) with "Hi H4") as %E4.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 5) 5 Hwf Hacc
                 ltac:(lia) with "Hi H5") as %E5.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 6) 6 Hwf Hacc
                 ltac:(lia) with "Hi H6") as %E6.
    iDestruct (wpt_byte_flat_pin σ a 8 dq (nth_byte w 7) 7 Hwf Hacc
                 ltac:(lia) with "Hi H7") as %E7.
    iPureIntro. split; [exact Hacc|]. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  (** WHAT THE FLAT PROJECTION HOLDS over the window — the fact the SC
      execute-lemma of an eight-byte load wants, verbatim. *)
  Lemma wpt8_flat (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8 a dq w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 8)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_flat_pin σ a dq w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  (** ... and that the window is PINNED for this hart, which is what the weak
      arm of [wstep_ok]'s read obligation asks for. *)
  Lemma wpt8_pinned (σ : wmstate) (a : Arch.pa) (dq : dfrac) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8 a dq w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_flat_pin σ a dq w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj2 (Hall j Hj)).
  Qed.

  (** MONOTONICITY across a step: the bundle is a [vProp], so [vwp_hold_mono]
      carries it over any view growth. *)
  Lemma wpt8_mono a dq w ws ws' :
    ws_le ws ws' -> vwp_hold (wpt8 a dq w) ws ⊢ vwp_hold (wpt8 a dq w) ws'.
  Proof. apply vwp_hold_mono. Qed.

  (** THE DECODE OF AN OWNED BUNDLE: the two pure facts, plus the eight
      elements at eight INDEPENDENT timestamps (a [↦w] binds one per byte —
      see [WeakStore]'s header note; the values are what the caller keeps). *)
  Lemma wpt8_at_elems (a : Arch.pa) (dq : dfrac) (w : bv 64) (ws : wstate) :
    vwp_hold (wpt8 a dq w) ws ⊢
      ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗ ⌜acc_wf a 8⌝ ∗
      ∃ t0 t1 t2 t3 t4 t5 t6 t7 : nat,
        wlat_pointsto (acc_addr a 0) dq t0 (nth_byte w 0) ∗
        wlat_pointsto (acc_addr a 1) dq t1 (nth_byte w 1) ∗
        wlat_pointsto (acc_addr a 2) dq t2 (nth_byte w 2) ∗
        wlat_pointsto (acc_addr a 3) dq t3 (nth_byte w 3) ∗
        wlat_pointsto (acc_addr a 4) dq t4 (nth_byte w 4) ∗
        wlat_pointsto (acc_addr a 5) dq t5 (nth_byte w 5) ∗
        wlat_pointsto (acc_addr a 6) dq t6 (nth_byte w 6) ∗
        wlat_pointsto (acc_addr a 7) dq t7 (nth_byte w 7).
  Proof.
    rewrite /wpt8 !vwp_hold_sep !vwp_hold_pure !wpt_at.
    iIntros "(%Hal & %Hacc & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct "H0" as (t0) "[H0 _]". iDestruct "H1" as (t1) "[H1 _]".
    iDestruct "H2" as (t2) "[H2 _]". iDestruct "H3" as (t3) "[H3 _]".
    iDestruct "H4" as (t4) "[H4 _]". iDestruct "H5" as (t5) "[H5 _]".
    iDestruct "H6" as (t6) "[H6 _]". iDestruct "H7" as (t7) "[H7 _]".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iExists t0, t1, t2, t3, t4, t5, t6, t7. iFrame.
  Qed.

  (** ... and the converse seam: an objective element bundle whose timestamp
      the hart's floor covers IS an owned eight-byte points-to. *)
  Lemma wlat8_wpt8 (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 64)
      (ws : wstate) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    acc_wf a 8 ->
    (forall j : nat, (j < 8)%nat -> (t <= flr (ws_view ws) (acc_addr a j))%nat) ->
    wlat8 a dq t w -∗ vwp_hold (wpt8 a dq w) ws.
  Proof.
    intros Hal Hacc Hfl. rewrite /wlat8 /wpt8 !vwp_hold_sep !vwp_hold_pure.
    iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iSplitL "H0"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 0%nat ltac:(lia)))|].
    iSplitL "H1"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 1%nat ltac:(lia)))|].
    iSplitL "H2"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 2%nat ltac:(lia)))|].
    iSplitL "H3"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 3%nat ltac:(lia)))|].
    iSplitL "H4"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 4%nat ltac:(lia)))|].
    iSplitL "H5"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 5%nat ltac:(lia)))|].
    iSplitL "H6"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 6%nat ltac:(lia)))|].
    by iApply (wpt_at_intro _ _ _ t ws (Hfl 7%nat ltac:(lia))).
  Qed.

  (** READING THE WORD OUT OF THE ELEMENTS, with no ownership, no receipt and
      no view hypothesis — the [WeakLock.wlat4_flat_gen] twin, and the lemma a
      racy leaf uses to name the value its [exec] fact must be supplied at.
      The bundle is HANDED BACK (the conclusion is pure). *)
  Lemma wlat8_flat_gen (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (w : bv 64) :
    wlog_wf (wm_log σ) -> acc_wf a 8 ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat8 a dq t w -∗
    ⌜(forall j : nat, (j < 8)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) /\
     (forall j : nat, (j < 8)%nat -> latest_ts (wm_log σ) (acc_addr a j) = t)⌝.
  Proof.
    intros Hwf Hacc. iIntros "Hi (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 0) 0 Hwf Hacc
                 ltac:(lia) with "Hi H0") as %E0.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 1) 1 Hwf Hacc
                 ltac:(lia) with "Hi H1") as %E1.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 2) 2 Hwf Hacc
                 ltac:(lia) with "Hi H2") as %E2.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 3) 3 Hwf Hacc
                 ltac:(lia) with "Hi H3") as %E3.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 4) 4 Hwf Hacc
                 ltac:(lia) with "Hi H4") as %E4.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 5) 5 Hwf Hacc
                 ltac:(lia) with "Hi H5") as %E5.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 6) 6 Hwf Hacc
                 ltac:(lia) with "Hi H6") as %E6.
    iDestruct (wlat_byte_flat_gen σ a 8 dq t (nth_byte w 7) 7 Hwf Hacc
                 ltac:(lia) with "Hi H7") as %E7.
    iPureIntro. split; intros j Hj;
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      first [exact (proj1 E0)|exact (proj1 E1)|exact (proj1 E2)|exact (proj1 E3)
            |exact (proj1 E4)|exact (proj1 E5)|exact (proj1 E6)|exact (proj1 E7)
            |exact (proj2 E0)|exact (proj2 E1)|exact (proj2 E2)|exact (proj2 E3)
            |exact (proj2 E4)|exact (proj2 E5)|exact (proj2 E6)|exact (proj2 E7)
            |lia].
  Qed.

End word8.

Notation "a ↦w₈{ dq } w" := (wpt8 a dq w)
  (at level 20, format "a  ↦w₈{ dq }  w") : bi_scope.

(* ====================================================================== *)
(** ** 4. The store window at width 8

    [wins8] is the shape eight successive [ghost_map_update]s leave behind, in
    the order §4b performs them (byte 0 first, so its insert is innermost) —
    and it IS [winsw] at [n := 8], which is where its two lookup lemmas and
    its [wlat_agree] come from. *)

Definition wins8 (a : Arch.pa) (T : nat) (v : bv 64)
    (mm : gmap Z (nat * bv 8)) : gmap Z (nat * bv 8) :=
  winsw a T v 8 mm.

Lemma wins8_winsw (a : Arch.pa) T (v : bv 64) mm :
  wins8 a T v mm = winsw a T v (N.to_nat 8) mm.
Proof. reflexivity. Qed.

Lemma wins8_lookup_in (a : Arch.pa) T (v : bv 64) mm (j : nat) :
  (j < 8)%nat -> wins8 a T v mm !! acc_addr a j = Some (T, nth_byte v j).
Proof. intros Hj. rewrite wins8_winsw. apply winsw_lookup_in. lia. Qed.

Lemma wins8_lookup_out (a : Arch.pa) T (v : bv 64) mm (z : Z) :
  ¬ (pa_z a <= z < pa_z a + 8) -> wins8 a T v mm !! z = mm !! z.
Proof.
  intros Hout. rewrite wins8_winsw. apply winsw_lookup_out.
  intros j Hj. rewrite /acc_addr. lia.
Qed.

(** THE EIGHT-BYTE WINDOW UPDATE, pure: the [n := 8] instance of §1. *)
Lemma wlat_agree_store8 img log (tid : option nat) k (a : Arch.pa) (v : bv 64)
    (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid k a 8 v])
             (wins8 a (S (length log)) v mm).
Proof.
  intros Hag. rewrite wins8_winsw.
  by apply (wlat_agree_store_w img log tid k a 8 v mm).
Qed.

Section store8.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE PRIMITIVE.  Eight full-fraction elements over the window, at
      arbitrary pre-timestamps and pre-values, one eight-byte message
      appended: the authority moves to the new log and the eight elements
      come back as a [wlat8] bundle at the message's own timestamp. *)
  Lemma wlat8_store_prim (tid : option nat) k (σ : wmstate) (a : Arch.pa)
      (v : bv 64) (t0 t1 t2 t3 t4 t5 t6 t7 : nat)
      (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
    k <> WCplain ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_pointsto (acc_addr a 0) (DfracOwn 1) t0 b0 -∗
    wlat_pointsto (acc_addr a 1) (DfracOwn 1) t1 b1 -∗
    wlat_pointsto (acc_addr a 2) (DfracOwn 1) t2 b2 -∗
    wlat_pointsto (acc_addr a 3) (DfracOwn 1) t3 b3 -∗
    wlat_pointsto (acc_addr a 4) (DfracOwn 1) t4 b4 -∗
    wlat_pointsto (acc_addr a 5) (DfracOwn 1) t5 b5 -∗
    wlat_pointsto (acc_addr a 6) (DfracOwn 1) t6 b6 -∗
    wlat_pointsto (acc_addr a 7) (DfracOwn 1) t7 b7 ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid k a 8 v]) ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hk. iIntros "Hi H0 H1 H2 H3 H4 H5 H6 H7".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wlat_pointsto /wlat_elem.
    iDestruct "H0" as "[H0 C0]". iDestruct "H1" as "[H1 C1]".
    iDestruct "H2" as "[H2 C2]". iDestruct "H3" as "[H3 C3]".
    iDestruct "H4" as "[H4 C4]". iDestruct "H5" as "[H5 C5]".
    iDestruct "H6" as "[H6 C6]". iDestruct "H7" as "[H7 C7]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 0)
            with "Hauth H0") as "[Hauth H0]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 1)
            with "Hauth H1") as "[Hauth H1]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 2)
            with "Hauth H2") as "[Hauth H2]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 3)
            with "Hauth H3") as "[Hauth H3]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 4)
            with "Hauth H4") as "[Hauth H4]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 5)
            with "Hauth H5") as "[Hauth H5]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 6)
            with "Hauth H6") as "[Hauth H6]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 7)
            with "Hauth H7") as "[Hauth H7]".
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins8 a (S (length (wm_log σ))) v mm), mc. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store8|].
      iPureIntro. by apply wcds_agree_nonplain.
    - rewrite /wlat8 /wlat_pointsto /wlat_elem. iFrame.
  Qed.

  (** THE OWNED PRIMITIVE at width 8 — the [wlat4_store_prim_own] twin. *)
  Lemma wlat8_store_prim_own (c : CPU) k (σ : wmstate) (a : Arch.pa)
      (v : bv 64) (t0 t1 t2 t3 t4 t5 t6 t7 : nat)
      (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_elem (acc_addr a 0) (DfracOwn 1) t0 b0 -∗ wown_st c (acc_addr a 0) -∗
    wlat_elem (acc_addr a 1) (DfracOwn 1) t1 b1 -∗ wown_st c (acc_addr a 1) -∗
    wlat_elem (acc_addr a 2) (DfracOwn 1) t2 b2 -∗ wown_st c (acc_addr a 2) -∗
    wlat_elem (acc_addr a 3) (DfracOwn 1) t3 b3 -∗ wown_st c (acc_addr a 3) -∗
    wlat_elem (acc_addr a 4) (DfracOwn 1) t4 b4 -∗ wown_st c (acc_addr a 4) -∗
    wlat_elem (acc_addr a 5) (DfracOwn 1) t5 b5 -∗ wown_st c (acc_addr a 5) -∗
    wlat_elem (acc_addr a 6) (DfracOwn 1) t6 b6 -∗ wown_st c (acc_addr a 6) -∗
    wlat_elem (acc_addr a 7) (DfracOwn 1) t7 b7 -∗ wown_st c (acc_addr a 7) ==∗
    wlat_interp (wm_img σ)
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat c)) k a 8 v]) ∗
    wlat8_own c a (S (length (wm_log σ))) v.
  Proof.
    iIntros "Hi H0 C0 H1 C1 H2 C2 H3 C3 H4 C4 H5 C5 H6 C6 H7 C7".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wlat_elem.
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 0)
            with "Hauth H0") as "[Hauth H0]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 1)
            with "Hauth H1") as "[Hauth H1]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 2)
            with "Hauth H2") as "[Hauth H2]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 3)
            with "Hauth H3") as "[Hauth H3]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 4)
            with "Hauth H4") as "[Hauth H4]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 5)
            with "Hauth H5") as "[Hauth H5]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 6)
            with "Hauth H6") as "[Hauth H6]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 7)
            with "Hauth H7") as "[Hauth H7]".
    iMod (wcds_store_list c (wwrite_msg (Some (fin_to_nat c)) k a 8 v)
            (wm_log σ)
            [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3;
             acc_addr a 4; acc_addr a 5; acc_addr a 6; acc_addr a 7]
            mc eq_refl (wwrite_msg_zs8 _ _ a v) Hagc
            with "Hc [C0 C1 C2 C3 C4 C5 C6 C7]") as (mc') "(Hc & %Hagc' & Hl)".
    { simpl. iFrame. }
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins8 a (S (length (wm_log σ))) v mm), mc'. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store8|by iPureIntro].
    - simpl. iDestruct "Hl" as "(C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & _)".
      rewrite /wlat8_own /wlat_elem. iFrame.
  Qed.

  (** THE BUNDLE UPDATE at an explicitly described post-state. *)
  Lemma wlat8_store_gen (tid : option nat) k (σ σ' : wmstate) (a : Arch.pa)
      (t : nat) (w v : bv 64) :
    k <> WCplain ->
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid k a 8 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat8 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hk Himg Hlog. rewrite /wlat8.
    iIntros "Hi (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    rewrite Himg Hlog.
    by iMod (wlat8_store_prim tid k σ a v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk
               with "Hi H0 H1 H2 H3 H4 H5 H6 H7") as "[$ $]".
  Qed.

  (** ... and at the interpreter's OWN write post-state, which is what a leaf
      hands its caller.  [acc_wf] is not consumed by the proof (the update is
      entirely on the [Z]-keyed side); it is kept as a premise because every
      caller has it and because it is what makes "the window" the eight bytes
      of [a] rather than a wrapped range. *)
  Lemma wlat8_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (t : nat) (w : bv 64) (v : bv (8 * 8)) :
    ak_latest ak = true ->
    acc_wf a 8 ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat8 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 8 v))
                (wm_log (wwrite_post tid σ ak a 8 v)) ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hlt _. iIntros "Hi Hl".
    iApply (wlat8_store_gen tid (wm_class_of ak (wm_ws σ)) σ
              (wwrite_post tid σ ak a 8 v) a t w v
              ltac:(unfold wm_class_of; rewrite Hlt; discriminate)
              (wwrite_post_img tid σ ak a 8 v) (wwrite_post_log tid σ ak a 8 v)
              with "Hi Hl").
  Qed.

  (** THE STORE RULE FOR THE BUNDLE, owned altitude.  The two pure conjuncts
      ride along unchanged; the post-view side condition is
      [WeakStore.flr_wwrite_post] (already width-generic), i.e. the store's
      own post-state raises the floor at every byte of the window. *)
  Lemma wpt8_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (w : bv 64) (v : bv (8 * 8)) :
    ak_latest ak = true ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt8 a (DfracOwn 1) w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 8 v))
                (wm_log (wwrite_post tid σ ak a 8 v)) ∗
    vwp_hold (wpt8 a (DfracOwn 1) v) (wm_ws (wwrite_post tid σ ak a 8 v)).
  Proof.
    intros Hlt. iIntros "Hi Hpt".
    iDestruct (wpt8_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iMod (wlat8_store_prim tid (wm_class_of ak (wm_ws σ)) σ a v
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ltac:(unfold wm_class_of; rewrite Hlt; discriminate)
            with "Hi H0 H1 H2 H3 H4 H5 H6 H7") as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img tid σ ak a 8 v) (wwrite_post_log tid σ ak a 8 v).
    iFrame "Hi".
    iApply (wlat8_wpt8 a (DfracOwn 1) (S (length (wm_log σ))) v
              _ Hal Hacc with "Hl").
    intros j Hj. apply (flr_wwrite_post tid σ ak a 8 v j). lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4c. THE OWNED ALTITUDE at width 8 *)

  Lemma wpt8_own_at_elems (c : CPU) (a : Arch.pa) (w : bv 64) (ws : wstate) :
    vwp_hold (wpt8_own c a w) ws ⊢
      ⌜is_aligned_paddr (Physaddr a) 8 = true⌝ ∗ ⌜acc_wf a 8⌝ ∗
      ∃ t0 t1 t2 t3 t4 t5 t6 t7 : nat,
        wlat_elem (acc_addr a 0) (DfracOwn 1) t0 (nth_byte w 0) ∗
          wown_st c (acc_addr a 0) ∗
        wlat_elem (acc_addr a 1) (DfracOwn 1) t1 (nth_byte w 1) ∗
          wown_st c (acc_addr a 1) ∗
        wlat_elem (acc_addr a 2) (DfracOwn 1) t2 (nth_byte w 2) ∗
          wown_st c (acc_addr a 2) ∗
        wlat_elem (acc_addr a 3) (DfracOwn 1) t3 (nth_byte w 3) ∗
          wown_st c (acc_addr a 3) ∗
        wlat_elem (acc_addr a 4) (DfracOwn 1) t4 (nth_byte w 4) ∗
          wown_st c (acc_addr a 4) ∗
        wlat_elem (acc_addr a 5) (DfracOwn 1) t5 (nth_byte w 5) ∗
          wown_st c (acc_addr a 5) ∗
        wlat_elem (acc_addr a 6) (DfracOwn 1) t6 (nth_byte w 6) ∗
          wown_st c (acc_addr a 6) ∗
        wlat_elem (acc_addr a 7) (DfracOwn 1) t7 (nth_byte w 7) ∗
          wown_st c (acc_addr a 7).
  Proof.
    rewrite /wpt8_own !vwp_hold_sep !vwp_hold_pure !wpt_own_h_at.
    iIntros "(%Hal & %Hacc & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct "H0" as (t0) "(H0 & S0 & _)".
    iDestruct "H1" as (t1) "(H1 & S1 & _)".
    iDestruct "H2" as (t2) "(H2 & S2 & _)".
    iDestruct "H3" as (t3) "(H3 & S3 & _)".
    iDestruct "H4" as (t4) "(H4 & S4 & _)".
    iDestruct "H5" as (t5) "(H5 & S5 & _)".
    iDestruct "H6" as (t6) "(H6 & S6 & _)".
    iDestruct "H7" as (t7) "(H7 & S7 & _)".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iExists t0, t1, t2, t3, t4, t5, t6, t7. iFrame.
  Qed.

  Lemma wlat8_own_wpt8_own (c : CPU) (a : Arch.pa) (t : nat) (w : bv 64)
      (ws : wstate) :
    is_aligned_paddr (Physaddr a) 8 = true ->
    acc_wf a 8 ->
    (forall j : nat, (j < 8)%nat -> (t <= flr (ws_view ws) (acc_addr a j))%nat) ->
    wlat8_own c a t w -∗ vwp_hold (wpt8_own c a w) ws.
  Proof.
    intros Hal Hacc Hfl.
    rewrite /wlat8_own /wpt8_own !vwp_hold_sep !vwp_hold_pure.
    iIntros "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3 & H4 & S4 & H5 & S5
              & H6 & S6 & H7 & S7)".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iSplitL "H0 S0";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 0%nat ltac:(lia))
                    with "H0 S0")|].
    iSplitL "H1 S1";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 1%nat ltac:(lia))
                    with "H1 S1")|].
    iSplitL "H2 S2";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 2%nat ltac:(lia))
                    with "H2 S2")|].
    iSplitL "H3 S3";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 3%nat ltac:(lia))
                    with "H3 S3")|].
    iSplitL "H4 S4";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 4%nat ltac:(lia))
                    with "H4 S4")|].
    iSplitL "H5 S5";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 5%nat ltac:(lia))
                    with "H5 S5")|].
    iSplitL "H6 S6";
      [by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 6%nat ltac:(lia))
                    with "H6 S6")|].
    by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 7%nat ltac:(lia))
                 with "H7 S7").
  Qed.

  Lemma wpt8_store_own (c : CPU) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (w : bv 64) (v : bv (8 * 8)) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt8_own c a w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post (Some (fin_to_nat c)) σ ak a 8 v))
                (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak a 8 v)) ∗
    vwp_hold (wpt8_own c a v)
             (wm_ws (wwrite_post (Some (fin_to_nat c)) σ ak a 8 v)).
  Proof.
    iIntros "Hi Hpt".
    iDestruct (wpt8_own_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3 & H4 & S4 & H5 & S5
        & H6 & S6 & H7 & S7)".
    iMod (wlat8_store_prim_own c (wm_class_of ak (wm_ws σ)) σ a v
            with "Hi H0 S0 H1 S1 H2 S2 H3 S3 H4 S4 H5 S5 H6 S6 H7 S7")
      as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img (Some (fin_to_nat c)) σ ak a 8 v)
            (wwrite_post_log (Some (fin_to_nat c)) σ ak a 8 v).
    iFrame "Hi".
    iApply (wlat8_own_wpt8_own c a (S (length (wm_log σ))) v _ Hal Hacc
              with "Hl").
    intros j Hj. apply (flr_wwrite_post (Some (fin_to_nat c)) σ ak a 8 v j).
    lia.
  Qed.

  Lemma wpt8_own_flat_pin (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8_own c a w) (wm_ws σ) -∗
    ⌜acc_wf a 8 /\
     forall j : nat, (j < 8)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j) /\
       pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. rewrite /wpt8_own !vwp_hold_sep !vwp_hold_pure.
    iIntros "Hi (%Hal & %Hacc & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 0) 0 Hwf Hacc
                 ltac:(lia) with "Hi H0") as %E0.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 1) 1 Hwf Hacc
                 ltac:(lia) with "Hi H1") as %E1.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 2) 2 Hwf Hacc
                 ltac:(lia) with "Hi H2") as %E2.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 3) 3 Hwf Hacc
                 ltac:(lia) with "Hi H3") as %E3.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 4) 4 Hwf Hacc
                 ltac:(lia) with "Hi H4") as %E4.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 5) 5 Hwf Hacc
                 ltac:(lia) with "Hi H5") as %E5.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 6) 6 Hwf Hacc
                 ltac:(lia) with "Hi H6") as %E6.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 8 (nth_byte w 7) 7 Hwf Hacc
                 ltac:(lia) with "Hi H7") as %E7.
    iPureIntro. split; [exact Hacc|]. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  Lemma wpt8_own_flat (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8_own c a w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 8)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_own_flat_pin c σ a w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  Lemma wpt8_own_pinned (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8_own c a w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 8)%nat -> pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_own_flat_pin c σ a w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj2 (Hall j Hj)).
  Qed.

End store8.

Notation "a ↦w₈ₒ w" := (wpt8_own cpu_id a w)
  (at level 20, format "a  ↦w₈ₒ  w") : bi_scope.

(* ====================================================================== *)
(** ** 5. The leaves

    The [wP]/[wV]/[wQ] families are the per-instruction obligations of
    [WeakInstr] §5.  Each of them was stated at width 4 with the [4] written
    into the body; every one is width-generic as it stands, so they are
    RESTATED here over an arbitrary [n] and the width-8 names are instances.
    [wP_load_w_4] & co. below check that the width-4 originals really are the
    [n := 4] instances, i.e. that nothing is lost by the generalization (the
    same sanity check [WeakStore.wlat_agree_store_win_singleton] makes). *)

(** THE SUBSUMPTION CHECKS: [WeakInstr]'s width-4 families are the [n := 4]
    instances of its own width-generic [_w] family, on the nose.  Kept as
    regression checks after the generalization landed (M4-prep found the
    identifications; they are now definitional). *)
Lemma wP_load_w_4 ea : wP_load_w 4 ea = wP_load ea.
Proof. reflexivity. Qed.
Lemma wP_mem_w_4 ea : wP_mem_w 4 ea = wP_mem ea.
Proof. reflexivity. Qed.
Lemma wV_store_w_4 ea : wV_store_w 4 ea = wV_store ea.
Proof. reflexivity. Qed.
Lemma wV_amo_aq_w_4 ea : wV_amo_aq_w 4 ea = wV_amo_aq ea.
Proof. reflexivity. Qed.
Lemma wV_load_w_4 ea : wV_load_w 4 ea = wV_load ea.
Proof. reflexivity. Qed.
Lemma wQ_load_w_4 ea : wQ_load_w 4 ea = wQ_load ea.
Proof. reflexivity. Qed.
Lemma wQ_store_w_4 tid ea (v : bv 32) : wQ_store_w 4 tid ea v = wQ_store tid ea v.
Proof. reflexivity. Qed.
Lemma wQ_amo_aq_w_4 tid ea (v : bv 32) :
  wQ_amo_aq_w 4 tid ea v = wQ_amo_aq tid ea v.
Proof. reflexivity. Qed.

(** The width-8 names. *)
Definition wP_load8 (ea : Arch.pa) : wmstate -> Prop := wP_load_w 8 ea.
Definition wP_mem8 (ea : Arch.pa) : wmstate -> Prop := wP_mem_w 8 ea.
Definition wV_store8 (ea : Arch.pa) : wmstate -> wstate -> Prop :=
  wV_store_w 8 ea.
Definition wV_amo_aq8 (ea : Arch.pa) : wmstate -> wstate -> Prop :=
  wV_amo_aq_w 8 ea.
Definition wQ_store8 (tid : option nat) (ea : Arch.pa) (v : bv 64)
  : wmstate -> wmstate -> Prop := wQ_store_w 8 tid ea v.

Definition wQ_amo_aq8 (tid : option nat) (ea : Arch.pa) (v : bv 64)
  : wmstate -> wmstate -> Prop := wQ_amo_aq_w 8 tid ea v.

Lemma wQ_store8_wV tid ea v σ σ' :
  wQ_store8 tid ea v σ σ' -> wV_store8 ea σ (wm_ws σ').
Proof. by intros (_ & _ & _ & ?). Qed.

Lemma wQ_amo_aq8_store tid ea v σ σ' :
  wQ_amo_aq8 tid ea v σ σ' -> wQ_store8 tid ea v σ σ'.
Proof. by intros (? & _ & _). Qed.

Lemma wQ_amo_aq8_gain tid ea v σ σ' :
  wQ_amo_aq8 tid ea v σ σ' -> wV_amo_aq8 ea σ (wm_ws σ').
Proof. by intros (_ & ? & _). Qed.

Lemma wQ_amo_aq8_excl tid ea v σ σ' :
  wQ_amo_aq8 tid ea v σ σ' ->
  wm_log σ' = (wm_log σ ++ [wwrite_msg tid WCexcl ea 8 v])%list.
Proof. by intros (_ & _ & ?). Qed.

Section leaves8.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types R : vProp Σ.

  (* ------------------------------------------------------------------ *)
  (** *** 5a. [ld] — the plain 8-byte LOAD, owned form

      Owning [ea ↦w₈{dq} w] at the hart's index does the whole job: it
      discharges the peel's read obligation ([wP_load8]) and it pins the flat
      doubleword, which is the premise the SC execute-lemma of a load takes
      verbatim.  The [wwp_lw4] twin. *)
  Lemma wwp_ld8 (σ : wmstate) (ea : Arch.pa) (dq : dfrac) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8 ea dq w) (wm_ws σ) -∗
    ⌜wP_load8 ea σ /\
     (forall j : nat, (j < 8)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j))⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_flat_pin σ ea dq w Hwf with "Hi Hpt") as %[Hacc Hall].
    iPureIntro. split.
    - rewrite /wP_load8 /wP_load_w. split; [exact Hacc|].
      intros j Hj. exact (proj2 (Hall j Hj)).
    - intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  (** The OWNED twin: an own read of an own-dirty byte is legal, so the
      whole load side is available at [wpt8_own] too. *)
  Lemma wwp_ld8_own (c : CPU) (σ : wmstate) (ea : Arch.pa) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt8_own c ea w) (wm_ws σ) -∗
    ⌜wP_load8 ea σ /\
     (forall j : nat, (j < 8)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j))⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt8_own_flat_pin c σ ea w Hwf with "Hi Hpt") as %[Hacc Hall].
    iPureIntro. split.
    - rewrite /wP_load8 /wP_load_w. split; [exact Hacc|].
      intros j Hj. exact (proj2 (Hall j Hj)).
    - intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  Lemma wwp_sd8_pmem_own (c : CPU) (σ : wmstate) (ea : Arch.pa) (w : bv 64) :
    vwp_hold (wpt8_own c ea w) (wm_ws σ) ⊢ ⌜wP_mem8 ea σ⌝.
  Proof.
    rewrite /wpt8_own !vwp_hold_sep !vwp_hold_pure.
    iIntros "(_ & %Hacc & _)". iPureIntro. exact Hacc.
  Qed.

  Lemma wwp_ld8_own_carry (c : CPU) (σ σ' : wmstate) (t : mstate) ea w :
    wstep_post σ σ' t ->
    vwp_hold (wpt8_own c ea w) (wm_ws σ) ⊢ vwp_hold (wpt8_own c ea w) (wm_ws σ').
  Proof. intros Hp. by apply wpt8_own_mono, (wstep_post_ws_le σ σ' t). Qed.

  (** ... and the frame: the loaded doubleword survives the step. *)
  Lemma wwp_ld8_carry (σ σ' : wmstate) (t : mstate) ea dq w :
    wstep_post σ σ' t ->
    vwp_hold (wpt8 ea dq w) (wm_ws σ) ⊢ vwp_hold (wpt8 ea dq w) (wm_ws σ').
  Proof. intros Hp. by apply wpt8_mono, (wstep_post_ws_le σ σ' t). Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 5b. [sd] — the 8-byte STORE

      A store has no read to pin, so its peel obligation is only
      wrap-freedom ([wP_mem8]).  Its weak-memory content is on the OUTPUT
      side and it is a TIMESTAMP: the message lands at [S (length (wm_log σ))]
      and [wV_store8] says the hart's own index covers it afterwards.  (The
      release deposit, [WeakInstr.wwp_release_deposit], is width-free and
      applies unchanged.) *)
  Lemma wwp_sd8_pmem (σ : wmstate) (ea : Arch.pa) (dq : dfrac) (w : bv 64) :
    vwp_hold (wpt8 ea dq w) (wm_ws σ) ⊢ ⌜wP_mem8 ea σ⌝.
  Proof.
    rewrite /wpt8 !vwp_hold_sep !vwp_hold_pure.
    iIntros "(_ & %Hacc & _)". iPureIntro. exact Hacc.
  Qed.

  (** The store's own post-view, in the form the next instruction consumes:
      after the store the hart's floor at every byte of the doubleword covers
      the store's timestamp. *)
  Lemma wwp_sw8_post (σ : wmstate) (ws' : wstate) ea :
    wV_store8 ea σ ws' ->
    forall j : nat, (j < 8)%nat ->
      view_byte (acc_addr ea j) (S (length (wm_log σ))) ⊑ ws_view ws'.
  Proof. intros HQ j Hj. apply view_byte_le. apply HQ. lia. Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 5c. [amoswap.d.aq] — the eight-byte ACQUIRE, invariant form

      The [WeakInstr.wwp_amoswap_w_aq_inv] twin, over the eight-byte element
      bundle.  The read half of an AMO is [ak_latest], so the bundle alone
      determines the value AND the timestamp, with no ownership and no
      hypothesis about the reader's views; the acquire's index gain at that
      timestamp thaws the releaser's deposited payload. *)
  Lemma wwp_amoswap_d_aq_inv R (σ : wmstate) (ws' : wstate)
      (ea : Arch.pa) (dq : dfrac) (t : nat) (w : bv 64) :
    wlog_wf (wm_log σ) ->
    acc_wf ea 8 ->
    wV_amo_aq8 ea σ ws' ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat8 ea dq t w -∗
    monPred_at R (view_scl t) -∗
    ⌜wP_mem8 ea σ⌝ ∗
    ⌜forall j : nat, (j < 8)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add ea j = Some (nth_byte w j)⌝ ∗
    ⌜view_scl t ⊑ ws_view ws'⌝ ∗
    vwp_hold R ws'.
  Proof.
    intros Hwf Hacc HQ. iIntros "Hi Hl HR".
    iDestruct (wlat8_flat_gen σ ea dq t w Hwf Hacc with "Hi Hl")
      as %[Hflat Hts].
    assert (Hscl : view_scl t ⊑ ws_view ws').
    { rewrite -(Hts 0%nat ltac:(lia)). apply HQ. lia. }
    iSplitR; [iPureIntro; exact Hacc|].
    iSplitR; [iPureIntro; exact Hflat|].
    iSplitR; [iPureIntro; exact Hscl|].
    rewrite /vwp_hold. by iApply (monPred_mono R _ _ Hscl with "HR").
  Qed.

  (** φ exporters at width 8 (φ-upgrade, deliverable C) — see
      [WeakStore.nv_ok_wpt4] / [nv_ok_wlat4_own]. *)
  Lemma nv_ok_wpt8 (c : CPU) img log (a : Arch.pa) (dq : dfrac) (w : bv 64)
      (ws : wstate) :
    wlat_interp img log -∗ vwp_hold (wpt8 a dq w) ws -∗
    ⌜forall j : nat, (j < 8)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi Hpt". iDestruct (wpt8_at_elems with "Hpt") as "(_ & _ & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H0") as %E0.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H1") as %E1.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H2") as %E2.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H3") as %E3.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H4") as %E4.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H5") as %E5.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H6") as %E6.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H7") as %E7.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  Lemma nv_ok_wpt8_own (c : CPU) img log (a : Arch.pa) (w : bv 64)
      (ws : wstate) :
    wlat_interp img log -∗ vwp_hold (wpt8_own c a w) ws -∗
    ⌜forall j : nat, (j < 8)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi Hpt".
    iDestruct (wpt8_own_at_elems with "Hpt") as "(_ & _ & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3
        & H4 & S4 & H5 & S5 & H6 & S6 & H7 & S7)".
    iDestruct (nv_ok_of_own_st with "Hi S0") as %E0.
    iDestruct (nv_ok_of_own_st with "Hi S1") as %E1.
    iDestruct (nv_ok_of_own_st with "Hi S2") as %E2.
    iDestruct (nv_ok_of_own_st with "Hi S3") as %E3.
    iDestruct (nv_ok_of_own_st with "Hi S4") as %E4.
    iDestruct (nv_ok_of_own_st with "Hi S5") as %E5.
    iDestruct (nv_ok_of_own_st with "Hi S6") as %E6.
    iDestruct (nv_ok_of_own_st with "Hi S7") as %E7.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  (** ... and the [nv_free] form off a PLAIN eight-byte bundle — what a
      shared, published slot (a page-table entry) exports.  Stronger than the
      [nv_ok] forms above: it is agent-independent
      ([WeakGhost.nv_ok_of_free]), which is what lets a walk leaf discharge
      its read footprint without naming the walking hart. *)
  Lemma nv_free_wlat8 img log (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 64) :
    wlat_interp img log -∗ wlat8 a dq t w -∗
    ⌜forall j : nat, (j < 8)%nat -> nv_free log (acc_addr a j)⌝.
  Proof.
    iIntros "Hi (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iDestruct (nv_free_of_pointsto with "Hi H0") as %E0.
    iDestruct (nv_free_of_pointsto with "Hi H1") as %E1.
    iDestruct (nv_free_of_pointsto with "Hi H2") as %E2.
    iDestruct (nv_free_of_pointsto with "Hi H3") as %E3.
    iDestruct (nv_free_of_pointsto with "Hi H4") as %E4.
    iDestruct (nv_free_of_pointsto with "Hi H5") as %E5.
    iDestruct (nv_free_of_pointsto with "Hi H6") as %E6.
    iDestruct (nv_free_of_pointsto with "Hi H7") as %E7.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

  Lemma nv_ok_wlat8_own (c : CPU) img log (a : Arch.pa) (t : nat) (w : bv 64) :
    wlat_interp img log -∗ wlat8_own c a t w -∗
    ⌜forall j : nat, (j < 8)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi (H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3
                 & H4 & S4 & H5 & S5 & H6 & S6 & H7 & S7)".
    iDestruct (nv_ok_of_own_st with "Hi S0") as %E0.
    iDestruct (nv_ok_of_own_st with "Hi S1") as %E1.
    iDestruct (nv_ok_of_own_st with "Hi S2") as %E2.
    iDestruct (nv_ok_of_own_st with "Hi S3") as %E3.
    iDestruct (nv_ok_of_own_st with "Hi S4") as %E4.
    iDestruct (nv_ok_of_own_st with "Hi S5") as %E5.
    iDestruct (nv_ok_of_own_st with "Hi S6") as %E6.
    iDestruct (nv_ok_of_own_st with "Hi S7") as %E7.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
      [exact E0|exact E1|exact E2|exact E3|exact E4|exact E5|exact E6|exact E7
      |lia].
  Qed.

End leaves8.

(* ====================================================================== *)
(** ** 6. Soundness check *)

Print Assumptions wpt8_store.
Print Assumptions wwp_ld8.
Print Assumptions wlat_agree_store_w.
