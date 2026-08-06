(** * WeakWord8.v — the [↦w₈] tower (M4-prep)

    THE EIGHT-BYTE TWIN of [WeakInstr]'s [↦w₄] tower and of [WeakStore]'s
    store-window update.  Everything the weak layer owns today is FOUR bytes
    wide — the lock word, the [started] flag — but the kernel's own data is
    mostly eight ([lk->cpu], [lk->name], every pointer, every [uint64]), and
    [WeakLock]'s header names the missing [↦w₈] tower as the reason its
    [lock_state] can only take two of its three values.  This file supplies
    it.

    ===================== WHAT IS IN HERE =====================

      §1  THE WIDTH-GENERIC WINDOW INSERT.  [winsw] is the [n]-fold insert
          [WeakStore.wins4] is the width-4 instance of, with its two lookup
          lemmas proved ONCE by induction, and [wlat_agree_store_w] is the
          width-generic [WeakStore.wlat_agree_store4] over it — the store
          window's pure part at every width at once.  (The framing lemma
          underneath, [WeakStore.wlat_agree_store_win], was already
          window-generic; only its INSTANCE was width-4.)
      §1b THE PER-BYTE BRIDGES, also width-generic: [wpt_byte_flat_pin] and
          [wlat_byte_flat_gen] are the one-byte guts that [wpt4_flat] /
          [wpt4_pinned] / [WeakLock.wlat4_flat_gen] each open-code four times
          at a fixed width.  Every eight-fold lemma below is eight one-line
          applications of one of these.
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
          eight-byte twin of [WeakInstr.wwp_amoswap_w_aq_inv].  The [wP]/[wV]/
          [wQ] families are stated WIDTH-GENERICALLY ([wP_load_w] & co.) with
          the width-8 names as instances; [wP_load_w_4] & co. check that the
          width-4 ones in [WeakInstr] are the [n := 4] instances.

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
(** ** 1. The window insert, at every width at once

    [winsw a T v n mm] is [mm] with the [n] bytes of [v] at [a] retargeted at
    timestamp [T] — byte 0 innermost, i.e. the shape [n] successive
    [ghost_map_update]s in index order leave behind.  [WeakStore.wins4] is
    [winsw … 4] (see [wins8_winsw] for the width-8 identification). *)

Fixpoint winsw (a : Arch.pa) (T : nat) {m : N} (v : bv m) (n : nat)
    (mm : gmap Z (nat * bv 8)) : gmap Z (nat * bv 8) :=
  match n with
  | O => mm
  | S k => <[acc_addr a k := (T, nth_byte v k)]> (winsw a T v k mm)
  end.

Lemma winsw_lookup_in (a : Arch.pa) (T : nat) {m : N} (v : bv m) (n : nat)
    (mm : gmap Z (nat * bv 8)) (j : nat) :
  (j < n)%nat -> winsw a T v n mm !! acc_addr a j = Some (T, nth_byte v j).
Proof.
  revert j. induction n as [|k IH]; intros j Hj; [exfalso; lia|]. simpl.
  destruct (decide (j = k)) as [->|Hne].
  - by rewrite lookup_insert.
  - rewrite lookup_insert_ne; [apply IH; lia|rewrite /acc_addr; lia].
Qed.

Lemma winsw_lookup_out (a : Arch.pa) (T : nat) {m : N} (v : bv m) (n : nat)
    (mm : gmap Z (nat * bv 8)) (z : Z) :
  (forall j : nat, (j < n)%nat -> acc_addr a j <> z) ->
  winsw a T v n mm !! z = mm !! z.
Proof.
  induction n as [|k IH]; intros Hne; [reflexivity|]. simpl.
  rewrite lookup_insert_ne; [apply IH; intros j Hj; apply Hne; lia
                            |apply Hne; lia].
Qed.

(** THE WINDOW UPDATE, pure part, at every width: appending a width-[n]
    store's message and retargeting the [n] elements at the fresh top keeps
    the latest-write map accurate.  [WeakStore.wlat_agree_store4] is the
    [n := 4] instance. *)
Lemma wlat_agree_store_w img log (tid : option nat) (a : Arch.pa) (n : N)
    {m : N} (v : bv m) (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid a n v])
             (winsw a (S (length log)) v (N.to_nat n) mm).
Proof.
  intros Hag.
  apply (wlat_agree_store_win img log _
           (fun z => pa_z a <= z < pa_z a + Z.of_N n) mm).
  - intros z Hz. by apply (wwrite_msg_win_none tid a n v z).
  - intros z tv Hz Hlk.
    assert (Hex : exists j : nat, (j < N.to_nat n)%nat /\ z = acc_addr a j).
    { exists (Z.to_nat (z - pa_z a)). rewrite /acc_addr. split; lia. }
    destruct Hex as (j & Hj & ->).
    rewrite (winsw_lookup_in a (S (length log)) v (N.to_nat n) mm j Hj) in Hlk.
    simplify_eq/=. split; [reflexivity|].
    by apply (wwrite_msg_byte tid a n v j).
  - intros z Hz. apply winsw_lookup_out. intros j Hj Heq.
    apply Hz. rewrite -Heq /acc_addr. lia.
  - exact Hag.
Qed.

(* ====================================================================== *)
(** ** 1b. The per-byte bridges, width-generic

    The one-byte content of the whole flat/pinned side.  Both are stated at
    the log's own key [acc_addr a j] (which is what a bundle carries) and
    convert to the [Arch.pa]-keyed flat map through [acc_wf_byte] — the
    conversion [acc_wf] exists to make available. *)

Section byte_bridges.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** An OWNED byte of an access window: what the flat projection holds
      there, and that it is pinned for this hart. *)
  Lemma wpt_byte_flat_pin (σ : wmstate) (a : Arch.pa) (n : N) (dq : dfrac)
      (b : bv 8) (j : nat) :
    wlog_wf (wm_log σ) -> acc_wf a n -> (j < N.to_nat n)%nat ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (acc_addr a j ↦w{dq} b) (wm_ws σ) -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b /\
     pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf Hacc Hj. iIntros "Hi Hpt".
    iDestruct (wpt_pinned_read σ (acc_addr a j) dq b with "Hi Hpt") as %Hpin.
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b⌝)%I as %Hfl.
    { iApply (wpt_flat_lookup σ (pa_add a j) dq b Hwf with "Hi [Hpt]").
      rewrite (acc_wf_byte a n j Hacc Hj). iExact "Hpt". }
    iPureIntro. by split.
  Qed.

  (** A BARE ELEMENT of an access window (no receipt, no view): the same flat
      fact, plus the identification of the element's timestamp with the
      byte's [latest_ts] — which is what makes an [ak_latest] read return
      exactly this element's value. *)
  Lemma wlat_byte_flat_gen (σ : wmstate) (a : Arch.pa) (n : N) (dq : dfrac)
      (t : nat) (b : bv 8) (j : nat) :
    wlog_wf (wm_log σ) -> acc_wf a n -> (j < N.to_nat n)%nat ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto (acc_addr a j) dq t b -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some b /\
     latest_ts (wm_log σ) (acc_addr a j) = t⌝.
  Proof.
    intros Hwf Hacc Hj. iIntros "Hi He".
    rewrite -(acc_wf_byte a n j Hacc Hj).
    iApply (wpt_img_flat_lookup_gen σ (pa_add a j) dq t b Hwf with "Hi [He]").
    rewrite (acc_wf_byte a n j Hacc Hj). iExact "He".
  Qed.

End byte_bridges.

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
  <[acc_addr a 7 := (T, nth_byte v 7)]>
  (<[acc_addr a 6 := (T, nth_byte v 6)]>
  (<[acc_addr a 5 := (T, nth_byte v 5)]>
  (<[acc_addr a 4 := (T, nth_byte v 4)]>
  (<[acc_addr a 3 := (T, nth_byte v 3)]>
  (<[acc_addr a 2 := (T, nth_byte v 2)]>
  (<[acc_addr a 1 := (T, nth_byte v 1)]>
  (<[acc_addr a 0 := (T, nth_byte v 0)]> mm))))))).

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
Lemma wlat_agree_store8 img log (tid : option nat) (a : Arch.pa) (v : bv 64)
    (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid a 8 v])
             (wins8 a (S (length log)) v mm).
Proof.
  intros Hag. rewrite wins8_winsw.
  by apply (wlat_agree_store_w img log tid a 8 v mm).
Qed.

Section store8.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE PRIMITIVE.  Eight full-fraction elements over the window, at
      arbitrary pre-timestamps and pre-values, one eight-byte message
      appended: the authority moves to the new log and the eight elements
      come back as a [wlat8] bundle at the message's own timestamp. *)
  Lemma wlat8_store_prim (tid : option nat) (σ : wmstate) (a : Arch.pa)
      (v : bv 64) (t0 t1 t2 t3 t4 t5 t6 t7 : nat)
      (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_pointsto (acc_addr a 0) (DfracOwn 1) t0 b0 -∗
    wlat_pointsto (acc_addr a 1) (DfracOwn 1) t1 b1 -∗
    wlat_pointsto (acc_addr a 2) (DfracOwn 1) t2 b2 -∗
    wlat_pointsto (acc_addr a 3) (DfracOwn 1) t3 b3 -∗
    wlat_pointsto (acc_addr a 4) (DfracOwn 1) t4 b4 -∗
    wlat_pointsto (acc_addr a 5) (DfracOwn 1) t5 b5 -∗
    wlat_pointsto (acc_addr a 6) (DfracOwn 1) t6 b6 -∗
    wlat_pointsto (acc_addr a 7) (DfracOwn 1) t7 b7 ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid a 8 v]) ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    iIntros "Hi H0 H1 H2 H3 H4 H5 H6 H7".
    iDestruct "Hi" as (mm) "[Hauth %Hag]". rewrite /wlat_pointsto.
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
    iModIntro. iSplitL "Hauth".
    - iExists (wins8 a (S (length (wm_log σ))) v mm). iFrame "Hauth".
      iPureIntro. by apply wlat_agree_store8.
    - rewrite /wlat8. iFrame.
  Qed.

  (** THE BUNDLE UPDATE at an explicitly described post-state. *)
  Lemma wlat8_store_gen (tid : option nat) (σ σ' : wmstate) (a : Arch.pa)
      (t : nat) (w v : bv 64) :
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid a 8 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat8 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Himg Hlog. rewrite /wlat8.
    iIntros "Hi (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    rewrite Himg Hlog.
    by iMod (wlat8_store_prim tid σ a v with "Hi H0 H1 H2 H3 H4 H5 H6 H7")
      as "[$ $]".
  Qed.

  (** ... and at the interpreter's OWN write post-state, which is what a leaf
      hands its caller.  [acc_wf] is not consumed by the proof (the update is
      entirely on the [Z]-keyed side); it is kept as a premise because every
      caller has it and because it is what makes "the window" the eight bytes
      of [a] rather than a wrapped range. *)
  Lemma wlat8_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (t : nat) (w : bv 64) (v : bv (8 * 8)) :
    acc_wf a 8 ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat8 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 8 v))
                (wm_log (wwrite_post tid σ ak a 8 v)) ∗
    wlat8 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros _. iIntros "Hi Hl".
    iApply (wlat8_store_gen tid σ (wwrite_post tid σ ak a 8 v) a t w v
              (wwrite_post_img tid σ ak a 8 v) (wwrite_post_log tid σ ak a 8 v)
              with "Hi Hl").
  Qed.

  (** THE STORE RULE FOR THE BUNDLE, owned altitude.  The two pure conjuncts
      ride along unchanged; the post-view side condition is
      [WeakStore.flr_wwrite_post] (already width-generic), i.e. the store's
      own post-state raises the floor at every byte of the window. *)
  Lemma wpt8_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (w : bv 64) (v : bv (8 * 8)) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt8 a (DfracOwn 1) w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 8 v))
                (wm_log (wwrite_post tid σ ak a 8 v)) ∗
    vwp_hold (wpt8 a (DfracOwn 1) v) (wm_ws (wwrite_post tid σ ak a 8 v)).
  Proof.
    iIntros "Hi Hpt".
    iDestruct (wpt8_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3 t4 t5 t6 t7)
      "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7)".
    iMod (wlat8_store_prim tid σ a v with "Hi H0 H1 H2 H3 H4 H5 H6 H7")
      as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img tid σ ak a 8 v) (wwrite_post_log tid σ ak a 8 v).
    iFrame "Hi".
    iApply (wlat8_wpt8 a (DfracOwn 1) (S (length (wm_log σ))) v
              _ Hal Hacc with "Hl").
    intros j Hj. apply (flr_wwrite_post tid σ ak a 8 v j). lia.
  Qed.

End store8.

(* ====================================================================== *)
(** ** 5. The leaves

    The [wP]/[wV]/[wQ] families are the per-instruction obligations of
    [WeakInstr] §5.  Each of them was stated at width 4 with the [4] written
    into the body; every one is width-generic as it stands, so they are
    RESTATED here over an arbitrary [n] and the width-8 names are instances.
    [wP_load_w_4] & co. below check that the width-4 originals really are the
    [n := 4] instances, i.e. that nothing is lost by the generalization (the
    same sanity check [WeakStore.wlat_agree_store_win_singleton] makes). *)

Definition wP_load_w (n : N) (ea : Arch.pa) : wmstate -> Prop :=
  fun σ => acc_wf ea n /\
           forall j : nat, (j < N.to_nat n)%nat -> pinned_read σ (acc_addr ea j).
Definition wP_mem_w (n : N) (ea : Arch.pa) : wmstate -> Prop :=
  fun _ => acc_wf ea n.
Definition wV_store_w (n : N) (ea : Arch.pa) : wmstate -> wstate -> Prop :=
  fun σ ws' => forall j : nat, (j < N.to_nat n)%nat ->
     (S (length (wm_log σ)) <= flr (ws_view ws') (acc_addr ea j))%nat.
Definition wV_amo_aq_w (n : N) (ea : Arch.pa) : wmstate -> wstate -> Prop :=
  fun σ ws' => forall j : nat, (j < N.to_nat n)%nat ->
     view_scl (latest_ts (wm_log σ) (acc_addr ea j)) ⊑ ws_view ws'.
Definition wQ_store_w (n : N) (tid : option nat) (ea : Arch.pa) {m : N}
    (v : bv m) : wmstate -> wmstate -> Prop :=
  fun σ σ' =>
    wm_img σ' = wm_img σ /\
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid ea n v])%list /\
    ws_le (wm_ws σ) (wm_ws σ') /\
    wV_store_w n ea σ (wm_ws σ').
Definition wQ_amo_aq_w (n : N) (tid : option nat) (ea : Arch.pa) {m : N}
    (v : bv m) : wmstate -> wmstate -> Prop :=
  fun σ σ' => wQ_store_w n tid ea v σ σ' /\ wV_amo_aq_w n ea σ (wm_ws σ').

(** THE SUBSUMPTION CHECKS: [WeakInstr]'s width-4 families are the [n := 4]
    instances, on the nose. *)
Lemma wP_load_w_4 ea : wP_load_w 4 ea = wP_load ea.
Proof. reflexivity. Qed.
Lemma wP_mem_w_4 ea : wP_mem_w 4 ea = wP_mem ea.
Proof. reflexivity. Qed.
Lemma wV_store_w_4 ea : wV_store_w 4 ea = wV_store ea.
Proof. reflexivity. Qed.
Lemma wV_amo_aq_w_4 ea : wV_amo_aq_w 4 ea = wV_amo_aq ea.
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
Proof. by intros [? _]. Qed.

Lemma wQ_amo_aq8_gain tid ea v σ σ' :
  wQ_amo_aq8 tid ea v σ σ' -> wV_amo_aq8 ea σ (wm_ws σ').
Proof. by intros [_ ?]. Qed.

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

End leaves8.

(* ====================================================================== *)
(** ** 6. Soundness check *)

Print Assumptions wpt8_store.
Print Assumptions wwp_ld8.
Print Assumptions wlat_agree_store_w.
