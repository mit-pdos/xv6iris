(** * WeakStore.v — the STORE WINDOW update (M3b item 1)

    WHAT THIS IS FOR.  Everything the weak layer owned across a store so far
    was ONE BYTE wide: [WeakGhost.wlat_agree_store] re-establishes the
    state-interpretation's latest-write tie only for a message that writes
    exactly one address, and [WeakVProp.wpt_store_rule] / [wpt_wwrite_byte]
    inherit that restriction.  The lock library cannot live with it.  A
    release is [sw] — ONE message covering FOUR bytes — and the acquire is
    [amoswap.w.aq], whose write half is the same four-byte message; and what
    the lock invariant holds over the lock word is a FOUR-BYTE bundle
    ([WeakInstr.wlat4], the bare objective element bundle that crosses the
    invariant boundary, or [WeakInstr.wpt4] at the owned altitude).  Neither
    bundle could be RETARGETED at the timestamp a store creates, so the
    invariant could be opened and read but never closed at the new value.

    This file supplies exactly that retargeting, at three altitudes:

      §1  [wlat_agree_store_win] — the PURE framing lemma, stated over an
          arbitrary window [W] rather than at width 4: the updated map holds
          the fresh message's bytes at the fresh top timestamp inside [W] and
          is unchanged outside it.  [WeakGhost.wlat_agree_store] is the
          singleton instance ([wlat_agree_store_win_singleton], stated here
          as the sanity check that nothing was lost in the generalization).
      §2  the width-[n] message facts: a [WeakInterp.wwrite_msg] writes
          nothing outside [[pa_z pa, pa_z pa + n)] — the general-width twin of
          [WeakVProp.wwrite_msg_byte1_none] — and the floor a whole-window
          store leaves at EVERY byte of its window ([flr_wwrite_post]), which
          is the [flr_store_post] the four-byte post-view side condition
          needs.
      §3  [wlat4_store] — the bundle update at the iProp altitude, full
          fraction, one four-byte message appended, all four elements
          retargeted at [S (length (wm_log σ))].  THIS is the deliverable the
          lock library consumes: it is what lets a releaser close the lock
          invariant at the value it just stored.
      §4  [wpt4_store] — the same at the vProp/[vwp_hold] altitude, with the
          bundle's two pure conjuncts (4-alignment and [acc_wf]) riding along
          unchanged and the post-view discharged from §2.

    NOTE ON THE PRE-TIMESTAMPS.  The primitive ([wlat4_store_prim]) takes the
    four elements at FOUR INDEPENDENT timestamps and values, not at a common
    one.  That is not generality for its own sake: [wpt4] existentially binds
    one timestamp PER BYTE (a [↦w] is "the latest write, whatever it is, and
    I have seen it"), so a bundle owned at the vProp altitude simply does not
    come with a common pre-timestamp — only the POST-timestamp is shared,
    because it is the one message's own.
*)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
(* [rv64d] is needed for [is_aligned_paddr], which [WeakInstr.wpt4] carries.
   It SHADOWS [filter] and [not] (durable notes): write [¬], never [not]. *)
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import WeakBridge.
Require Import WeakInstr.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The framing lemma over an arbitrary window

    [W] is the set of addresses the caller retargeted.  The three premises
    say: the message writes nothing outside [W]; every entry the new map has
    INSIDE [W] is the fresh message's byte at the fresh top timestamp; and
    outside [W] the map did not move.  Note that [W] may be strictly larger
    than the message's footprint (an address in [W] that the new map has no
    entry for is simply not constrained), which is what makes the "window"
    reading — a whole four-byte access — the natural instance.

    NO DECIDABILITY OF [W] IS ASSUMED.  The proof needs [W a] to fire the
    second premise and only has [¬¬ W a]; the conclusion it wants out of that
    premise is a conjunction of two DECIDABLE equations, so [dec_stable]
    closes the gap.  Keeping [W] an arbitrary [Prop] is what lets a caller
    write the window as a plain [Z] range with no instance plumbing. *)

Lemma wlat_agree_store_win img log (m : wmsg) (W : Z -> Prop)
    (mm mm' : gmap Z (nat * bv 8)) :
  (forall a', ¬ W a' -> msg_byte m a' = None) ->
  (forall a' tv, W a' -> mm' !! a' = Some tv ->
      tv.1 = S (length log) /\ msg_byte m a' = Some tv.2) ->
  (forall a', ¬ W a' -> mm' !! a' = mm !! a') ->
  wlat_agree img log mm ->
  wlat_agree img (log ++ [m]) mm'.
Proof.
  intros Hout Hin Hframe Hag a tv Ha.
  destruct (decide (msg_byte m a = None)) as [Hnone|Hsome].
  - (* the message does not write [a] — so [a] is outside [W] (an entry
       inside [W] would have to BE the message's byte), and the old element
       survives the append *)
    assert (HnW : ¬ W a).
    { intros HW. destruct (Hin a tv HW Ha) as [_ Hb].
      rewrite Hnone in Hb. discriminate. }
    rewrite (Hframe a HnW) in Ha.
    apply latest_val_app; [by apply Hag|].
    apply not_writes_in_app_new. intros m0 Hm0.
    apply elem_of_list_singleton in Hm0 as ->. exact Hnone.
  - (* the message writes [a], hence [a] is in [W] (classically — and the
       consequence is decidable, so constructively too) *)
    assert (HW : ¬ ¬ W a).
    { intros HnW. apply Hsome. exact (Hout a HnW). }
    assert (Hd : tv.1 = S (length log) /\ msg_byte m a = Some tv.2).
    { apply dec_stable. intros Hno. apply HW. intros HWa.
      apply Hno. exact (Hin a tv HWa Ha). }
    destruct Hd as [Ht Hb]. rewrite Ht. split.
    + rewrite log_byte_S (lookup_app_r log [m] (length log) (Nat.le_refl _))
              Nat.sub_diag /=. exact Hb.
    + rewrite length_app /=. intros (t & Hlo & Hhi & _). lia.
Qed.

(** THE SANITY CHECK: [WeakGhost.wlat_agree_store] is the singleton instance,
    at [W := (= a)].  (Restated rather than re-proved — the point is that the
    general lemma really does subsume the one-byte one.) *)
Lemma wlat_agree_store_win_singleton img log (m : wmsg) a v'
    (mm : gmap Z (nat * bv 8)) :
  msg_byte m a = Some v' ->
  (forall a', a' <> a -> msg_byte m a' = None) ->
  wlat_agree img log mm ->
  wlat_agree img (log ++ [m]) (<[a := (S (length log), v')]> mm).
Proof.
  intros Hma Hother Hag.
  apply (wlat_agree_store_win img log m (fun z => z = a) mm).
  - exact Hother.
  - intros a' tv -> Hlk. rewrite lookup_insert in Hlk. simplify_eq/=.
    split; [reflexivity|exact Hma].
  - intros a' Hne. by rewrite lookup_insert_ne.
  - exact Hag.
Qed.

(* ====================================================================== *)
(** ** 2. What a width-[n] store's message writes, and the floor it leaves *)

(** The general-width twin of [WeakVProp.wwrite_msg_byte1_none]: outside the
    half-open range the access covers, the message is silent. *)
Lemma wwrite_msg_win_none tid (pa : Arch.pa) (n : N) {w : N} (v : bv w) (a : Z) :
  ¬ (pa_z pa <= a < pa_z pa + Z.of_N n) ->
  msg_byte (wwrite_msg tid pa n v) a = None.
Proof.
  intros Hout. rewrite /msg_byte /wwrite_msg /=.
  case_bool_decide as Hle; [|reflexivity].
  apply lookup_ge_None_2. rewrite length_map length_seq. lia.
Qed.

(** ... and it IS the one-byte lemma at [n = 1]. *)
Lemma wwrite_msg_win_none1 tid (pa : Arch.pa) (v : bv (8 * 1)) (a : Z) :
  a <> pa_z pa -> msg_byte (wwrite_msg tid pa 1 v) a = None.
Proof.
  intros Hne. apply (wwrite_msg_win_none tid pa 1 v a).
  change (Z.of_N 1) with 1. lia.
Qed.

(** THE WINDOW FLOOR.  [WeakVProp.flr_store_post] covers the ONE byte a
    single-byte store wrote; a width-[n] store raises the floor at every byte
    of its window, because [WeakMem.store_post_run] folds [store_post] over
    all of them and a fold only ever raises. *)
Lemma coh_store_post_bytes_in ws rl (as_ : list Z) t a :
  a ∈ as_ -> (t <= coh (store_post_bytes ws rl as_ t) a)%nat.
Proof.
  rewrite /store_post_bytes. revert ws.
  induction as_ as [|a0 l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; simpl.
  - etrans; [apply store_post_coh|].
    exact (proj1 (store_post_fold_le rl t l (store_post ws rl a t)) a).
  - by apply IH.
Qed.

Lemma flr_store_post_run ws rl base (n : nat) t (j : nat) :
  (j < n)%nat ->
  (t <= flr (ws_view (store_post_run ws rl base n t)) (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite flr_ws_view.
  assert (Hmem : (base + Z.of_nat j) ∈ map (fun k : nat => base + Z.of_nat k) (seq 0 n)).
  { apply elem_of_list_In, in_map_iff. exists j.
    split; [reflexivity|apply in_seq; lia]. }
  pose proof (coh_store_post_bytes_in ws rl _ t _ Hmem) as Hc.
  rewrite /store_post_run. lia.
Qed.

(** The two projections of the interpreter's own write post-state that this
    file needs (the log one is [WeakInterp.wwrite_post_log]). *)
Lemma wwrite_post_img tid (s : wmstate) ak (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) :
  wm_img (wwrite_post tid s ak pa n v) = wm_img s.
Proof. reflexivity. Qed.

(** ... hence: after a width-[n] store, the hart's floor at EVERY byte of the
    window covers the store's own timestamp.  This is the [flr_store_post] of
    the window, and it is the whole post-view side condition of §4. *)
Lemma flr_wwrite_post tid (σ : wmstate) ak (a : Arch.pa) (n : N)
    (v : bv (8 * n)) (j : nat) :
  (j < N.to_nat n)%nat ->
  (S (length (wm_log σ))
     <= flr (ws_view (wm_ws (wwrite_post tid σ ak a n v))) (acc_addr a j))%nat.
Proof.
  intros Hj.
  change (wm_ws (wwrite_post tid σ ak a n v))
    with (store_post_run (wm_ws σ) (ak_sync ak) (pa_z a) (N.to_nat n)
                         (S (length (wm_log σ)))).
  rewrite /acc_addr. by apply flr_store_post_run.
Qed.

(* ====================================================================== *)
(** ** 3. The four-byte instance of the window update, pure part

    [wins4] is the shape four successive [ghost_map_update]s leave behind, in
    the order §4 performs them (byte 0 first, so its insert is innermost). *)

Definition wins4 (a : Arch.pa) (T : nat) (v : bv 32)
    (mm : gmap Z (nat * bv 8)) : gmap Z (nat * bv 8) :=
  <[acc_addr a 3 := (T, nth_byte v 3)]>
  (<[acc_addr a 2 := (T, nth_byte v 2)]>
  (<[acc_addr a 1 := (T, nth_byte v 1)]>
  (<[acc_addr a 0 := (T, nth_byte v 0)]> mm))).

Lemma wins4_lookup_in (a : Arch.pa) T (v : bv 32) mm (j : nat) :
  (j < 4)%nat -> wins4 a T v mm !! acc_addr a j = Some (T, nth_byte v j).
Proof.
  intros Hj.
  assert (H10 : acc_addr a 1 <> acc_addr a 0). { rewrite /acc_addr. lia. }
  assert (H20 : acc_addr a 2 <> acc_addr a 0). { rewrite /acc_addr. lia. }
  assert (H30 : acc_addr a 3 <> acc_addr a 0). { rewrite /acc_addr. lia. }
  assert (H21 : acc_addr a 2 <> acc_addr a 1). { rewrite /acc_addr. lia. }
  assert (H31 : acc_addr a 3 <> acc_addr a 1). { rewrite /acc_addr. lia. }
  assert (H32 : acc_addr a 3 <> acc_addr a 2). { rewrite /acc_addr. lia. }
  rewrite /wins4. destruct j as [|[|[|[|j]]]]; [| | | |lia].
  - rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
            lookup_insert //.
  - rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert_ne // lookup_insert //.
  - rewrite lookup_insert //.
Qed.

Lemma wins4_lookup_out (a : Arch.pa) T (v : bv 32) mm (z : Z) :
  ¬ (pa_z a <= z < pa_z a + 4) -> wins4 a T v mm !! z = mm !! z.
Proof.
  intros Hout.
  assert (H0 : acc_addr a 0 <> z). { rewrite /acc_addr. lia. }
  assert (H1 : acc_addr a 1 <> z). { rewrite /acc_addr. lia. }
  assert (H2 : acc_addr a 2 <> z). { rewrite /acc_addr. lia. }
  assert (H3 : acc_addr a 3 <> z). { rewrite /acc_addr. lia. }
  rewrite /wins4 lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
          lookup_insert_ne //.
Qed.

(** THE FOUR-BYTE WINDOW UPDATE, pure: appending the store's message and
    retargeting the four elements at the fresh top keeps the whole map
    accurate. *)
Lemma wlat_agree_store4 img log tid (a : Arch.pa) (v : bv 32)
    (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid a 4 v])
             (wins4 a (S (length log)) v mm).
Proof.
  intros Hag.
  apply (wlat_agree_store_win img log _ (fun z => pa_z a <= z < pa_z a + 4) mm).
  - intros z Hz. apply (wwrite_msg_win_none tid a 4 v z).
    change (Z.of_N 4) with 4. exact Hz.
  - intros z tv Hz Hlk.
    assert (Hcase : z = acc_addr a 0 \/ z = acc_addr a 1 \/
                    z = acc_addr a 2 \/ z = acc_addr a 3).
    { rewrite /acc_addr. lia. }
    destruct Hcase as [Hz4|[Hz4|[Hz4|Hz4]]]; subst z.
    + rewrite (wins4_lookup_in a (S (length log)) v mm 0 ltac:(lia)) in Hlk.
      simplify_eq/=. split; [reflexivity|].
      apply (wwrite_msg_byte tid a 4 v 0). lia.
    + rewrite (wins4_lookup_in a (S (length log)) v mm 1 ltac:(lia)) in Hlk.
      simplify_eq/=. split; [reflexivity|].
      apply (wwrite_msg_byte tid a 4 v 1). lia.
    + rewrite (wins4_lookup_in a (S (length log)) v mm 2 ltac:(lia)) in Hlk.
      simplify_eq/=. split; [reflexivity|].
      apply (wwrite_msg_byte tid a 4 v 2). lia.
    + rewrite (wins4_lookup_in a (S (length log)) v mm 3 ltac:(lia)) in Hlk.
      simplify_eq/=. split; [reflexivity|].
      apply (wwrite_msg_byte tid a 4 v 3). lia.
  - intros z Hz. by apply wins4_lookup_out.
  - exact Hag.
Qed.

(* ====================================================================== *)
(** ** 4. The bundle updates *)

Section store.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE PRIMITIVE.  Four full-fraction elements over the window, at
      arbitrary pre-timestamps and pre-values (see the header's note), one
      four-byte message appended: the authority moves to the new log and the
      four elements come back as a [wlat4] bundle at the message's own
      timestamp. *)
  Lemma wlat4_store_prim (tid : option nat) (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (t0 t1 t2 t3 : nat) (b0 b1 b2 b3 : bv 8) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_pointsto (acc_addr a 0) (DfracOwn 1) t0 b0 -∗
    wlat_pointsto (acc_addr a 1) (DfracOwn 1) t1 b1 -∗
    wlat_pointsto (acc_addr a 2) (DfracOwn 1) t2 b2 -∗
    wlat_pointsto (acc_addr a 3) (DfracOwn 1) t3 b3 ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid a 4 v]) ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    iIntros "Hi H0 H1 H2 H3".
    iDestruct "Hi" as (mm) "[Hauth %Hag]". rewrite /wlat_pointsto.
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 0)
            with "Hauth H0") as "[Hauth H0]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 1)
            with "Hauth H1") as "[Hauth H1]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 2)
            with "Hauth H2") as "[Hauth H2]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 3)
            with "Hauth H3") as "[Hauth H3]".
    iModIntro. iSplitL "Hauth".
    - iExists (wins4 a (S (length (wm_log σ))) v mm). iFrame "Hauth".
      iPureIntro. by apply wlat_agree_store4.
    - rewrite /wlat4. iFrame.
  Qed.

  (** THE BUNDLE UPDATE at an explicitly described post-state — the shape
      [WeakVProp.wpt_store_rule] has, so a caller that knows only "the image
      did not move and the log grew by this message" can fire it. *)
  Lemma wlat4_store_gen (tid : option nat) (σ σ' : wmstate) (a : Arch.pa)
      (t : nat) (w v : bv 32) :
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid a 4 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Himg Hlog. rewrite /wlat4. iIntros "Hi (H0 & H1 & H2 & H3)".
    rewrite Himg Hlog.
    by iMod (wlat4_store_prim tid σ a v with "Hi H0 H1 H2 H3") as "[$ $]".
  Qed.

  (** ... and at the interpreter's OWN write post-state, which is what a leaf
      hands the lock library.  [acc_wf] is not consumed by the proof (the
      update is entirely on the [Z]-keyed side); it is kept as a premise
      because every caller has it and because it is what makes "the window"
      the four bytes of [a] rather than a wrapped range. *)
  Lemma wlat4_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (t : nat) (w : bv 32) (v : bv (8 * 4)) :
    acc_wf a 4 ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 4 v))
                (wm_log (wwrite_post tid σ ak a 4 v)) ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros _. iIntros "Hi Hl".
    iApply (wlat4_store_gen tid σ (wwrite_post tid σ ak a 4 v) a t w v
              (wwrite_post_img tid σ ak a 4 v) (wwrite_post_log tid σ ak a 4 v)
              with "Hi Hl").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4b. the same at the [vwp_hold] / [wpt4] altitude *)

  (** The decode of an owned bundle: the two pure facts, plus the four
      elements at FOUR timestamps (whose values the caller no longer needs —
      the store overwrites them). *)
  Lemma wpt4_at_elems (a : Arch.pa) (dq : dfrac) (w : bv 32) (ws : wstate) :
    vwp_hold (wpt4 a dq w) ws ⊢
      ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗ ⌜acc_wf a 4⌝ ∗
      ∃ t0 t1 t2 t3 : nat,
        wlat_pointsto (acc_addr a 0) dq t0 (nth_byte w 0) ∗
        wlat_pointsto (acc_addr a 1) dq t1 (nth_byte w 1) ∗
        wlat_pointsto (acc_addr a 2) dq t2 (nth_byte w 2) ∗
        wlat_pointsto (acc_addr a 3) dq t3 (nth_byte w 3).
  Proof.
    rewrite /wpt4 !vwp_hold_sep !vwp_hold_pure !wpt_at.
    iIntros "(%Hal & %Hacc & H0 & H1 & H2 & H3)".
    iDestruct "H0" as (t0) "[H0 _]". iDestruct "H1" as (t1) "[H1 _]".
    iDestruct "H2" as (t2) "[H2 _]". iDestruct "H3" as (t3) "[H3 _]".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iExists t0, t1, t2, t3. iFrame.
  Qed.

  (** THE GLUE the acquire side wants too: an objective element bundle whose
      timestamp the hart's floor covers IS an owned four-byte points-to. *)
  Lemma wlat4_wpt4 (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 32)
      (ws : wstate) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    acc_wf a 4 ->
    (forall j : nat, (j < 4)%nat -> (t <= flr (ws_view ws) (acc_addr a j))%nat) ->
    wlat4 a dq t w -∗ vwp_hold (wpt4 a dq w) ws.
  Proof.
    intros Hal Hacc Hfl. rewrite /wlat4 /wpt4 !vwp_hold_sep !vwp_hold_pure.
    iIntros "(H0 & H1 & H2 & H3)".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iSplitL "H0"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 0%nat ltac:(lia)))|].
    iSplitL "H1"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 1%nat ltac:(lia)))|].
    iSplitL "H2"; [by iApply (wpt_at_intro _ _ _ t ws (Hfl 2%nat ltac:(lia)))|].
    by iApply (wpt_at_intro _ _ _ t ws (Hfl 3%nat ltac:(lia))).
  Qed.

  (** THE STORE RULE FOR THE BUNDLE, owned altitude.  The two pure conjuncts
      ride along unchanged; the post-view side condition is [flr_wwrite_post],
      i.e. the store's own post-state raises the floor at every byte of the
      window. *)
  Lemma wpt4_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (w : bv 32) (v : bv (8 * 4)) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt4 a (DfracOwn 1) w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 4 v))
                (wm_log (wwrite_post tid σ ak a 4 v)) ∗
    vwp_hold (wpt4 a (DfracOwn 1) v) (wm_ws (wwrite_post tid σ ak a 4 v)).
  Proof.
    iIntros "Hi Hpt".
    iDestruct (wpt4_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3) "(H0 & H1 & H2 & H3)".
    iMod (wlat4_store_prim tid σ a v with "Hi H0 H1 H2 H3") as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img tid σ ak a 4 v) (wwrite_post_log tid σ ak a 4 v).
    iFrame "Hi".
    iApply (wlat4_wpt4 a (DfracOwn 1) (S (length (wm_log σ))) v
              _ Hal Hacc with "Hl").
    intros j Hj. apply (flr_wwrite_post tid σ ak a 4 v j). lia.
  Qed.

End store.

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions wlat_agree_store_win.
Print Assumptions wlat4_store.
Print Assumptions wpt4_store.
