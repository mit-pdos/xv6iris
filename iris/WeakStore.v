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
      §3  [winsw] / [wlat_agree_store_w] — THE WINDOW INSERT AT EVERY WIDTH
          AT ONCE, and the pure window update over it.  [wins4] (§3b) and
          [WeakWord8.wins8] are its [n := 4] / [n := 8] instances, on the
          nose; the four- and eight-byte [wlat_agree] lemmas are one [apply]
          of the generic one each.
      §4  [wlat4_store] — the bundle update at the iProp altitude, full
          fraction, one four-byte message appended, all four elements
          retargeted at [S (length (wm_log σ))].  THIS is the deliverable the
          lock library consumes: it is what lets a releaser close the lock
          invariant at the value it just stored.
      §4b [wpt4_store] — the same at the vProp/[vwp_hold] altitude, with the
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
Require Import WeakLang.
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
Lemma wwrite_msg_win_none tid k (pa : Arch.pa) (n : N) {w : N} (v : bv w) (a : Z) :
  ¬ (pa_z pa <= a < pa_z pa + Z.of_N n) ->
  msg_byte (wwrite_msg tid k pa n v) a = None.
Proof.
  intros Hout. rewrite /msg_byte /wwrite_msg /=.
  case_bool_decide as Hle; [|reflexivity].
  apply lookup_ge_None_2. rewrite length_map length_seq. lia.
Qed.

(** ... and it IS the one-byte lemma at [n = 1]. *)
Lemma wwrite_msg_win_none1 tid k (pa : Arch.pa) (v : bv (8 * 1)) (a : Z) :
  a <> pa_z pa -> msg_byte (wwrite_msg tid k pa 1 v) a = None.
Proof.
  intros Hne. apply (wwrite_msg_win_none tid k pa 1 v a).
  change (Z.of_N 1) with 1. lia.
Qed.

(** WHICH ADDRESSES A WIDTH-[n] STORE CAN WRITE — the contrapositive of
    [wwrite_msg_win_none], packaged as "the message's footprint is inside the
    caller's list".  This is the frame premise the C/D/S window update of §3c
    takes, and it is discharged once per width. *)
Lemma wwrite_msg_zs tid k (a : Arch.pa) (n : N) {w : N} (v : bv w)
    (zs : list Z) :
  (forall j : nat, (j < N.to_nat n)%nat -> acc_addr a j ∈ zs) ->
  forall z, msg_byte (wwrite_msg tid k a n v) z <> None -> z ∈ zs.
Proof.
  intros Hzs z Hz.
  destruct (decide (pa_z a <= z < pa_z a + Z.of_N n)) as [Hr|Hr];
    [|by destruct Hz; apply (wwrite_msg_win_none tid k a n v z Hr)].
  assert (Heq : z = acc_addr a (Z.to_nat (z - pa_z a)))
    by (rewrite /acc_addr; lia).
  rewrite Heq. apply Hzs. rewrite /acc_addr in Heq. lia.
Qed.

Lemma wwrite_msg_zs4 tid k (a : Arch.pa) {w : N} (v : bv w) :
  forall z, msg_byte (wwrite_msg tid k a 4 v) z <> None ->
    z ∈ [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3].
Proof.
  apply (wwrite_msg_zs tid k a 4 v).
  intros j Hj. change (N.to_nat 4) with 4%nat in Hj.
  destruct j as [|[|[|[|j]]]];
    [set_solver|set_solver|set_solver|set_solver|lia].
Qed.

Lemma wwrite_msg_zs8 tid k (a : Arch.pa) {w : N} (v : bv w) :
  forall z, msg_byte (wwrite_msg tid k a 8 v) z <> None ->
    z ∈ [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3;
         acc_addr a 4; acc_addr a 5; acc_addr a 6; acc_addr a 7].
Proof.
  apply (wwrite_msg_zs tid k a 8 v).
  intros j Hj. change (N.to_nat 8) with 8%nat in Hj.
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];
    [set_solver|set_solver|set_solver|set_solver
    |set_solver|set_solver|set_solver|set_solver|lia].
Qed.

(** T2-0's FRAMING OF THE STATE MAP ACROSS A NON-PLAIN STORE, per width.
    [WeakGhost.wcds_ok_store_nonplain] is false at a [WLock] byte, so a
    generic store site must say why its own window carries none — and every
    such site holds four (eight) fragments AT ONE AND THE SAME state, whose
    ghost-map lookups are exactly what these take. *)
Lemma wcds_agree_nonplain4 log tid k (a : Arch.pa) {w : N} (v : bv w) mc
    (s0 : wcds) :
  k <> WCplain -> is_wlock s0 = false ->
  mc !! acc_addr a 0 = Some s0 -> mc !! acc_addr a 1 = Some s0 ->
  mc !! acc_addr a 2 = Some s0 -> mc !! acc_addr a 3 = Some s0 ->
  wcds_agree log mc ->
  wcds_agree (log ++ [wwrite_msg tid k a 4 v]) mc.
Proof.
  intros Hk Hnl K0 K1 K2 K3 Hag.
  apply (wcds_agree_nonplain_win _ _ _
           [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3]);
    [done|apply (wwrite_msg_zs4 _ _ a v)| |exact Hag].
  intros z s Hz Hs. assert (s = s0) as ->; [|exact Hnl].
  apply elem_of_cons in Hz as [->|Hz]; [congruence|].
  apply elem_of_cons in Hz as [->|Hz]; [congruence|].
  apply elem_of_cons in Hz as [->|Hz]; [congruence|].
  apply elem_of_cons in Hz as [->|Hz]; [congruence|].
  by apply elem_of_nil in Hz.
Qed.

Lemma wcds_agree_nonplain8 log tid k (a : Arch.pa) {w : N} (v : bv w) mc
    (s0 : wcds) :
  k <> WCplain -> is_wlock s0 = false ->
  (forall j : nat, (j < 8)%nat -> mc !! acc_addr a j = Some s0) ->
  wcds_agree log mc ->
  wcds_agree (log ++ [wwrite_msg tid k a 8 v]) mc.
Proof.
  intros Hk Hnl K Hag.
  apply (wcds_agree_nonplain_win _ _ _
           [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3;
            acc_addr a 4; acc_addr a 5; acc_addr a 6; acc_addr a 7]);
    [done|apply (wwrite_msg_zs8 _ _ a v)| |exact Hag].
  intros z s Hz Hs. assert (s = s0) as ->; [|exact Hnl].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 0%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 1%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 2%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 3%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 4%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 5%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 6%nat ltac:(lia)); congruence|].
  apply elem_of_cons in Hz as [->|Hz];
    [pose proof (K 7%nat ltac:(lia)); congruence|].
  by apply elem_of_nil in Hz.
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
  rewrite /store_post_run ctrl_post_coh. lia.
Qed.

(** D3-2: the same, for the DEPENDENCY-CARRYING store.  The operand views go
    into the forward bank and into [w_vcap]; the coherence floors are the
    dependency-free ones, so the window's post-view fact is unchanged. *)
Lemma flr_store_post_run_d ws rl vaddr vdata base (n : nat) t (j : nat) :
  (j < n)%nat ->
  (t <= flr (ws_view (store_post_run_d ws rl vaddr vdata base n t))
          (base + Z.of_nat j))%nat.
Proof.
  intros Hj. rewrite flr_ws_view.
  pose proof (store_post_run_d_coh ws rl vaddr vdata base n t j Hj). lia.
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
(** ** 3. THE WINDOW INSERT, AT EVERY WIDTH AT ONCE

    [winsw a T v n mm] is [mm] with the [n] bytes of [v] at [a] retargeted at
    timestamp [T] — byte 0 innermost, i.e. the shape [n] successive
    [ghost_map_update]s in index order leave behind.  This is the PRIMARY
    statement; [wins4] below and [WeakWord8.wins8] are its [n := 4] and
    [n := 8] instances, on the nose (both identifications are [reflexivity]).

    The width is a [N] on the message side ([WeakInterp.wwrite_msg] takes a
    [N]) and a [nat] on the insert-chain side, so [winsw] takes the [nat] and
    §3's [wlat_agree_store_w] converts at [N.to_nat] — the one place the two
    spellings meet. *)

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
    the latest-write map accurate.  [wlat_agree_store4] and
    [WeakWord8.wlat_agree_store8] are the [n := 4] / [n := 8] instances. *)
Lemma wlat_agree_store_w img log (tid : option nat) k (a : Arch.pa) (n : N)
    {m : N} (v : bv m) (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid k a n v])
             (winsw a (S (length log)) v (N.to_nat n) mm).
Proof.
  intros Hag.
  apply (wlat_agree_store_win img log _
           (fun z => pa_z a <= z < pa_z a + Z.of_N n) mm).
  - intros z Hz. by apply (wwrite_msg_win_none tid k a n v z).
  - intros z tv Hz Hlk.
    assert (Hex : exists j : nat, (j < N.to_nat n)%nat /\ z = acc_addr a j).
    { exists (Z.to_nat (z - pa_z a)). rewrite /acc_addr. split; lia. }
    destruct Hex as (j & Hj & ->).
    rewrite (winsw_lookup_in a (S (length log)) v (N.to_nat n) mm j Hj) in Hlk.
    simplify_eq/=. split; [reflexivity|].
    by apply (wwrite_msg_byte tid k a n v j).
  - intros z Hz. apply winsw_lookup_out. intros j Hj Heq.
    apply Hz. rewrite -Heq /acc_addr. lia.
  - exact Hag.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** 3b. The four-byte instance

    [wins4] is the shape four successive [ghost_map_update]s leave behind, in
    the order §4 performs them (byte 0 first, so its insert is innermost) —
    and it IS [winsw] at [n := 4], which is where its two lookup lemmas and
    its [wlat_agree] come from. *)

Definition wins4 (a : Arch.pa) (T : nat) (v : bv 32)
    (mm : gmap Z (nat * bv 8)) : gmap Z (nat * bv 8) :=
  winsw a T v 4 mm.

Lemma wins4_winsw (a : Arch.pa) T (v : bv 32) mm :
  wins4 a T v mm = winsw a T v (N.to_nat 4) mm.
Proof. reflexivity. Qed.

Lemma wins4_lookup_in (a : Arch.pa) T (v : bv 32) mm (j : nat) :
  (j < 4)%nat -> wins4 a T v mm !! acc_addr a j = Some (T, nth_byte v j).
Proof. intros Hj. rewrite wins4_winsw. apply winsw_lookup_in. lia. Qed.

Lemma wins4_lookup_out (a : Arch.pa) T (v : bv 32) mm (z : Z) :
  ¬ (pa_z a <= z < pa_z a + 4) -> wins4 a T v mm !! z = mm !! z.
Proof.
  intros Hout. rewrite wins4_winsw. apply winsw_lookup_out.
  intros j Hj. rewrite /acc_addr. lia.
Qed.

(** THE FOUR-BYTE WINDOW UPDATE, pure: the [n := 4] instance of §3. *)
Lemma wlat_agree_store4 img log tid k (a : Arch.pa) (v : bv 32)
    (mm : gmap Z (nat * bv 8)) :
  wlat_agree img log mm ->
  wlat_agree img (log ++ [wwrite_msg tid k a 4 v])
             (wins4 a (S (length log)) v mm).
Proof.
  intros Hag. rewrite wins4_winsw.
  by apply (wlat_agree_store_w img log tid k a 4 v mm).
Qed.

(* ====================================================================== *)
(** ** 3c. THE C/D/S WINDOW, AT EVERY WIDTH AT ONCE (φ-upgrade §1)

    The state map is keyed by the same addresses as the latest-write map but
    carries no value, so its window update is simply "set these addresses to
    one common state".  [winsl] is that; the store's own window is the list
    of its byte addresses, and BOTH widths (and the one-byte rule of
    [WeakVProp]) are instances. *)

Fixpoint winsl (zs : list Z) (s : wcds) (mc : gmap Z wcds) : gmap Z wcds :=
  match zs with
  | [] => mc
  | z :: zs' => <[z := s]> (winsl zs' s mc)
  end.

Lemma winsl_lookup_in zs s mc z : z ∈ zs -> winsl zs s mc !! z = Some s.
Proof.
  induction zs as [|z0 zs IH]; intros Hz; [by apply elem_of_nil in Hz|].
  simpl. apply elem_of_cons in Hz as [->|Hz]; [by rewrite lookup_insert|].
  destruct (decide (z = z0)) as [->|Hne]; [by rewrite lookup_insert|].
  rewrite lookup_insert_ne //. by apply IH.
Qed.

Lemma winsl_lookup_out zs s mc z : z ∉ zs -> winsl zs s mc !! z = mc !! z.
Proof.
  induction zs as [|z0 zs IH]; intros Hz; [reflexivity|]. simpl.
  rewrite lookup_insert_ne; [apply IH|]; set_solver.
Qed.

(** THE OWNED WINDOW UPDATE, pure.  Inside the window the state becomes the
    class's own step ([WDirty c] for a plain store, [WClean] for a release —
    the D→C flip); outside, nothing moved and the message wrote nothing. *)
(** [WCexcl] maps to [WDirty c] rather than [WClean]: an exclusive store
    neither dirties nor publishes, so the honest step is "keep the state" —
    and [WDirty c] is the WEAKENING of both possible incoming states
    ([wcds_clean_dirty]), which keeps the target uniform across the window
    and so keeps the primitive premise-free. *)
Definition wcds_plain_step (c : CPU) (k : wm_class) : wcds :=
  match k with WCrel => WClean | _ => WDirty c end.

Lemma wcds_agree_winsl log mnew (zs : list Z) (c : CPU) mc :
  wm_tid mnew = Some (fin_to_nat c) ->
  (forall z, msg_byte mnew z <> None -> z ∈ zs) ->
  (forall z, z ∈ zs -> exists s, mc !! z = Some s /\ (s = WClean \/ s = WDirty c)) ->
  wcds_agree log mc ->
  wcds_agree (log ++ [mnew]) (winsl zs (wcds_plain_step c (wm_ak mnew)) mc).
Proof.
  intros Htid Hcov Hold Hag z s Hz.
  destruct (decide (z ∈ zs)) as [Hin|Hout].
  - rewrite (winsl_lookup_in zs _ mc z Hin) in Hz. simplify_eq.
    destruct (Hold z Hin) as (s0 & Hs0 & Hs0ok).
    pose proof (wcds_ok_store_own log mnew z c s0 Htid Hs0ok (Hag z s0 Hs0))
      as Hstep.
    destruct (wm_ak mnew) eqn:Hk; simpl in Hstep |- *; [exact Hstep|exact Hstep|].
    destruct Hs0ok as [-> | ->]; simpl in Hstep;
      [by apply wcds_clean_dirty|exact Hstep].
  - rewrite (winsl_lookup_out zs _ mc z Hout) in Hz.
    apply wcds_ok_app; [|by apply Hag].
    intros m0 Hm0. apply elem_of_list_singleton in Hm0 as ->.
    destruct (msg_byte mnew z) as [b|] eqn:Hb; [|reflexivity].
    exfalso. apply Hout, Hcov. by rewrite Hb.
Qed.

Section cdswin.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wcds_lookup_list (c : CPU) (zs : list Z) mc :
    ghost_map_auth weak_cds_name 1 mc -∗ ([∗ list] z ∈ zs, wown_st c z) -∗
    ⌜forall z, z ∈ zs ->
       exists s, mc !! z = Some s /\ (s = WClean \/ s = WDirty c)⌝.
  Proof.
    iIntros "Ha Hl". iInduction zs as [|z zs] "IH"; simpl.
    - iPureIntro. intros z Hz. by apply elem_of_nil in Hz.
    - iDestruct "Hl" as "[Hz Hl]".
      iDestruct (wown_st_lookup with "Ha Hz") as %Hz0.
      iDestruct ("IH" with "Ha Hl") as %Hrest.
      iPureIntro. intros z' Hz'. apply elem_of_cons in Hz' as [->|Hz'];
        [exact Hz0|by apply Hrest].
  Qed.

  Lemma wcds_update_list (c : CPU) (zs : list Z) (snew : wcds) mc :
    (snew = WClean \/ snew = WDirty c) ->
    ghost_map_auth weak_cds_name 1 mc -∗ ([∗ list] z ∈ zs, wown_st c z) ==∗
    ghost_map_auth weak_cds_name 1 (winsl zs snew mc) ∗
    ([∗ list] z ∈ zs, wown_st c z).
  Proof.
    intros Hnew. iIntros "Ha Hl".
    iInduction zs as [|z zs] "IH" forall (mc); simpl; [by iFrame|].
    iDestruct "Hl" as "[Hz Hl]".
    iMod ("IH" with "Ha Hl") as "[Ha Hl]".
    iDestruct "Hz" as (s) "[Hz _]". rewrite /wcds_el.
    iMod (ghost_map_update snew with "Ha Hz") as "[Ha Hz]".
    iModIntro. iFrame "Ha Hl". iExists snew. by iFrame "Hz".
  Qed.

  (** THE C/D/S HALF OF AN OWNED STORE, width-generic: hand it the state
      authority and the window's owned states, get back the authority at the
      new log and the window's owned states.  Both bundle prims below are one
      application of it. *)
  Lemma wcds_store_list (c : CPU) (mnew : wmsg) (log : list wmsg)
      (zs : list Z) mc :
    wm_tid mnew = Some (fin_to_nat c) ->
    (forall z, msg_byte mnew z <> None -> z ∈ zs) ->
    wcds_agree log mc ->
    ghost_map_auth weak_cds_name 1 mc -∗ ([∗ list] z ∈ zs, wown_st c z) ==∗
    ∃ mc', ghost_map_auth weak_cds_name 1 mc' ∗
           ⌜wcds_agree (log ++ [mnew]) mc'⌝ ∗
           ([∗ list] z ∈ zs, wown_st c z).
  Proof.
    intros Htid Hcov Hag. iIntros "Ha Hl".
    iDestruct (wcds_lookup_list with "Ha Hl") as %Hold.
    iMod (wcds_update_list c zs (wcds_plain_step c (wm_ak mnew))
            with "Ha Hl") as "[Ha Hl]".
    { destruct (wm_ak mnew); simpl; [by right|by left|by right]. }
    iModIntro. iExists _. iFrame "Ha Hl". iPureIntro.
    by apply wcds_agree_winsl.
  Qed.

End cdswin.

(* ====================================================================== *)
(** ** 4. The bundle updates *)

Section store.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE OWNED FOUR-BYTE BUNDLES (φ-upgrade §1).  [wlat4]'s and [wpt4]'s
      twins with the byte states OWNED (clean-or-dirty-by-[c]) rather than
      pinned clean: the shape a plain store consumes and produces. *)
  Definition wlat4_own (c : CPU) (a : Arch.pa) (t : nat) (w : bv 32) : iProp Σ :=
    (wlat_elem (acc_addr a 0) (DfracOwn 1) t (nth_byte w 0) ∗
       wown_st c (acc_addr a 0) ∗
     wlat_elem (acc_addr a 1) (DfracOwn 1) t (nth_byte w 1) ∗
       wown_st c (acc_addr a 1) ∗
     wlat_elem (acc_addr a 2) (DfracOwn 1) t (nth_byte w 2) ∗
       wown_st c (acc_addr a 2) ∗
     wlat_elem (acc_addr a 3) (DfracOwn 1) t (nth_byte w 3) ∗
       wown_st c (acc_addr a 3))%I.

  Definition wpt4_own (c : CPU) (a : Arch.pa) (w : bv 32) : vProp Σ :=
    (⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗ ⌜acc_wf a 4⌝ ∗
     wpt_own_h c (acc_addr a 0) (nth_byte w 0) ∗
     wpt_own_h c (acc_addr a 1) (nth_byte w 1) ∗
     wpt_own_h c (acc_addr a 2) (nth_byte w 2) ∗
     wpt_own_h c (acc_addr a 3) (nth_byte w 3))%I.

  Lemma wpt4_own_of_wpt4 c a w : wpt4 a (DfracOwn 1) w ⊢ wpt4_own c a w.
  Proof.
    rewrite /wpt4 /wpt4_own !wpt_own_h_of_wpt. iIntros "$".
  Qed.

  Lemma wpt4_own_facts c a w :
    wpt4_own c a w ⊢ ⌜is_aligned_paddr (Physaddr a) 4 = true /\ acc_wf a 4⌝.
  Proof. iIntros "(% & % & _)". by iPureIntro. Qed.

  Lemma wpt4_own_mono c a w ws ws' :
    ws_le ws ws' ->
    vwp_hold (wpt4_own c a w) ws ⊢ vwp_hold (wpt4_own c a w) ws'.
  Proof. apply vwp_hold_mono. Qed.

  (** THE PRIMITIVE.  Four full-fraction elements over the window, at
      arbitrary pre-timestamps and pre-values (see the header's note), one
      four-byte message appended: the authority moves to the new log and the
      four elements come back as a [wlat4] bundle at the message's own
      timestamp. *)
  Lemma wlat4_store_prim (tid : option nat) k (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (t0 t1 t2 t3 : nat) (b0 b1 b2 b3 : bv 8) :
    k <> WCplain ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_pointsto (acc_addr a 0) (DfracOwn 1) t0 b0 -∗
    wlat_pointsto (acc_addr a 1) (DfracOwn 1) t1 b1 -∗
    wlat_pointsto (acc_addr a 2) (DfracOwn 1) t2 b2 -∗
    wlat_pointsto (acc_addr a 3) (DfracOwn 1) t3 b3 ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid k a 4 v]) ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hk. iIntros "Hi H0 H1 H2 H3".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hc & %Hagc)".
    rewrite /wlat_pointsto /wlat_elem.
    iDestruct "H0" as "[H0 C0]". iDestruct "H1" as "[H1 C1]".
    iDestruct "H2" as "[H2 C2]". iDestruct "H3" as "[H3 C3]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 0)
            with "Hauth H0") as "[Hauth H0]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 1)
            with "Hauth H1") as "[Hauth H1]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 2)
            with "Hauth H2") as "[Hauth H2]".
    iMod (ghost_map_update (S (length (wm_log σ)), nth_byte v 3)
            with "Hauth H3") as "[Hauth H3]".
    (* T2-0: the window's four bytes are pinned CLEAN by the very fragments
       the caller handed in, so none of them is a [WLock] byte — which is
       what [wcds_agree_nonplain_win] needs to frame the state map across a
       non-plain store. *)
    iDestruct (ghost_map_lookup with "Hc C0") as %K0.
    iDestruct (ghost_map_lookup with "Hc C1") as %K1.
    iDestruct (ghost_map_lookup with "Hc C2") as %K2.
    iDestruct (ghost_map_lookup with "Hc C3") as %K3.
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins4 a (S (length (wm_log σ))) v mm), mc. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store4|].
      iPureIntro.
      exact (wcds_agree_nonplain4 _ tid k a v mc WClean Hk eq_refl
               K0 K1 K2 K3 Hagc).
    - rewrite /wlat4 /wlat_pointsto /wlat_elem. iFrame.
  Qed.

  (** THE OWNED PRIMITIVE — the entry form of every PLAIN store.  It takes
      the window's value elements at full fraction PLUS its owned C/D states,
      and gives them back with the states stepped: dirty after a [WCplain]
      store, clean after a [WCrel] one (the D->C flip).  Its side condition is
      the mirror of the clean form's: an exclusive store may not run through
      it, because it neither dirties nor publishes. *)
  Lemma wlat4_store_prim_own (c : CPU) k (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (t0 t1 t2 t3 : nat) (b0 b1 b2 b3 : bv 8) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat_elem (acc_addr a 0) (DfracOwn 1) t0 b0 -∗ wown_st c (acc_addr a 0) -∗
    wlat_elem (acc_addr a 1) (DfracOwn 1) t1 b1 -∗ wown_st c (acc_addr a 1) -∗
    wlat_elem (acc_addr a 2) (DfracOwn 1) t2 b2 -∗ wown_st c (acc_addr a 2) -∗
    wlat_elem (acc_addr a 3) (DfracOwn 1) t3 b3 -∗ wown_st c (acc_addr a 3) ==∗
    wlat_interp (wm_img σ)
      (wm_log σ ++ [wwrite_msg (Some (fin_to_nat c)) k a 4 v]) ∗
    wlat4_own c a (S (length (wm_log σ))) v.
  Proof.
    iIntros "Hi H0 C0 H1 C1 H2 C2 H3 C3".
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
    iMod (wcds_store_list c (wwrite_msg (Some (fin_to_nat c)) k a 4 v)
            (wm_log σ) [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3]
            mc eq_refl (wwrite_msg_zs4 _ _ a v) Hagc
            with "Hc [C0 C1 C2 C3]") as (mc') "(Hc & %Hagc' & Hl)".
    { simpl. iFrame. }
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins4 a (S (length (wm_log σ))) v mm), mc'. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store4|by iPureIntro].
    - simpl. iDestruct "Hl" as "(C0 & C1 & C2 & C3 & _)".
      rewrite /wlat4_own /wlat_elem. iFrame.
  Qed.

  (** THE BUNDLE UPDATE at an explicitly described post-state — the shape
      [WeakVProp.wpt_store_rule] has, so a caller that knows only "the image
      did not move and the log grew by this message" can fire it. *)
  Lemma wlat4_store_gen (tid : option nat) k (σ σ' : wmstate) (a : Arch.pa)
      (t : nat) (w v : bv 32) :
    k <> WCplain ->
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid k a 4 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hk Himg Hlog. rewrite /wlat4. iIntros "Hi (H0 & H1 & H2 & H3)".
    rewrite Himg Hlog.
    by iMod (wlat4_store_prim tid k σ a v _ _ _ _ _ _ _ _ Hk
               with "Hi H0 H1 H2 H3") as "[$ $]".
  Qed.

  (** ... and at the interpreter's OWN write post-state, which is what a leaf
      hands the lock library.  [acc_wf] is not consumed by the proof (the
      update is entirely on the [Z]-keyed side); it is kept as a premise
      because every caller has it and because it is what makes "the window"
      the four bytes of [a] rather than a wrapped range. *)
  Lemma wlat4_store (tid : option nat) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (t : nat) (w : bv 32) (v : bv (8 * 4)) :
    ak_latest ak = true ->
    acc_wf a 4 ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 4 v))
                (wm_log (wwrite_post tid σ ak a 4 v)) ∗
    wlat4 a (DfracOwn 1) (S (length (wm_log σ))) v.
  Proof.
    intros Hlt _. iIntros "Hi Hl".
    iApply (wlat4_store_gen tid (wm_class_of ak (wm_ws σ)) σ
              (wwrite_post tid σ ak a 4 v) a t w v
              ltac:(unfold wm_class_of; rewrite Hlt; discriminate)
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
    ak_latest ak = true ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt4 a (DfracOwn 1) w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post tid σ ak a 4 v))
                (wm_log (wwrite_post tid σ ak a 4 v)) ∗
    vwp_hold (wpt4 a (DfracOwn 1) v) (wm_ws (wwrite_post tid σ ak a 4 v)).
  Proof.
    intros Hlt. iIntros "Hi Hpt".
    iDestruct (wpt4_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3) "(H0 & H1 & H2 & H3)".
    iMod (wlat4_store_prim tid (wm_class_of ak (wm_ws σ)) σ a v
            _ _ _ _ _ _ _ _ ltac:(unfold wm_class_of; rewrite Hlt; discriminate)
            with "Hi H0 H1 H2 H3") as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img tid σ ak a 4 v) (wwrite_post_log tid σ ak a 4 v).
    iFrame "Hi".
    iApply (wlat4_wpt4 a (DfracOwn 1) (S (length (wm_log σ))) v
              _ Hal Hacc with "Hl").
    intros j Hj. apply (flr_wwrite_post tid σ ak a 4 v j). lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4c. THE OWNED ALTITUDE — [wpt4_own] (φ-upgrade §1)

      The decode / re-assembly pair and the store rule, exactly mirroring
      §4b's clean ones but carrying the byte states instead of pinning them
      clean.  This is what an [sw] leaf consumes and produces. *)

  Lemma wpt4_own_at_elems (c : CPU) (a : Arch.pa) (w : bv 32) (ws : wstate) :
    vwp_hold (wpt4_own c a w) ws ⊢
      ⌜is_aligned_paddr (Physaddr a) 4 = true⌝ ∗ ⌜acc_wf a 4⌝ ∗
      ∃ t0 t1 t2 t3 : nat,
        wlat_elem (acc_addr a 0) (DfracOwn 1) t0 (nth_byte w 0) ∗
          wown_st c (acc_addr a 0) ∗
        wlat_elem (acc_addr a 1) (DfracOwn 1) t1 (nth_byte w 1) ∗
          wown_st c (acc_addr a 1) ∗
        wlat_elem (acc_addr a 2) (DfracOwn 1) t2 (nth_byte w 2) ∗
          wown_st c (acc_addr a 2) ∗
        wlat_elem (acc_addr a 3) (DfracOwn 1) t3 (nth_byte w 3) ∗
          wown_st c (acc_addr a 3).
  Proof.
    rewrite /wpt4_own !vwp_hold_sep !vwp_hold_pure !wpt_own_h_at.
    iIntros "(%Hal & %Hacc & H0 & H1 & H2 & H3)".
    iDestruct "H0" as (t0) "(H0 & S0 & _)".
    iDestruct "H1" as (t1) "(H1 & S1 & _)".
    iDestruct "H2" as (t2) "(H2 & S2 & _)".
    iDestruct "H3" as (t3) "(H3 & S3 & _)".
    iSplitR; [iPureIntro; exact Hal|]. iSplitR; [iPureIntro; exact Hacc|].
    iExists t0, t1, t2, t3. iFrame.
  Qed.

  Lemma wlat4_own_wpt4_own (c : CPU) (a : Arch.pa) (t : nat) (w : bv 32)
      (ws : wstate) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    acc_wf a 4 ->
    (forall j : nat, (j < 4)%nat -> (t <= flr (ws_view ws) (acc_addr a j))%nat) ->
    wlat4_own c a t w -∗ vwp_hold (wpt4_own c a w) ws.
  Proof.
    intros Hal Hacc Hfl.
    rewrite /wlat4_own /wpt4_own !vwp_hold_sep !vwp_hold_pure.
    iIntros "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3)".
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
    by iApply (wpt_own_h_at_intro c _ _ t ws (Hfl 3%nat ltac:(lia))
                 with "H3 S3").
  Qed.

  (** THE OWNED STORE RULE at the interpreter's own write post-state. *)
  Lemma wpt4_store_own (c : CPU) (σ : wmstate) (ak : akinfo) (a : Arch.pa)
      (w : bv 32) (v : bv (8 * 4)) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt4_own c a w) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post (Some (fin_to_nat c)) σ ak a 4 v))
                (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak a 4 v)) ∗
    vwp_hold (wpt4_own c a v)
             (wm_ws (wwrite_post (Some (fin_to_nat c)) σ ak a 4 v)).
  Proof.
    iIntros "Hi Hpt".
    iDestruct (wpt4_own_at_elems with "Hpt") as "(%Hal & %Hacc & Hpt)".
    iDestruct "Hpt" as (t0 t1 t2 t3) "(H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3)".
    iMod (wlat4_store_prim_own c (wm_class_of ak (wm_ws σ)) σ a v
            with "Hi H0 S0 H1 S1 H2 S2 H3 S3") as "[Hi Hl]".
    iModIntro.
    rewrite (wwrite_post_img (Some (fin_to_nat c)) σ ak a 4 v)
            (wwrite_post_log (Some (fin_to_nat c)) σ ak a 4 v).
    iFrame "Hi".
    iApply (wlat4_own_wpt4_own c a (S (length (wm_log σ))) v _ Hal Hacc
              with "Hl").
    intros j Hj. apply (flr_wwrite_post (Some (fin_to_nat c)) σ ak a 4 v j).
    lia.
  Qed.

  (** THE OWNED LOAD FACTS: the flat window and its pinnedness, four
      applications of [WeakInstr.wpt_own_h_byte_flat_pin]. *)
  Lemma wpt4_own_flat_pin (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 32) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4_own c a w) (wm_ws σ) -∗
    ⌜acc_wf a 4 /\ forall j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j) /\
       pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. rewrite /wpt4_own !vwp_hold_sep !vwp_hold_pure.
    iIntros "Hi (%Hal & %Hacc & H0 & H1 & H2 & H3)".
    iDestruct (wpt_own_h_byte_flat_pin c σ a 4 (nth_byte w 0) 0 Hwf Hacc
                 ltac:(lia) with "Hi H0") as %E0.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 4 (nth_byte w 1) 1 Hwf Hacc
                 ltac:(lia) with "Hi H1") as %E1.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 4 (nth_byte w 2) 2 Hwf Hacc
                 ltac:(lia) with "Hi H2") as %E2.
    iDestruct (wpt_own_h_byte_flat_pin c σ a 4 (nth_byte w 3) 3 Hwf Hacc
                 ltac:(lia) with "Hi H3") as %E3.
    iPureIntro. split; [exact Hacc|]. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  Lemma wpt4_own_flat (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 32) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4_own c a w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 4)%nat ->
       wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt4_own_flat_pin c σ a w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj1 (Hall j Hj)).
  Qed.

  Lemma wpt4_own_pinned (c : CPU) (σ : wmstate) (a : Arch.pa) (w : bv 32) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (wpt4_own c a w) (wm_ws σ) -∗
    ⌜forall j : nat, (j < 4)%nat -> pinned_read σ (acc_addr a j)⌝.
  Proof.
    intros Hwf. iIntros "Hi Hpt".
    iDestruct (wpt4_own_flat_pin c σ a w Hwf with "Hi Hpt") as %[_ Hall].
    iPureIntro. intros j Hj. exact (proj2 (Hall j Hj)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4d. THE SYNC ALTITUDE — [wlat4_sync] (φ-upgrade, deliverable A)

      A byte the kernel RACY-READS (the [started] flag) has to be in the S
      state, or [WeakRacy]'s load rules cannot be given their new
      [WeakGhost.sync_win] premise.  S is entered by DISCARDING the state
      element, so the four-byte bundle for such a word is:

        the four VALUE elements at full fraction — a store still consumes
        and retargets them — plus the four PERSISTENT sync witnesses, which
        it does not.

      What the S state buys is exactly what the racy rules need and what
      §C's preservation reads: [WeakGhost.wcds_sync] says NO [WCplain]
      message ever writes the byte, so no racy read of it can observe an
      unpublished owned store.  And it is self-enforcing: a plain store
      needs the full-fraction state element, which a sync byte does not
      have ([WeakGhost.wcds_el_sync_excl]), so the only stores that can
      reach the word are the non-plain ones — precisely the class
      [wlat4_store_prim] already requires. *)

  Definition wlat4_el (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 32)
      : iProp Σ :=
    (wlat_elem (acc_addr a 0) dq t (nth_byte w 0) ∗
     wlat_elem (acc_addr a 1) dq t (nth_byte w 1) ∗
     wlat_elem (acc_addr a 2) dq t (nth_byte w 2) ∗
     wlat_elem (acc_addr a 3) dq t (nth_byte w 3))%I.

  Lemma wlat4_el_of_wlat4 (a : Arch.pa) (dq : dfrac) (t : nat) (w : bv 32) :
    wlat4 a dq t w -∗ wlat4_el a dq t w.
  Proof.
    rewrite /wlat4 /wlat4_el /wlat_pointsto.
    iIntros "([H0 _] & [H1 _] & [H2 _] & [H3 _])". iFrame "H0 H1 H2 H3".
  Qed.

  Definition wlat4_sync (a : Arch.pa) (t : nat) (w : bv 32) : iProp Σ :=
    (wlat4_el a (DfracOwn 1) t w ∗ sync_win a 4)%I.

  Lemma wlat4_sync_win (a : Arch.pa) (t : nat) (w : bv 32) :
    wlat4_sync a t w -∗ sync_win a 4.
  Proof. iIntros "[_ #$]". Qed.

  (** The elementwise reading, the twin of [WeakStarted.wlat4_latest_val]
      over the bare elements. *)
  Lemma wlat4_el_latest_val (img : _) (log : list wmsg) (a : Arch.pa)
      (dq : dfrac) (t : nat) (w : bv 32) :
    wlat_interp img log -∗ wlat4_el a dq t w -∗
    ⌜forall j : nat, (j < 4)%nat ->
       latest_val (img_z img) log (acc_addr a j) t (nth_byte w j)⌝.
  Proof.
    iIntros "Hi (H0 & H1 & H2 & H3)".
    iDestruct (wlat_lookup_elem with "Hi H0") as %E0.
    iDestruct (wlat_lookup_elem with "Hi H1") as %E1.
    iDestruct (wlat_lookup_elem with "Hi H2") as %E2.
    iDestruct (wlat_lookup_elem with "Hi H3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** THE MINT.  A word no message has ever written — which is every [.bss]
      word at boot, and exactly what the escrow's own allocation premise
      says — may be turned sync once and for all, giving up the four clean
      states for the four persistent witnesses. *)
  Lemma wlat4_sync_mint (img : _) (log : list wmsg) (a : Arch.pa) (t : nat)
      (w : bv 32) :
    (forall j : nat, (j < 4)%nat -> wcds_sync log (acc_addr a j)) ->
    wlat_interp img log -∗ wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp img log ∗ wlat4_sync a t w.
  Proof.
    intros Hsy. rewrite /wlat4 /wlat_pointsto.
    iIntros "Hi ([E0 C0] & [E1 C1] & [E2 C2] & [E3 C3])".
    rewrite /wclean.
    iMod (sync_mint img log _ _ (Hsy 0%nat ltac:(lia)) with "Hi C0")
      as "[Hi #S0]".
    iMod (sync_mint img log _ _ (Hsy 1%nat ltac:(lia)) with "Hi C1")
      as "[Hi #S1]".
    iMod (sync_mint img log _ _ (Hsy 2%nat ltac:(lia)) with "Hi C2")
      as "[Hi #S2]".
    iMod (sync_mint img log _ _ (Hsy 3%nat ltac:(lia)) with "Hi C3")
      as "[Hi #S3]".
    iModIntro. iFrame "Hi". rewrite /wlat4_sync /wlat4_el. iFrame "E0 E1 E2 E3".
    by iApply (sync_win4 a with "S0 S1 S2 S3").
  Qed.

  (** THE SYNC STORE.  [wlat4_store_prim]'s twin: the state map is untouched
      (the sync entries survive by [WeakGhost.wcds_ok_store_nonplain]), only
      the four value elements move to the fresh message's timestamp. *)
  Lemma wlat4_sync_store_prim (tid : option nat) k (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (t : nat) (w : bv 32) :
    k <> WCplain ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4_sync a t w ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid k a 4 v]) ∗
    wlat4_sync a (S (length (wm_log σ))) v.
  Proof.
    intros Hk. iIntros "Hi [(H0 & H1 & H2 & H3) #Hs]".
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
    (* T2-0: the window is pinned SYNC by the persistent witnesses, so it
       carries no [WLock] byte. *)
    iDestruct (sync_win_byte a 4 0 ltac:(simpl; lia) with "Hs") as "S0".
    iDestruct (sync_win_byte a 4 1 ltac:(simpl; lia) with "Hs") as "S1".
    iDestruct (sync_win_byte a 4 2 ltac:(simpl; lia) with "Hs") as "S2".
    iDestruct (sync_win_byte a 4 3 ltac:(simpl; lia) with "Hs") as "S3".
    rewrite /sync_byte /wcds_el.
    iDestruct (ghost_map_lookup with "Hc S0") as %K0.
    iDestruct (ghost_map_lookup with "Hc S1") as %K1.
    iDestruct (ghost_map_lookup with "Hc S2") as %K2.
    iDestruct (ghost_map_lookup with "Hc S3") as %K3.
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins4 a (S (length (wm_log σ))) v mm), mc. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store4|].
      iPureIntro. exact (wcds_agree_nonplain4 _ tid k a v mc WSync Hk eq_refl
                           K0 K1 K2 K3 Hagc).
    - rewrite /wlat4_sync /wlat4_el /wlat_elem. by iFrame "H0 H1 H2 H3 Hs".
  Qed.

  (** The FLAT reading of the sync bundle — [WeakLock.wlat4_flat_gen]'s twin
      over the bare elements, which is what the racy waiter needs to know
      the flag word is in memory. *)
  Lemma wlat_el_flat_pin (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (v : bv 8) :
    wlog_wf (wm_log σ) ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_elem (pa_z a) dq t v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v /\
     latest_ts (wm_log σ) (pa_z a) = t⌝.
  Proof.
    intros Hwf. iIntros "Hi He".
    iDestruct (wlat_lookup_elem with "Hi He") as %Hlat.
    iDestruct (wlat_flat_lookup_e σ a dq t v Hwf with "Hi He") as %Hfl.
    iPureIntro. split; [exact Hfl|]. exact (latest_val_ts _ _ _ _ _ Hlat).
  Qed.

  Lemma wlat4_el_flat_gen (σ : wmstate) (a : Arch.pa) (dq : dfrac) (t : nat)
      (w : bv 32) :
    wlog_wf (wm_log σ) -> acc_wf a 4 ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4_el a dq t w -∗
    ⌜(forall j : nat, (j < 4)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) /\
     (forall j : nat, (j < 4)%nat -> latest_ts (wm_log σ) (acc_addr a j) = t)⌝.
  Proof.
    intros Hwf Hacc. iIntros "Hi (H0 & H1 & H2 & H3)".
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 0 = Some (nth_byte w 0)
               /\ latest_ts (wm_log σ) (acc_addr a 0) = t⌝)%I as %E0.
    { rewrite -(acc_wf_byte a 4 0 Hacc ltac:(lia)).
      iApply (wlat_el_flat_pin σ (pa_add a 0) dq t (nth_byte w 0) Hwf
                with "Hi [H0]").
      rewrite (acc_wf_byte a 4 0 Hacc ltac:(lia)). iExact "H0". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 1 = Some (nth_byte w 1)
               /\ latest_ts (wm_log σ) (acc_addr a 1) = t⌝)%I as %E1.
    { rewrite -(acc_wf_byte a 4 1 Hacc ltac:(lia)).
      iApply (wlat_el_flat_pin σ (pa_add a 1) dq t (nth_byte w 1) Hwf
                with "Hi [H1]").
      rewrite (acc_wf_byte a 4 1 Hacc ltac:(lia)). iExact "H1". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 2 = Some (nth_byte w 2)
               /\ latest_ts (wm_log σ) (acc_addr a 2) = t⌝)%I as %E2.
    { rewrite -(acc_wf_byte a 4 2 Hacc ltac:(lia)).
      iApply (wlat_el_flat_pin σ (pa_add a 2) dq t (nth_byte w 2) Hwf
                with "Hi [H2]").
      rewrite (acc_wf_byte a 4 2 Hacc ltac:(lia)). iExact "H2". }
    iAssert (⌜wflat (wm_img σ) (wm_log σ) !! pa_add a 3 = Some (nth_byte w 3)
               /\ latest_ts (wm_log σ) (acc_addr a 3) = t⌝)%I as %E3.
    { rewrite -(acc_wf_byte a 4 3 Hacc ltac:(lia)).
      iApply (wlat_el_flat_pin σ (pa_add a 3) dq t (nth_byte w 3) Hwf
                with "Hi [H3]").
      rewrite (acc_wf_byte a 4 3 Hacc ltac:(lia)). iExact "H3". }
    iPureIntro. split; intros j Hj;
      destruct j as [|[|[|[|j]]]];
      solve [ exact (proj1 E0) | exact (proj1 E1) | exact (proj1 E2)
            | exact (proj1 E3) | exact (proj2 E0) | exact (proj2 E1)
            | exact (proj2 E2) | exact (proj2 E3) | lia ].
  Qed.

  Lemma wlat4_sync_flat_gen (σ : wmstate) (a : Arch.pa) (t : nat) (w : bv 32) :
    wlog_wf (wm_log σ) -> acc_wf a 4 ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4_sync a t w -∗
    ⌜(forall j : nat, (j < 4)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) /\
     (forall j : nat, (j < 4)%nat -> latest_ts (wm_log σ) (acc_addr a j) = t)⌝.
  Proof.
    intros Hwf Hacc. iIntros "Hi [He _]".
    by iApply (wlat4_el_flat_gen σ a (DfracOwn 1) t w Hwf Hacc with "Hi He").
  Qed.

  Lemma wlat4_sync_store_gen (tid : option nat) k (σ σ' : wmstate)
      (a : Arch.pa) (t : nat) (w v : bv 32) :
    k <> WCplain ->
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid k a 4 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4_sync a t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat4_sync a (S (length (wm_log σ))) v.
  Proof.
    intros Hk Himg Hlog. iIntros "Hi Hw". rewrite Himg Hlog.
    by iMod (wlat4_sync_store_prim tid k σ a v t w Hk with "Hi Hw") as "[$ $]".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4d'. THE LOCK ALTITUDE — [wlat4L] (T2-0, S6 §4/§6b)

      The lock word's four bytes ride the FOURTH C/D/S state
      ([WeakGhost.WLock]) rather than [WClean], so the bundle
      [WeakLock.wlock_inv] holds is the [wlat4_sync] shape with the four
      persistent sync witnesses replaced by four EXCLUSIVE lock fragments:

        the four VALUE elements at full fraction — a store retargets them —
        plus the four [WLock] state fragments, which it hands back unchanged
        (the state does not move; only the log grows).

      What the [WLock] state buys is the VALUE PROTOCOL, which nothing else
      in the framework can state: a store may reach these bytes only through
      [wlat4L_store_gen], whose premise is that the message is acquire- or
      release-shaped ([WeakGhost.wlock_shaped]).  A plain store cannot: it
      needs [wown_st], i.e. a [WClean]/[WDirty] element, which disagrees with
      the auth ([WeakGhost.wlock_st_clean_excl]).  And a NON-protocol
      exclusive store cannot either, because [wlat4_store_prim]'s
      [wlat_pointsto] carries [wclean].

      [n0] — the log length at registration — is a parameter of [wlat4_lock]
      and EXISTENTIAL in [wlat4L], so that [WeakLock.wlock_inv] keeps its
      arity and every downstream statement about it is unchanged. *)

  Definition wlock_win (a : Arch.pa) (n0 : nat) : iProp Σ :=
    (wlock_st (acc_addr a 0) (pa_z a) n0 ∗ wlock_st (acc_addr a 1) (pa_z a) n0 ∗
     wlock_st (acc_addr a 2) (pa_z a) n0 ∗
     wlock_st (acc_addr a 3) (pa_z a) n0)%I.

  Definition wlat4_lock (a : Arch.pa) (n0 : nat) (t : nat) (w : bv 32)
      : iProp Σ :=
    (wlat4_el a (DfracOwn 1) t w ∗ wlock_win a n0)%I.

  (** The bundle [wlock_inv] holds.  [n0] is hidden — a client never names
      the registration point; the export does, off the fragment. *)
  Definition wlat4L (a : Arch.pa) (t : nat) (w : bv 32) : iProp Σ :=
    (∃ n0 : nat, wlat4_lock a n0 t w)%I.

  Global Instance wlock_win_timeless a n0 : Timeless (wlock_win a n0).
  Proof. rewrite /wlock_win. apply _. Qed.
  Global Instance wlat4_lock_timeless a n0 t w : Timeless (wlat4_lock a n0 t w).
  Proof. rewrite /wlat4_lock /wlat4_el /wlat_elem. apply _. Qed.
  Global Instance wlat4L_timeless a t w : Timeless (wlat4L a t w).
  Proof. rewrite /wlat4L. apply _. Qed.
  Global Instance wlat4L_objective a t w :
    Objective (⎡wlat4L a t w⎤ : vProp Σ).
  Proof. apply _. Qed.

  Lemma wlock_win_lookup (a : Arch.pa) (n0 : nat) mc :
    ghost_map_auth weak_cds_name 1 mc -∗ wlock_win a n0 -∗
    ⌜forall j : nat, (j < 4)%nat ->
       mc !! acc_addr a j = Some (WLock (pa_z a) n0)⌝.
  Proof.
    iIntros "Ha (S0 & S1 & S2 & S3)".
    iDestruct (wlock_st_lookup with "Ha S0") as %K0.
    iDestruct (wlock_st_lookup with "Ha S1") as %K1.
    iDestruct (wlock_st_lookup with "Ha S2") as %K2.
    iDestruct (wlock_st_lookup with "Ha S3") as %K3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact K0|exact K1|exact K2|exact K3|lia].
  Qed.

  (** THE REGISTRATION MINT: an ordinary (clean) four-byte element bundle
      becomes the lock word's bundle, registered at the CURRENT log length —
      where the protocol's suffix obligation is vacuous, so the word's
      pre-registration history ([initlock]'s plain store) is irrelevant. *)
  Lemma wlat4L_mint (img : _) (log : list wmsg) (a : Arch.pa) (t : nat)
      (w : bv 32) :
    wlat_interp img log -∗ wlat4 a (DfracOwn 1) t w ==∗
    wlat_interp img log ∗ wlat4L a t w.
  Proof.
    rewrite /wlat4 /wlat_pointsto.
    iIntros "Hi ([E0 C0] & [E1 C1] & [E2 C2] & [E3 C3])".
    iMod (wlock_register img log (acc_addr a 0) (pa_z a)
            ltac:(rewrite /acc_addr; lia) with "Hi C0") as "[Hi L0]".
    iMod (wlock_register img log (acc_addr a 1) (pa_z a)
            ltac:(rewrite /acc_addr; lia) with "Hi C1") as "[Hi L1]".
    iMod (wlock_register img log (acc_addr a 2) (pa_z a)
            ltac:(rewrite /acc_addr; lia) with "Hi C2") as "[Hi L2]".
    iMod (wlock_register img log (acc_addr a 3) (pa_z a)
            ltac:(rewrite /acc_addr; lia) with "Hi C3") as "[Hi L3]".
    iModIntro. iFrame "Hi". iExists (length log).
    rewrite /wlat4_lock /wlat4_el /wlock_win. iFrame.
  Qed.

  (** THE PROTOCOL STORE.  [wlat4_sync_store_prim]'s twin: the state map is
      untouched (the [WLock] entries survive by
      [WeakGhost.wcds_ok_store_lock]), only the four value elements move —
      and the price is the shape premise, which is the whole content of
      T2-0. *)
  Lemma wlat4_lock_store_prim (tid : option nat) k (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (n0 t : nat) (w : bv 32) :
    wlock_shaped (wwrite_msg tid k a 4 v) ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4_lock a n0 t w ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid k a 4 v]) ∗
    wlat4_lock a n0 (S (length (wm_log σ))) v.
  Proof.
    intros Hsh. iIntros "Hi [(H0 & H1 & H2 & H3) Hlk]".
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
    iDestruct (wlock_win_lookup with "Hc Hlk") as %K.
    iModIntro. iSplitL "Hauth Hc".
    - iExists (wins4 a (S (length (wm_log σ))) v mm), mc. iFrame "Hauth Hc".
      iSplitR; [iPureIntro; by apply wlat_agree_store4|].
      iPureIntro.
      apply (wcds_agree_store_lock _ _ _
               [acc_addr a 0; acc_addr a 1; acc_addr a 2; acc_addr a 3]
               (pa_z a) n0); [reflexivity|exact Hsh
                             |apply (wwrite_msg_zs4 _ _ a v)| |exact Hagc].
      intros z Hz.
      apply elem_of_cons in Hz as [->|Hz]; [apply (K 0%nat); lia|].
      apply elem_of_cons in Hz as [->|Hz]; [apply (K 1%nat); lia|].
      apply elem_of_cons in Hz as [->|Hz]; [apply (K 2%nat); lia|].
      apply elem_of_cons in Hz as [->|Hz]; [apply (K 3%nat); lia|].
      by apply elem_of_nil in Hz.
    - rewrite /wlat4_lock /wlat4_el /wlat_elem. by iFrame.
  Qed.

  Lemma wlat4L_store_prim (tid : option nat) k (σ : wmstate) (a : Arch.pa)
      (v : bv 32) (t : nat) (w : bv 32) :
    wlock_shaped (wwrite_msg tid k a 4 v) ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4L a t w ==∗
    wlat_interp (wm_img σ) (wm_log σ ++ [wwrite_msg tid k a 4 v]) ∗
    wlat4L a (S (length (wm_log σ))) v.
  Proof.
    intros Hsh. iIntros "Hi Hw". iDestruct "Hw" as (n0) "Hw".
    iMod (wlat4_lock_store_prim tid k σ a v n0 t w Hsh with "Hi Hw")
      as "[$ Hw]".
    iModIntro. by iExists n0.
  Qed.

  (** ... at an explicitly described post-state — the shape the lock cores
      have ([WeakLock.wlat4_store_gen]'s twin). *)
  Lemma wlat4L_store_gen (tid : option nat) k (σ σ' : wmstate) (a : Arch.pa)
      (t : nat) (w v : bv 32) :
    wlock_shaped (wwrite_msg tid k a 4 v) ->
    wm_img σ' = wm_img σ ->
    wm_log σ' = (wm_log σ ++ [wwrite_msg tid k a 4 v])%list ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wlat4L a t w ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    wlat4L a (S (length (wm_log σ))) v.
  Proof.
    intros Hsh Himg Hlog. iIntros "Hi Hw". rewrite Himg Hlog.
    by iMod (wlat4L_store_prim tid k σ a v t w Hsh with "Hi Hw") as "[$ $]".
  Qed.

  (** The FLAT reading, [WeakLock.wlat4_flat_gen]'s twin over the lock
      bundle — what the acquire's spin test branches on. *)
  Lemma wlat4L_flat_gen (σ : wmstate) (a : Arch.pa) (t : nat) (w : bv 32) :
    wlog_wf (wm_log σ) -> acc_wf a 4 ->
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat4L a t w -∗
    ⌜(forall j : nat, (j < 4)%nat ->
        wflat (wm_img σ) (wm_log σ) !! pa_add a j = Some (nth_byte w j)) /\
     (forall j : nat, (j < 4)%nat -> latest_ts (wm_log σ) (acc_addr a j) = t)⌝.
  Proof.
    intros Hwf Hacc. iIntros "Hi Hw". iDestruct "Hw" as (n0) "[He _]".
    by iApply (wlat4_el_flat_gen σ a (DfracOwn 1) t w Hwf Hacc with "Hi He").
  Qed.

  (** THE EXPORT AT THE BUNDLE ALTITUDE (T2-0's deliverable): the lock
      word's whole VALUE PROTOCOL, per byte, read off the bundle the
      invariant holds.  [n0] stays hidden — the statement says "there is a
      registration point past which every message on this byte is
      acquire- or release-shaped", which is exactly what S6 §3 case #5
      consumes. *)
  Lemma wlp_at_wlat4L (img : _) (log : list wmsg) (a : Arch.pa) (t : nat)
      (w : bv 32) :
    wlat_interp img log -∗ wlat4L a t w -∗
    ⌜exists n0 : nat, forall j : nat, (j < 4)%nat ->
       wlp_at log (acc_addr a j) (pa_z a) n0⌝.
  Proof.
    iIntros "Hi Hw". iDestruct "Hw" as (n0) "[_ (S0 & S1 & S2 & S3)]".
    iDestruct (wlp_at_of_lock with "Hi S0") as %P0.
    iDestruct (wlp_at_of_lock with "Hi S1") as %P1.
    iDestruct (wlp_at_of_lock with "Hi S2") as %P2.
    iDestruct (wlp_at_of_lock with "Hi S3") as %P3.
    iPureIntro. exists n0. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact P0|exact P1|exact P2|exact P3|lia].
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** 4e. THE φ EXPORTERS (φ-upgrade, deliverable C)

      What a data leaf pays its violation-freedom obligation with: one
      [WeakGhost.nv_ok] per byte of the window it touched, read off the very
      bundle it is handing back.  A LOADED window presents clean fragments
      (arm (a)); a STORED window presents the owned byte states the store
      primitive just produced (arm (b), the [WDirty] arm — the obligation
      quantifies over authors other than this hart). *)

  Lemma nv_ok_wpt4 (c : CPU) img log (a : Arch.pa) (dq : dfrac) (w : bv 32)
      (ws : wstate) :
    wlat_interp img log -∗ vwp_hold (wpt4 a dq w) ws -∗
    ⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi Hpt". iDestruct (wpt4_at_elems with "Hpt") as "(_ & _ & Hels)".
    iDestruct "Hels" as (t0 t1 t2 t3) "(H0 & H1 & H2 & H3)".
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H0") as %E0.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H1") as %E1.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H2") as %E2.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  Lemma nv_ok_wlat4_own (c : CPU) img log (a : Arch.pa) (t : nat) (w : bv 32) :
    wlat_interp img log -∗ wlat4_own c a t w -∗
    ⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi (H0 & S0 & H1 & S1 & H2 & S2 & H3 & S3)".
    iDestruct (nv_ok_of_own_st with "Hi S0") as %E0.
    iDestruct (nv_ok_of_own_st with "Hi S1") as %E1.
    iDestruct (nv_ok_of_own_st with "Hi S2") as %E2.
    iDestruct (nv_ok_of_own_st with "Hi S3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  Lemma nv_ok_wlat4 (c : CPU) img log (a : Arch.pa) (dq : dfrac) (t : nat)
      (w : bv 32) :
    wlat_interp img log -∗ wlat4 a dq t w -∗
    ⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi (H0 & H1 & H2 & H3)".
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H0") as %E0.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H1") as %E1.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H2") as %E2.
    iDestruct (nv_ok_of_pointsto _ _ c with "Hi H3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  (** The lock bundle's φ payment (T2-0).  It goes through the [WLock] arm,
      which carries [wcds_clean] as a conjunct precisely so that the
      acquire/release leaves keep paying their obligation off the very bundle
      they hand back. *)
  Lemma nv_ok_wlat4L (c : CPU) img log (a : Arch.pa) (t : nat) (w : bv 32) :
    wlat_interp img log -∗ wlat4L a t w -∗
    ⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi Hw". iDestruct "Hw" as (n0) "[_ (S0 & S1 & S2 & S3)]".
    iDestruct (nv_ok_of_lock _ _ c with "Hi S0") as %E0.
    iDestruct (nv_ok_of_lock _ _ c with "Hi S1") as %E1.
    iDestruct (nv_ok_of_lock _ _ c with "Hi S2") as %E2.
    iDestruct (nv_ok_of_lock _ _ c with "Hi S3") as %E3.
    iPureIntro. intros j Hj.
    destruct j as [|[|[|[|j]]]]; [exact E0|exact E1|exact E2|exact E3|lia].
  Qed.

  Lemma nv_ok_wlat4_sync (c : CPU) img log (a : Arch.pa) (t : nat) (w : bv 32) :
    wlat_interp img log -∗ wlat4_sync a t w -∗
    ⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝.
  Proof.
    iIntros "Hi [_ #Hs]".
    iAssert (⌜forall j : nat, (j < 4)%nat -> nv_ok log c (acc_addr a j)⌝)%I
      as %H; [|by iPureIntro].
    rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
    iApply (nv_ok_of_sync _ _ c with "Hi").
    by iApply (sync_win_byte a 4 j ltac:(simpl; lia) with "Hs").
  Qed.

End store.

Notation "a ↦w₄ₒ w" := (wpt4_own cpu_id a w)
  (at level 20, format "a  ↦w₄ₒ  w") : bi_scope.

(* ====================================================================== *)
(** ** 5. Soundness check *)

Print Assumptions wlat_agree_store_win.
Print Assumptions wlat4_store.
Print Assumptions wpt4_store.
