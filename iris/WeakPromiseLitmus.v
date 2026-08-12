(** * WeakPromiseLitmus.v — LB is REACHABLE in the full promising machine

    The W1 litmus sanity check of the M6 robustness effort
    ([claude-notes/projects/weak-memory-m6.md], W1's last box): the LOAD
    BUFFERING weak outcome [r1 = r2 = 1] is a genuine behavior of
    [WeakPromise.v]'s FULL promising machine.

    Together with [WeakLitmus.v]'s [lb_inv] — which proves the SAME outcome
    unreachable in the promise-free machine — this is the "the new machine is
    really weaker" check.  See the closing comment.

    Import surface is deliberately minimal: stdpp + [WeakMem] + [WeakPromise].
    In particular [WeakLitmus] is NOT imported (only cited); the handful of
    literal bytes and addresses it also uses are re-built locally. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite relations list.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Bytes, addresses, the era-initial image

    Same construction as [WeakLitmus.v]'s (cribbed, not imported): everything
    is a literal so the concrete side conditions reduce by computation. *)

Definition b0 : bv 8 := Z_to_bv 8 0.
Definition b1 : bv 8 := Z_to_bv 8 1.

Lemma b1_unsigned : bv_unsigned b1 = 1.
Proof. by vm_compute. Qed.

(** The two litmus bytes. *)
Local Notation ax := (0%Z).
Local Notation ay := (8%Z).

Definition img0m : gmap Z (bv 8) := <[ax := b0]> {[ay := b0]}.
Definition img0 : image := λ a, img0m !! a.

Lemma img0_x : img0 ax = Some b0.
Proof. rewrite /img0 /img0m lookup_insert //. Qed.
Lemma img0_y : img0 ay = Some b0.
Proof. rewrite /img0 /img0m lookup_insert_ne // lookup_singleton //. Qed.

(** The two messages the test produces: hart 0's [y := 1] and hart 1's
    [x := 1].  Both are single-byte. *)
Local Notation MY := (WMsg ay [b1] (Some 0%nat) WCplain).
Local Notation MX := (WMsg ax [b1] (Some 1%nat) WCplain).

Lemma msg_byte_hit a v tid k : msg_byte (WMsg a [v] tid k) a = Some v.
Proof.
  rewrite /msg_byte /=.
  rewrite (bool_decide_eq_true_2 (a ≤ a)%Z); [lia|].
  rewrite Z.sub_diag //.
Qed.

Lemma log_byte_MY : log_byte img0 [MY] 1%nat ay = Some b1.
Proof. rewrite /= msg_byte_hit //. Qed.

Lemma log_byte_MX : log_byte img0 [MY; MX] 2%nat ax = Some b1.
Proof. rewrite /= msg_byte_hit //. Qed.

(* ------------------------------------------------------------------ *)
(** ** The program: [P] for the two LB harts

    [WeakPromise]'s machine is parametric in an abstract per-agent LTS
    [pstep : P → wlabel → P → Prop].  The LB harts need exactly three
    program states, and the state after the load RECORDS the value read —
    that register is the [r1]/[r2] of the litmus outcome, so the final
    theorem can state [r1 = r2 = 1] by naming program states only. *)

Inductive lbp :=
| LBLoad (ald ast : Z)
    (** about to load from [ald]; will then store 1 to [ast] *)
| LBStore (ast : Z) (r : bv 8)
    (** loaded [r]; about to store 1 to [ast] *)
| LBDone (r : bv 8).
    (** finished, having read [r] *)

Global Instance lbp_eq_dec : EqDecision lbp.
Proof. solve_decision. Defined.

(** The LTS.  A plain (non-acquire, non-latest) single-byte load, then a
    plain single-byte store of [b1].  Note the load emits the value it read
    into the continuation — that is where the litmus register lives — while
    the store's label carries no read at all, which is precisely why hart 0's
    store may be PROMISED before its load has happened. *)
Inductive lbstep : lbp → wlabel → lbp → Prop :=
| LBSLoad ald ast t r :
    lbstep (LBLoad ald ast) (LLoad false false ald [(t, r)]) (LBStore ast r)
| LBSStore ast r :
    lbstep (LBStore ast r) (LStore false ast [b1]) (LBDone r).

(** LB: hart 0 = [load x; y := 1]; hart 1 = [load y; x := 1]. *)
Definition lb_p0 : lbp := LBLoad ax ay.
Definition lb_p1 : lbp := LBLoad ay ax.

(* ------------------------------------------------------------------ *)
(** ** Discharging the side conditions of the four memory steps *)

(** [read_ok_single] (the [∀ j] collapse at one byte) moved to
    [WeakPromise.v] with the W4 lift batch. *)

(** Both LB loads read a message that sits ABOVE the reader's whole floor
    (the reader has observed nothing at all yet), so the coherence window
    [readable] forbids is empty. *)
Lemma readable_above_floor img log ws base t v :
  log_byte img log t base = Some v →
  (Nat.max (load_vpre ws false) (coh ws base) ≤ t)%nat →
  readable img log ws (load_vpre ws false) base t.
Proof.
  intros Hv Hle. split; [by eexists|].
  intros (t' & ? & ? & _). lia.
Qed.

Lemma ws_init_floor a t : (Nat.max (load_vpre ws_init false) (coh ws_init a) ≤ t)%nat.
Proof. rewrite coh_init /load_vpre /=. lia. Qed.

(** Hart 1 reads hart 0's PROMISED (not yet fulfilled) message at ts = 1. *)
Lemma read_ok_h1 : read_ok img0 [MY] ws_init false false ay [(1%nat, b1)].
Proof.
  apply read_ok_single; [apply log_byte_MY|].
  eapply readable_above_floor; [apply log_byte_MY|apply ws_init_floor].
Qed.

(** Hart 0 reads hart 1's message at ts = 2 — its own view is still pristine
    (a promise step does not touch [pa_ws]). *)
Lemma read_ok_h0 : read_ok img0 [MY; MX] ws_init false false ax [(2%nat, b1)].
Proof.
  apply read_ok_single; [apply log_byte_MX|].
  eapply readable_above_floor; [apply log_byte_MX|apply ws_init_floor].
Qed.

(** [load_post_run_single] (a single-byte load's post-state, unfolded once)
    moved to [WeakMem.v] with the W4 lift batch. *)

(** Hart 1's state after its load is still bounded by the one-message log —
    the [ws_bounded] premise of [wpstep_store_now]. *)
Lemma ws_bounded_h1 : ws_bounded (load_post_run ws_init false ay [1%nat]) 1%nat.
Proof.
  apply load_post_run_bounded; [apply ws_bounded_init|].
  apply Forall_singleton. lia.
Qed.

(** THE KEY SIDE CONDITION — hart 0 fulfilling its ts = 1 promise of [y]
    AFTER having read [x] at ts = 2:

    - COH: the load touched byte [x] only, so [coh] at [y] is still 0 < 1.
    - EXT: [fulfil_vpre ws false = w_vwNew ws], and a PLAIN (non-acquire)
      load raises only [vrOld] and [coh] — [w_vwNew] is still 0 < 1.

    This is exactly the [po ∪ rf] cycle: were the load an acquire (or were a
    fence in between), [w_vwNew] would have been raised to 2 and EXT would
    fail, which is the fenced arm of the M6 argument in miniature. *)
Lemma fulfil_ok_h0 :
  fulfil_ok (load_post_run ws_init false ax [2%nat]) false ay 1%nat 1%nat.
Proof.
  rewrite load_post_run_single. split.
  - intros j Hj. assert (ay + Z.of_nat j = ay) as -> by lia.
    rewrite /load_post_at /= coh_upd_ne; [done|].
    rewrite lookup_empty /=. lia.
  - rewrite /fulfil_vpre /load_post_at /=. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The theorem: the LB weak outcome is a behavior of the full machine

    The interleaving (timestamps are nats; the log starts empty, so hart 0's
    promise lands at ts = 1):

      1. hart 0 PROMISES [y := 1]                     (WPPromise, ts = 1)
      2. hart 1 LOADS y, reading the PROMISE           (WPLoad, t = 1 → r2 = 1)
      3. hart 1 STORES [x := 1]                        (wpstep_store_now, ts = 2)
      4. hart 0 LOADS x, reading hart 1's store        (WPLoad, t = 2 → r1 = 1)
      5. hart 0 FULFILS its promise                    (WPFulfil, ts = 1)

    Step 5 is what makes this a BEHAVIOR rather than a doomed run: the final
    configuration has every promise set empty ([no_promises]). *)

Theorem lb_weak_outcome_reachable :
  ∃ (cfg : wpcfg lbp) (ag0 ag1 : wpagent lbp),
    (* a genuine behavior of the FULL machine: reachable, all promises kept *)
    wp_behavior lbstep img0 [lb_p0; lb_p1] cfg ∧
    (* hart 0's final program state records r1 = 1 … *)
    pc_ags cfg !! 0%nat = Some ag0 ∧ pa_st ag0 = LBDone b1 ∧
    (* … and hart 1's records r2 = 1 *)
    pc_ags cfg !! 1%nat = Some ag1 ∧ pa_st ag1 = LBDone b1.
Proof.
  eexists. do 2 eexists. split; [split|].
  { (* ---- the interleaving ---- *)
    (* 1. hart 0 PROMISES y := 1; the log was empty, so ts = 1 *)
    eapply rtc_l.
    { eapply (WPPromise lbstep _ 0%nat _ ay [b1] WCplain); [reflexivity|done]. }
    (* 2. hart 1 LOADS y and reads that promise *)
    eapply rtc_l.
    { eapply (WPLoad lbstep _ 1%nat _ false false ay [(1%nat, b1)]);
        [reflexivity|apply LBSLoad|apply read_ok_h1]. }
    (* 3. hart 1 STORES x := 1 (promise + immediate fulfil at the fresh top) *)
    eapply rtc_transitive.
    { eapply (wpstep_store_now lbstep _ 1%nat _ false ax [b1] WCplain);
        [reflexivity|apply LBSStore|done|apply ws_bounded_h1|set_solver]. }
    (* 4. hart 0 LOADS x and reads hart 1's store *)
    eapply rtc_l.
    { eapply (WPLoad lbstep _ 0%nat _ false false ax [(2%nat, b1)]);
        [reflexivity|apply LBSLoad|apply read_ok_h0]. }
    (* 5. hart 0 FULFILS its ts = 1 promise of y := 1 *)
    eapply rtc_l; [|apply rtc_refl].
    eapply (WPFulfil lbstep _ 0%nat _ false ay [b1] WCplain 1%nat);
      [reflexivity|apply LBSStore|set_solver|reflexivity|apply fulfil_ok_h0]. }
  { (* ---- every promise discharged ---- *)
    intros i ag Hlk. destruct i as [|[|i]]; simplify_eq/=; [set_solver|done]. }
  (* ---- the outcome: both harts recorded the value 1 ---- *)
  split_and!; reflexivity.
Qed.

(** The same statement with the litmus registers spelled out numerically:
    [r1 = r2 = 1]. *)
Corollary lb_weak_outcome_regs :
  ∃ (cfg : wpcfg lbp) (ag0 ag1 : wpagent lbp) (r1 r2 : bv 8),
    wp_behavior lbstep img0 [lb_p0; lb_p1] cfg ∧
    pc_ags cfg !! 0%nat = Some ag0 ∧ pa_st ag0 = LBDone r1 ∧
    pc_ags cfg !! 1%nat = Some ag1 ∧ pa_st ag1 = LBDone r2 ∧
    bv_unsigned r1 = 1 ∧ bv_unsigned r2 = 1.
Proof.
  destruct lb_weak_outcome_reachable as (cfg & ag0 & ag1 & ? & ? & ? & ? & ?).
  exists cfg, ag0, ag1, b1, b1.
  split_and!; try done; apply b1_unsigned.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The promise-free contrast (no proof here — a pointer)

    [WeakLitmus.v]'s LB section ([lb_c0] / [lb_inv] / [lb_forbidden]) proves
    that the SAME outcome — both harts reading 1 — is UNREACHABLE in the
    promise-free machine: with no promises, a store cannot enter the log
    before the program-order-earlier load has resolved, so an [x]-message must
    be preceded in the log by a [y]-message and vice versa, and that descent
    is impossible in a finite append-only log ([WeakLitmus.lb_descend]).

    That contrast is exactly the sanity check W1 asks for.  [WeakLitmus] is
    deliberately not imported here: it is cited, so that this file's import
    surface stays [WeakMem] + [WeakPromise].

    Consequences worth recording:

    - The full machine is STRICTLY weaker than the promise-free one, so the
      promise-free ⊆ full inclusion ([WeakPromise.wpstep_store_now], used at
      step 3 above) is not an equivalence — W1's erasure bridge really does
      have to be one-directional.
    - The single side condition standing between "promise-free" and this
      behavior is [fulfil_ok]'s EXT ([fulfil_vpre ws rl < ts]).  Step 5 goes
      through only because a PLAIN load leaves [w_vwNew] at 0; an acquire
      load, or a [fence r,rw] between the load and the store, raises
      [w_vwNew] to 2 and kills the fulfilment.  That is the miniature of the
      M6 Layer-1 argument for the fenced store class (D-M6-5's surviving pin
      is precisely [w_vwNew]). *)
