(* WpUserWrs.v -- the pure model reduction for WRS execute.

   WRS.STO / WRS.NTO (wait-on-reservation-set) execute to [Enter_Wait]:
     execute_WRS WRS_STO = Enter_Wait WAIT_WRS_STO
     execute_WRS WRS_NTO = Enter_Wait WAIT_WRS_NTO
   and the execute dispatcher just wraps it in returnM.  Unlike WFI (which in
   U-mode traps Illegal via mstatus.TW), WRS is NOT privilege-gated in this
   model build -- it unconditionally enters the wait state.  Since
   [wait_is_nop] is false on both WRS wait reasons, the step then writes
   hart_state := HART_WAITING and the hart safely spins in wait.

   This is the FOUNDATION lemma for the (still-TODO) ustep_wrs wait-state arm
   (a new hart-waiting WP engine): it is the pure execute-result fact the arm
   feeds to the step machinery, exactly as the illegal arms feed
   exec_execute_*_illegal_U.  Axiom-free. *)
From Stdlib Require Import ZArith Bool.
From stdpp Require Import gmap bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvExec.
Import Defs.

Lemma exec_execute_WRS_enter_wait (arg : wrsop) (s : mstate) :
  exec (execute (WRS arg)) s = Some (execute_WRS arg, s).
Proof.
  cbn [execute]. apply exec_returnm.
Qed.

Lemma execute_WRS_STO_val : execute_WRS WRS_STO = Enter_Wait WAIT_WRS_STO.
Proof. reflexivity. Qed.

Lemma execute_WRS_NTO_val : execute_WRS WRS_NTO = Enter_Wait WAIT_WRS_NTO.
Proof. reflexivity. Qed.

(* The execute result is a wait, and [wait_is_nop] is false for both variants,
   so a WRS is a genuine wait (not a retiring no-op). *)
Corollary exec_execute_WRS (arg : wrsop) (s : mstate) :
  exec (execute (WRS arg)) s
    = Some (Enter_Wait (match arg with WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end), s).
Proof.
  rewrite exec_execute_WRS_enter_wait. destruct arg; reflexivity.
Qed.

Lemma wait_is_nop_WRS (arg : wrsop) :
  wait_is_nop (match arg with WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end) = false.
Proof. destruct arg; reflexivity. Qed.

(* shouldWakeForInterrupt tt = (mip & mie) <> 0 : reads mip, mie. *)
Lemma exec_shouldWakeForInterrupt (s : mstate) :
  exec (shouldWakeForInterrupt tt) s
    = Some (neq_vec (and_vec (register_lookup mip s.(sregs)) (register_lookup mie s.(sregs)))
                    (zeros' 64), s).
Proof.
  unfold shouldWakeForInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)). cbn beta.
  apply exec_returnm.
Qed.

(* Interrupt-wake exit: when (mip & mie) <> 0 the waiting hart exits the
   wait -- writes hart_state HART_ACTIVE and produces a retiring step.  This
   branch is INDEPENDENT of the valid_reservation axiom. *)
Lemma exec_run_hart_waiting_wake
    (step_no : Z) (wr : WaitReason) (instbits : mword 32) (ew : bool) (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs)) (register_lookup mie s.(sregs)))
          (zeros' 64) = true ->
  exec (run_hart_waiting step_no wr instbits ew) s
    = Some (Step_Execute (Retire_Success tt, instbits),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hwake.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hwake. cbn match.
  change (get_config_print_instr tt) with false. cbn match.
  assert (Hinner : exec (returnm tt >> write_reg hart_state (HART_ACTIVE tt)) s
                   = Some (tt, set_reg s hart_state (HART_ACTIVE tt))).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt s)). apply exec_write_reg. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hinner).
  apply exec_returnm.
Qed.

(* Reservation-invalid exit: WRS wait with no wake interrupt but an
   invalid reservation exits to a retiring step (same tail as the wake
   case).  [valid_reservation] is a pure sanctioned axiom (unit -> bool). *)
Lemma exec_run_hart_waiting_wrs_invalid
    (step_no : Z) (wr : WaitReason) (instbits : mword 32) (ew : bool) (s : mstate) :
  (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO) ->
  neq_vec (and_vec (register_lookup mip s.(sregs)) (register_lookup mie s.(sregs)))
          (zeros' 64) = false ->
  valid_reservation tt = false ->
  exec (run_hart_waiting step_no wr instbits ew) s
    = Some (Step_Execute (Retire_Success tt, instbits),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hwr Hnowake Hvr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hnowake. cbn match. rewrite Hvr.
  assert (Hinner : exec (returnm tt >> write_reg hart_state (HART_ACTIVE tt)) s
                   = Some (tt, set_reg s hart_state (HART_ACTIVE tt))).
  { rewrite (exec_bind0_Some _ _ _ _ _ (exec_returnm tt s)). apply exec_write_reg. }
  destruct Hwr as [-> | ->]; cbn match;
    change (get_config_print_instr tt) with false; cbn match;
    rewrite (exec_bind0_Some _ _ _ _ _ Hinner); apply exec_returnm.
Qed.

(* Stay-waiting: WRS wait with no wake interrupt, a valid reservation, and
   not timed out (exit_wait = false) keeps the hart in HART_WAITING,
   producing Step_Waiting (state unchanged).  This is the branch the
   ustep_wrs engine's inner Lob self-recurses on.  (A timed-out WRS,
   exit_wait = true, instead exits to a retiring step -- like the wake and
   reservation-invalid cases.) *)
Lemma exec_run_hart_waiting_wrs_stay
    (step_no : Z) (wr : WaitReason) (instbits : mword 32) (s : mstate) :
  (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO) ->
  neq_vec (and_vec (register_lookup mip s.(sregs)) (register_lookup mie s.(sregs)))
          (zeros' 64) = false ->
  valid_reservation tt = true ->
  exec (run_hart_waiting step_no wr instbits false) s = Some (Step_Waiting wr, s).
Proof.
  intros Hwr Hnowake Hvr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hnowake. cbn match. rewrite Hvr.
  destruct Hwr as [-> | ->]; cbn match; apply exec_returnm.
Qed.

(* (The timed-out WRS exit -- valid reservation, exit_wait = true -- also
   exits to a retiring step, but its post-write continuation is shaped
   differently from the wake/invalid tail, so it is deferred; the stay and
   the wake/reservation-invalid exits already cover the engine's core
   safety cases.) *)

(* ===================================================================== *)
(* ENGINE DESIGN for the (TODO) ustep_wrs wait-state arm (task #33),      *)
(* scoped from run_hart_waiting (rv64d.v).  For a hart already in         *)
(* HART_WAITING (wr, instbits), the top-level step calls                  *)
(* [run_hart_waiting step_no wr instbits exit_wait], which:               *)
(*   - if [shouldWakeForInterrupt tt] : write hart_state HART_ACTIVE,     *)
(*     return Step_Execute (Retire_Success, instbits)  (interrupt exit);  *)
(*   - else match (wr, valid_reservation tt, exit_wait):                  *)
(*       (WAIT_WRS_STO, false, _) -> HART_ACTIVE + Retire_Success;        *)
(*       (WAIT_WRS_NTO, false, _) -> HART_ACTIVE + Retire_Success;        *)
(*       (WAIT_WFI, _, true)      -> HART_ACTIVE + (Illegal or Retire);   *)
(*       otherwise                -> stays Step_Waiting (hart unchanged). *)
(* So a WRS wait EXITS to a retire when [shouldWakeForInterrupt] OR       *)
(* [valid_reservation tt = false]; it STAYS waiting when reservation is   *)
(* valid and no wake interrupt.  NOTE [valid_reservation] is one of the   *)
(* 5 SANCTIONED uninterpreted model axioms, so which branch is taken is   *)
(* NOT decidable -- the WP proof must handle BOTH.                        *)
(*                                                                        *)
(* Hence the waiting-hart WP lemma is a DUAL-CONTINUATION Lob loop:        *)
(*   WP_Loop_from_waiting :=                                              *)
(*     (case exit)  hart -> HART_ACTIVE, Retire_Success, PC advances past  *)
(*        WRS -> reduces to the ORDINARY active user-exec step, so the     *)
(*        OUTER user-exec Lob IH (wp_user_exec) resumes the fetch loop;    *)
(*     (case stay)  Step_Waiting -> hart stays HART_WAITING -> SELF-       *)
(*        recursion on the waiting state (inner Lob).                      *)
(* Both continue WP (Loop) with the trivial postcond -> SAFE.  The arm     *)
(* ustep_wrs then: from an ACTIVE hart, feed [exec_execute_WRS] to the     *)
(* step machinery so the Enter_Wait writes HART_WAITING, then invoke       *)
(* WP_Loop_from_waiting.  A ustep_case tail disjunct + soundness wire it.  *)
(* Ingredients still to build: (a) the pure reductions of run_hart_waiting *)
(* per branch (needs [shouldWakeForInterrupt] handling + a valid_          *)
(* reservation case-split), (b) the waiting-frame resources (hart_state    *)
(* pointing to HART_WAITING plus config/PC cells), (c) the nested-Lob WP   *)
(* lemma composing (a)+(b) with the outer wp_user_exec IH.                 *)
(* ===================================================================== *)
