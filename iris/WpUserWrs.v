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
