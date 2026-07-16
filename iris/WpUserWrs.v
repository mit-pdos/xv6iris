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
Require Import RiscvLang RiscvExec RiscvTryStep.
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

(* ===================================================================== *)
(* §4 The three riscv_step reductions the ustep_wrs engine needs.          *)
(*                                                                        *)
(* try_step (rv64d.v:41736) reads hart_state and branches:                *)
(*   ACTIVE  -> run_hart_active  ; WAITING -> run_hart_waiting.            *)
(* The dispatch match then runs, THEN a SECOND read of hart_state         *)
(* selects the epilogue: HART_WAITING -> returnM true (NO tick_pc, NO     *)
(* minstret bump); HART_ACTIVE -> tick_pc >> (bump if retired&&inc).      *)
(*                                                                        *)
(* (1) ENTER-WAIT: an ACTIVE hart executes WRS -> Enter_Wait; the         *)
(*     dispatch WRITES hart_state := HART_WAITING (so the second read     *)
(*     takes the WAITING epilogue, PC unchanged).  This is the branch     *)
(*     [exec_riscv_step_notretire] canNOT reach -- its [Hhart_trap]       *)
(*     assumes the hart is still ACTIVE after dispatch, false here.       *)
(* (2) STAY: a WAITING hart run_hart_waiting stays (Step_Waiting); its     *)
(*     dispatch just asserts hart_is_waiting; the WAITING epilogue        *)
(*     returns true.  State unchanged bar the minstret_increment write.   *)
(* (3) WAKE: a WAITING hart run_hart_waiting exits (Retire_Success, hart  *)
(*     -> HART_ACTIVE); the ACTIVE epilogue tick_pc's PC := nextPC and    *)
(*     bumps minstret when [b].  Shaped exactly like a retiring step.     *)
(* ===================================================================== *)

Section WrsEnterWait.
  Context (s s_x : mstate) (wr : WaitReason) (instbits : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (Enter_Wait wr, instbits), s_x).
  Hypothesis Hnop : wait_is_nop wr = false.

  Let s_wait : mstate := set_reg s_x hart_state (HART_WAITING (wr, instbits)).

  Lemma exec_riscv_step_enter_wait : exec riscv_step s = Some (tt, s_wait).
  Proof using All.
    assert (Hts : exec (try_step 0 false) s = Some (true, s_wait)).
    { unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
        apply (exec_read_reg hart_state s_a). }
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    (* dispatch (Enter_Wait) >> read hart_state >>= match10 *)
    change (get_config_print_instr tt) with false.
    cbn match. cbv zeta. rewrite Hnop. cbn match beta iota.
    (* dispatch body = returnM tt >> write_reg hart_state (HART_WAITING ...) *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind0_Some.
            2:{ apply exec_returnM. }
            apply (exec_write_reg hart_state (HART_WAITING (wr, instbits)) s_x). }
        apply (exec_read_reg hart_state s_wait). }
    assert (Hw : register_lookup hart_state s_wait.(sregs) = HART_WAITING (wr, instbits)).
    { unfold s_wait, set_reg; cbn [sregs]. apply register_lookup_set. }
    rewrite Hw. cbn beta iota. apply exec_returnM. }
    unfold riscv_step. rewrite (exec_bind_Some _ _ _ _ _ Hts). reflexivity.
  Qed.
End WrsEnterWait.

Section WrsWaitStay.
  Context (s : mstate) (wr : WaitReason) (instbits : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_w :
    register_lookup hart_state s_a.(sregs) = HART_WAITING (wr, instbits).
  Hypothesis Hstay :
    exec (run_hart_waiting 0 wr instbits false) s_a = Some (Step_Waiting wr, s_a).

  (* STAY: the WAITING hart run_hart_waiting keeps waiting; the dispatch just
     asserts hart_is_waiting and the WAITING epilogue returns true.  Only the
     minstret_increment cell was written (s -> s_a), so the machine loops in
     place -- the self-recursion branch of the inner Löb. *)
  Lemma exec_riscv_step_waiting_stay : exec riscv_step s = Some (tt, s_a).
  Proof using All.
    assert (Hts : exec (try_step 0 false) s = Some (true, s_a)).
    { unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
        apply (exec_read_reg hart_state s_a). }
    cbn beta. rewrite Hhart_w. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hstay). cbn beta.
    cbn match.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg hart_state s_a). }
            rewrite Hhart_w. unfold Defs.assert_exp. cbn [hart_is_waiting]. reflexivity. }
        apply (exec_read_reg hart_state s_a). }
    rewrite Hhart_w. cbn beta iota. apply exec_returnM. }
    unfold riscv_step. rewrite (exec_bind_Some _ _ _ _ _ Hts). reflexivity.
  Qed.
End WrsWaitStay.

Section WrsWaitWake.
  Context (s : mstate) (wr : WaitReason) (instbits : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_w :
    register_lookup hart_state s_a.(sregs) = HART_WAITING (wr, instbits).
  (* WAKE / reservation-invalid: run_hart_waiting exits the wait -- writes
     hart_state HART_ACTIVE and produces a RETIRING step.  Its state is
     [s_wake]; the ACTIVE epilogue then tick_pc's PC := nextPC and bumps
     minstret when [b].  This is the exit branch of the inner Löb -- it lands
     back in an ACTIVE frame with PC advanced past the WRS. *)
  Let s_wake : mstate := set_reg s_a hart_state (HART_ACTIVE tt).
  Hypothesis Hwake :
    exec (run_hart_waiting 0 wr instbits false) s_a
      = Some (Step_Execute (Retire_Success tt, instbits), s_wake).

  Let s_tick : mstate := set_reg s_wake PC (register_lookup nextPC s_wake.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_waiting_wake : exec riscv_step s = Some (tt, s_final).
  Proof using All.
    assert (Hha : register_lookup hart_state s_wake.(sregs) = HART_ACTIVE tt).
    { unfold s_wake, set_reg; cbn [sregs]. apply register_lookup_set. }
    assert (Hmi : register_lookup (R_bool minstret_increment) s_wake.(sregs) = b).
    { unfold s_wake, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ | reflexivity ].
      unfold s_a, set_reg; cbn [sregs]. apply register_lookup_set. }
    assert (Hts : exec (try_step 0 false) s = Some (false, s_final)).
    { unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some. 2:{ apply exec_write_reg. }
        apply (exec_read_reg hart_state s_a). }
    cbn beta. rewrite Hhart_w. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hwake). cbn beta.
    cbn match.
    (* dispatch (Retire_Success) >> read hart_state >>= match10 *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg hart_state s_wake). }
            rewrite Hha. unfold Defs.assert_exp. cbn [hart_is_active]. reflexivity. }
        apply (exec_read_reg hart_state s_wake). }
    rewrite Hha. cbn beta iota.
    (* ACTIVE epilogue: tick_pc >> (and_boolM (returnM true) (read mi)) >>= ... *)
    erewrite exec_bind0_Some. 2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some. 2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    change (get_config_rvfi tt) with false.
    replace (register_lookup minstret_increment
               (set_reg s_wake PC (register_lookup nextPC s_wake.(sregs))).(sregs))
      with b.
    2:{ unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ (exact Hmi || (symmetry; exact Hmi)) | reflexivity ]. }
    unfold s_final, s_tick.
    destruct b.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some. 2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity. }
    unfold riscv_step. rewrite (exec_bind_Some _ _ _ _ _ Hts). reflexivity.
  Qed.
End WrsWaitWake.
