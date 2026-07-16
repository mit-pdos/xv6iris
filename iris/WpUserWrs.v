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

(* ===================================================================== *)
(* §5 The Iris wait-state engine for WRS.                                  *)
(*                                                                        *)
(*   [user_waiting_frame] : the user_frame resource bundle with           *)
(*     hart_state pointing to HART_WAITING and the PC PINNED to the WRS    *)
(*     va (nextPC owned but its value existential -- the wake exit reads   *)
(*     it into PC).                                                        *)
(*   [wp_wait_loop] : the inner Löb loop.  A waiting hart either STAYS     *)
(*     (Step_Waiting, self-recursion) or EXITS (interrupt-wake or an       *)
(*     invalid reservation), retiring back into the ordinary user frame    *)
(*     and resuming the OUTER user-exec loop.  Both branches are handled   *)
(*     because [valid_reservation] is an uninterpreted axiom.             *)
(*   [ustep_wrs] : the arm -- from an ACTIVE user_frame, execute a WRS     *)
(*     (Enter_Wait), landing in the waiting frame, then run wp_wait_loop.  *)
(*                                                                        *)
(* NOTE the hart_state cell is WRITTEN here (ACTIVE<->WAITING), which      *)
(* needs FULL ownership; the user_frame carries hart_state at fraction     *)
(* [dq], so the two loop lemmas take the side condition [dq = DfracOwn 1]  *)
(* (satisfied by every real instantiation -- each hart owns its own        *)
(* registers).                                                            *)
(* ===================================================================== *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
From stdpp Require Import gmap.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins.
Require Import SailStdpp.Values SailStdpp.MachineWord SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import SmodeCore WpIntrCore WpDecodeBridge.
Require Import UmodeFetch UmodeFetchC UmodeEcall UmodeWalk.
Require Import UptInv WpUserLoop WpUserBase UmodeStep.
Require Import Riscv.rv64d_types Riscv.rv64d.
Import Defs.
Local Open Scope Z_scope.

Section WpUserWrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (U : uctx).

  Local Notation stvec_v := (stvec_v U).
  Local Notation mie_v := (mie_v U).
  Local Notation midl_v := (midl_v U).
  Local Notation medl_v := (medl_v U).
  Local Notation mip_v := (mip_v U).
  Local Notation meip := (meip U).
  Local Notation seip := (seip U).
  Local Notation satp0 := (satp0 U).
  Local Notation root := (root U).
  Local Notation slots := (slots U).
  Local Notation spec := (spec U).
  Local Notation pmpcfg0 := (pmpcfg0 U).
  Local Notation pmpaddr00 := (pmpaddr00 U).
  Local Notation code := (code U).
  Local Notation data := (data U).
  Local Notation dq := (dq U).
  Local Notation dqc := (dqc U).
  Local Notation Hmm := (Hmm U).
  Local Notation Hs0 := (Hs0 U).
  Local Notation Hsatpmode := (Hsatpmode U).
  Local Notation Hasid := (Hasid U).
  Local Notation Hroot := (Hroot U).
  Local Notation Htvd := (Htvd U).
  Local Notation HpmpA := (HpmpA U).
  Local Notation Hpmp_ord := (Hpmp_ord U).
  Local Notation HpmpX := (HpmpX U).
  Local Notation HpmpR := (HpmpR U).
  Local Notation HpmpW := (HpmpW U).
  Local Notation Hpmp_cov := (Hpmp_cov U).
  Local Notation Hpter := (Hpter U).
  Local Notation Hspec := (Hspec U).

  Local Notation user_frame := (WpUserBase.user_frame U).
  Local Notation user_trap_frame := (WpUserBase.user_trap_frame U).
  Local Notation user_cfg := (WpUserBase.user_cfg U).
  Local Notation user_code := (WpUserBase.user_code U).
  Local Notation user_data := (WpUserBase.user_data U).

  (* ------------------------------------------------------------------ *)
  (* The waiting frame.                                                   *)
  (* ------------------------------------------------------------------ *)
  Definition user_waiting_frame
      (wr : WaitReason) (instbits : mword 32) (va : mword 64) : iProp Σ :=
    (∃ (ms_v sc_v stval_v sepc_v npc : mword 64)
       (g : gmap regidx (mword 64))
       (tlbvec : vec (option TLB_Entry) (2 ^ 6)),
      ⌜_get_Mstatus_SXL ms_v = 'b"10"⌝ ∗
      ⌜upt_tlb_ok spec tlbvec⌝ ∗
      hart_state ↦ᵣ{ dq } HART_WAITING (wr, instbits) ∗
      cur_privilege ↦ᵣ User ∗
      mstatus ↦ᵣ ms_v ∗
      scause ↦ᵣ sc_v ∗
      stval ↦ᵣ stval_v ∗
      sepc ↦ᵣ sepc_v ∗
      tlb ↦ᵣ tlbvec ∗
      PC ↦ᵣ va ∗
      nextPC ↦ᵣ npc ∗
      gpr_file g ∗
      upt_inv root slots spec ∗
      user_code ∗
      user_data ∗
      user_cfg)%I.

  (* ------------------------------------------------------------------ *)
  (* The inner Löb loop.                                                  *)
  (* ------------------------------------------------------------------ *)

  Lemma wp_wait_loop (wr : WaitReason) (instbits : mword 32) (va : mword 64)
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO) ->
    dq = DfracOwn 1 ->
    minstret_inv -∗
    hw_config -∗
    ▷ ((user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
       (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    user_waiting_frame wr instbits va -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hwr Hdq) "#Hinv #Hhw".
    iLöb as "IHwait".
    iIntros "Hk Hwframe".
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ) "[Hreg [Hmem Hdev]] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct "Hwframe" as (ms_v sc_v stval_v sepc_v npc g tlbvec)
      "(%HSXL & %Hok & Hhs & Hpriv & Hms & Hscause & Hstval & Hsepc &
        Htlb & Hpc & Hnpc & Hgpr & Hupt & #Hcode & Hdata & Hcfg)".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    assert (Hhart_w :
      register_lookup hart_state (set_reg σ (R_bool minstret_increment) b).(sregs)
        = HART_WAITING (wr, instbits)).
    { unfold set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    (* case-split the model branch on shouldWakeForInterrupt then reservation *)
    destruct (neq_vec (and_vec
                (register_lookup mip (set_reg σ (R_bool minstret_increment) b).(sregs))
                (register_lookup mie (set_reg σ (R_bool minstret_increment) b).(sregs)))
                (zeros' 64)) eqn:Hwk.
    - (* WAKE (interrupt pending): exit to an ACTIVE retiring step *)
      pose proof (exec_run_hart_waiting_wake 0 wr instbits false
                    (set_reg σ (R_bool minstret_increment) b) Hwk) as Hrun.
      pose proof (exec_riscv_step_waiting_wake σ wr instbits b Hsi Hhart_w Hrun) as Hstep.
      (* --- WAKE tail --- *)
      iEval (rewrite Hdq) in "Hhs".
      iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
      iEval (rewrite <- Hdq) in "Hhs".
      iDestruct (reg_valid with "Hreg Hmst") as %Lmstw.
      assert (Lnpcw : register_lookup nextPC
          (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs)
            = npc).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ | reflexivity].
        rewrite irrelevant_register_set; [ exact Lnpc | reflexivity]. }
      iMod (reg_update _ PC _ (register_lookup nextPC
              (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs))
            with "Hreg Hpc") as "[Hreg Hpc]".
      assert (Lmstt : register_lookup minstret
          (set_reg (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)) PC
             (register_lookup nextPC
                (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs))).(sregs)
            = mst).
      { unfold set_reg; cbn [sregs].
        rewrite irrelevant_register_set; [ exact Lmstw | reflexivity]. }
      iEval (rewrite Lnpcw) in "Hpc".
      destruct b.
      * iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro. iExists _. iSplitR; [ iPureIntro; exact Hstep | ].
        iNext. iModIntro.
        rewrite /mstate_interp. cbn [sregs mem mdev]. rewrite Lmstt.
        unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev".
        iSplitL "Hmst Hmi"; [ iExists (add_vec_int mst 1), true; iFrame | ].
        iDestruct "Hk" as "[Hkf _]". iApply "Hkf".
        iExists ms_v, sc_v, stval_v, sepc_v, npc, g, tlbvec.
        iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hgpr Hupt Hcode Hdata Hcfg".
        iSplitR; [ iPureIntro; exact HSXL | ].
        iSplitR; [ iPureIntro; exact Hok | ].
        unfold pc_is. iFrame "Hpc Hnpc".
      * iModIntro. iExists _. iSplitR; [ iPureIntro; exact Hstep | ].
        iNext. iModIntro.
        rewrite /mstate_interp. unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev".
        iSplitL "Hmst Hmi"; [ iExists mst, false; iFrame | ].
        iDestruct "Hk" as "[Hkf _]". iApply "Hkf".
        iExists ms_v, sc_v, stval_v, sepc_v, npc, g, tlbvec.
        iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hgpr Hupt Hcode Hdata Hcfg".
        iSplitR; [ iPureIntro; exact HSXL | ].
        iSplitR; [ iPureIntro; exact Hok | ].
        unfold pc_is. iFrame "Hpc Hnpc".
    - (* no interrupt: consult the reservation *)
      destruct (valid_reservation tt) eqn:Hvr.
      + (* STAY: reservation valid, keep waiting -- self-recurse *)
        pose proof (exec_run_hart_waiting_wrs_stay 0 wr instbits
                      (set_reg σ (R_bool minstret_increment) b) Hwr Hwk Hvr) as Hrun.
        pose proof (exec_riscv_step_waiting_stay σ wr instbits b Hsi Hhart_w Hrun) as Hstep.
        iModIntro. iExists _. iSplit; [ iPureIntro; exact Hstep | ].
        iNext. iModIntro.
        rewrite /mstate_interp. unfold set_reg; cbn [sregs mem mdev].
        iFrame "Hreg Hmem Hdev".
        iSplitL "Hmst Hmi".
        { iExists mst, b. iFrame. }
        iApply ("IHwait" with "[Hk]").
        { iNext. iExact "Hk". }
        iExists ms_v, sc_v, stval_v, sepc_v, npc, g, tlbvec.
        iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hpc Hnpc Hgpr Hupt Hcode Hdata Hcfg".
        iSplitR; [ iPureIntro; exact HSXL | ].
        iPureIntro; exact Hok.
      + (* WAKE (invalid reservation): exit to an ACTIVE retiring step *)
        pose proof (exec_run_hart_waiting_wrs_invalid 0 wr instbits false
                      (set_reg σ (R_bool minstret_increment) b) Hwr Hwk Hvr) as Hrun.
        pose proof (exec_riscv_step_waiting_wake σ wr instbits b Hsi Hhart_w Hrun) as Hstep.
        (* --- WAKE tail (identical to the interrupt-wake case) --- *)
        iEval (rewrite Hdq) in "Hhs".
        iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
        iEval (rewrite <- Hdq) in "Hhs".
        iDestruct (reg_valid with "Hreg Hmst") as %Lmstw.
        assert (Lnpcw : register_lookup nextPC
            (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs)
              = npc).
        { unfold set_reg; cbn [sregs].
          rewrite irrelevant_register_set; [ | reflexivity].
          rewrite irrelevant_register_set; [ exact Lnpc | reflexivity]. }
        iMod (reg_update _ PC _ (register_lookup nextPC
                (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs))
              with "Hreg Hpc") as "[Hreg Hpc]".
        assert (Lmstt : register_lookup minstret
            (set_reg (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)) PC
               (register_lookup nextPC
                  (set_reg (set_reg σ (R_bool minstret_increment) b) hart_state (HART_ACTIVE tt)).(sregs))).(sregs)
              = mst).
        { unfold set_reg; cbn [sregs].
          rewrite irrelevant_register_set; [ exact Lmstw | reflexivity]. }
        iEval (rewrite Lnpcw) in "Hpc".
        destruct b.
        * iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
          iModIntro. iExists _. iSplitR; [ iPureIntro; exact Hstep | ].
          iNext. iModIntro.
          rewrite /mstate_interp. cbn [sregs mem mdev]. rewrite Lmstt.
          unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev".
          iSplitL "Hmst Hmi"; [ iExists (add_vec_int mst 1), true; iFrame | ].
          iDestruct "Hk" as "[Hkf _]". iApply "Hkf".
          iExists ms_v, sc_v, stval_v, sepc_v, npc, g, tlbvec.
          iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hgpr Hupt Hcode Hdata Hcfg".
          iSplitR; [ iPureIntro; exact HSXL | ].
          iSplitR; [ iPureIntro; exact Hok | ].
          unfold pc_is. iFrame "Hpc Hnpc".
        * iModIntro. iExists _. iSplitR; [ iPureIntro; exact Hstep | ].
          iNext. iModIntro.
          rewrite /mstate_interp. unfold set_reg; cbn [sregs mem mdev]. iFrame "Hreg Hmem Hdev".
          iSplitL "Hmst Hmi"; [ iExists mst, false; iFrame | ].
          iDestruct "Hk" as "[Hkf _]". iApply "Hkf".
          iExists ms_v, sc_v, stval_v, sepc_v, npc, g, tlbvec.
          iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hgpr Hupt Hcode Hdata Hcfg".
          iSplitR; [ iPureIntro; exact HSXL | ].
          iSplitR; [ iPureIntro; exact Hok | ].
          unfold pc_is. iFrame "Hpc Hnpc".
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The WRS arm.                                                         *)
  (* From an ACTIVE user_frame, fetch+decode WRS, run the ACTIVE step     *)
  (* (Enter_Wait) into the waiting frame, then invoke [wp_wait_loop].     *)
  (* The premise list clones [wp_instr_u_hit]'s fetch-hit bundle with     *)
  (* the decode target fixed to [WRS arg].                               *)
  (* ------------------------------------------------------------------ *)
  Lemma ustep_wrs
      (va : mword 64) (vpn : mword 27) (ie : uwalk_info)
      (w : mword 32) (arg : wrsop) (ms_v sc_v stval_v sepc_v : mword 64)
      (g : gmap regidx (mword 64))
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      E (Φ : mval -> iProp Σ) :
    ↑minstretN ⊆ E ->
    dq = DfracOwn 1 ->
    (* fetch-hit facts (verbatim from wp_instr_u_hit) *)
    vec_access_dec tlbvec (tlb_hash (__id 39) vpn) = Some (upt_entry vpn ie) ->
    uw_check_ok (InstructionFetch tt) ie ->
    update_PTE_Bits (uw_pte0 ie) (InstructionFetch tt) = None ->
    _get_PTE_Ext_PBMT (ext_bits_of_PTE (uw_pte0 ie)) = ('b"00" : mword 2) ->
    (forall j : nat, (j < 4)%nat ->
       code !! pa_add (u_pa (upt_entry vpn ie) va vpn) j = Some (nth_byte w j)) ->
    _get_Mstatus_SXL ms_v = 'b"10" ->
    is_aligned_vaddr (Virtaddr va) 4 = true ->
    neq_vec (bits_of_virtaddr (Virtaddr va))
       (sign_extend' 64 (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0)) = false ->
    autocast (T := mword) (subrange_vec_dec
       (subrange_vec_dec (bits_of_virtaddr (Virtaddr va)) (Z.sub 39 1) 0) (Z.sub 39 1) pagesize_bits) = vpn ->
    is_aligned_paddr (Physaddr (u_pa (upt_entry vpn ie) va vpn)) 4 = true ->
    isRVC (subrange_vec_dec w 15 0) = false ->
    (* decode to WRS at the concrete user decode state *)
    (forall s0, agree_on D_u s0 dstateU -> exec (ext_decode w) s0 = Some (WRS arg, s0)) ->
    is_lpad_instruction (WRS arg) = false ->
    upt_tlb_ok spec tlbvec ->
    hw_config -∗
    minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ User -∗
    mstatus ↦ᵣ ms_v -∗
    scause ↦ᵣ sc_v -∗
    stval ↦ᵣ stval_v -∗
    sepc ↦ᵣ sepc_v -∗
    tlb ↦ᵣ tlbvec -∗
    pc_is va -∗
    gpr_file g -∗
    upt_inv root slots spec -∗
    user_code -∗
    user_data -∗
    user_cfg -∗
    ▷ ((user_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
       (user_trap_frame -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros HN Hdq Hvec Hchk0 HupdN Hpbmt0 Hcw HSXL Hval Hcanon Hvpn_def Hpaal
           HnotRVC Hdec Hnlpad Hok.
    set (wr := match arg with WRS_STO => WAIT_WRS_STO | WRS_NTO => WAIT_WRS_NTO end).
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hpcpair
             Hgpr Hupt #Hcode Hdata Hcfg Hk".
    iDestruct "Hpcpair" as "[Hpc Hnpc]".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np &
        %HmisaA & %Hmisa_val0 & %Hmseccfg_val0)".
    pose proof (elp_no_lp elp0 Help_np) as Help0.
    iDestruct "Hcfg" as "(Hstvec & Hmie & Hmidl & Hmedl & Hmip & Hmeip & Hseip &
                          Hsatp & Hmenv & Hsenv & Hmst0 & Hsst0 & Hpmpc & Hpmpa)".
    (* leaf facts transported onto the stored entry *)
    assert (Hchk' : forall (mxr do_sum : bool) s0,
      exec (check_PTE_permission (InstructionFetch tt) User mxr do_sum
              (Mk_PTE_Flags (subrange_vec_dec (tlb_get_pte 8 (upt_entry vpn ie)) 7 0))
              (ext_bits_of_PTE (tlb_get_pte 8 (upt_entry vpn ie))) tt) s0
        = Some (PTE_Check_Success tt, s0)).
    { rewrite upt_entry_pte. exact Hchk0. }
    assert (Hupd' : update_PTE_Bits (tlb_get_pte 8 (upt_entry vpn ie)) (InstructionFetch tt)
                      = (None : option (mword 64))).
    { rewrite upt_entry_pte. exact HupdN. }
    assert (Hpbmt' : forall s0, exec (tlb_get_pbmt (upt_entry vpn ie)) s0
                                  = Some (PBMT_PMA, s0)).
    { intros s0. exact (upt_entry_pbmt vpn ie s0 Hpbmt0). }
    iApply (wp_exec_step_minstret E (E ∖ ↑minstretN) Φ HN with "Hinv").
    iIntros (σ) "[Hreg [Hmem Hdev]] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    (* should_inc at the ORIGINAL σ (needed by exec_riscv_step_enter_wait) *)
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    (* From here Hreg is at s_a := set_reg σ (R_bool minstret_increment) b, so all
       reg_valid facts come out at s_a -- exactly as wp_instr_u_hit's engine hands
       the caller the minstret-incremented state. *)
    iDestruct (reg_valid with "Hreg Hpc") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid with "Hreg Hms") as %Lms.
    iDestruct (reg_valid with "Hreg Htlb") as %Ltlb.
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmidl") as %Lmidl.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hsatp") as %Lsatp.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iDestruct (reg_valid_dq with "Hreg Hsenv") as %Lsenv.
    iDestruct (reg_valid_dq with "Hreg Hmst0") as %Lmst0.
    iDestruct (reg_valid_dq with "Hreg Hsst0") as %Lsst0.
    iDestruct (reg_valid_dq with "Hreg Hpmpc") as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hpmpa") as %Lpmpa.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hpma") as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Help") as %Lelp.
    set (pa := u_pa (upt_entry vpn ie) va vpn) in *.
    set (sa := set_reg σ (R_bool minstret_increment) b) in *.
    iAssert (⌜forall j : nat, (N.of_nat j < 4)%N ->
               σ.(mem) !! (pa_add pa j) = Some (nth_byte w j)⌝)%I as %Hbf.
    { iIntros (j Hj).
      iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw j ltac:(lia)) with "Hcode") as "Hbj".
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram pa⌝)%I as %Hram.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 0%nat ltac:(lia)) with "Hcode") as "Hb0".
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iAssert (⌜addr_is_ram (pa_add pa 3)⌝)%I as %Hram3.
    { iDestruct (big_sepM_lookup (fun a b => (a ↦ₘ□ b)%I) code _ _
                   (Hcw 3%nat ltac:(lia)) with "Hcode") as "Hb3".
      iDestruct (mem_ram with "Hb3") as %Hr3. iPureIntro. exact Hr3. }
    pose proof (addr_is_ram_not_in_clint _ Hram) as Hnc.
    pose proof (addr_is_ram_not_in_sig _ Hram) as Hns.
    (* memory is unchanged by the minstret_increment write: sa.(mem) = σ.(mem) *)
    assert (Hmemeq : sa.(mem) = σ.(mem)) by (unfold sa, set_reg; reflexivity).
    assert (HES : exec (currentlyEnabled Ext_S) sa = Some (true, sa)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. rewrite Lmisa. exact HmisaS. }
    assert (Hdisp : exec (dispatchInterrupt User) sa = Some (None, sa)).
    { apply exec_dispatchInterrupt_none_U.
      exact (exec_getPendingSet_user_none sa mip_v mie_v midl_v meip seip
               HES Lmip Lmeip Lseip Lmie Lmidl Hmm Hs0). }
    assert (HSXL' : _get_Mstatus_SXL (register_lookup mstatus sa.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    pose proof (exec_translateAddr_fetch_hit_u (upt_entry vpn ie) vpn Hchk' Hupd'
                  Hpbmt' (upt_entry_match vpn ie) va satp0 tlbvec sa
                  Lpriv HSXL' Lsatp Hsatpmode Hasid Ltlb Hvec Hcanon Hvpn_def) as Htr.
    destruct (Hpma_all pa 4) as (region & Hpmam & Hpmax & _ & _ & _).
    assert (HA' : pmpAddrMatchType_encdec_backwards
              (_get_Pmpcfg_ent_A (vec_access_dec (register_lookup pmpcfg_n sa.(sregs)) 0)) = TOR)
      by (rewrite Lpmpc; exact HpmpA).
    assert (Hord' : zopz0zKzJ_u (zeros' 64) (vec_access_dec (register_lookup pmpaddr_n sa.(sregs)) 0) = false)
      by (rewrite Lpmpa; exact Hpmp_ord).
    assert (HX' : eq_vec (_get_Pmpcfg_ent_X (vec_access_dec (register_lookup pmpcfg_n sa.(sregs)) 0)) ('b"1") = true)
      by (rewrite Lpmpc; exact HpmpX).
    assert (Hrange' : pmpRangeMatch (Z.mul (uint (zeros' 64 : mword 64)) 4)
              (Z.mul (uint (vec_access_dec (register_lookup pmpaddr_n sa.(sregs)) 0)) 4)
              (uint pa) (uint (to_bits 64 4)) = PMP_Match).
    { rewrite Lpmpa.
      exact (ram_fetch_pmp pa (vec_access_dec pmpaddr00 0) 4 3
               ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
               Hram Hram3 Hpmp_cov). }
    assert (Hpmam' : matching_pma_region (register_lookup pma_regions sa.(sregs))
              (Physaddr pa) 4 = Some region)
      by (rewrite Lpma; exact Hpmam).
    pose proof (exec_fetch_F_Base_4_U_gen va pa w sa sa region
                  Lpc Hval Htr HA' Hord' Hrange' HX' Hpmam' Hpaal Hpmax
                  (within_clint_false pa 4 sa Hnc ltac:(lia))
                  (within_sig_false pa 4 sa Hns ltac:(lia))
                  (within_htif_false pa 4 sa Lhtif)
                  (addr_is_ram_not_dev _ Hram)
                  ltac:(rewrite Hmemeq; exact Hbf) Lpriv HnotRVC) as Hfetch.
    assert (Lmenv' : register_lookup menvcfg sa.(sregs) = MENVCFG_S)
      by (rewrite Lmenv; reflexivity).
    assert (Lmisa' : register_lookup misa sa.(sregs) = MISA_C)
      by (rewrite Lmisa; exact Hmisa_val0).
    pose proof (Hdec sa
                  (agree_u sa Lpriv Lmenv' Lsenv Lmst0 Lsst0 Lmisa')) as Hdec'.
    assert (Hlpad : eq_vec (register_lookup elp sa.(sregs))
                      (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Lelp; exact Help_np).
    (* the ACTIVE step: run_hart_active reaches Enter_Wait via exec_execute_WRS *)
    assert (Hha : exec (run_hart_active 0) sa
                    = Some (Step_Execute (Enter_Wait wr, zero_extend' 32 w),
                            set_reg sa nextPC (add_vec_int va 4))).
    { apply (exec_hart_active_progress_base_gen User sa sa
               (set_reg sa nextPC (add_vec_int va 4)) w (WRS arg) va
               (Enter_Wait wr) Lpriv Hdisp Hfetch Hdec' Hlpad Hnlpad Lpc).
      - exact (exec_execute_WRS arg (set_reg sa nextPC (add_vec_int va 4))).
      - exact I. }
    assert (Hhart_a : register_lookup hart_state sa.(sregs) = HART_ACTIVE tt) by exact Lhs.
    (* the whole riscv_step: ACTIVE -> HART_WAITING *)
    pose proof (exec_riscv_step_enter_wait σ (set_reg sa nextPC (add_vec_int va 4))
                  wr (zero_extend' 32 w) b Hsi Hhart_a Hha (wait_is_nop_WRS arg)) as Hstep.
    (* ghost bookkeeping: nextPC := va+4, hart_state := WAITING *)
    iMod (reg_update _ nextPC _ (add_vec_int va 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iEval (rewrite Hdq) in "Hhs".
    iMod (reg_update _ hart_state _ (HART_WAITING (wr, zero_extend' 32 w))
            with "Hreg Hhs") as "[Hreg Hhs]".
    iEval (rewrite <- Hdq) in "Hhs".
    iModIntro. iExists _. iSplitR; [ iPureIntro; exact Hstep | ].
    iNext. iModIntro.
    rewrite /mstate_interp. unfold set_reg; cbn [sregs mem mdev].
    iFrame "Hreg Hmem Hdev".
    iSplitL "Hmst Hmi"; [ iExists mst, b; iFrame | ].
    (* rebuild user_cfg and hand the waiting frame to wp_wait_loop *)
    iApply (wp_wait_loop wr (zero_extend' 32 w) va E Φ HN
              ltac:(destruct arg; [ left | right ]; reflexivity) Hdq
              with "Hinv Hhw [Hk]").
    { iNext. iExact "Hk". }
    iExists ms_v, sc_v, stval_v, sepc_v, (add_vec_int va 4), g, tlbvec.
    iFrame "Hhs Hpriv Hms Hscause Hstval Hsepc Htlb Hpc Hnpc Hgpr Hupt Hcode Hdata".
    iSplitR; [ iPureIntro; exact HSXL | ].
    iSplitR; [ iPureIntro; exact Hok | ].
    rewrite /user_cfg.
    iFrame "Hstvec Hmie Hmidl Hmedl Hmip Hmeip Hseip Hsatp Hmenv Hsenv
            Hmst0 Hsst0 Hpmpc Hpmpa".
  Qed.

End WpUserWrs.
