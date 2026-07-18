(* UserTrap.v -- the U-mode trap tower: the exec-level reduction of taking
   a trap OUT OF USER MODE into the kernel's stvec handler.

   ONE cause-generic tower serves every trap: [trap_handler del_priv c pc
   info ext] writes the same register sequence for interrupts and for
   synchronous exceptions -- only the scause value (interrupt bit + cause
   bits, both functions of [c]) and the stval value ([tval info]: the
   faulting address/info, or 0) differ.  The tower is proven once over an
   abstract [c : TrapCause] and [info : option (mword 64)] (Section
   [UTrapReduce]); [handle_interrupt], [exception_handler] and
   [handle_exception] are equational instances inside the same section.
   Mirrors WpIntrCore's Supervisor tower ([TrapReduce]); the semantic
   difference from S-mode is the SPP write: trapping FROM User records
   SPP := 0 (so the handler's sret returns to User).

   [utrap_ms] is the delivered mstatus as a function of the pre-trap one
   (SPELP := elp; SPIE := SIE; SIE := 0; SPP := 0, in the model's exact
   update order), with the bit facts the [user_trap_frame] re-assembly
   needs: SIE = 0, SPP = 0, and MPRV / MXR / SXL preserved
   ([trap_mstatus_ok] from [user_mstatus_ok]).                            *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
From iris.program_logic Require Import language lifting.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv InstrBytes WpGpr.
Require Import WpDecode WpLeafCommon WpGprCsrwB WpIntrBits WpIntrCore.
Require Import UserPt UserExec UserStep.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The delivered mstatus and its bit facts.                             *)
(* ===================================================================== *)

(* trap-from-User mstatus transform (SPP := 0; otherwise = trap_ms) *)
Definition utrap_ms (elp_v : mword 1) (ms : mword 64) : mword 64 :=
  let ms_e := update_subrange_vec_dec ms 23 23 elp_v in
  let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e) in
  let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0") in
  update_subrange_vec_dec ms_b 8 8 ('b"0").

Lemma utrap_ms_SIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SIE (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SPIE (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPIE (utrap_ms elp_v ms) = _get_Mstatus_SIE ms.
Proof. unfold utrap_ms, _get_Mstatus_SPIE, _get_Mstatus_SIE; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SPP (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SPP (utrap_ms elp_v ms) = ('b"0" : mword 1).
Proof. unfold utrap_ms, _get_Mstatus_SPP; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MPRV (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MPRV (utrap_ms elp_v ms) = _get_Mstatus_MPRV ms.
Proof. unfold utrap_ms, _get_Mstatus_MPRV; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_MXR (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_MXR (utrap_ms elp_v ms) = _get_Mstatus_MXR ms.
Proof. unfold utrap_ms, _get_Mstatus_MXR; cbn zeta; mw_prep; tb1. Qed.

Lemma utrap_ms_SXL (elp_v : mword 1) (ms : mword 64) :
  _get_Mstatus_SXL (utrap_ms elp_v ms) = _get_Mstatus_SXL ms.
Proof. unfold utrap_ms, _get_Mstatus_SXL; cbn zeta; mw_prep; tb2. Qed.

(* ===================================================================== *)
(* §2 Exception delegation at User: with the cause's medeleg bit set (and  *)
(* S present), a synchronous exception from U delegates to Supervisor.     *)
(* ===================================================================== *)
Lemma exec_exception_delegatee_U (e : ExceptionType) (medl : mword 64) s :
  register_lookup medeleg s.(sregs) = medl ->
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  bit_to_bool (access_vec_dec medl (uint (exceptionType_bits_forwards e))) = true ->
  exec (exception_delegatee e User) s = Some (Supervisor, s).
Proof.
  intros Hmedl HES Hbit.
  unfold exception_delegatee. cbv zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg medeleg s)). cbn beta.
  rewrite Hmedl.
  match goal with |- exec (Defs.bind ?L _) s = _ =>
    assert (Hsup : exec L s = Some (true, s)) end.
  { rewrite (exec_and_boolM_Some _ _ _ _ _ HES). cbn match.
    rewrite Hbit. apply exec_returnm. }
  rewrite (exec_bind_Some _ _ _ _ _ Hsup). cbn beta. cbn match.
  replace (zopz0zI_u (privLevel_to_bits Supervisor) (privLevel_to_bits User))
    with false by (vm_compute; reflexivity).
  cbn match. apply exec_returnm.
Qed.

(* ===================================================================== *)
(* §3 The trap tower at cur_priv = User, generic in the CAUSE [c] and the  *)
(* tval payload [info]; delivery privilege Supervisor (delegated).         *)
(* ===================================================================== *)
Section UTrapReduce.
  Context (s : mstate) (c : TrapCause) (info : option (mword 64)) (pc0 : mword 64).
  Context (ms_v sc_old stvec_v : mword 64) (elp_v : mword 1).
  Hypothesis Hpriv : register_lookup cur_privilege s.(sregs) = User.
  Hypothesis Hms : register_lookup mstatus s.(sregs) = ms_v.
  Hypothesis Hsc : register_lookup scause s.(sregs) = sc_old.
  Hypothesis Hstvec : register_lookup stvec s.(sregs) = stvec_v.
  Hypothesis Help : register_lookup elp s.(sregs) = elp_v.
  Hypothesis HmisaS : eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true.
  Hypothesis Htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = TV_Direct.
  Hypothesis Hpc : register_lookup PC s.(sregs) = pc0.

  (* the model's exact write order *)
  Let ms_e := update_subrange_vec_dec ms_v 23 23 elp_v.
  Let s1 := set_reg s mstatus ms_e.
  Let s1e := set_reg s1 elp (landing_pad_bits_backwards NO_LP_EXPECTED).
  Let c1 := update_subrange_vec_dec sc_old (64 - 1) (64 - 1)
              (bool_to_bit (trapCause_is_interrupt c)).
  Let s2 := set_reg s1e scause c1.
  Let c2 := update_subrange_vec_dec c1 (64 - 2) 0
              (zero_extend' (64 - 1) (trapCause_bits_forwards c)).
  Let s3 := set_reg s2 scause c2.
  Let ms_a := update_subrange_vec_dec ms_e 5 5 (_get_Mstatus_SIE ms_e).
  Let s4 := set_reg s3 mstatus ms_a.
  Let ms_b := update_subrange_vec_dec ms_a 1 1 ('b"0").
  Let s5 := set_reg s4 mstatus ms_b.
  Let ms_c := update_subrange_vec_dec ms_b 8 8 ('b"0").
  Let s6 := set_reg s5 mstatus ms_c.
  Let s7 := set_reg s6 stval (tval info).
  Let s8 := set_reg s7 sepc pc0.
  Let s9 := set_reg s8 cur_privilege Supervisor.

  Lemma exec_trap_handler_U :
    exec (trap_handler Supervisor c pc0 info None) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold trap_handler.
    change (orb (get_config_print_exception tt) (get_config_print_interrupt tt)) with false.
    cbn match.
    assert (HZ : exec (Defs.bind0 (returnM tt) (hartSupports Ext_Zicfilp)) s = Some (true, s))
      by apply (exec_hartSupports_Zicfilp s).
    rewrite (exec_bind_Some _ _ _ _ _ HZ). cbn beta. cbn match.
    assert (HZP : exec (zicfilp_preserve_elp_on_trap Supervisor) s = Some (tt, s1e)).
    { unfold zicfilp_preserve_elp_on_trap. cbn match.
      match goal with |- exec (Defs.bind0 ?A _) _ = _ =>
        assert (HARM : exec A s = Some (tt, s1)) end.
      { rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mstatus s)). cbn beta.
        rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg elp s)). cbn beta.
        rewrite Hms Help.
        apply exec_write_reg. }
      rewrite (exec_bind0_Some _ _ _ _ _ HARM).
      unfold reset_elp. apply exec_write_reg. }
    rewrite (exec_bind0_Some _ _ _ _ _ HZP).
    assert (HES1 : exec (currentlyEnabled Ext_S) s1e = Some (true, s1e)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal.
      unfold s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _ HES1). cbn beta.
    assert (HAE : exec (Defs.assert_exp' true "no supervisor mode present for delegation") s1e
                  = Some (eq_refl, s1e)).
    { unfold Defs.assert_exp'. cbn match. apply exec_returnm. }
    rewrite (exec_bind_Some _ _ _ _ _ HAE). cbn beta.
    (* scause chain *)
    assert (Hrd1 : exec (Defs.read_reg scause : M _) s1e = Some (sc_old, s1e)).
    { rewrite (exec_read_reg scause s1e). unfold s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hsc. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s1e)).
    assert (Hrd2 : exec (Defs.read_reg scause : M _) s2 = Some (c1, s2)).
    { rewrite (exec_read_reg scause s2). unfold s2, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrd2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg scause _ s2)).
    (* mstatus chain *)
    assert (Hrm1 : exec (Defs.read_reg mstatus : M _) s3 = Some (ms_e, s3)).
    { rewrite (exec_read_reg mstatus s3). unfold s3, s2, s1e, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s1, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hrm1). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s3)).
    assert (Hrm2 : exec (Defs.read_reg mstatus : M _) s4 = Some (ms_a, s4)).
    { rewrite (exec_read_reg mstatus s4). unfold s4, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm2). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s4)).
    assert (Hrm3 : exec (Defs.read_reg mstatus : M _) s5 = Some (ms_b, s5)).
    { rewrite (exec_read_reg mstatus s5). unfold s5, set_reg; cbn [sregs].
      rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrm3). cbn beta.
    assert (Hrp : exec (Defs.read_reg cur_privilege : M _) s5 = Some (User, s5)).
    { rewrite (exec_read_reg cur_privilege s5).
      unfold s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hpriv. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrp). cbn beta. cbn match.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM ('b"0" : mword 1) s5)). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg mstatus _ s5)).
    cbn match.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg stval _ s6)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg sepc _ s7)).
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg cur_privilege _ s8)).
    cbn [handle_trap_extension].
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_track_trap_S (trapCause_is_interrupt c) (trapCause_bits_forwards c) s9)).
    assert (Hrc : exec (Defs.read_reg scause : M _) s9 = Some (c2, s9)).
    { rewrite (exec_read_reg scause s9).
      unfold s9, s8, s7, s6, s5, s4, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      unfold s3, set_reg; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrc). cbn beta.
    unfold prepare_trap_vector.
    assert (Hrt : exec (Defs.read_reg stvec : M _) s9 = Some (stvec_v, s9)).
    { rewrite (exec_read_reg stvec s9).
      unfold s9, s8, s7, s6, s5, s4, s3, s2, s1e, s1, set_reg; cbn [sregs].
      repeat (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite Hstvec. reflexivity. }
    rewrite (exec_bind_Some _ _ _ _ _ Hrt). cbn beta.
    unfold tvec_addr. rewrite Htvd. cbn match.
    unfold stvec_base. apply exec_returnm.
  Qed.

  (* --- instances: the three model entry points that reach the tower --- *)

  Lemma exec_handle_interrupt_U (i : InterruptType)
      (Hc : c = Interrupt i) (Hinfo : info = None) :
    exec (handle_interrupt i Supervisor) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_interrupt.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
    rewrite Hpc.
    rewrite <- Hc. rewrite <- Hinfo.
    rewrite (exec_bind_Some _ _ _ _ _ exec_trap_handler_U).
    apply exec_set_next_pc.
  Qed.

  Lemma exec_exception_handler_U (e : ExceptionType) (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    exec (exception_handler User (make_sync_exception e xv) pc0) s
      = Some (stvec_base stvec_v, s9).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd.
    unfold exception_handler.
    cbn [make_sync_exception sync_exception_trap sync_exception_excinfo
         sync_exception_ext].
    assert (HESs : exec (currentlyEnabled Ext_S) s = Some (true, s)).
    { rewrite exec_currentlyEnabled_S. do 2 f_equal. exact HmisaS. }
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_exception_delegatee_U e _ s eq_refl HESs Hdel)).
    cbn beta.
    change (get_config_print_exception tt) with false. cbn match.
    erewrite exec_bind0_Some. 2: apply exec_returnm.
    rewrite <- Hc. rewrite <- Hinfo.
    apply exec_trap_handler_U.
  Qed.

  Lemma exec_handle_exception_U (e : ExceptionType) (xv : mword 64)
      (Hc : c = rv64d_types.Exception e)
      (Hinfo : info = xtval_exception_value e xv)
      (Hdel : bit_to_bool (access_vec_dec (register_lookup medeleg s.(sregs))
                (uint (exceptionType_bits_forwards e))) = true) :
    exec (handle_exception xv e) s
      = Some (tt, set_reg s9 nextPC (stvec_base stvec_v)).
  Proof using Hpriv Hms Hsc Hstvec Help HmisaS Htvd Hpc.
    unfold handle_exception.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite Hpriv.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)). cbn beta.
    rewrite Hpc.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_exception_handler_U e xv Hc Hinfo Hdel)).
    apply exec_set_next_pc.
  Qed.

End UTrapReduce.

(* run_hart_active on a pending interrupt at User: NO fetch, NO decode, NO
   execute; the state is untouched (dispatchInterrupt only reads). *)
Lemma exec_run_hart_active_pending_U (s : mstate) (i : InterruptType) (p : Privilege) :
  register_lookup cur_privilege s.(sregs) = User ->
  exec (dispatchInterrupt User) s = Some (Some (i, p), s) ->
  exec (run_hart_active 0) s = Some (Step_Pending_Interrupt (i, p), s).
Proof.
  intros Hpriv Hdisp.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0.
  rewrite execR_early_return. cbn match.
  reflexivity.
Qed.

(* ===================================================================== *)
(* §4 The Iris INTERRUPT arm: a pending delegated interrupt traps the      *)
(* ACTIVE user hart to stvec, producing [user_trap_frame].  Rides the      *)
(* live [wp_exec_step_interrupt_inv] engine; the wire cells are BORROWED   *)
(* (dfrac-generic) and handed back to the continuation.                    *)
(* ===================================================================== *)

(* ===================================================================== *)
(* §5 The trapish riscv_step wrappers: a step whose run_hart_active        *)
(* result is a FAILED FETCH or an execute-produced TRAP delivers the       *)
(* exception (tower above) and ticks PC := nextPC (= the handler base);    *)
(* neither shape retires, so minstret is NOT bumped.                       *)
(* ===================================================================== *)

Section StepFetchFailure.
  Context (s s_f s_trap : mstate) (vaddr : mword 64) (ex : ExceptionType) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a = Some (Step_Fetch_Failure (Virtaddr vaddr, ex), s_f).
  Hypothesis Hhe :
    exec (handle_exception vaddr ex) s_f = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_fetch_failure : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Fetch_Failure arm: handle_exception, then the epilogue *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhe. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    (* retired = false: and_boolM (returnM false) _ short-circuits *)
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepFetchFailure.

Section StepExecuteIllegal.
  Context (s s_x s_trap : mstate) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (Illegal_Instruction tt, ib), s_x).
  Hypothesis Hhe :
    exec (handle_exception (zero_extend' 64 ib) (E_Illegal_Instr tt)) s_x
      = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  (* an executed instruction found ILLEGAL (every privileged instruction at
     User: mret / sret / wfi / the sfence and sinval families): try_step's
     dedicated arm delivers E_Illegal_Instr with the INSTRUCTION BITS as
     tval; the step does not retire. *)
  Lemma exec_riscv_step_execute_illegal : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Execute (Illegal_Instruction ...) arm: handle_exception, epilogue *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hhe. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepExecuteIllegal.

Section StepExecuteTrap.
  Context (s s_x s_trap : mstate) (p : Privilege) (exc : sync_exception)
          (pcx : mword 64) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart_a : register_lookup hart_state s_a.(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) s_a
      = Some (Step_Execute (rv64d_types.Trap (p, exc, pcx), ib), s_x).
  Hypothesis Hxh :
    exec (Defs.bind (exception_handler p exc pcx) set_next_pc) s_x
      = Some (tt, s_trap).
  Hypothesis Hhart_trap : register_lookup hart_state s_trap.(sregs) = HART_ACTIVE tt.

  Let s_tick : mstate := set_reg s_trap PC (register_lookup nextPC s_trap.(sregs)).

  Lemma exec_riscv_step_execute_trap : exec (riscv_step false) s = Some (tt, s_tick).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_tick))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta.
    cbn match.
    (* Step_Execute (Trap ...) arm: exception_handler >>= set_next_pc *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ exact Hxh. }
        apply (exec_read_reg hart_state s_trap). }
    rewrite Hhart_trap. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ apply (exec_returnM false s_tick). }
        cbn beta iota. apply (exec_returnM false s_tick). }
    cbn beta iota.
    apply exec_returnm.
  Qed.
End StepExecuteTrap.
