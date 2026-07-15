(* HartActiveExecuteAs.v -- run_hart_active progress for an F_Base fetch whose
   execute expands via ExecuteAs to a base instruction (SINVAL_VMA -> executes
   as SFENCE_VMA).  SmodeCore's exec_hart_active_progress_base_gen forbids an
   ExecuteAs result (Hnotexec), and exec_hart_active_progress_RVC_gen handles
   ExecuteAs only on the F_RVC path.  This is the missing F_Base + ExecuteAs
   case: it splices the base-fetch front (F_Base w, the and_boolM landing-pad
   check) with the RVC ExecuteAs tail (re-dispatch to [other]).  The net
   Step_Execute result carries the re-dispatched [resf], so a caller whose
   [other] executes to Illegal_Instruction gets the identical run-level fact
   the direct base case produces. *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvExec RiscvTryStep.
Local Open Scope Z_scope.
Import Defs.

Lemma exec_hart_active_progress_base_ExecuteAs_gen
    (priv : Privilege) (s s_f s_x : mstate) (w : mword 32) (instr other : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Base w, s_f) ->
  exec (ext_decode w) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction instr = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 4))
    = Some (ExecuteAs other, set_reg s_f nextPC (add_vec_int pc 4)) ->
  exec (execute other) (set_reg s_f nextPC (add_vec_int pc 4)) = Some (resf, s_x) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad HpcF Hexec Hexec2.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_bind execR_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  unfold and_boolM.
  rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
  rewrite execR_returnR. cbn match. cbn match.
  rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
  rewrite execR_liftR Hexec. cbn match. cbn match.
  (* ExecuteAs other -> liftR (execute other) -> resf, fed to Step_Execute *)
  rewrite execR_bind execR_liftR Hexec2. cbn match.
  rewrite execR_returnR. cbn match. reflexivity.
Qed.
