From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import MinstretInv WpGpr RegFile.
Require Import ExecCommon WpIntrCore.
Require Import UserPtTree UserExec UserStep UserTrap.
Local Open Scope Z_scope.
Import Defs.

Section UserClassify.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).
  Context (Rut : uptd -> iProp Σ).

  (* The full execute-result outcome space at U-mode: retire, delegated
     user-trap, illegal, or enter-wait (WRS).  This REPLACES the 2-way
     [exec_step_result_ok] -- the earlier spec that could not classify the
     illegal / enter-wait families and so made the totalities unprovable. *)
  Definition u_result_ok (r : ExecutionResult) : Prop :=
    r = Retire_Success tt
    \/ (exists e xv pcx, r = rv64d_types.Trap (User, make_sync_exception e xv, pcx)
                         /\ user_exc e = true)
    \/ r = Illegal_Instruction tt
    \/ (exists wr, r = Enter_Wait wr /\ (wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO)).

  (* The full run_hart_active outcome for an active hart: an executed result
     (any of the four above) or a fetch failure. *)
  Definition u_step_outcome (st : Step) : Prop :=
    (exists (r : ExecutionResult) (ib : mword 32), st = Step_Execute (r, ib) /\ u_result_ok r)
    \/ (exists (e : ExceptionType) (xv : mword 64),
          st = Step_Fetch_Failure (Virtaddr xv, e) /\ user_exc e = true).

  (* ------------------------------------------------------------------- *)
  (* WHAT USED TO BE HERE, and where it went.                              *)
  (*                                                                       *)
  (* [active_step_obligation] packaged ONE WHOLE [run_hart_active] as an    *)
  (* [exec] fact plus a move of [mstate_interp]; [active_step_branch] then  *)
  (* case-split its outcome and ran the trap tower under                    *)
  (* [wp_exec_step_minstret].  Under per-node semantics BOTH are gone, and  *)
  (* neither is a loss:                                                     *)
  (*                                                                       *)
  (*   * the six-way outcome split IS [HartStepFull.swp_try_step_full]'s    *)
  (*     match, proved once, privilege-agnostically, over the model rather  *)
  (*     than over this tier;                                               *)
  (*   * the whole-[run_hart_active] obligation IS                          *)
  (*     [HartRunFull.swp_run_hart_active_U], whose fetch obligation is     *)
  (*     match-shaped and whose execute obligation is result-generic --     *)
  (*     which is what let the four U-mode outcomes ([u_result_ok] below)   *)
  (*     stop being a special case;                                         *)
  (*   * the trap delivery ([deliver_user_trap] + [UserTrap.utrap_ghost])   *)
  (*     IS [HartMemRun.swp_hmrun_of_exec] at [mm := empty] off             *)
  (*     [UserTrap]'s four [goodmb] twins -- the register-WRITING analogue  *)
  (*     of [HartGoodb.hval_of_goodb], which [goodb] cannot be because it   *)
  (*     refuses every [RegWrite].                                          *)
  (*                                                                       *)
  (* What survives is exactly the U-mode CLASSIFICATION of an outcome --    *)
  (* [u_result_ok] / [u_step_outcome] above -- which is tier content and    *)
  (* has no per-node analogue to be replaced by.                            *)
  (* ------------------------------------------------------------------- *)

End UserClassify.
