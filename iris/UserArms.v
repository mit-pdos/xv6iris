(* UserArms.v -- the payload-form RETIRE and EXECUTE-TRAP arms of the user
   step classification.

   [UserStepFull.v]'s unified step wrapper opens the wire invariant, decides
   the dispatch, and -- when no interrupt is pending -- hands the whole step
   to the classification [active_class], which must produce the
   [wp_exec_step_minstret] payload: ONE [riscv_step] reduction plus the
   re-established interp.  The classification's per-family case analysis
   always ends in one of a small set of STEP SHAPES; this file provides
   them:

     [retire_branch]        run_hart_active retires ([Retire_Success]) --
                            compute, control flow, fences, nops.  The
                            classification discharges the abstract
                            [retire_obligation] (UserCompute.v) for the
                            family; this arm does the try_step bookkeeping
                            (tick + conditional minstret bump) and
                            re-establishes [user_inv].
     [execute_trap_branch]  run_hart_active returns an execute-produced
                            sync trap (ecall / ebreak / illegal / memory
                            page fault) -- the arm runs the delegated trap
                            tower to stvec and produces [user_trap_frame].
                            The classification discharges
                            [execute_trap_obligation] (below).
     [fetch_fault_branch]   run_hart_active returns a FAILED FETCH
                            (misaligned / non-canonical / unmapped /
                            denied / needs-update pc) -- same tower, same
                            frame; the fetch never reaches execute, so the
                            gpr file and nextPC are untouched and stay with
                            the arm ([fetch_fault_obligation] hands over
                            only interp + [user_pt_inv], the TLB may fill on a
                            partially-successful split fetch).
     [illegal_branch]       run_hart_active returns [Illegal_Instruction]
                            (every privileged instruction at User --
                            mret / sret / wfi / the sfence and sinval
                            families; see UserExecFacts.v): try_step's
                            dedicated arm delivers E_Illegal_Instr with
                            the INSTRUCTION BITS as tval; the gpr file is
                            untouched, but nextPC moved (the pre-execute
                            write), so [illegal_obligation] hands it over.

     [enter_wait_branch]    run_hart_active returns [Enter_Wait] (a user
                            WRS): hart_state := WAITING, NO pc tick, NO
                            bump -- PC stays at the WRS, nextPC after it
                            (the decoupled WAITING shape [user_inv]
                            binds); re-enters [user_inv].

   All arms are WIRE-FREE: the dispatch decision reaches them as a pure
   fact at the post-minstret-increment states (∀ over the written bit), so
   no arm ever owns the wire cells.  Each does its own minstret prelude
   (the write is the first thing [try_step] does, so it belongs to the
   step shape, not to the classification).  The step-shape arm set is
   COMPLETE: retire / interrupt (inlined in the wrapper) / execute-trap /
   fetch-fault / illegal / enter-wait.                                     *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import UserPtTree UserExec.
Local Open Scope Z_scope.
Import Defs.

Section UserArms.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* ------------------------------------------------------------------- *)
  (* The RETIRE arm.  The caller supplies the per-family                   *)
  (* [retire_obligation] at the post-increment state (∀ over the written   *)
  (* bit -- the reductions never read minstret_increment, so the           *)
  (* classification discharges it uniformly); the arm does the minstret    *)
  (* prelude, runs the obligation, ticks PC to the retired pc, bumps       *)
  (* minstret when due, and re-enters [user_inv].                          *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The EXECUTE-TRAP obligation: the per-family fact the classification   *)
  (* discharges when execute produces a synchronous trap (ecall / ebreak / *)
  (* illegal / memory page fault).  Same ownership discipline as            *)
  (* [retire_obligation]: it owns what fetch+execute mutate (interp, gpr    *)
  (* file, nextPC, [user_pt_inv]; [user_cfg] borrowed for the decode reads)     *)
  (* and returns them at the post-execute state [s_x], with the run         *)
  (* reduction ending in [Trap] at User with a DELEGATED user exception.    *)
  (* The post-execute nextPC [va'] is whatever execute left there (the      *)
  (* trap tower overwrites it with the handler base).                       *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The EXECUTE-TRAP arm: run the delegated trap tower at the             *)
  (* post-execute state, tick PC to the handler base (no minstret bump --  *)
  (* the step does not retire), and produce [user_trap_frame].             *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The FETCH-FAULT obligation: the fetch fails before reaching execute   *)
  (* (misaligned / non-canonical / unmapped / denied / needs-update pc),   *)
  (* with a DELEGATED user exception.  The fetch writes neither the gpr    *)
  (* file nor nextPC, so only the interp (a split fetch may fill the TLB   *)
  (* on its successful half) and [user_pt_inv] change hands; [user_cfg] is     *)
  (* borrowed for the reads.  The ADUE-sensitive flavor corollaries        *)
  (* (UserFetch.v) are what discharge this; the arm below is cause-generic.*)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The FETCH-FAULT arm: [handle_exception] runs the same delegated trap  *)
  (* tower at the post-fetch state (sepc := the faulting pc, read from     *)
  (* PC; stval := the faulting address), PC ticks to the handler base, no  *)
  (* minstret bump -- and the machine is [user_trap_frame].                *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The ILLEGAL obligation: execute found the instruction ILLEGAL         *)
  (* (privileged instruction at User).  The gpr file is untouched; nextPC  *)
  (* moved (the pre-execute write) and the fetch may have filled the TLB,  *)
  (* so interp + the nextPC cell + [user_pt_inv] change hands.  The cause is   *)
  (* FIXED (E_Illegal_Instr, delegated by [uc_del]); the tval is the       *)
  (* instruction bits, supplied by try_step's dedicated arm.               *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The ILLEGAL arm: try_step's Illegal_Instruction arm runs the          *)
  (* delegated tower at the post-execute state with tval = the             *)
  (* INSTRUCTION BITS and sepc := the faulting pc (read from PC); PC       *)
  (* ticks to the handler base, no bump -- [user_trap_frame].              *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The ENTER-WAIT obligation: execute returned [Enter_Wait] (a user WRS  *)
  (* -- the reason is pinned to the two user-reachable ones, which is      *)
  (* exactly [user_hart_ok] for the WAITING re-entry).  Like the illegal   *)
  (* shape, the gpr file is untouched but nextPC moved (the pre-execute    *)
  (* write) and the fetch may have filled the TLB.                         *)
  (* ------------------------------------------------------------------- *)

  (* ------------------------------------------------------------------- *)
  (* The ENTER-WAIT arm: hart_state := HART_WAITING (wr, ib); NO pc tick,  *)
  (* NO bump -- PC stays at the WRS and nextPC after it, the decoupled     *)
  (* WAITING shape [user_inv] binds ([wp_user_step_waiting] later wakes    *)
  (* or stays from there).                                                 *)
  (* ------------------------------------------------------------------- *)

End UserArms.
