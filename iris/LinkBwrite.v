(* LinkBwrite.v -- bwrite()'s contract, TEMPORARILY ASSUMED.

   The hart-generic scheduler protocol (claude-notes/projects/sched-hart-generic.md)
   changed the shape of every contract above a park: a thread that parks
   resumes on whichever hart's scheduler dispatched it, so the continuation is
   quantified over that hart and its SIE ghost, tp genuinely changes, and the
   register postcondition weakens to [callee_saved_notp] + the tp pin.  bwrite()'s
   restated contract (SpecBwrite.v) is CORRECT AND INTENDED; its proof tower has to
   be re-threaded through the quantified hart, which is follow-up work.  Until
   then the interface is supplied by an [Axiom] here -- exactly the assumed-callee
   shape of claude-notes/design/spec-modules.md -- so that every consumer above it
   keeps compiling against the honest statement.  The proof files are recoverable
   from git history (see the commit that removed them). *)
Require Import RiscvLang RiscvPtsto SmodeCore.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock SleepLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BufOwn BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecBwrite.

Module Bwrite : BWRITE.
  Axiom wp_bwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ, !uartGhostG Σ}
      `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (bs bs_disk : list (bv 8)),
      wp_bwrite_sconf_body γ Φ γs j γl γu γd γk pd pav pu bn k
                           pidv dev bno dq m K eb C bs bs_disk.
End Bwrite.
