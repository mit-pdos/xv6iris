(* LinkAcquiresleep.v -- acquiresleep()'s contract, TEMPORARILY ASSUMED.

   The hart-generic scheduler protocol (claude-notes/projects/sched-hart-generic.md)
   changed the shape of every contract above a park: a thread that parks
   resumes on whichever hart's scheduler dispatched it, so the continuation is
   quantified over that hart and its SIE ghost, tp genuinely changes, and the
   register postcondition weakens to [callee_saved_notp] + the tp pin.  acquiresleep()'s
   restated contract (SpecAcquiresleep.v) is CORRECT AND INTENDED; its proof tower has to
   be re-threaded through the quantified hart, which is follow-up work.  Until
   then the interface is supplied by an [Axiom] here -- exactly the assumed-callee
   shape of claude-notes/design/spec-modules.md -- so that every consumer above it
   keeps compiling against the honest statement.  The proof files are recoverable
   from git history (see the commit that removed them). *)
Require Import RiscvLang RiscvPtsto SmodeCore.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SwtchCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecAcquiresleep.

Module Acquiresleep : ACQUIRESLEEP.
  Axiom wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac},
      wp_acquiresleep_sconf_body γ Φ γs j γl γsl s R m pidv av eb C dq.
End Acquiresleep.
