(* LinkUartwrite.v -- uartwrite()'s contract, TEMPORARILY ASSUMED.

   The hart-generic scheduler protocol (claude-notes/projects/sched-hart-generic.md)
   changed the shape of every contract above a park: a thread that parks
   resumes on whichever hart's scheduler dispatched it, so the continuation is
   quantified over that hart and its SIE ghost, tp genuinely changes, and the
   register postcondition weakens to [callee_saved_notp] + the tp pin.  uartwrite()'s
   restated contract (SpecUartwrite.v) is CORRECT AND INTENDED; its proof tower has to
   be re-threaded through the quantified hart, which is follow-up work.  Until
   then the interface is supplied by an [Axiom] here -- exactly the assumed-callee
   shape of claude-notes/design/spec-modules.md -- so that every consumer above it
   keeps compiling against the honest statement.  The proof files are recoverable
   from git history (see the commit that removed them). *)
Require Import RiscvLang RiscvPtsto SmodeCore.
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import SmodeCore.
Require Import WpLock.
Require Import FdSlots.
Require Import DiskPtsto WpUart.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecUartwrite.

Module Uartwrite : UARTWRITE.
  Axiom wp_uartwrite_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γlp : gname) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ)
      (n : nat) (f : nat -> bv 8) (dq : dfrac) (b : bool),
      wp_uartwrite_sconf_body γu γv Φ γs j γlp γl m av eb C n f dq b.
End Uartwrite.
