(* LinkSyscall.v -- the one place syscall()'s contract is ASSUMED.

   syscall() has no proof: it is an indirect call through [syscalls[]], so
   proving it means proving the dispatch AND all twenty-two sys_* entries.
   This link supplies [SpecSyscall.SYSCALL] with an [Axiom], the way
   [LinkPrintk.v] does for printk's general path and [LinkConsoleintr.v]
   for consoleintr, which keeps usertrap's proof a functor over the interface
   and axiom-free in itself.  Discharging it later replaces this file and
   nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan.

   [syscall_env] is defined here as [emp] rather than left abstract, because
   a [Module Type] whose [Parameter] is a resource FAMILY cannot be
   discharged by an axiom without also fixing the family.  [emp] is the
   honest reading of "assumed": the axiom claims syscall runs on the process
   block alone.  A real ProofSyscall.v replaces the definition and the axiom
   together, and no caller changes -- which is the whole reason the
   environment is a parameter rather than thirty spelled-out conjuncts. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import SpecSyscall]
   does not put them in scope transitively, and backtick generalization then
   silently invents fresh binders with those names (durable-notes.md, the
   typeclass-sweep traps). *)
Require Import WpLock FdSlots IrefSlots.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import SpecSyscall.

Module Syscall : SYSCALL.
  (* hart-free, as the interface requires -- see SpecSyscall's note on
     [syscall_env]: usertrap frames this across [true]-indexed steps. *)
  Definition syscall_env
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
    `{GEN : GenId}
    (γf : gname) (pj : mword 64) : iProp Σ := emp%I.

  Axiom wp_syscall_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (C : iProp Σ)
      (pid : mword 32) (V : pprivate),
      wp_syscall_sconf_body syscall_env γf γs j γl m av C pid V.
End Syscall.
