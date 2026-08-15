(* LinkSysOpenStub.v -- sys_open() has no proof (claude-notes/projects/fs-sysfile.md).
   Supplies [SpecSysOpenStub.SYSOPEN] with an [Axiom], mirroring
   [LinkKerneltrap.v]'s idiom for an assumed callee (Module + [Axiom], not
   [Declare Module], so [tools/proof_coverage.py]'s textual scan finds it).
   [ProofSyscall.v]'s dispatch takes [SYSOPEN] as a functor argument; this
   is the only place that argument is discharged, and discharging it for
   real (proving sys_open) replaces this file and nothing else. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock FdSlots IrefSlots.
Require Import FileInvDefs.
Require Import BioInv.
Require Import SpecFileclose.
Require Import KallocInv.
Require Import DiskPtsto DiskInv.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
Require Import ProcInv.
Require Import SpecSysOpenStub.
Require Import ProcAvail.

Module SysOpenAx : SYSOPEN.
  Axiom wp_sys_open_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (R : gname -> mword 64 -> iProp Σ)
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_sys_open_sconf_body R γf γs j γl bn fn us ip dqi m av pid V lks.
End SysOpenAx.
