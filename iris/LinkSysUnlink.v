(* LinkSysUnlink.v -- sys_unlink() has no proof (claude-notes/projects/fs-sysfile.md).
   Supplies [SpecSysUnlink.SYSUNLINK] with an [Axiom]; see LinkSysOpen.v's
   header for the full rationale, identical here. *)
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
Require Import SpecSysUnlink.
Require Import ProcAvail.

Module SysUnlinkAx : SYSUNLINK.
  Axiom wp_sys_unlink_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (R : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_sys_unlink_sconf_body R γf γs j γl bn fn us ip dqi m av pid V lks.
End SysUnlinkAx.
