(* LinkSysUnlink.v -- sys_unlink()'s seal.

   THE CONTRACT IS THE REAL ONE (SpecSysUnlink.v), and the proof is being
   built (claude-notes/projects/fs-sysfile.md, "S7-unlink").  Until the walk
   lands, [SpecSysUnlink.SYSUNLINK] is supplied with an [Axiom] -- visible
   to [Print Assumptions] and to [tools/proof_coverage.py]'s textual scan,
   unlike a bare [Declare Module] -- exactly as LinkKerneltrap.v does
   (claude-notes/design/spec-modules.md, "An ASSUMED callee: Module Type +
   an Axiom in the link").

   WHEN THE WALK LANDS, this file becomes
     [Module SysUnlink := SysUnlinkProof Argstr BeginOp Nameiparent Ilock
                            Namecmp Dirlookup Memset Readi Writei Iupdate
                            Iunlockput EndOp.]
   and the axiom retires with it. *)
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
Require Import BioDefs.
Require Import KallocInv.
Require Import DiskPtsto.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import IrefSlots.
Require Import ProcDefs.
Require Import SpecSysUnlink.
Require Import ProcAvail.

Module SysUnlinkAx : SYSUNLINK.
  Axiom wp_sys_unlink_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
             !fsCrashG Σ, !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γf : gname) (γa : gname) (γpr : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (dqb dqs dqbs : dfrac)
      (v0 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_unlink_sconf_body γf γa γpr gs j gl gu gd gk pd pav pu bn g gfs
                               gi cn gtl cov logstart bmapstart inodestart
                               nib size dev used dqb dqs dqbs v0 pid V
                               m K eb b lks.
End SysUnlinkAx.
