(* LinkBalloc.v -- the one place balloc's contract is ASSUMED.

   Most link files instantiate a proof functor against its callees' PROOFS;
   balloc has none yet, so this link supplies the interface with an [Axiom]
   instead -- the single assumption the bmap cone rests on
   ([tools/proof_coverage.py] reports it as such).  Isolating it here means
   [ProofBmap.v] itself is axiom-free: it is a functor over [BALLOC], and
   proving balloc later replaces this file and nothing else.

   What proving balloc needs is the BITMAP INVARIANT -- which agent holds a
   free block's [fsblock] half and its exclusive [blk_own] token while the
   block is free, tied to bit b of the bitmap block.  [FsBlocks.fs_alloc]
   already mints both per covered block at boot, so the material exists; the
   design decision does not (claude-notes/design/fs-inode.md, "balloc's
   contract -- ASSUMED for now").

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.                                       *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock FdSlots WpUart.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import SpecBalloc.

Module Balloc : BALLOC.
  Axiom wp_balloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_balloc_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart dev u pidv dq m K eb C b.
End Balloc.
