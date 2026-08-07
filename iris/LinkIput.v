(* LinkIput.v -- the one place iput's contract is ASSUMED.

   Most link files instantiate a proof functor against its callees' PROOFS;
   iput has none, so this link supplies the interface with an [Axiom] --
   the single fs-side assumption kexit's cone rests on
   ([tools/proof_coverage.py] reports it as such).  Isolating it here means
   [ProofKexit.v] itself is a functor over [IPUT], and proving iput later
   replaces this file and nothing else.

   What proving iput needs is the INODE LAYER: an itable invariant, the
   per-inode reference algebra that [ProcInv.cwd_ref] is today a placeholder
   for, and itrunc.  None of that exists yet
   (claude-notes/design/fs-inode.md), which is exactly why the contract is
   worth stating first -- kexit's shape does not depend on any of it.

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
Require Import SpecIput.

Module Iput : IPUT.
  Axiom wp_iput_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ,
             !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (ip : mword 64) (n : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_iput_sconf_body Φ γs j γl γu γd γk pd pav pu bn γ γfs
                         cov logstart dev ip n pidv dq m K eb C b.
End Iput.
