(* LinkPlicinit.v -- the one place plicinit's contract is ASSUMED.

   plicinit WAS proven, over the raw [plic_frag] half (ProofPlicinit.v, which
   this link sealed).  [SpecPlicinit] is now stated over [WpUart.plic_inv] --
   the PLIC gateway latches from step 0, so no CPU precondition may hold the
   fragment raw -- and the proof is being re-worked over the invariant-opening
   ACCESSOR-form PLIC store leaf.  Until then the interface is supplied by an
   [Axiom], the way [LinkKerneltrap.v] does for kerneltrap, which keeps
   [ProofMain.v] a functor over [PLICINIT] and axiom-free.  The deleted proof
   script is in git history -- see claude-notes/projects/main-boot.md, G1.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import SpecPlicinit.

Module Plicinit : PLICINIT.
  Axiom wp_plicinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat),
      wp_plicinit_sconf_body γ Φ m0 n.
End Plicinit.
