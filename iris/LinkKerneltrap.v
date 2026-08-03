(* LinkKerneltrap.v -- the one place kerneltrap's contract is ASSUMED.

   Every other link file in the tree instantiates a proof functor against its
   callees' PROOFS.  kerneltrap has none, so this link supplies the interface
   with an [Axiom] instead -- the single assumption the kernelvec cone rests
   on ([tools/proof_coverage.py] reports it as such).  Isolating it here means
   [ProofKernelvec.v] itself is axiom-free: it is a functor over [KERNELTRAP],
   and proving kerneltrap later replaces this file, nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.                                       *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import SpecKerneltrap.

Module Kerneltrap : KERNELTRAP.
  Axiom kerneltrap_returns :
    forall `{!riscvGS Σ} `{GenId} `{CpuId} `{!sieG Σ}
      (γ : gname) (dq : dfrac)
      (m : regfile) (spv rava : mword 64)
      (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64)
      (Phi : mval -> iProp Σ),
      wp_kerneltrap_returns_body γ dq m spv rava satp0 tlbvec
        pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17
        v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 Phi.
End Kerneltrap.
