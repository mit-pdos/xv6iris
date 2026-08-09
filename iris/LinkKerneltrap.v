(* LinkKerneltrap.v -- kerneltrap's two interfaces, instantiated.

   [Kerneltrap] is the REAL one now: [KerneltrapProof] applied to its three
   callees' proofs, so [Kerneltrap.wp_kerneltrap_sconf] is a theorem and this
   file assumes nothing about it.

   [KerneltrapRet] is the legacy round-trip contract, still supplied with an
   [Axiom] because [ProofKernelvec.v] is still a functor over it.  That is the
   ONE assumption left in the kernelvec cone, and it is no longer about
   whether kerneltrap works -- it is about the shape of the handler contract:
   [intr_handler_spec] does not yet hand the handler the trap CSRs, the
   per-cpu bookkeeping, a deep enough stack carve, or a hart-generic Loeb
   (explicit-cpuid Stage 2, claude-notes/projects/kerneltrap.md step 10).
   When that lands, [KerneltrapRet], [KERNELTRAP_RETURNS], [kv_cell] and
   [kt_clobbered] all go, and nothing else changes.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.                                      *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import SpecKerneltrap.
Require Import ProofKerneltrap.
Require Import LinkDevintr LinkMyproc LinkYield.

(* THE REAL THING: a theorem, over its callees' proofs. *)
Module Kerneltrap := KerneltrapProof Devintr Myproc Yield.

(* the legacy contract kernelvec still runs against -- see the header *)
Module KerneltrapRet : KERNELTRAP_RETURNS.
  Axiom kerneltrap_returns :
    forall `{!riscvGS Σ} `{GenId} `{CpuId} `{!sieG Σ}
      (γ : gname) (dq : dfrac)
      (m : regfile) (spv rava : mword 64)
      (satp0 : mword 64)
      (tlbvec : vec (option TLB_Entry) (2 ^ 6))
      (pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17 : mword 64)
      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : bv 64),
      wp_kerneltrap_returns_body γ dq m spv rava satp0 tlbvec
        pa1 pa2 pa3 pa4 pa5 pa6 pa7 pa8 pa9 pa10 pa11 pa12 pa13 pa14 pa15 pa16 pa17
        v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17.
End KerneltrapRet.
