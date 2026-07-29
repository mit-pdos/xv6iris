(* LinkAllocpid.v -- allocpid's one instance.

   ASSUMED, in the [Module Type] + [Axiom] shape (design/spec-modules.md):
   allocpid has no proof yet, but its interface is what allocproc's proof
   should be a functor over whether or not anyone has discharged it, and
   writing it this way keeps ProofAllocproc.v axiom-free and makes proving
   allocpid a one-file replacement.  The [Axiom] keyword (rather than
   [Declare Module]) is deliberate: tools/proof_coverage.py finds assumptions
   by scanning for it. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import IntrDefs.
Require Import SpecPanic.
Require Import SpecAllocpid.

Module Allocpid : ALLOCPID.
  Axiom wp_allocpid_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γp : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_allocpid_sconf_body γ Φ γp m av n eb p C.
End Allocpid.
