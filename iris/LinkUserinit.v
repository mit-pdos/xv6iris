(* LinkUserinit.v -- the one place userinit's contract is ASSUMED.

   userinit has no proof: its callee [namei] pulls in the whole file-system
   cone.  So this link supplies the interface with an [Axiom] instead of
   instantiating a functor over a proof, exactly as [LinkKerneltrap.v] does for
   kerneltrap.  Isolating the assumption here is what keeps [ProofMain.v]
   axiom-free -- main's proof is a functor over [USERINIT] -- and proving
   userinit later replaces this file and nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import SpecUserinit]
   does not put them in scope transitively, and backtick generalization then
   silently invents fresh binders with those names. *)
Require Import WpLock KallocInv FdSlots.
Require Import SpecUserinit.

Module Userinit : USERINIT.
  Axiom wp_userinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γs : list gname)
      (m0 : regfile) (K : nat)
      (eb : bool) (pj : mword 64) (C : iProp Σ)
      (on : option nat) (v0 : mword 64) (b : bool),
      wp_userinit_sconf_body γa γs m0 K eb pj C on v0 b.
End Userinit.
