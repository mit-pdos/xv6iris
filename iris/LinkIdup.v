(* LinkIdup.v -- the one place idup's contract is ASSUMED.  See SpecIdup.v's
   header for why: there is no inode model, so [ProcInv.cwd_ref] is a
   placeholder ([FileInv.inode_ref], literally [emp]) and nothing about
   [ip->ref]/[itable.lock] is statable against real code yet.  Written with
   an explicit [Axiom] rather than a [Declare Module] for the same reason
   [LinkIput.v] is: [Print Assumptions] sees either, but only the [Axiom]
   keyword is visible to [tools/proof_coverage.py]'s textual scan. *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import WpLock.
Require Import FileInv.
Require Import SpecIdup.

Module Idup : IDUP.
  Axiom wp_idup_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile)
      (ip : mword 64) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (K : nat) (b : bool),
      wp_idup_sconf_body Φ m ip n eb p C K b.
End Idup.
