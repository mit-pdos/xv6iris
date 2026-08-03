(* LinkPrintkGen.v -- the one place printk's GENERAL-path contract is ASSUMED.

   The panic path is proven ([LinkPrintk.v], over [ProofPrintk.v]); the general
   path is not -- it is blocked on uartputc_sync's general contract
   (claude-notes/projects/printk.md).  So this link supplies [PRINTK_GEN] with
   an [Axiom], the way [LinkKerneltrap.v] does for kerneltrap, which keeps every
   caller's proof (main's, first) a functor over the interface and axiom-free.
   Discharging it later replaces this file and nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith String.
From stdpp Require Import list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import SpecPrintkGen]
   does not put them in scope transitively, and backtick generalization then
   silently invents fresh binders with those names. *)
Require Import WpLock DiskPtsto WpUart.
Require Import SpecPrintk SpecPrintkGen.

Module PrintkGen : PRINTK_GEN.
  Axiom wp_printk_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool),
      wp_printk_gen_sconf_body γpr γd γv Φ m0 K eb pj C dqf f descs b.
End PrintkGen.
