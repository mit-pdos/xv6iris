(* LinkConsoleinit.v -- the one place consoleinit's contract is ASSUMED.

   consoleinit WAS proven, as a functor over [INITLOCK] and [UARTINIT]
   (ProofConsoleinit.v, which this link instantiated).  Its statement moved to
   the invariant form with uartinit's (SpecUartinit.v / SpecConsoleinit.v), so
   its proof is deleted along with ProofUartinit.v and the interface is supplied
   by an [Axiom] until both come back -- see
   claude-notes/projects/main-boot.md, G1.  Isolating the assumption here keeps
   [ProofMain.v] a functor over [CONSOLEINIT] and axiom-free.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith String.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecConsoleinit] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import WpUart.
Require Import SpecConsoleinit.

Module Consoleinit : CONSOLEINIT.
  Axiom wp_consoleinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool)
      (vclock : bv 32) (vcname vccpu : bv 64)
      (vtlock : bv 32) (vtname vtcpu : bv 64)
      (dread0 dwrite0 : mword 64),
      wp_consoleinit_sconf_body γ γd Φ m K l b0 vclock vcname vccpu
                                vtlock vtname vtcpu dread0 dwrite0.
End Consoleinit.
