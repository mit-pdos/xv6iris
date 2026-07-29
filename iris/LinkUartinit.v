(* LinkUartinit.v -- the one place uartinit's contract is ASSUMED.

   uartinit WAS proven, over the raw [uart_frag] half (ProofUartinit.v, which
   this link instantiated against [Uart] and [Initlock]).  That proof rested on
   "device init runs before the device invariant exists", which is incompatible
   with the UART thread running from step 0, so [SpecUartinit] is now stated
   over [WpUart.uart_inv] and the proof is being re-worked over the
   invariant-opening ACCESSOR-form UART store leaf.  Until that lands the
   interface is supplied by an [Axiom], the way [LinkKerneltrap.v] does for
   kerneltrap, so every caller (consoleinit, then main) stays a functor over
   [UARTINIT] and axiom-free.  Discharging it replaces this file and restores
   ProofUartinit.v, nothing else.  The deleted proof script is in git history
   and is the starting point for the rework -- see
   claude-notes/projects/main-boot.md, G1.

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
(* the classes the binder list generalizes over: [Require Import SpecUartinit]
   does not put them in scope transitively, and backtick generalization then
   silently invents fresh binders with those names. *)
Require Import WpUart.
Require Import SpecUartinit.

Module Uartinit : UARTINIT.
  Axiom wp_uartinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (vlock : bv 32) (vname vcpu : bv 64),
      wp_uartinit_sconf_body γ γd Φ m K l b0 vlock vname vcpu.
End Uartinit.
