(* LinkConsoleintr.v -- the one place consoleintr's contract is ASSUMED.

   The second file of its kind (LinkKerneltrap.v is the first).  Every other
   link file in the tree instantiates a proof functor against its callees'
   PROOFS; consoleintr has none, so this link supplies the interface with an
   [Axiom] instead -- the single assumption the uartintr cone rests on
   ([tools/proof_coverage.py] reports it as such).  Isolating it here means
   [ProofUartintr.v] itself is axiom-free: it is a functor over [CONSOLEINTR],
   and proving consoleintr later replaces this file, nothing else.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan.

   What the assumption does and does not say: see SpecConsoleintr.v -- in
   particular, it is silent about the UART, which the echo path really does
   touch. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import FdSlots WpLock.
Require Import SpecConsoleintr.

Module Consoleintr : CONSOLEINTR.
  Axiom wp_consoleintr_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_consoleintr_sconf_body Φ m γs pme lvl K eb C b.
End Consoleintr.
