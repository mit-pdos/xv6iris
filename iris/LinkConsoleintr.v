(* LinkConsoleintr.v -- consoleintr's proof, instantiated against its callees'.

   It WAS an [Axiom] -- the one assumption the uartintr cone rested on --
   because consoleintr had no proof.  xv6 `a28e94b` deleted its
   [case C('P'): procdump()] arm, which left its callees at exactly acquire /
   consputc / release / wakeup; all four are proven and linked, so this file
   is now an ordinary functor application and [tools/proof_coverage.py] no
   longer reports an axiom here.

   WHAT THE PROOF CHANGED IN THE CONTRACT: the assumption was silent about
   the UART, and the echo path is not -- [consputc] reaches
   [uartputc_sync], which takes tx_lock and writes the THR.  So
   SpecConsoleintr.v's contract grew [WpUart.dev_inv] and the bundled
   [console_caps], and lost two premises that were vacuous.  See that file. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import LinkAcquire LinkConsputc LinkRelease LinkWakeup.
Require Import ProofConsoleintr.

Module Consoleintr := ConsoleintrProof Acquire Consputc Release Wakeup.
