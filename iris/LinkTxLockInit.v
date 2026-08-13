(* LinkTxLockInit.v -- the boot ghost step that brings the UART transmit lock
   up, ASSUMED.

   WHAT THE AXIOM SAYS is exactly what uartinit's [initlock(&tx_lock, "uart")]
   followed by the usual [WpLock.newlock] step gives: hand over the
   transmitter token (which is all [UartTxInv.tx_res] is) and the frozen DLAB
   fact, and get [UartTxInv.is_txlock] back.  It consumes the token because
   the lock owns it, and it is a fancy update because minting a lock allocates
   ghost state and an invariant.

   THE PIECES ARE ALL PRESENT NOW; WHAT IS MISSING IS THE ASSEMBLY.
   uartinit's contract takes [SpecProcinit.lk_raw a_tx_lock] and hands back
   [lk_fresh a_tx_lock "uart"], consoleinit passes both straight through, and
   [SpecMain.main_locks_raw] carries the [lk_raw] entry -- so a boot assembly
   in main() holds the [lk_fresh] this axiom would otherwise have to invent.
   What it does NOT yet hold at that point is the RESOURCE: [tx_res γu] is the
   exclusive transmitter token, and main gives that token to printk's
   [pr.lock].  Which lock owns the transmitter is being settled by the printk
   effort (claude-notes/projects/uart-driver.md); until that lands, main
   drops its [lk_fresh] and this axiom stands in for the whole step.

   ISOLATED HERE, AND DELIBERATELY SEPARATE FROM LinkUartwrite.v.  That file
   assumes uartwrite's contract because its PROOF is not written; this one
   assumes the lock is minted.  The two retire independently -- proving
   uartwrite does not mint the lock, and minting the lock does not prove
   uartwrite -- and keeping them apart is what stops either from hiding the
   other in [Print Assumptions].

   Written out with an explicit [Axiom] rather than a [Declare Module]: both
   are visible to [Print Assumptions], but only the keyword is visible to
   [tools/proof_coverage.py]'s textual axiom scan. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Base SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpLock.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.

(* [E] is left universally quantified rather than pinned at ⊤: the only
   consumer is a boot assembly, and which mask it runs at is not this
   assumption's business. *)
Axiom tx_lock_init :
  forall `{!riscvGS Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ}
    `{GEN : RiscvLang.GenId}
    (γu : uart_names) (l : list (bv 8)) (E : coPset),
    uart_tx_own γu l -∗ uart_dlab_off γu ={E}=∗
      ∃ γl : gname, is_txlock γl γu.
