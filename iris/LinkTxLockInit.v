(* LinkTxLockInit.v -- the one place kernel-defects.md D2 is ASSUMED.

   THIS AXIOM STANDS IN FOR A MISSING LINE OF C, not for a missing proof.

   xv6 `ae96fd0` made the UART transmit lock a sleeplock

       static struct sleeplock tx_lock;

   and deleted uartinit's `initlock(&tx_lock, "uart")` without adding an
   `initsleeplock(&tx_lock, "uart")` in its place.  Nothing anywhere calls
   one.  The kernel still WORKS -- a zeroed sleeplock reads as unlocked, which
   is what every field `initsleeplock` would write already is -- but the two
   NAME fields stay NULL, and both [WpLock.lock_name] and [SleepLock.sl_name]
   say the name field points at a real NUL-terminated string.  At a NULL field
   that obligation is `(0 : mword 64) ↦ₛ□ s`, and address 0 is not in this
   model's memory map.

   So [UartTxInv.is_txlock] is not merely unproven, it is UNPROVABLE from the
   source as it stands, and every contract that takes it as a premise --
   SpecUartwrite's, and anything the boot chain would eventually hand it
   through -- has a premise no caller can discharge.  The full write-up, and
   the two ways out (add the one line of C, or index a lock's name by
   [option string] so an anonymous lock can be minted from zeroed bytes), is
   claude-notes/kernel-defects.md D2.

   ISOLATED HERE, AND DELIBERATELY SEPARATE FROM LinkUartwrite.v.  That file
   assumes uartwrite's contract because its PROOF is not written; this one
   assumes the lock exists because the SOURCE cannot create it.  The two
   retire independently -- proving uartwrite does not fix D2, and fixing D2
   does not prove uartwrite -- and keeping them apart is what stops either
   from hiding the other in [Print Assumptions].

   WHAT THE AXIOM SAYS is exactly what a real `initsleeplock(&tx_lock,
   "uart")` followed by the usual newlock step would give: hand over the
   transmitter token (which is all [UartTxInv.tx_res] is, now that the
   `tx_busy` certificate is gone) and the frozen DLAB fact, and get the lock
   back.  It consumes the token because the lock owns it, and it is a fancy
   update because minting a lock allocates ghost state and an invariant.

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
      ∃ γl γsl : gname, is_txlock γl γsl γu.
