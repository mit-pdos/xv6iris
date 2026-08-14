(* LinkUartwrite.v -- uartwrite's proof functor, instantiated against its
   callees' PROOFS.

   uartwrite's contract used to be ASSUMED here (an [Axiom], the fourth file of
   that kind).  It is not any more: [ProofUartwrite.UartwriteProof] is a real
   proof of [SpecUartwrite.UARTWRITE] and this file only applies it.

   THE CALLEES ARE THE SPLIT SLEEP PROTOCOL'S: sleep_prepare, acquire, release
   and sleep -- xv6 `d80e61c5` takes and releases [tx_lock] INSIDE the byte
   loop and parks holding nothing, so [tx_lock] is a SPINLOCK again and the
   `ae96fd0` sleeplock era's acquiresleep/releasesleep are gone.  Hence the
   functor's parameter list, and hence [UartTxInv.is_txlock]'s single ghost.

   THE OTHER GAP UNDER THIS ONE IS ALSO CLOSED.  [is_txlock] used to be assumed
   separately, in a [LinkTxLockInit.v] whose axiom claimed it out of the
   transmitter token and the frozen DLAB alone.  That statement was never
   provable -- it omitted the lock's STORAGE ([SpecProcinit.lk_fresh], which
   [WpLock.newlock] needs) -- and it had no consumer, so the file is deleted.
     Both halves now exist for real.  kernel-defects.md D2 ("upstream never
   initializes tx_lock") was fixed upstream: `b7c25cf` added an [initsleeplock]
   and `d80e61c5` settled on [initlock(&tx_lock, "uart")] with tx_lock a
   spinlock again, so [main_locks_raw] carries [lk_raw a_tx_lock] down through
   consoleinit and uartinit hands [lk_fresh a_tx_lock "uart"] back (ProofMain
   binds it as [Hlkfresh]).  And the RESOURCE half stopped being contested when
   `d80e61c5` put uartputc_sync behind tx_lock too: [SpecPrintk.pr_res] is
   [emp] now, so the transmitter is tx_lock's alone.
     What is left is a CONSUMER, not a gap: nothing main promises mentions
   [is_txlock], so wiring the [newlock] in means putting [is_txlock] into the
   deposit payload first (ProofMain says where). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
From Stdlib Require Import String.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
(* the classes the binder list generalizes over: [Require Import
   SpecUartwrite] does not put them in scope transitively, and backtick
   generalization then silently invents fresh binders with those names. *)
Require Import WpLock FdSlots IrefSlots.
Require Import DiskPtsto WpUart.
Require Import LinkUart LinkAcquire LinkRelease LinkSleep LinkSleepPrepare.
Require Import ProofUartwrite.
Require Import SpecUartwrite.

Module Uartwrite := UartwriteProof Acquire Release Sleep SleepPrepare Uart.
