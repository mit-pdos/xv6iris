(* LinkUartwriteLoc.v -- the LOCATED uartwrite proof, instantiated against
   the same callees' proofs as [LinkUartwrite.v].

   The located walk ([ProofUartwriteLoc.v]) is a copy-adapt of the landed
   one and a functor over exactly the same five contracts, so this file is
   [LinkUartwrite.v] with one name changed.  Its point is that the located
   contract is INHABITED and not merely stated: [UartwriteLoc] is a closed
   instance of [SpecUartwriteLoc.UARTWRITE_LOC], with no assumption of its
   own beyond the five the landed instance already carries.

   Both instances coexist, and that is deliberate (R10): a caller that does
   not chain receipts keeps calling [Uartwrite], and the retirement step
   that deletes the sublist-only walk deletes this pair of files' older
   half, not its newer one. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
From Stdlib Require Import String.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import LinkUart LinkAcquire LinkRelease LinkSleep LinkSleepPrepare.
Require Import ProofUartwriteLoc.

Module UartwriteLoc := UartwriteLocProof Acquire Release Sleep SleepPrepare Uart.
