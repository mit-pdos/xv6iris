(* LinkConsolewrite.v -- consolewrite's proof, instantiated against its
   callees'.

   The walk takes [UARTWRITE_LOC], the uartwrite contract that carries the
   accepted-trace receipt, so [Consolewrite] is a closed instance of
   [SpecConsolewrite.CONSOLEWRITE] -- the whole device-side chain from the
   THR store up to consolewrite's return value is PROVED, with no assumption
   beyond either_copyin's and the four the uartwrite instance already
   carries.

   What is still a functor above this is [SpecFilewrite.FILEWRITE] --
   filewrite itself, whose FD_DEVICE arm is where this instance gets
   consumed, at EVERY major and not only the console's: the cell is "null or
   consolewrite" everywhere, and consolewrite's contract is the general form
   because its seed premise is free where the caller supplied none. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import LinkEitherCopyin LinkUartwriteLoc.
Require Import ProofConsolewrite.

Module Consolewrite := ConsolewriteProof EitherCopyin UartwriteLoc.
