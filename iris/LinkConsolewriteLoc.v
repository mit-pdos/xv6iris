(* LinkConsolewriteLoc.v -- the LOCATED consolewrite proof, instantiated
   against its callees'.

   [LinkConsolewrite.v] with the uartwrite instance swapped for the located
   one: the located walk takes [UARTWRITE_LOC] where the landed walk takes
   [UARTWRITE], and nothing else about the pair differs.  So
   [ConsolewriteLoc] is a closed instance of
   [SpecConsolewriteLoc.CONSOLEWRITE_LOC] -- the whole device-side chain
   from the THR store up to consolewrite's return value is PROVED, with no
   assumption beyond either_copyin's and the four the uartwrite instance
   already carries.

   What is still a functor above this is [SpecFilewriteCons.FILEWRITE_CONS]
   -- filewrite's device arm, which is where this instance gets consumed. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import LinkEitherCopyin LinkUartwriteLoc.
Require Import ProofConsolewriteLoc.

Module ConsolewriteLoc := ConsolewriteLocProof EitherCopyin UartwriteLoc.
