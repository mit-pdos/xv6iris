(* LinkConsolewrite.v -- consolewrite's proof, instantiated against its
   callees'.

   It WAS an [Axiom] (the fourth of its kind, beside LinkKerneltrap.v,
   LinkConsoleintr.v and LinkConsoleread.v), because filewrite's FD_DEVICE arm
   dispatches through [devsw[f->major].write], the console is the only device
   xv6 installs, and consolewrite had no proof.  It has one now
   (ProofConsolewrite.v), so this file is an ordinary two-argument functor
   application and the filewrite cone lost an assumption.

   What consolewrite needs from a caller grew with the proof, and the growth
   is the honest part: [SpecConsolewrite.v] now asks for [WpUart.dev_inv] and
   [UartTxInv.is_txlock] -- uartwrite's whole credential -- where the axiom
   was silent about the transmitter altogether.  Both are persistent and both
   ride in [SpecFilewrite.filewrite_dev_caps]. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import RegFile.
Require Import FdSlots WpLock.
Require Import KallocInv.
Require Import FileInv ProcInv.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import LinkEitherCopyin LinkUartwrite.
Require Import ProofConsolewrite.
Require Import SpecConsolewrite.

Module Consolewrite := ConsolewriteProof EitherCopyin Uartwrite.
