(* LinkConsoleread.v -- consoleread's proof, instantiated against its
   callees'.

   It WAS an [Axiom] -- the single assumption the fileread cone rested on --
   because consoleread had no proof.  It has one now (ProofConsoleread.v), so
   this file is an ordinary functor application over the seven contracts
   consoleread actually calls, and [tools/proof_coverage.py] no longer reports
   an axiom here.

   What consoleread asks of a caller is unchanged by the proof:
   [ConsoleInv.is_conslock] and nothing else about the console -- see
   SpecConsoleread.v.  The ring's CONTENTS are still not promised, and that is
   a property of [ConsoleInv.cons_res] rather than of this link. *)
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
Require Import ProcInv.
Require Import FileInvDefs.
Require Import ConsoleInv.
Require Import LinkMyproc LinkAcquire LinkKilled LinkSleepPrepare LinkSleep.
Require Import LinkEitherCopyout LinkRelease.
Require Import ProofConsoleread.
Require Import SpecConsoleread.

Module Consoleread :=
  ConsolereadProof Myproc Acquire Killed SleepPrepare Sleep EitherCopyout Release.
