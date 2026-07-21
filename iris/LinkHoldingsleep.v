(* LinkHoldingsleep.v -- instantiates the Holdingsleep proof against its
   callees' proofs (acquire / release / myproc).  Sealed, so this is the only
   place the four ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecHoldingsleep SpecAcquire SpecRelease SpecMyproc.
Require Import LinkAcquire LinkRelease LinkMyproc WpSconfHoldingsleep.

Module Holdingsleep := HoldingsleepProof Acquire Release Myproc.
