(* LinkInitsleeplock.v -- instantiates the Initsleeplock proof against its
   callee's proof (initlock).  Sealed, so this is the only place the two ever
   meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecInitsleeplock SpecInitlock.
Require Import LinkInitlock WpSconfInitsleeplock.

Module Initsleeplock := InitsleeplockProof Initlock.
