(* LinkPrintkinit.v -- instantiates the Printkinit proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPrintkinit SpecInitlock.
Require Import LinkInitlock WpSconfPrintkinit.

Module Printkinit := PrintkinitProof Initlock.
