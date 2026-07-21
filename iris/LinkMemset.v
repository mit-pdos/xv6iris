(* LinkMemset.v -- instantiates the Memset proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMemsetParts.
Require Import WpSconfMemset.

Module Memset := MemsetProof.
