(* LinkMemsetPage.v -- instantiates the MemsetPage proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMemsetPage SpecMemset.
Require Import LinkMemset WpSconfMemsetPage.

Module MemsetPage := MemsetPageProof Memset.
