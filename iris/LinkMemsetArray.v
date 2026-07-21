(* LinkMemsetArray.v -- instantiates the general Memset (array) proof against
   its callees' proofs (the memset prefix/loop/suffix parts).  Sealed, so this
   is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMemset SpecMemsetParts.
Require Import LinkMemset WpMemsetArray.

Module MemsetArray := MemsetArrayProof Memset.
