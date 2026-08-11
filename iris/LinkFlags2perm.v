(* LinkFlags2perm.v -- instantiates the Flags2perm proof.  flags2perm has no
   callees, so Flags2permProof takes no functor arguments; this is the sole
   meeting point of the spec and its sealed proof. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecFlags2perm.
Require Import ProofFlags2perm.

Module Flags2perm := Flags2permProof.
