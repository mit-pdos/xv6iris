(* LinkWriteHead.v -- instantiates the WriteHead proof against its callees'
   proofs (bread / bwrite / brelse).  Sealed, so this is the only place the
   four ever meet. *)
Require Import LinkBread LinkBwrite LinkBrelse ProofWriteHead.

Module WriteHead := WriteHeadProof Bread Bwrite Brelse.
