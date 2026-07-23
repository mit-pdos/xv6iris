(* LinkMyproc.v -- instantiates the Myproc proof against its callee's proof
   (push_off / pop_off).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkPushOff ProofMyproc.

Module Myproc := MyprocProof PushOff.
