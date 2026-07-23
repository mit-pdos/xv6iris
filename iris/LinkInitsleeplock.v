(* LinkInitsleeplock.v -- instantiates the Initsleeplock proof against its
   callee's proof (initlock).  Sealed, so this is the only place the two ever
   meet. *)
Require Import LinkInitlock ProofInitsleeplock.

Module Initsleeplock := InitsleeplockProof Initlock.
