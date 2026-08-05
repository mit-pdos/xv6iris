(* LinkKkill.v -- instantiates the Kkill proof against its callees' proofs
   (acquire / release).  Sealed, so this is the only place the three meet. *)
Require Import LinkAcquire LinkRelease ProofKkill.

Module Kkill := KkillProof Acquire Release.
