(* LinkLogWrite.v -- instantiates the LogWrite proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet. *)
Require Import LinkAcquire LinkRelease LinkBpin ProofLogWrite.

Module LogWrite := LogWriteProof Acquire Release Bpin.
