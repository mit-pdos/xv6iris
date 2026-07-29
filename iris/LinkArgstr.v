(* LinkArgstr.v -- instantiates the Argstr proof against its callees' proofs.
   argaddr is INLINED in argstr's machine code, so the callees are argraw (not
   argaddr) and fetchstr.  Sealed, so this is the only place the three meet. *)
Require Import LinkArgraw LinkFetchstr.
Require Import ProofArgstr.

Module Argstr := ArgstrProof Argraw Fetchstr.
