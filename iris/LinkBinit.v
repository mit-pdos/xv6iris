(* LinkBinit.v -- instantiates the binit proof against its callees' proofs
   (initlock and initsleeplock).  Sealed, so this is the only place the three
   ever meet. *)
Require Import LinkInitlock LinkInitsleeplock ProofBinit.

Module Binit := BinitProof Initlock Initsleeplock.
