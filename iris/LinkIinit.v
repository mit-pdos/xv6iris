(* LinkIinit.v -- instantiates the iinit proof against its callees' proofs
   (initlock and initsleeplock).  Sealed, so this is the only place the three
   ever meet. *)
Require Import LinkInitlock LinkInitsleeplock ProofIinit.

Module Iinit := IinitProof Initlock Initsleeplock.
