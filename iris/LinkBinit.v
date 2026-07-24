(* LinkBinit.v *)
Require Import SpecInitlock SpecInitsleeplock SpecBinit ProofBinit.

Module LinkBinit (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : BINIT :=
  BinitProof Initlock Initsleeplock.
