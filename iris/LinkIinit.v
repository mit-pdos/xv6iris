(* LinkIinit.v *)
Require Import SpecInitlock SpecInitsleeplock SpecIinit ProofIinit.

Module LinkIinit (Initlock : INITLOCK) (Initsleeplock : INITSLEEPLOCK) : IINIT :=
  IinitProof Initlock Initsleeplock.
