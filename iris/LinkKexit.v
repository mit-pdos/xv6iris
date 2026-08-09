(* LinkKexit.v -- instantiates the Kexit proof against its callees' proofs.
   Sealed, so this is the only place the ten ever meet.

   [Iput] is the one assumption in the cone (LinkIput.v); everything else --
   including [Fileclose], which kexit calls once per open descriptor and which
   was the last of them to be proved -- is a real proof. *)
Require Import LinkMyproc LinkFileclose LinkBeginOp LinkIput LinkEndOp
                LinkAcquire LinkReparent LinkWakeup LinkRelease LinkSched
                ProofKexit.

Module Kexit := KexitProof Myproc Fileclose BeginOp Iput EndOp
                          Acquire Reparent Wakeup Release Sched.
