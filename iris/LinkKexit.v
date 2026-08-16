(* LinkKexit.v -- instantiates the Kexit proof against its callees' proofs.
   Sealed, so this is the only place the ten ever meet.

   EVERY ONE OF THE TEN IS A REAL PROOF as of C6b -- [Iput] is [LinkIput]'s,
   over the real inode cache, and the bridging axiom this file used to import
   is gone.  [Print Assumptions Kexit.wp_kexit_sconf] is therefore the Sail
   platform's five primitives plus functional extensionality, and nothing
   else: the exit path carries no file-system assumption. *)
Require Import LinkMyproc LinkFileclose LinkBeginOp LinkIput LinkEndOp
                LinkAcquire LinkReparent LinkWakeup LinkRelease LinkSched
                ProofKexit LinkPanic.

Module Kexit := KexitProof Myproc Fileclose BeginOp Iput EndOp
                          Acquire Reparent Wakeup Release Sched Panic.
