(* LinkKexit.v -- instantiates the Kexit proof against its callees' proofs.
   Sealed, so this is the only place the ten ever meet.

   [IputCompat] is the one assumption in the cone; everything else --
   including [Fileclose], which kexit calls once per open descriptor and which
   was the last of them to be proved -- is a real proof.

   IT IS NOT [LinkIput.Iput] ANY MORE.  iput is PROVEN as of C6a, against
   [SpecIput.IPUT2] (the real inode cache); this cone still speaks the
   frozen [emp]-shaped [SpecIput.IPUT], which v2 does not imply and cannot
   (LinkIputCompat.v says exactly why).  Repointing here rather than
   changing [ProofKexit.v] is what keeps this cone's proof untouched until
   C6b retires the placeholder. *)
Require Import LinkMyproc LinkFileclose LinkBeginOp LinkIputCompat LinkEndOp
                LinkAcquire LinkReparent LinkWakeup LinkRelease LinkSched
                ProofKexit.

Module Kexit := KexitProof Myproc Fileclose BeginOp IputCompat EndOp
                          Acquire Reparent Wakeup Release Sched.
