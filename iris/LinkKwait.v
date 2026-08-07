(* LinkKwait.v -- kwait's proof, instantiated against the REAL proofs of the
   seven functions it calls. *)
Require Import LinkAcquire LinkRelease LinkMyproc LinkKilled LinkSleep
        LinkCopyout LinkFreeproc ProofKwait.

Module Kwait := KwaitProof Acquire Release Myproc Killed Sleep Copyout Freeproc.
