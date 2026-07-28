(* LinkPiperead.v -- instantiate piperead's proof functor at the proven
   callees, sealing it as PIPEREAD.  This is what makes piperead count as
   PROVEN (tools/proof_coverage.py): the functor is sealed by its Module
   Type, so linking it discharges every assumption it was written against.
   [SleepGen] is the lock-generic sleep (SpecSleep.v's SLEEP_GEN) -- the
   pipe's lock is cancellable, so the static-[is_lock] SLEEP will not do. *)
Require Import LinkMyproc LinkAcquire LinkKilled LinkWakeup LinkSleep LinkCopyout LinkRelease.
Require Import ProofPiperead.

Module Piperead := PipereadProof Myproc AcquireGen Killed Wakeup SleepGen Copyout ReleaseGen.
