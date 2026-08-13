(* LinkPiperead.v -- instantiate piperead's proof functor at the proven
   callees, sealing it as PIPEREAD.  This is what makes piperead count as
   PROVEN (tools/proof_coverage.py): the functor is sealed by its Module
   Type, so linking it discharges every assumption it was written against.

   The split sleep protocol takes TWO callees here ([SleepPrepare] and
   [Sleep]), and neither is lock-generic: piperead drops and re-takes the
   pipe's cancellable lock itself, through [ReleaseGen] / [AcquireGen]. *)
Require Import LinkMyproc LinkAcquire LinkKilled LinkWakeup LinkSleepPrepare LinkSleep LinkCopyout LinkRelease.
Require Import ProofPiperead.

Module Piperead := PipereadProof Myproc AcquireGen Killed Wakeup SleepPrepare Sleep Copyout ReleaseGen.
