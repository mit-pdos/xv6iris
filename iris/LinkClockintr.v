(* LinkClockintr.v -- instantiates the clockintr proof against its callees'
   proofs (cpuid / acquire / release / wakeup).  Sealed, so this is the only
   place the five ever meet. *)
Require Import LinkCpuid LinkAcquire LinkRelease LinkWakeup ProofClockintr.

Module Clockintr := ClockintrProof Cpuid Acquire Release Wakeup.
