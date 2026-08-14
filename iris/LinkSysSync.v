(* LinkSysSync.v -- instantiates the sys_sync proof against its callees'
   proofs (acquire / release / sleep_prepare / sleep).  Sealed, so this is
   the only place the five ever meet. *)
Require Import LinkAcquire LinkRelease LinkSleepPrepare LinkSleep ProofSysSync.

Module SysSync := SysSyncProof Acquire Release SleepPrepare Sleep.
