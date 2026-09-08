(* LinkSysSync.v -- instantiates the sys_sync proof against its callees'
   proofs (acquire / release / sleep_prepare / sleep).  Sealed, so this is
   the only place the five ever meet.

   ONE MODULE: [SpecSysSync.SYS_SYNC] is sys_sync's only contract -- the
   machine frame plus the caller's batch witness in and the durability
   receipt [flushed_sync γ e] out -- so the walk seals it directly and
   nothing is derived here.  [ProofSyscall]'s arm 22 takes the witness at
   zero and drops the receipt at its own call site. *)
Require Import LinkAcquire LinkRelease LinkSleepPrepare LinkSleep ProofSysSync.

Module SysSync := SysSyncProof Acquire Release SleepPrepare Sleep.
