(* LinkSysSync.v -- instantiates the sys_sync proof against its callees'
   proofs (acquire / release / sleep_prepare / sleep).  Sealed, so this is
   the only place the five ever meet.

   TWO MODULES SINCE THE BANKING (fs-syscall-specs lane Y).  The walk proves
   the DURABILITY form [SYS_SYNC_FLUSH] -- the landed statement plus the
   caller's batch witness in and the receipt [flushed_sync γ e] out -- and
   the landed [SYS_SYNC] is derived from it, not re-proved, by the
   weakening functor that has stood beside the contract since lane Y landed
   it.  So [SpecSysSync.v] is byte-identical, [ProofSyscall]'s arm 22 takes
   [SysSync.wp_sys_sync_sconf] exactly as it did, and "the postcondition
   only grows" (R10) is a theorem rather than an intention. *)
Require Import LinkAcquire LinkRelease LinkSleepPrepare LinkSleep ProofSysSync.
Require Import SpecSysSyncFlush.

Module SysSyncFlush := SysSyncProof Acquire Release SleepPrepare Sleep.
Module SysSync := SysSyncFlushWeaken SysSyncFlush.
