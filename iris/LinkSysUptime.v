(* LinkSysUptime.v -- instantiates the SysUptime proof against its callees'
   proofs (acquire / release).  Sealed, so this is the only place the three
   ever meet. *)
Require Import LinkAcquire LinkRelease ProofSysUptime.

Module SysUptime := SysUptimeProof Acquire Release.
