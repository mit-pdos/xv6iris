(* LinkSysKill.v -- instantiates the SysKill proof against its callees'
   proofs (argint / kkill).  Sealed, so this is the only place the three
   meet. *)
Require Import LinkArgint LinkKkill ProofSysKill.

Module SysKill := SysKillProof Argint Kkill.
