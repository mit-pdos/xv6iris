(* LinkSysClose.v -- instantiates the SysClose proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet.

   sys_close was proved long before this file could exist: [Fileclose] was
   its one callee without a proof. *)
Require Import LinkArgfd LinkMyproc LinkFileclose ProofSysClose.

Module SysClose := SysCloseProof Argfd Myproc Fileclose.
