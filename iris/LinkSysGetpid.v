(* LinkSysGetpid.v -- instantiates the SysGetpid proof against its callee's
   proof (myproc).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMyproc ProofSysGetpid.

Module SysGetpid := SysGetpidProof Myproc.
