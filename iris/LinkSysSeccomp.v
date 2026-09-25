(* LinkSysSeccomp.v -- sys_seccomp's proof, instantiated against the REAL
   proofs of its two callees (argaddr, myproc). *)
Require Import LinkArgaddr LinkMyproc ProofSysSeccomp.

Module SysSeccomp := SysSeccompProof Argaddr Myproc.
