(* LinkSysFstat.v -- instantiates the SysFstat proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet.

   sys_fstat is the FIRST of fs-sysfile's three syscall shells to link.  Its
   one blocking callee was filestat, and filestat's contract was uncallable
   by any syscall until S4' made [filestat_fs_env] content-independent --
   which is why this file could not exist at S4. *)
Require Import LinkArgaddr LinkArgfd LinkFilestat ProofSysFstat.

Module SysFstat := SysFstatProof Argaddr Argfd Filestat.
