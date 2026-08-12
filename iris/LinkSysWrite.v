(* LinkSysWrite.v -- instantiates the SysWrite proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   sys_write is the THIRD of fs-sysfile's three syscall shells to link.  Its
   one blocking callee was filewrite, and filewrite's contract was uncallable
   by any syscall until S4' made [filewrite_fs_env] content- and
   slot-independent and gave the device table's write column its own owner
   ([SpecFilewrite.filewrite_devsw]).

   THE ASSUMPTION THIS ADDS over sys_fstat's is exactly one, and it comes in
   through [LinkFilewrite]:
   [LinkConsolewrite.Consolewrite.wp_consolewrite_sconf] is an Axiom (the
   FD_DEVICE arm dispatches through [devsw[major].write], the console is the
   only device xv6 installs, and consolewrite has no proof).  Note what does
   NOT appear even though it runs underneath: balloc's Axiom.  filewrite's
   writei is the ALLOCATING one, but [LinkBalloc.v] is a proof. *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFilewrite ProofSysWrite.

Module SysWrite := SysWriteProof Argaddr Argint Argfd Filewrite.
