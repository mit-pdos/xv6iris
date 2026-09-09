(* LinkSysWrite.v -- instantiates the SysWrite proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   sys_write is the THIRD of fs-sysfile's three syscall shells to link.  Its
   one blocking callee was filewrite, and filewrite's contract was uncallable
   by any syscall until S4' made [filewrite_fs_env] content- and
   slot-independent and gave the device table's write column its own owner
   ([SpecFilewrite.filewrite_devsw]).

   THIS CONE ASSUMES NOTHING of its own.  Its FD_DEVICE arm dispatches
   through [devsw[major].write] into consolewrite
   ([LinkConsolewrite]), which is a proof down to the UART's THR store;
   and note what does not appear even though it runs underneath: balloc's
   Axiom.  filewrite's writei is the ALLOCATING one, but [LinkBalloc.v] is a
   proof. *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFilewrite ProofSysWrite.

Module SysWrite := SysWriteProof Argaddr Argint Argfd Filewrite.
