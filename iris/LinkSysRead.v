(* LinkSysRead.v -- instantiates the SysRead proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   sys_read is the SECOND of fs-sysfile's three syscall shells to link.  Its
   one blocking callee was fileread, and fileread's contract was uncallable
   by any syscall until S4' made [fileread_fs_env] content- and
   slot-independent and gave the device table's read column its own owner
   ([SpecFileread.fileread_devsw]).

   THE ASSUMPTION THIS ADDS over sys_fstat's is exactly one, and it comes in
   through [LinkFileread]: [LinkConsoleread.Consoleread.wp_consoleread_sconf]
   is an Axiom (the FD_DEVICE arm dispatches through [devsw[major].read], the
   console is the only device xv6 installs, and consoleread has no proof).
   Everything else under argaddr / argint / argfd / fileread is a real
   proof. *)
Require Import LinkArgaddr LinkArgint LinkArgfd LinkFileread ProofSysRead.

Module SysRead := SysReadProof Argaddr Argint Argfd Fileread.
