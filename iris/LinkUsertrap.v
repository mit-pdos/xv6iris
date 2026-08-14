(* LinkUsertrap.v -- instantiates usertrap's proof against its eleven
   callees' interfaces.  Sealed, so this is the only place they ever meet.

   NINE OF THE ELEVEN ARE REAL PROOFS: myproc, killed, setkilled, devintr,
   vmfault, yield, prepare_return, kexit and kernelvec.  The two that are not
   are the two the coverage report already records as ASSUMED --
   [LinkSyscall]'s [Axiom] (the syscall dispatcher, whose own proof is the
   next project) and [LinkPrintk]'s (printk's GENERAL path, which
   usertrap's unexpected-scause arm genuinely calls; printk's PANIC path is
   proved, and the panic arm of usertrap is refuted rather than proved, so
   nothing here rests on it).

   [Print Assumptions Usertrap.wp_usertrap] is therefore the standing
   platform axioms + functional extensionality + consoleintr (inherited
   through devintr's UART cone) + those two. *)
Require Import LinkSyscall LinkPrintk LinkMyproc LinkKilled LinkSetkilled
                LinkDevintr LinkVmfault LinkYield LinkPrepareReturn LinkKexit
                LinkKernelvec
                ProofUsertrap.

Module Usertrap := UsertrapProof Syscall PrintkGen Myproc Killed Setkilled
                                 Devintr Vmfault Yield PrepareReturn Kexit
                                 Kernelvec.
