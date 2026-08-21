(* LinkUsertrap.v -- instantiates usertrap's proof against its eleven
   callees' interfaces.  Sealed, so this is the only place they ever meet.

   TEN OF THE ELEVEN ARE REAL PROOFS: myproc, killed, setkilled, devintr,
   vmfault, yield, prepare_return, kexit, kernelvec -- and, since all
   twenty-two dispatch arms landed, [LinkSyscall]'s [Syscall] too.  This
   header used to name it as the second assumed link "whose own proof is the
   next project"; that project is done, and [LinkSyscall.v] now assumes
   nothing at all.

   THE ONE THAT IS NOT is [LinkPrintk]'s (printk's GENERAL path, which
   usertrap's unexpected-scause arm genuinely calls; printk's PANIC path is
   proved, and the panic arm of usertrap is refuted rather than proved, so
   nothing here rests on it).

   [Print Assumptions Usertrap.wp_usertrap] is therefore the standing
   platform axioms + functional extensionality + consoleintr (inherited
   through devintr's UART cone) + that one.  Note this is NOT the boot-cone
   audit: usertrap is not reachable from [SystemAdequacy] yet, so none of
   this appears in [SystemAssumptions.v]'s list. *)
Require Import LinkSyscall LinkPrintk LinkMyproc LinkKilled LinkSetkilled
                LinkDevintr LinkVmfault LinkYield LinkPrepareReturn LinkKexit
                LinkKernelvec
                ProofUsertrap.

Module Usertrap := UsertrapProof Syscall PrintkGen Myproc Killed Setkilled
                                 Devintr Vmfault Yield PrepareReturn Kexit
                                 Kernelvec.
