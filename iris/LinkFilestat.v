(* LinkFilestat.v -- instantiates the Filestat proof against its callees'.
   Sealed, so this is the only place the five ever meet.

   ALL FIVE ARE REAL PROOFS -- myproc, ilock, stati, iunlock and copyout --
   so this cone rests on nothing but the platform axioms.  filestat has no
   device arm (see SpecFilestat.v's header: the [bltu] is a single unsigned
   range test and both surviving types take the inode path), so unlike
   LinkFileread there is no assumed consoleread here; and it reaches no
   allocator, so balloc's Axiom does not appear either. *)
Require Import LinkMyproc LinkIlock LinkStati LinkIunlock LinkCopyout
                ProofFilestat.

Module Filestat := FilestatProof Myproc Ilock Stati Iunlock Copyout.
