(* LinkFileread.v -- instantiates the Fileread proof against its callees'.
   Sealed, so this is the only place the five ever meet.

   [Consoleread] is the one that is ASSUMED (LinkConsoleread.v supplies its
   contract with an [Axiom], the single assumption this cone rests on: the
   FD_DEVICE arm dispatches through [devsw[f->major].read], the console is the
   only device xv6 installs, and consoleread has no proof).  The other four --
   piperead, ilock, readi, iunlock -- are real proofs, and readi reaches bmap
   through [BMAP_NOALLOC], so balloc's Axiom does NOT appear here. *)
Require Import LinkPiperead LinkIlock LinkReadi LinkIunlock LinkConsoleread
                ProofFileread.

Module Fileread := FilereadProof Piperead Ilock Readi Iunlock Consoleread.
