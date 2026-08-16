(* LinkFilewrite.v -- instantiates the Filewrite proof against its callees'.
   Sealed, so this is the only place the seven ever meet.

   [Consolewrite] is the one that is ASSUMED (LinkConsolewrite.v supplies its
   contract with an [Axiom], the single assumption this cone rests on: the
   FD_DEVICE arm dispatches through [devsw[f->major].write], the console is
   the only device xv6 installs, and consolewrite has no proof).  The other
   six -- pipewrite, ilock, writei, iunlock, begin_op and end_op -- are real
   proofs.

   NOTE WHAT DOES *NOT* APPEAR, and it is the one thing a reader is likely
   to expect: balloc's Axiom.  filewrite's writei is the ALLOCATING one
   ([BMAP_ALLOC] through bmap), so balloc really does run underneath this
   module -- but [LinkBalloc.v] is a proof, not an assumption, and S3s's
   [Print Assumptions] over Writei/Balloc/Bmap confirms the five platform
   axioms and funext and nothing else.

   The functor's parameter ORDER is Pipewrite, Ilock, Writei, Iunlock,
   BeginOp, EndOp, Consolewrite -- see [ProofFilewrite.v]'s [Module
   FilewriteProof] line, which is the only authority on it. *)
Require Import LinkPipewrite LinkIlock LinkWritei LinkIunlock LinkBeginOp
                LinkEndOp LinkConsolewrite LinkPanic
                ProofFilewrite.

Module Filewrite := FilewriteProof Pipewrite Ilock Writei Iunlock BeginOp
                                   EndOp Consolewrite Panic.
