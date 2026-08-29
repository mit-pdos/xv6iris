(* LinkFilewriteAU.v -- instantiates the FILEWRITE_AU proof against its
   callees' proofs.  Sealed, so this is the only place the five ever meet.

   FIVE, NOT EIGHT, AND THAT IS THE POINT.  [LinkFilewrite.v] instantiates
   the landed walk against Pipewrite, Ilock, Writei, Iunlock, BeginOp,
   EndOp, Consolewrite and Panic, and its ONE assumption comes in through
   Consolewrite ([LinkConsolewrite.v] supplies that contract with an Axiom:
   the FD_DEVICE arm dispatches through [devsw[major].write] and
   consolewrite has no proof).  [FILEWRITE_AU] pins the descriptor to
   [FdOpen rb true (FdInode i)], so the pipe, device and panic arms are
   refuted rather than walked -- and the axiom leaves the cone with them.
   The five that remain (ilock, writei, iunlock, begin_op, end_op) are all
   real proofs.

   Note what does NOT appear even though it runs underneath: balloc's
   Axiom.  filewrite's writei is the ALLOCATING one, but [LinkBalloc.v] is
   a proof.

   The functor's parameter ORDER is Ilock, Writei, Iunlock, BeginOp, EndOp
   -- see [ProofFilewriteAU.v]'s [Module FilewriteAUProof] line, which is
   the only authority on it. *)
Require Import LinkIlock LinkWritei LinkIunlock LinkBeginOp LinkEndOp
                ProofFilewriteAU.

Module FilewriteAU := FilewriteAUProof Ilock Writei Iunlock BeginOp EndOp.
