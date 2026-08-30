(* LinkFilereadAU.v -- instantiates the FILEREAD_AU proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet.

   THREE, NOT SIX, AND THAT IS THE POINT.  [LinkFileread.v] instantiates the
   landed walk against Piperead, Ilock, Readi, Iunlock, Consoleread and Panic,
   and its ONE assumption comes in through Consoleread ([LinkConsoleread.v]
   supplies that contract with an Axiom: the FD_DEVICE arm dispatches through
   [devsw[major].read] and consoleread has no proof).  [FILEREAD_AU] pins the
   descriptor to [FdOpen true wb (FdInode i)], so the readable test, the pipe
   arm, the device arm and the panic arm are refuted rather than walked -- and
   the axiom leaves the cone with them.  The three that remain (ilock, readi,
   iunlock) are all real proofs.

   Note what does NOT appear even though it runs underneath: balloc's Axiom.
   readi reaches bmap through [BMAP_NOALLOC], exactly as the landed link
   records.

   The functor's parameter ORDER is Ilock, Readi, Iunlock -- see
   [ProofFilereadAU.v]'s [Module FilereadAUProof] line, which is the only
   authority on it. *)
Require Import LinkIlock LinkReadi LinkIunlock ProofFilereadAU.

Module FilereadAU := FilereadAUProof Ilock Readi Iunlock.
