(* LinkFilewrite.v -- instantiates the Filewrite proof against its callees'.
   Sealed, so this is the only place the seven ever meet.

   THE CONSOLE CALLEE IS A PROOF.  filewrite's FD_DEVICE arm relays the
   UART's accepted-trace receipt on the console major, so it calls
   [SpecConsolewrite.CONSOLEWRITE] -- consolewrite's ONE contract, which is
   the general form at every OTHER major too (its seed premise is free
   there), so the walk needs a single call site.  All eight callees are real
   proofs; nothing in this cone is assumed.

   NOTE WHAT DOES *NOT* APPEAR, and it is the one thing a reader is likely
   to expect: balloc's Axiom.  filewrite's writei is the ALLOCATING one
   ([BMAP_ALLOC] through bmap), so balloc really does run underneath this
   module -- but [LinkBalloc.v] is a proof, not an assumption, and S3s's
   [Print Assumptions] over Writei/Balloc/Bmap confirms the five platform
   axioms and funext and nothing else.

   The functor's parameter ORDER is Pipewrite, Ilock, Writei, Iunlock,
   BeginOp, EndOp, Consolewrite, Panic -- see [ProofFilewrite.v]'s
   [Module FilewriteProof] line, which is the only authority on it. *)
Require Import LinkPipewrite LinkIlock LinkWritei LinkIunlock LinkBeginOp
                LinkEndOp LinkConsolewrite LinkPanic
                ProofFilewrite.

Module Filewrite := FilewriteProof Pipewrite Ilock Writei Iunlock BeginOp
                                   EndOp Consolewrite Panic.
