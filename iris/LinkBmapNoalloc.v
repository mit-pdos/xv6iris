(* LinkBmapNoalloc.v -- bmap's second contract, for a caller that cannot
   allocate (readi, which runs outside a transaction).  Under
   [bv_unsigned (blkmap_get bm fbn) <> 0] all three balloc arms are dead, so
   this instance takes only bread and brelse -- NOT balloc and NOT log_write
   -- and therefore carries none of LinkBalloc.v's Axiom.  The proof body is
   shared with [LinkBmap.v]'s: both are wrappers over ProofBmap.v's
   [BmapCore], which is parameterised by whether the allocation arms are
   live.  Precedent: LinkWalkNoalloc.v. *)
Require Import LinkBread LinkBrelse ProofBmap.

Module BmapNoalloc := BmapNoallocProof Bread Brelse.
