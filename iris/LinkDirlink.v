(* LinkDirlink.v -- the only file where dirlink's proof meets its callees'.
   All five are real proofs and none of them is assumed:

   - dirlookup arrives through LinkDirlookup.v (readi / namecmp / iget);
   - readi arrives through LinkReadi.v, whose bmap instance is the
     no-allocation one;
   - iput arrives through LinkIput.v;
   - strncpy arrives through LinkStrncpy.v;
   - writei arrives through LinkWritei.v, whose bmap CAN allocate -- balloc
     is itself proven (LinkBalloc.v), so nothing new is assumed here; what
     writei's cone carries is the THREADED printk obligation, which
     [SpecDirlink]'s [printk_gen_contract] premise passes straight through
     to dirlink's callers.

   panic is NOT a module here.  dirlink's one panic -- panic("dirlink read")
   at +0x60 -- is DEAD: the contract's GRANULARITY premise makes every loop
   readi full-length ([ProofDirlookupParts.dlk_rd_clamp_full]), so the
   [bne a0,s3] at +0x3e always falls through.  dirlink's OWN arm,
   panic("dirlink read") at +0x68, is discharged against [Panic] below; the
   [kernel_data] / [panic_env] it takes also feed dirlookup / readi / iput /
   writei, whose arms are theirs.

   So this cone's assumption count stays at the five platform axioms plus
   funext. *)
Require Import LinkDirlookup LinkReadi LinkIput LinkStrncpy LinkWritei
        LinkPanic ProofDirlink.

Module Dirlink := DirlinkProof Dirlookup Readi Iput Strncpy Writei Panic.
