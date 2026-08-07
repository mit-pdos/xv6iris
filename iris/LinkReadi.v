(* LinkReadi.v -- the only file where readi's proof meets its callees'.
   ALL FOUR are proven and none of them can allocate: bmap arrives through
   its second contract [BMAP_NOALLOC] (LinkBmapNoalloc.v), whose proof term
   never mentions LinkBalloc.v's Axiom.  So readi -- unlike writei, which
   inherits balloc's caveat through bmap -- rests on nothing assumed. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecReadi SpecBmap SpecBread SpecBrelse SpecEitherCopyout.
Require Import LinkBmapNoalloc LinkBread LinkBrelse LinkEitherCopyout ProofReadi.

Module Readi := ReadiProof BmapNoalloc Bread Brelse EitherCopyout.
