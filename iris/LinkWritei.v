(* LinkWritei.v -- the only file where writei's proof meets its callees'.
   Five of its six callees are PROVEN (bread, brelse, log_write,
   either_copyin, iupdate); the sixth, bmap, carries the `!' caveat because
   it rests on the still-assumed balloc (LinkBalloc.v's single Axiom).  So
   writei inherits exactly that one caveat in tools/proof_coverage.py and
   nothing else. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWritei SpecBmap SpecBread SpecBrelse SpecLogWrite
        SpecEitherCopyin SpecIupdate.
Require Import LinkBmap LinkBread LinkBrelse LinkLogWrite LinkEitherCopyin
        LinkIupdate ProofWritei.

Module Writei := WriteiProof Bmap Bread Brelse LogWrite EitherCopyin Iupdate.
