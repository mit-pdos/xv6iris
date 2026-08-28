(* LinkCreateAU.v -- create's ATOMIC-UPDATE proof composed with its
   callees', the ERA nameiparent in place of the landed one.

   [LinkCreate.v]'s shape with ONE argument changed: the walk arrives
   through [LinkNparWrapEra.v] ([NparWrap], nameiparent at
   [SpecNparWrapEra.wp_npar_wrap_era]) instead of through
   [LinkNameiparent.v].  The other six are the same real proofs
   [LinkCreate] composes -- ilock, iunlockput, dirlookup, ialloc, iupdate,
   dirlink -- so nothing new is assumed anywhere.

   The T_DIR sub-branch's two module arguments are not missing: they never
   existed.  [ProofCreateAU] fixes [ty = T_DEVICE] and refutes the +0xca
   branch outright, so [cr_mkdir_half] / [cr_fail_mkdir_half] have no
   counterpart in that file at all (SpecCreateAU's header, difference (2)).

   This cone's assumption count is therefore [LinkCreate]'s with the era
   walk's in place of the landed walk's -- and those are byte-identical
   ([LinkNparWrapEra]'s header: the two platform axioms plus funext). *)
Require Import LinkNparWrapEra LinkIlock LinkIunlockput LinkDirlookup
        LinkIalloc LinkIupdate LinkDirlink
        ProofCreateAU.

Module CreateAU := CreateAUProof NparWrap Ilock Iunlockput Dirlookup
                                 Ialloc Iupdate Dirlink.
