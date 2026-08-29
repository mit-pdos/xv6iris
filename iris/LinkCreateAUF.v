(* LinkCreateAUF.v -- create's T_FILE ATOMIC-UPDATE proof composed with its
   callees'.

   [LinkCreateAU.v] verbatim with [CreateAUFProof] in place of
   [CreateAUProof]: the seven module arguments are the same seven real
   proofs -- the ERA nameiparent ([NparWrap]), ilock, iunlockput, dirlookup,
   ialloc, iupdate, dirlink -- so nothing new is assumed anywhere and this
   cone's assumption count is [LinkCreateAU]'s exactly.

   The T_DIR sub-branch's two module arguments are still not missing and
   still never existed: [ProofCreateAUF] pins [ty = T_FILE], and
   [T_FILE <> T_DIR] refutes the +0xca branch just as [T_DEVICE <> T_DIR]
   does one file over (SpecCreateAUF's header). *)
Require Import LinkNparWrapEra LinkIlock LinkIunlockput LinkDirlookup
Require Import TsoCtx.
        LinkIalloc LinkIupdate LinkDirlink
        ProofCreateAUF.

Module CreateAUF := CreateAUFProof NparWrap Ilock Iunlockput Dirlookup
                                   Ialloc Iupdate Dirlink.
