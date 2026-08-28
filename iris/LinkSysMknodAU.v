(* LinkSysMknodAU.v -- the sys_mknod ATOMIC-UPDATE proof composed with its
   callees'.

   [LinkSysMknod.v]'s cone plus ONE argument: create arrives TWICE, at the
   landed contract ([Create], through LinkCreate.v) and at the AU one
   ([CreateAU], through LinkCreateAU.v).  Both are real proofs and they
   share every callee but the walk, so nothing new is assumed -- the AU
   copy reaches nameiparent through the ERA wrapper and the landed one
   through the frozen wrapper, and [LinkNparWrapEra]'s header records that
   the two walks' assumption sets are byte-identical.

   WHY BOTH.  The era walk is absolute-paths-only, so the fetched string
   decides which contract this function can call; the relative branch is
   what the ret-0 arm's escape disjunct is about (SpecSysMknodAUEra's
   header, finding (3)).  When the era walk grows its relative arm the
   [Create] argument comes off and this file has six again. *)
Require Import LinkBeginOp LinkArgint LinkArgstr LinkCreate LinkCreateAU
        LinkIunlockput LinkEndOp ProofSysMknodAU.

Module SysMknodAU := SysMknodAUProof BeginOp Argint Argstr Create CreateAU
                                     Iunlockput EndOp.
