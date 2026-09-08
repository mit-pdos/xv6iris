(* LinkSysMknod.v -- the sys_mknod proof composed with its callees'.

   SIX arguments: create arrives ONCE, at its AU contract ([CreateAU],
   through LinkCreateAU.v), because the era walk takes a relative start and
   the proof therefore calls one create contract for every fetched string.
   The AU copy reaches nameiparent through the era wrapper, and
   [LinkNparWrapEra]'s header records that the two walks' assumption sets
   are byte-identical. *)
Require Import LinkBeginOp LinkArgint LinkArgstr LinkCreateAU
        LinkIunlockput LinkEndOp ProofSysMknod.

Module SysMknod := SysMknodProof BeginOp Argint Argstr CreateAU
                                 Iunlockput EndOp.
