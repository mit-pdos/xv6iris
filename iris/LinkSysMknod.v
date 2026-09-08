(* LinkSysMknod.v -- the sys_mknod proof composed with its callees'.

   SIX arguments: create arrives ONCE, at its one contract ([Create],
   through LinkCreate.v), called at [T_DEVICE].  The era walk takes a
   relative start, so the proof calls one create contract for every fetched
   string; create reaches nameiparent through the era wrapper, and
   [LinkNparWrapEra]'s header records that the walk's assumption set is the
   frozen walk's, byte for byte. *)
Require Import LinkBeginOp LinkArgint LinkArgstr LinkCreate
        LinkIunlockput LinkEndOp ProofSysMknod.

Module SysMknod := SysMknodProof BeginOp Argint Argstr Create
                                 Iunlockput EndOp.
