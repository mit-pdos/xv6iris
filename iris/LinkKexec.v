(* LinkKexecAU.v -- the AU kexec's callees, discharged.

   [LinkKexecPin.v]'s list exactly: [LinkKexec.v]'s sixteen plus
   [LinkNameiEra.NameiEra], the era-traced namei ([SpecNameiEra.NAMEI_ERA])
   the AU walk calls where the landed walk calls [Namei].  BOTH are
   supplied -- the landed one because the blocks this cone opens as
   [PA.LA] / [PA.T] / [PB..PD] are functors over it, the era one because
   [ProofKexecAUA.kxc_a1_au] makes the call.

   So this cone's assumption count is [LinkKexec]'s union [LinkNameiEra]'s,
   which is what the pinned lane's Link file already records. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkNameiEra LinkIlock
        LinkReadi LinkIunlockput LinkEndOp LinkProcPagetable
        LinkProcFreepagetable LinkWalkaddr LinkFlags2perm LinkUvmalloc
        LinkUvmclear LinkStrlen LinkCopyout LinkSafestrcpy
        LinkPanic ProofKexecAU.

Module KexecAU := KexecAUProof Myproc BeginOp Namei NameiEra Ilock Readi
                               Iunlockput EndOp
                               ProcPagetableGen ProcFreepagetable Walkaddr
                               Flags2perm Uvmalloc Uvmclear Strlen Copyout
                               Safestrcpy Panic.
