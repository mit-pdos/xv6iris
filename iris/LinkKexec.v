(* LinkKexec.v -- kexec's callees, discharged.

   Sixteen function contracts plus [LinkNameiEra.NameiEra], the era-traced
   namei ([SpecNameiEra.NAMEI_ERA]) the contract's walk calls.  BOTH namei
   forms are supplied -- the plain one because the blocks this cone opens
   as [PA.LA] / [PA.T] / [PB..PD] are functors over it, the era one because
   [ProofKexecA.kxc_a1_au] makes the call.

   So this cone's assumption count is the plain kexec cone's union
   [LinkNameiEra]'s. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkNameiEra LinkIlock
        LinkReadi LinkIunlockput LinkEndOp LinkProcPagetable
        LinkProcFreepagetable LinkWalkaddr LinkFlags2perm LinkUvmalloc
        LinkUvmclear LinkStrlen LinkCopyout LinkSafestrcpy
        LinkPanic ProofKexec.

Module Kexec := KexecProof Myproc BeginOp Namei NameiEra Ilock Readi
                           Iunlockput EndOp
                           ProcPagetableGen ProcFreepagetable Walkaddr
                           Flags2perm Uvmalloc Uvmclear Strlen Copyout
                           Safestrcpy Panic.
