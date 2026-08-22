(* LinkKexecPinned.v -- where kexec("/init")'s PINNED proof meets its
   callees', at the same sixteen functor arguments [LinkKexec.v] uses.

   THE SEVENTEENTH ARGUMENT IS THE PINNED WALK.  Phase A consumes
   [NameiInitPinned.wp_namei_init_pinned], which functors over
   [SpecNameiTr.NAMEI_TR]; it enters as [NT] here rather than through a
   [Require Import Link*] inside [ProofKexecPinnedA.v], so that neither that
   file nor [SpecKexecPinned.v] carries the namex link cone.  Apart from
   [NT], the list below is byte-for-byte [LinkKexec.v]'s, and the two
   contracts are linked against exactly the same callee proofs.

   [ProcPagetableGen], NOT [ProcPagetable], for [LinkKexec.v]'s reason. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkIlock LinkReadi
        LinkIunlockput LinkEndOp LinkProcPagetable LinkProcFreepagetable
        LinkWalkaddr LinkFlags2perm LinkUvmalloc LinkUvmclear LinkStrlen
        LinkCopyout LinkSafestrcpy
        LinkPanic LinkNameiTr ProofKexecPinned.

Module KexecPinned := KexecPinnedProof Myproc BeginOp Namei Ilock Readi
                                       Iunlockput EndOp ProcPagetableGen
                                       ProcFreepagetable Walkaddr
                                       Flags2perm Uvmalloc Uvmclear Strlen
                                       Copyout Safestrcpy Panic
                                       LinkNameiTr.NameiTr.
