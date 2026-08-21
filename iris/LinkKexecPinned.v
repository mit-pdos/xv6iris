(* LinkKexecPinned.v -- where kexec("/init")'s PINNED proof meets its
   callees', at the same sixteen functor arguments [LinkKexec.v] uses.

   THE ONE THING TO NOTICE IS WHAT IS *NOT* HERE.  The pinned walk consumes
   [NameiInitPinned.wp_namei_init_pinned], which is a closed THEOREM --
   [DirViewPin.NameiPinnedI] is already instantiated at
   [LinkNameiTr.NameiTr] -- so the pinned namei enters through the proof
   file's imports rather than as a seventeenth module argument.  The list
   below is therefore byte-for-byte [LinkKexec.v]'s, and the two contracts
   are linked against exactly the same callee proofs.

   [ProcPagetableGen], NOT [ProcPagetable], for [LinkKexec.v]'s reason. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkIlock LinkReadi
        LinkIunlockput LinkEndOp LinkProcPagetable LinkProcFreepagetable
        LinkWalkaddr LinkFlags2perm LinkUvmalloc LinkUvmclear LinkStrlen
        LinkCopyout LinkSafestrcpy
        LinkPanic ProofKexecPinned.

Module KexecPinned := KexecPinnedProof Myproc BeginOp Namei Ilock Readi
                                       Iunlockput EndOp ProcPagetableGen
                                       ProcFreepagetable Walkaddr
                                       Flags2perm Uvmalloc Uvmclear Strlen
                                       Copyout Safestrcpy Panic.
