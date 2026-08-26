(* ====================================================================== *)
(*  OFF THE BUILD (durable-disk lane E-unpin).  This file's row in          *)
(*  iris/_CoqProject is commented out: it is part of the era-0             *)
(*  pinned-/init story, whose premises were                                *)
(*  [FsCfgBoot.fs_cfg_alloc]'s [dv_pin ROOTINO ...] / [fv_pin 7 ...] --    *)
(*  image-CONTENT facts, false at any era after a crash, now removed from  *)
(*  the boot chain (era 0 included).  The source is KEPT, unedited below,  *)
(*  to be PORTED by the file-system behaviour project onto its abstract    *)
(*  state; the handoff banner at the top of                                *)
(*  claude-notes/projects/namei-pinned-lookup.md is the owner's ruling and *)
(*  the full list of files taken off the build.                            *)
(* ====================================================================== *)
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
