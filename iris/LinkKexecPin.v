(* LinkKexecPin.v -- the pinned kexec's callees, discharged.

   [LinkKexec.v]'s list with ONE addition: [LinkNameiEra.NameiEra], the
   era-traced namei ([SpecNameiEra.NAMEI_ERA]) the pinned walk calls where
   the landed walk calls [Namei].  BOTH are supplied -- the landed one
   because the blocks this file's cone opens as [LA] / [T] / [PB..PD] are
   functors over it, the era one because [kxc_a1p] makes the call.  They are
   the same 26 bytes of namei proved twice over the same namex; nothing is
   assumed by either.

   So this cone's assumption count is [LinkKexec]'s union
   [LinkNameiEra]'s -- the five platform axioms plus funext, which is what
   the era walk's own Link file records. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkNameiEra LinkIlock
        LinkReadi LinkIunlockput LinkEndOp LinkProcPagetable
        LinkProcFreepagetable LinkWalkaddr LinkFlags2perm LinkUvmalloc
        LinkUvmclear LinkStrlen LinkCopyout LinkSafestrcpy
        LinkPanic ProofKexecPin.

Module KexecPin := KexecPinProof Myproc BeginOp Namei NameiEra Ilock Readi
                                 Iunlockput EndOp
                                 ProcPagetableGen ProcFreepagetable Walkaddr
                                 Flags2perm Uvmalloc Uvmclear Strlen Copyout
                                 Safestrcpy Panic.

(* ===================================================================== *)
(*  THE SENTENCE, UNCONDITIONALLY.                                        *)
(*                                                                        *)
(*  [SpecKexecPin.wp_kexec_pinned_body] -- the Module Type's own           *)
(*  statement, quoted through the module -- on every ONE-ELEMENT pinned    *)
(*  path, which is both era-0 instances.  See ProofKexecPin.v's header     *)
(*  (4) and ProofKexecPinTrace.v's for why the general arm is a            *)
(*  statement-lane question and not a proof debt.                          *)
(* ===================================================================== *)
Notation wp_kexec_pinned_1hop := KexecPin.wp_kexec_pinned_1hop (only parsing).
Notation wp_kexec_pinned_run := KexecPin.wp_kexec_pinned_run (only parsing).
