(* LinkKexec.v -- the only file where kexec's proof meets its callees'.

   Sixteen functor arguments, and kexec is the one function in the tree that
   reaches all three subsystems at once, so this is where the FS cone, the
   page-table cone and the string/copy cone finally join:

   - the FS transaction: begin_op / end_op (LinkBeginOp.v, LinkEndOp.v) and,
     inside it, namei -> ilock -> readi -> iunlockput (LinkNamei.v,
     LinkIlock.v, LinkReadi.v, LinkIunlockput.v) -- iunlockput is kexec's
     only route to iput, and hence the one that used to carry iput's
     [iput_acquiresleep_order_ADMITTED] into this cone (that axiom is gone --
     claude-notes/projects/iput-acquiresleep.md);
   - the address space: proc_pagetable (LinkProcPagetable.v) at its GENERAL
     [PROC_PAGETABLE_GEN] instantiation, uvmalloc / uvmclear / walkaddr
     (LinkUvmalloc.v, LinkUvmclear.v, LinkWalkaddr.v) and, on every [bad:]
     path plus the commit, proc_freepagetable (LinkProcFreepagetable.v);
   - the arguments: strlen and copyout per argument (LinkStrlen.v,
     LinkCopyout.v), safestrcpy for p->name (LinkSafestrcpy.v);
   - plus myproc (LinkMyproc.v) and flags2perm (LinkFlags2perm.v).

   [ProcPagetableGen], NOT [ProcPagetable]: kexec runs at
   [kalloc_env ga None] (uvmalloc and proc_freepagetable both require it)
   and tests proc_pagetable's result against 0, so it is the caller that can
   use the uncounted arm -- see claude-notes/projects/kexec.md, "What is NOT
   blocked".

   panic is not a module argument.  The one live panic kexec can reach is
   ilock's [ilock: no type], which [SpecIlock] does not refute; the contract
   takes [panic_wp_any] and threads it to the callees, never consuming it
   locally. *)
Require Import LinkMyproc LinkBeginOp LinkNamei LinkIlock LinkReadi
        LinkIunlockput LinkEndOp LinkProcPagetable LinkProcFreepagetable
        LinkWalkaddr LinkFlags2perm LinkUvmalloc LinkUvmclear LinkStrlen
        LinkCopyout LinkSafestrcpy
        ProofKexec.

Module Kexec := KexecProof Myproc BeginOp Namei Ilock Readi Iunlockput EndOp
                           ProcPagetableGen ProcFreepagetable Walkaddr
                           Flags2perm Uvmalloc Uvmclear Strlen Copyout
                           Safestrcpy.
