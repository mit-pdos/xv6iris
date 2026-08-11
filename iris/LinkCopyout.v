(* LinkCopyout.v -- instantiates the Copyout proof against its callees' proofs
   (walkaddr, vmfault, the no-alloc walk, memmove).  Sealed, so this is the
   only place the five ever meet. *)
Require Import LinkWalkaddr LinkVmfault LinkWalkNoalloc LinkMemmove.
Require Import ProofCopyout.

(* the process contract, unchanged: what either_copyout, piperead, kwait,
   readi and sys_pipe already speak *)
Module Copyout := CopyoutProof Walkaddr Vmfault WalkNoalloc Memmove.

(* the general one, whose license is indexed by an [arm]: the process's
   [p->sz] / [p->pagetable] cells at [true], "the destination range is
   already mapped as valid user leaves" at [false].  The [false] arm is what
   a caller copying into a table it has built but not yet installed (kexec)
   needs, since it has no such cells to offer; [Copyout] above is the [true]
   arm and is derived from this module. *)
Module CopyoutGen := CopyoutCore Walkaddr Vmfault WalkNoalloc Memmove.
