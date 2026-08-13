(* LinkCopyout.v -- instantiates the Copyout proof against its callees' proofs
   (walkaddr, vmfault, the no-alloc walk, memmove).  Sealed, so this is the
   only place the five ever meet. *)
Require Import LinkWalkaddr LinkVmfault LinkWalkNoalloc LinkMemmove.
Require Import ProofCopyout.

(* THE contract -- there is only one now.  There used to be a second module
   [CopyoutGen] over [COPYOUT_GEN], whose license was indexed by an [arm]:
   the process's [p->sz] / [p->pagetable] cells at [true], "the destination
   range is already mapped as valid user leaves" at [false], the [false] arm
   being what kexec needed since it copies into a table it has built but not
   yet installed.  xv6 `4f2fc8b` made vmfault take the size as an argument and
   map into the table it was handed, so copyout touches no proc cell on any
   path and there is nothing left for [arm] to select between; the whole
   apparatus is deleted (SpecCopyout.v).  kexec passes [psz]. *)
Module Copyout := CopyoutProof Walkaddr Vmfault WalkNoalloc Memmove.
