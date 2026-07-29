(* LinkCopyinstr.v -- instantiates the Copyinstr proof against its callee's
   proof.  walkaddr is copyinstr's ONLY callee (it never faults a page in, so
   there is no vmfault and no memmove here), which makes this the smallest
   link in the copy family.  Sealed, so this is the only place the two meet. *)
Require Import LinkWalkaddr.
Require Import ProofCopyinstr.

Module Copyinstr := CopyinstrProof Walkaddr.
