(* LinkSysDupAU.v -- sys_dup's ATOMIC-UPDATE form composed with its three
   callees' proofs.

   [LinkSysDup.v]'s cone EXACTLY: argfd, fdalloc and filedup, at the same
   three implementations, because the AU walk is the landed walk with the fd
   bundle sharpened and no callee's contract changed (SpecSysDupAU's header:
   dup touches NO fs state, so no era/AU form of any callee enters).  This
   composition therefore assumes nothing the landed sys_dup does not. *)
Require Import LinkArgfd LinkFdalloc LinkFiledup ProofSysDupAU.
Require Import TsoCtx.

Module SysDupAU := SysDupAUProof Argfd Fdalloc Filedup.
