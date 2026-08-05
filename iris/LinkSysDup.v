(* LinkSysDup.v -- the one place sys_dup's proof meets its three callees'.

   All three are implemented, so sys_dup is proven AND linked: argfd through
   argint/argraw/myproc, fdalloc through myproc, filedup through
   acquire/release. *)
Require Import LinkArgfd LinkFdalloc LinkFiledup ProofSysDup.

Module SysDup := SysDupProof Argfd Fdalloc Filedup.
