(* LinkSysPipe.v -- instantiates the SysPipe proof against its callees'
   proofs.  Sealed, so this is the only place the six ever meet.

   Both [Pipealloc] and [Fileclose] had to wait on fileclose's proof --
   pipealloc closes untyped files on its error paths, sys_pipe closes pipe
   files on three of its four exits. *)
Require Import LinkMyproc LinkArgaddr LinkPipealloc LinkFdalloc LinkFileclose
                LinkCopyout ProofSysPipe.

Module SysPipe := SysPipeProof Myproc Argaddr Pipealloc Fdalloc Fileclose Copyout.
