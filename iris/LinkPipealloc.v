(* LinkPipealloc.v -- instantiates the Pipealloc proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   The [Fileclose] argument is why this file could not be written before:
   pipealloc's two error paths close the files it has just allocated. *)
Require Import LinkFilealloc LinkKalloc LinkInitlock LinkFileclose
                ProofPipealloc.

Module Pipealloc := PipeallocProof Filealloc Kalloc Initlock Fileclose.
