(* LinkFreeDesc.v -- instantiates free_desc's proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecFreeDesc SpecWakeup.
Require Import LinkWakeup ProofFreeDesc.

Module FreeDesc := FreeDescProof Wakeup.
