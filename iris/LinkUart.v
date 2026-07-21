(* LinkUart.v -- instantiates the Uart proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecUart.
Require Import WpSconfUart.

Module Uart := UartProof.
