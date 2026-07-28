(* LinkConsputc.v -- instantiates the Consputc proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkUartPutc ProofConsputc.

Module Consputc := ConsputcProof UartPutc.
