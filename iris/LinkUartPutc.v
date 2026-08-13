(* LinkUartPutc.v -- instantiates the UartPutc proof against its callees'
   proofs.  Sealed, so this is the only place they ever meet. *)
Require Import LinkUart LinkAcquire LinkRelease ProofUartPutc.

Module UartPutc := UartPutcProof Uart Acquire Release.
