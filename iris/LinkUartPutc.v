(* LinkUartPutc.v -- instantiates the UartPutc proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkUart WpSconfUartPutc.

Module UartPutc := UartPutcProof Uart.
