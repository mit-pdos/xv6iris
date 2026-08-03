(* LinkUartwrite.v -- instantiates the Uartwrite proof against its callees'
   proofs (acquire / release / sleep) and the sealed UART device leaves.
   Sealed, so this is the only place they ever meet. *)
Require Import LinkAcquire LinkRelease LinkSleep LinkUart ProofUartwrite.

Module Uartwrite := UartwriteProof Acquire Release Sleep Uart.
