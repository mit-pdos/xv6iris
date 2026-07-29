(* LinkUartinit.v -- instantiates the Uartinit proof against its callee's
   proof (Initlock) and the UART device leaves (Uart).  Sealed, so this is the
   only place the three ever meet. *)
Require Import LinkUart LinkInitlock ProofUartinit.

Module Uartinit := UartinitProof Uart Initlock.
