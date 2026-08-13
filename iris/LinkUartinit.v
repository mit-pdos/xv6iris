(* LinkUartinit.v -- instantiates the Uartinit proof against the UART device
   leaves (Uart).  Sealed, so this is the only place the two ever meet.

   ae96fd0 deleted uartinit's [initlock(&tx_lock,"uart")], so Initlock is no
   longer a callee and no longer a functor argument. *)
Require Import LinkUart ProofUartinit.

Module Uartinit := UartinitProof Uart.
