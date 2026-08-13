(* LinkUartinit.v -- instantiates the Uartinit proof against the UART device
   leaves (Uart).  Sealed, so this is the only place the two ever meet.

   b7c25cf restored the transmit lock's initializer -- as an
   [initsleeplock(&tx_lock,"uart")] now that ae96fd0 made it a sleeplock -- so
   Initsleeplock is a callee again, and a functor argument. *)
Require Import LinkUart LinkInitsleeplock ProofUartinit.

Module Uartinit := UartinitProof Uart Initsleeplock.
