(* LinkUartintr.v -- instantiates the Uartintr proof against its callees'
   proofs (acquire / release / wakeup) and the sealed UART device leaves.
   consoleintr is the one callee with no proof: LinkConsoleintr.v supplies its
   contract as an Axiom, and this is where that assumption enters the cone. *)
Require Import LinkAcquire LinkRelease LinkWakeup LinkConsoleintr LinkUart ProofUartintr.

Module Uartintr := UartintrProof Acquire Release Wakeup Consoleintr Uart.
