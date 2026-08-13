(* LinkUartintr.v -- instantiates the Uartintr proof against its callees'
   proofs (wakeup) and the sealed UART device leaves.  consoleintr is the one
   callee with no proof: LinkConsoleintr.v supplies its contract as an Axiom,
   and this is where that assumption enters the cone.

   ae96fd0's uartintr takes NO LOCK, so acquire and release are no longer
   callees and no longer functor arguments. *)
Require Import LinkWakeup LinkConsoleintr LinkUart ProofUartintr.

Module Uartintr := UartintrProof Wakeup Consoleintr Uart.
