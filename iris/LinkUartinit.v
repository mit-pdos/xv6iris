(* LinkUartinit.v -- instantiates the Uartinit proof against its callees: the
   UART device leaves (Uart) and initsleeplock.  Sealed, so this is the only
   place the three ever meet.

   THE SECOND ARGUMENT CAME BACK.  `ae96fd0` deleted uartinit's
   `initlock(&tx_lock,"uart")` and left the transmit sleeplock uninitialized
   (kernel-defects.md D2, which we reported); `b7c25cf` fixes it with
   `initsleeplock(&tx_lock, "uart")`, so uartinit has a callee again.

   BEWARE: FORGETTING THE ARGUMENT HERE COMPILES.  Rocq accepts PARTIAL
   functor application, so `UartinitProof Uart` against the two-argument
   functor silently defines [Uartinit] as a FUNCTOR rather than a module --
   this file goes green and the mistake surfaces only downstream, where
   `ConsoleinitProof Initlock Uartinit` rejects it.  A Link file compiling is
   not on its own evidence that it links the right things. *)
Require Import LinkUart LinkInitsleeplock ProofUartinit.

Module Uartinit := UartinitProof Uart Initsleeplock.
