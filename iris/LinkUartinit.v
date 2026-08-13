(* LinkUartinit.v -- instantiates the Uartinit proof against its callees: the
   UART device leaves (Uart) and initlock.  Sealed, so this is the only place
   the three ever meet.

   BEWARE: FORGETTING THE SECOND ARGUMENT HERE COMPILES.  Rocq accepts PARTIAL
   functor application, so `UartinitProof Uart` against the two-argument
   functor silently defines [Uartinit] as a FUNCTOR rather than a module --
   this file goes green and the mistake surfaces only downstream, where
   `ConsoleinitProof Initlock Uartinit` rejects it.  A Link file compiling is
   not on its own evidence that it links the right things; the check that
   works is a module-type ascription (`Module Chk : UARTINIT := Uartinit.`),
   which a functor cannot satisfy. *)
Require Import LinkUart LinkInitlock ProofUartinit.

Module Uartinit := UartinitProof Uart Initlock.
