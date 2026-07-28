(* LinkConsoleinit.v -- instantiates the Consoleinit proof against its callees'
   proofs (Initlock and Uartinit).  Sealed, so this is the only place the three
   ever meet. *)
Require Import LinkInitlock LinkUartinit ProofConsoleinit.

Module Consoleinit := ConsoleinitProof Initlock Uartinit.
