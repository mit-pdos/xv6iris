(* LinkUartinit.v -- instantiates the Uartinit proof against its callee's
   proof (Initlock) and the UART device leaves (Uart).  Sealed, so this is the
   only place the three ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecUartinit SpecUart SpecInitlock.
Require Import LinkUart LinkInitlock WpSconfUartinit.

Module Uartinit := UartinitProof Uart Initlock.
