(* LinkUartinit.v -- instantiates the Uartinit proof against its ONE callee.

   At XV6_REV 163d39b uartinit is a two-call wrapper around [uartinitone], so
   this file links exactly one thing: the UART device leaves and [initlock]
   are reached through [Uartinitone]'s own seal ([LinkUartinitone]) and never
   appear here.

   The module-type ascription below is the check that a Link file's own
   compiling does not give: Rocq accepts PARTIAL functor application, so a
   missing argument would leave [Uartinit] a FUNCTOR and go green. *)
Require Import SpecUartinit.
Require Import LinkUartinitone ProofUartinit.

Module Uartinit := UartinitProof Uartinitone.
Module ChkUartinit : UARTINIT := Uartinit.
