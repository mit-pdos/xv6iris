(* LinkDevintr.v -- instantiates the Devintr proof against its five callees'
   proofs.  All five are real proofs; devintr's only assumed content is what
   uartintr already carries (consoleintr, via LinkConsoleintr.v). *)
Require Import SpecDevintr SpecPlicClaim SpecPlicComplete SpecUartintr
        SpecVirtioDiskIntr SpecClockintr.
Require Import LinkPlicClaim LinkPlicComplete LinkUartintr LinkVirtioDiskIntr
        LinkClockintr ProofDevintr.

Module Devintr := DevintrProof PlicClaim PlicComplete Uartintr VirtioDiskIntr Clockintr.
