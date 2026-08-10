(* LinkIget.v -- instantiates the Iget proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet.

   Unlike LinkIdup.v there is no [Axiom] here to retire: iget's contract was
   never assumed, because nothing above it had been proven yet.  What this
   file adds is the closed instance, which is what moves iget from
   "interface stated, no Link instantiates it" to PROVEN in
   [tools/proof_coverage.py].

   The two callees are acquire and release.  panic is NOT a module here: the
   "iget: no inodes" arm is LIVE (SpecIget.v's header), and it diverges
   through the [panic_wp_any] resource the contract already takes, so no
   further instantiation is needed for it. *)
Require Import LinkAcquire LinkRelease ProofIget.

Module Iget := IgetProof Acquire Release.
