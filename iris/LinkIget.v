(* LinkIget.v -- instantiates the Iget proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet.

   Unlike LinkIdup.v there is no [Axiom] here to retire: iget's contract was
   never assumed, because nothing above it had been proven yet.  What this
   file adds is the closed instance, which is what moves iget from
   "interface stated, no Link instantiates it" to PROVEN in
   [tools/proof_coverage.py].

   The callees are acquire, release and panic.  The "iget: no inodes" arm is
   LIVE (SpecIget.v's header) and is discharged against [Panic] -- note it
   fires while iget HOLDS itable.lock, which is what the contract's
   [n + 3 < 2^31] and the rank table's "itable" < "pr" edge pay for. *)
Require Import LinkAcquire LinkRelease LinkPanic ProofIget.

Module Iget := IgetProof Acquire Release Panic.
