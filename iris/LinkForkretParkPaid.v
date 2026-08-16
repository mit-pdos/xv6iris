(* LinkForkretParkPaid.v -- the PROVED park, instantiated: fresh-process
   parking against forkret's real contract (minus the [first] premise,
   which is [LinkForkretNF.v]'s Axiom and the only assumption in this cone).

   Type-checking this file is what makes [ProofForkretPark.v] a statement
   about the actual kernel: the WP its record's resume wand discharges is
   forkret's, at the closed trap loop's residue, and the record it builds is
   the one [SchedCtx.procs_inv] stores.

   THIS IS NOT YET WHAT [LinkForkretPark.v] PROVIDES.  kfork uses the
   ASSUMED [FORKRET_PARK], whose contract does not carry
   [SpecForkretPark.forkret_park_pkg] -- the child's free kernel stack and
   the closer that builds the trap loop's kernel-side bundle for it.  Those
   are resources kfork's own environment does not have, so the two cannot be
   joined by a functor application; joining them is a change to kfork's
   contract (and, behind it, to sys_fork's and to the syscall environment's),
   which is where the remaining work is.  Until then the tree carries both:
   this theorem, and the Axiom it is aimed at. *)
Require Import LinkForkretNF.
Require Import ProofForkretPark.

Module ForkretParkPaid := ForkretParkProof ForkretNF.
