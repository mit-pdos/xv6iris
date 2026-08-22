(* LinkForkretParkPaid.v -- the park of a fresh process, PROVED and
   instantiated: [ProofForkretPark.ForkretParkProof] at the real forkret
   ([LinkForkret.Forkret]).  This is what [LinkUserinit] and [LinkKfork]
   apply their functors to; [LinkForkretPark.v]'s [Axiom] -- the unpaid
   form -- is what it replaces.  No assumption is introduced here: the cone
   is forkret's (proved, both arms) and the park's (proved, no admits). *)
Require Import LinkForkret.
Require Import ProofForkretPark.

Module ForkretParkPaid := ForkretParkProof Forkret.
