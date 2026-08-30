(* LinkSysMknodAUStable.v -- the mknod stable corollary at the REAL AU
   proof, so the form is an unconditional theorem rather than a functor.

   [LinkSysMknodAU]'s [SysMknodAU] is [SYSMKNOD_AU_ERA] sealed against
   seven real callee proofs; this file feeds it to the derivation.  It
   assumes NOTHING NEW -- the derivation opens no invariant and steps no
   instruction, so [Print Assumptions SysMknodAUStable.wp_sys_mknod_au_era_stable]
   is [LinkSysMknodAU]'s own set. *)
Require Import LinkSysMknodAU ProofSysMknodAUEraStable.

Module SysMknodAUStable := SysMknodAUEraStable SysMknodAU.
