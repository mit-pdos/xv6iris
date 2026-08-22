(* LinkUserinit.v -- userinit's proof meets its four callees'.

   IT IS A FUNCTOR APPLICATION NOW, not an [Axiom].  The axiom that used to
   live here assumed userinit's whole body; what stands in its place is
   [LinkNameiRootBoot]'s, one call further down and four persistent
   inode-cache rows wide (see [SpecNameiRootBoot.v]'s header).

   [Allocproc] is the COUNTED instance ([LinkAllocproc.v] exports both):
   userinit does not test allocproc's result, so its caller's page budget
   and [ProcAvail.procs_avail (Some (S k))] are what refute the two null
   arms.  kfork, which has no budget, takes [AllocprocGen] instead.

   [NameiRootBoot] is namei at its ROOT CORNER and at the BOOT client's
   premises -- not [LinkNameiRoot.NameiRoot], which is the same corner at
   the four icache rows main cannot yet produce.  The proven corner stays in
   the build; this link is what will be re-pointed at it when it can.

   [ForkretPark] is the other assumption in the cone, and it is the one
   [LinkKfork.v] already adds: turning a fresh process's raw saved context
   into a member of the scheduler's swtch chain is a Loeb argument about
   forkret ([SpecForkretPark.v]'s header, which names userinit as the other
   place a process is parked at RUNNABLE from scratch -- this one). *)
Require Import LinkAllocproc.
Require Import LinkNameiRootBoot.
Require Import LinkRelease.
Require Import LinkForkretParkPaid.
Require Import ProofUserinit.

Module Userinit := UserinitProof Allocproc NameiRootBoot Release ForkretParkPaid.
