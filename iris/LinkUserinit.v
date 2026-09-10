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
Require Import ProofUser ProofUexecWp.
Require Import ProofUserinit.

(* THE GENERIC USER-EXECUTION WP, at the real user-safety theorem.  The
   KERNEL does not use it: userinit parks the first process with the exec
   bundle the system theorem hands down, and kfork's child gets a copy of
   the parent's slot.  Its one reader is the GENERIC APPLICATION's discharge
   of that hypothesis ([SystemAdequacy.init_boot_of_sup], through
   [UexecExecMint.uslot_mint]), which is why the module is built here, above
   the whole user-safety cone and below adequacy.  [UexecGen] is a
   repackaging of [ProofUser.UserProof.wp_user_exec_closed] and nothing
   more, so this application adds no assumption. *)
Module UG := UexecGen UserProof.

Module Userinit := UserinitProof Allocproc NameiRootBoot Release ForkretParkPaid.
