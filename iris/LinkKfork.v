(* LinkKfork.v -- instantiates kfork's proof against its ten callees' proofs.
   Sealed, so this is the only place the eleven ever meet.

   ALLOCPROC IS THE *GEN* INSTANCE, not the counted one: kfork calls
   allocproc with no page budget, so both of allocproc's own freeproc
   failure tails are LIVE code here and its post has three arms.  That is
   what `LinkAllocproc.v` exports `AllocprocGen` for.

   RELEASE APPEARS TWICE, once for `FREEPROC`'s sibling in kfork's
   uvmcopy-failure tail and once for the three releases in the RUNNABLE
   park; both are the same `Release`.

   THE ONE ASSUMPTION THIS ADDS is `ForkretPark` -- turning a fresh
   process's raw saved context into a member of the scheduler's swtch
   chain, which is a Loeb argument about `forkret` that nothing in the tree
   proves yet.  `SpecForkretPark.v`'s header argues at length why isolating
   exactly that step is honest and why kfork cannot dodge it the way
   `userinit` does (userinit is assumed WHOLESALE; kfork's body is ordinary
   provable code).  Proving forkret / usertrapret / userret
   (claude-notes/projects/uservec.md) retires that file and changes nothing
   here.  The other assumption in the cone, `Iput`, arrives through
   `Filedup`/`Idup`'s own transitive callees, not from this file. *)
Require Import LinkMyproc LinkAllocproc LinkUvmcopy LinkFreeproc.
Require Import LinkRelease LinkAcquire LinkFiledup LinkIdup.
Require Import LinkSafestrcpy.
Require Import ProofKforkMain.

(* The functor is [KforkProof], not [Kfork]: tools/proof_coverage.py matches
   the instantiation with `Module (\w+) := (\w+) ...`, and a QUALIFIED name on
   the right (`ProofKforkMain.Kfork`) does not match it -- the function would
   silently read `assumed` despite being proven and linked.  Every other Link
   file in the tree uses the same bare `<F>Proof` convention. *)
Module Kfork := KforkProof
  Myproc AllocprocGen Uvmcopy Freeproc Release Acquire
  Filedup Idup Safestrcpy.
