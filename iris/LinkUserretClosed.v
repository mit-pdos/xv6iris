(* LinkUserretClosed.v -- instantiate the CLOSED userret contract with the
   real proofs: the userret trampoline ([LinkUserret]), the closed
   user-execution WP ([ProofUser]) and uservec ([LinkUservec], itself
   applied to the real usertrap and userret).  Type-checking this file is
   what makes the trap loop a theorem about the actual kernel rather than a
   composition of interfaces. *)
Require Import LinkUserret LinkUservec LinkUsertrap.
Require Import ProofUserretClosed.

(* uservec, at the real usertrap and userret (Coq will not take a functor
   application in argument position, so it is named first) *)
Module UservecI := Uservec Usertrap Userret.

(* NO [USER] ARGUMENT.  Since MILESTONE G the trap loop mints no WP -- it
   runs the one it pulls out of the residue and re-deposits the one user
   execution returns -- so generic safety ([ProofUser.UserProof]) no longer
   enters the composition here.  It enters at INITIALIZATION instead:
   [LinkUserinit] passes [UexecGen UserProof] to [ProofUserinit], which is
   what puts a WP in a never-run process's residue at forkret's park. *)
Module UserretClosedD :=
  UserretClosedProof Userret UservecI.
