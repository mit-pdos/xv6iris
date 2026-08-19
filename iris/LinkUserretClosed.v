(* LinkUserretClosed.v -- instantiate the CLOSED userret contract with the
   real proofs: the userret trampoline ([LinkUserret]), the closed
   user-execution WP ([ProofUser]) and uservec ([LinkUservec], itself
   applied to the real usertrap and userret).  Type-checking this file is
   what makes the trap loop a theorem about the actual kernel rather than a
   composition of interfaces.

   USER-RULED TEMPORARY AXIOM (2026-08-19): the closed user-execution WP is
   taken from [UserExecAxiom], NOT from [ProofUser] -- see that file's header
   for the ruling, the in-flight discharge and the revival procedure. *)
Require Import LinkUserret UserExecAxiom LinkUservec LinkUsertrap.
Require Import ProofUserretClosed.

(* uservec, at the real usertrap and userret (Coq will not take a functor
   application in argument position, so it is named first) *)
Module UservecI := Uservec Usertrap Userret.

Module UserretClosedD :=
  UserretClosedProof Userret UserProof_USER_RULED_TEMPORARY_AXIOM UservecI.
