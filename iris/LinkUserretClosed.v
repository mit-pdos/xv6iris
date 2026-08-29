(* LinkUserretClosed.v -- instantiate the CLOSED userret contract with the
   real proofs: the userret trampoline ([LinkUserret]), the closed
   user-execution WP ([ProofUser]) and uservec ([LinkUservec], itself
   applied to the real usertrap and userret).  Type-checking this file is
   what makes the trap loop a theorem about the actual kernel rather than a
   composition of interfaces. *)
Require Import LinkUserret LinkUservec LinkUsertrap.
Require Import ProofUser ProofUexecWp.
Require Import ProofUserretClosed.

(* uservec, at the real usertrap and userret (Coq will not take a functor
   application in argument position, so it is named first) *)
Module UservecI := Uservec Usertrap Userret.

(* THE [UEXEC_GEN] ARGUMENT IS BACK (milestone J, refutation R-c), and only
   for this functor.  MILESTONE G's "neither run site names USER" held while
   the loop merely CIRCULATED a forall-state WP.  With the keyed contract two
   of the round's arms are kernel mints by design -- exec-success, where
   [UexecRound.uround_ok]'s left disjunct says nothing at all because the new
   program's slot is built by exec, and fork, where nothing yet states
   [r <> 0] (K2) -- so the loop needs a generic inhabitant to fall back on.
   It reaches it through [UexecCond.cond_entry_slot], so a process whose key
   qualifies picks up sync's own constructor instead.
   [UexecGen] is a repackaging of [ProofUser.UserProof.wp_user_exec_closed]
   and nothing more, so this application adds no assumption -- and
   [LinkUserinit] / [LinkSysFork] already carry the same one. *)
Module UGrc := UexecGen UserProof.

Module UserretClosedD :=
  UserretClosedProof Userret UservecI UGrc.
