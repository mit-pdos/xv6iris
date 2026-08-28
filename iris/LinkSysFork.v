(* LinkSysFork.v -- sys_fork's proof, instantiated against the REAL proof of
   its one callee.  kfork's contract has exactly one payer and this is it. *)
Require Import LinkKfork ProofSysFork.
Require Import ProofUser ProofUexecWp.

(* THE GENERIC USER-EXECUTION WP, at the real user-safety theorem.  kfork's
   contract takes the CHILD'S WP as a linear premise (parking a process
   consumes one), and sys_fork is kfork's one caller, so this is where the
   generic inhabitant is minted for every forked process -- the second of the
   tree's two mint sites, [LinkUserinit]'s being the first.  [UexecGen] is a
   repackaging of [ProofUser.UserProof.wp_user_exec_closed] and nothing more,
   so this application adds no assumption. *)
Module UG := UexecGen UserProof.

Module SysFork := SysForkProof Kfork UG.
