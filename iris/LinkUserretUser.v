(* LinkUserretUser.v -- instantiates the userret -> user-execution dovetail
   (UserretUser.v) against the real sealed proofs: the userret trampoline
   proof (LinkUserret) and the closed user-execution WP (ProofUser).  This
   is the machine-checked statement that userret's postcondition feeds
   [user_inv] and SpecUser's WP with nothing missing.

   USER-RULED TEMPORARY AXIOM (2026-08-19): the closed user-execution WP is
   taken from [UserExecAxiom], NOT from [ProofUser] -- see that file's header
   for the ruling, the in-flight discharge and the revival procedure. *)
Require Import LinkUserret UserExecAxiom UserretUser.

Module UserretUserD := UserretUser Userret UserProof_USER_RULED_TEMPORARY_AXIOM.
