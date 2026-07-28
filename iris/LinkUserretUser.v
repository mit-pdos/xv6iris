(* LinkUserretUser.v -- instantiates the userret -> user-execution dovetail
   (UserretUser.v) against the real sealed proofs: the userret trampoline
   proof (LinkUserret) and the closed user-execution WP (ProofUser).  This
   is the machine-checked statement that userret's postcondition feeds
   [user_inv] and SpecUser's WP with nothing missing. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecUserret SpecUser.
Require Import LinkUserret ProofUser UserretUser.

Module UserretUserD := UserretUser Userret UserProof.
