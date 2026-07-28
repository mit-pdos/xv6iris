(* LinkUserret.v -- the sealed userret proof instance.  ProofUserret takes
   no functor arguments (userret has no callees -- it is leaf assembly),
   so the sealed module already is the instance; this link only gives it
   the canonical name consumers require. *)
Require Import ProofUserret.

Module Userret := UserretProof.
