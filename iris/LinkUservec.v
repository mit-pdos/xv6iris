(* LinkUservec.v -- instantiate the uservec interface with its proof.

   [UservecProof] (ProofUservec.v) is sealed by [SpecUservec.USERVEC], so
   this one-line functor application is what makes uservec count as a
   PROVEN whole-function contract: every consumer of [USERVEC] can be fed
   [Uservec] and needs nothing from the proof file itself. *)
Require Import ProofUservec.

Module Uservec := UservecProof.
