(* LinkNparWrapEra.v -- nameiparent's single callee at the NAMEIPARENT era
   trace contract, discharged.

   [LinkNameiparent.v]'s shape with the era walk in place of the landed one:
   nameiparent calls exactly one function, and [LinkNparEra.NparEra] is the
   nameiparent-side era walk's real proof composed with its own nine
   callees.  Nothing is assumed here and nameiparent has no panic of its own
   -- the [kernel_data] and [panic_env] it takes are threaded straight into
   namex.

   So this cone's assumption count is the walk's: the two platform axioms
   ([resv_matches], [resv_is_valid]) plus funext -- byte-identical to
   [LinkNamexEra]'s. *)
Require Import LinkNparEra.
Require Import ProofNparWrapEra.

Module NparWrap := NparWrapEraProof NparEra.
