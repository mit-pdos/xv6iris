(* LinkMemsetPage.v -- instantiates the MemsetPage proof against its callee's
   proof (the general array-memset spec).  Sealed, so this is the only place
   the two ever meet. *)
Require Import LinkMemsetArray WpSconfMemsetPage.

Module MemsetPage := MemsetPageProof MemsetArray.
