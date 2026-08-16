(* LinkDirlookup.v -- the only file where dirlookup's proof meets its
   callees'.  All three are real proofs and none of them is assumed:

   - readi arrives through LinkReadi.v, whose bmap instance is the
     no-allocation one, so balloc's Axiom does NOT reach this cone;
   - namecmp arrives through LinkNamecmp.v, i.e. strncmp;
   - iget arrives through LinkIget.v (acquire / release).

   panic is NOT a module here.  Both of dirlookup's panics are DEAD --
   panic("dirlookup not DIR") is refuted from the contract's
   [di_type dn = T_DIR] premise and panic("dirlookup read") from the
   GRANULARITY premise via [ProofDirlookupParts.dlk_rd_clamp_full] -- so the
   [panic_wp_any] resource the contract takes is threaded to readi and iget
   and never consumed locally.

   So this cone's assumption count stays at the five platform axioms plus
   funext. *)
Require Import LinkReadi LinkNamecmp LinkIget LinkPanic ProofDirlookup.

Module Dirlookup := DirlookupProof Readi Namecmp Iget Panic.
