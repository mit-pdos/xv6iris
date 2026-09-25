/-
Link `safestrcpy` at the source-ownership contract (`SpecSafestrcpySrc`):
the sealed proof instance kexec's composition imports.  `safestrcpy` calls
nothing, so the interface closes with no callee premises.
-/
import Xv6.ProofSafestrcpySrc

namespace Xv6

/-- The proved `safestrcpy` interface with Rocq's `ssc_src_ok` disjunct. -/
theorem SafestrcpySrc : SAFESTRCPY_SRC := safestrcpySrc_proof

end Xv6
