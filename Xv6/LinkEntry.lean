/-
Link `_entry`: the sealed proof instance clients import.  `_entry` has no
callees in interface shape, so this only names the instance uniformly.
-/
import Xv6.ProofEntry

namespace Xv6

/-- The proved `_entry` interface. -/
theorem Entry : ENTRY := EntryProof

end Xv6
