/-
Link `flags2perm`: the sealed proof instance clients import.  No callees.
-/
import Xv6.ProofFlags2perm

namespace Xv6

/-- The proved `flags2perm` interface. -/
theorem Flags2perm : FLAGS2PERM := flags2perm_proof

end Xv6
