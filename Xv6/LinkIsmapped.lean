/-
Link `ismapped`: the proof instance clients import.  It calls `walk` with
`alloc = 0`; the interface stays a parameter here, so a client may close
it with the linked one (`LinkWalk`) or with its own.
-/
import Xv6.ProofIsmapped

namespace Xv6

/-- The proved `ismapped` interface, given the non-allocating `walk`. -/
theorem Ismapped (W : WALK_NOALLOC) : ISMAPPED := ismapped_proof W

end Xv6
