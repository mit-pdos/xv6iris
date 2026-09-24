/-
Link `walkaddr`: the proof instance clients import.  It calls `walk` with
`alloc = 0`; the interface stays a parameter here, so a client may close
it with the linked one (`LinkWalk`) or with its own.
-/
import Xv6.ProofWalkaddr

namespace Xv6

/-- The proved `walkaddr` interface, given the non-allocating `walk`. -/
theorem Walkaddr (W : WALK_NOALLOC) : WALKADDR := walkaddr_proof W

end Xv6
