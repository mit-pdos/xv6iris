/-
`uvmclear`'s interface, from its proof and the interface of the
non-allocating `walk`.
-/
import Xv6.ProofUvmclear

namespace Xv6

/-- `uvmclear` meets its specification, given non-allocating `walk`. -/
theorem Uvmclear (W : WALK_NOALLOC) : UVMCLEAR := uvmclear_proof W

end Xv6
