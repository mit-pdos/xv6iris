/-
`uvmdealloc`'s interface, from its proof and the interface of `uvmunmap`.
-/
import Xv6.ProofUvmdealloc

namespace Xv6

/-- `uvmdealloc` meets its freeing contract, given `uvmunmap`'s. -/
theorem Uvmdealloc (UM : UVMUNMAP) : UVMDEALLOC := uvmdealloc_proof UM

end Xv6
