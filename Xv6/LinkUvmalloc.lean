/-
`uvmalloc`'s and `uvmdealloc`'s interfaces, from their proofs and the
interfaces of `uvmunmap`, `kalloc`, `kfree`, `memset` and `mappages` (the
uncounted contract).
-/
import Xv6.ProofUvmalloc

namespace Xv6

open Xv6.UPtAlloc

/-- `uvmdealloc` meets its freeing contract, given `uvmunmap`'s. -/
theorem Uvmdealloc (UM : UVMUNMAP) : UVMDEALLOC := uvmdealloc_proof UM

/-- `uvmalloc` meets its contract, given `kalloc`, `kfree`, `memset`,
`mappages` (uncounted) and `uvmunmap` (for the rollback via `uvmdealloc`). -/
theorem Uvmalloc (KAL : KALLOC) (KF : KFREE) (MS : MEMSET) (MA : MAPPAGES_ANY)
    (UM : UVMUNMAP) : UVMALLOC :=
  uvmalloc_proof KAL KF MS MA (uvmdealloc_proof UM)

end Xv6
