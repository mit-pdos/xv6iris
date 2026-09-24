/-
`uvmalloc`'s interface, from its proof and the interfaces of `uvmunmap`,
`kalloc`, `kfree`, `memset` and `mappages` (the uncounted contract); the
rollback goes through `uvmdealloc`'s proof.
-/
import Xv6.ProofUvmalloc
import Xv6.ProofUvmdealloc

namespace Xv6

open Xv6.UPtAlloc

/-- `uvmalloc` meets its contract, given `kalloc`, `kfree`, `memset`,
`mappages` (uncounted) and `uvmunmap` (for the rollback via `uvmdealloc`). -/
theorem Uvmalloc (KAL : KALLOC) (KF : KFREE) (MS : MEMSET) (MA : MAPPAGES_ANY)
    (UM : UVMUNMAP) : UVMALLOC :=
  uvmalloc_proof KAL KF MS MA (uvmdealloc_proof UM)

end Xv6
