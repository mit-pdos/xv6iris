/-
Link `uvmcopy`: the proof instance clients import.  `uvmcopy` calls `walk`
(no-alloc), `kalloc`, `kfree`, `memmove`, `mappages` (uncounted) and
`uvmunmap`; those interfaces stay parameters here, so a client may close them
with the linked ones or with its own.
-/
import Xv6.ProofUvmcopy

namespace Xv6

/-- The proved `uvmcopy` interface, given its callees. -/
theorem Uvmcopy (W : WALK_NOALLOC) (KAL : KALLOC) (KF : KFREE) (MM : MEMMOVE)
    (MA : MAPPAGES_ANY) (UM : UVMUNMAP) : UVMCOPY :=
  uvmcopy_proof W KAL KF MM MA UM

end Xv6
