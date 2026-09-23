/-
Link `walk`: the proof instances clients import.  `walk` calls `kalloc`
and `memset`; the interfaces stay parameters here, so a client may close
them with the linked ones (`LinkKalloc`, `LinkMemset`) or with its own.
-/
import Xv6.ProofWalk

namespace Xv6

/-- The proved `walk` interface (allocating), given `kalloc` and `memset`. -/
theorem Walk (KAL : KALLOC) (MS : MEMSET) : WALK := walk_proof KAL MS

/-- The proved `walk` interface with `alloc = 0`. -/
theorem WalkNoalloc : WALK_NOALLOC := walk_noalloc_proof

end Xv6
