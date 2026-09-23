/-
Link `allocproc`: the proof instance clients import.  `allocproc` calls
`acquire`, `release`, `kalloc`, `memset`, `proc_pagetable` and `freeproc`
(and takes `pid_lock` as an `isLock` in its contract); the interfaces stay
parameters here, so a client may close them with the linked ones or with
its own.
-/
import Xv6.ProofAllocproc

namespace Xv6

/-- The proved `allocproc` interface, given `acquire`, `release`, `kalloc`,
`memset`, `proc_pagetable` and `freeproc`. -/
theorem Allocproc (AC : ACQUIRE) (RE : RELEASE) (KAL : KALLOC) (MS : MEMSET)
    (PP : PROC_PAGETABLE) (FP : FREEPROC) : ALLOCPROC :=
  allocproc_proof AC RE KAL MS PP FP

end Xv6
