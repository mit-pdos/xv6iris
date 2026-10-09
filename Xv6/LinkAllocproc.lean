/-
Link `allocproc`: the proof instance clients import.  `allocproc` calls
`myproc` (NI M4 pids: the inlined allocpid's partition reads the caller's
slot), `acquire`, `release`, `kalloc`, `memset`, `proc_pagetable` and `freeproc`
(and takes `pid_lock` as an `isLock` in its contract); the interfaces stay
parameters here, so a client may close them with the linked ones or with
its own.
-/
import Xv6.ProofAllocproc

namespace Xv6

/-- The proved `allocproc` interface, given `myproc`, `acquire`, `release`,
`kalloc`, `memset`, `proc_pagetable` and `freeproc`. -/
theorem Allocproc (MP : MYPROC) (AC : ACQUIRE) (RE : RELEASE) (KAL : KALLOC) (MS : MEMSET)
    (PP : PROC_PAGETABLE) (FP : FREEPROC) : ALLOCPROC :=
  allocproc_proof MP AC RE KAL MS PP FP

end Xv6
