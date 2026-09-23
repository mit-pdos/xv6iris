/-
Link `uvmcreate`: the proof instance clients import.  `uvmcreate` calls
`kalloc` and `memset`; the interfaces stay parameters here, so a client may
close them with the linked ones (`LinkKalloc`, `LinkMemset`) or with its own.
-/
import Xv6.ProofUvmcreate

namespace Xv6

/-- The proved `uvmcreate` interface, given `kalloc` and `memset`. -/
theorem Uvmcreate (KAL : KALLOC) (MS : MEMSET) : UVMCREATE := uvmcreate_proof KAL MS

end Xv6
