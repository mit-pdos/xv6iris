/-
Link `kvmmake`: the proof instance clients import.  `kvmmake` calls
`kalloc`, `memset`, `kvmmap` and `proc_mapstacks`; the interfaces stay
parameters here, so a client may close them with the linked ones
(`LinkKalloc`, `LinkMemset`, `LinkKvmmap`, ...) or with its own.
-/
import Xv6.ProofKvmmake

namespace Xv6

/-- The proved `kvmmake` interface, given `kalloc`, `memset`, `kvmmap` and
`proc_mapstacks`. -/
theorem Kvmmake (KAL : KALLOC) (MS : MEMSET) (KM : KVMMAP) (PM : PROC_MAPSTACKS) : KVMMAKE :=
  kvmmake_proof KAL MS KM PM

end Xv6
