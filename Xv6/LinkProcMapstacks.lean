/-
`proc_mapstacks`' interface, from its proof and the interfaces of `kalloc`
and `kvmmap`.
-/
import Xv6.ProofProcMapstacks

namespace Xv6

/-- `proc_mapstacks` meets its specification, given `kalloc`'s and `kvmmap`'s. -/
theorem ProcMapstacks (KAL : KALLOC) (KM : KVMMAP) : PROC_MAPSTACKS := proc_mapstacks_proof KAL KM

end Xv6
