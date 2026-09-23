/-
`vmfault`'s and `uvmclear`'s interfaces, from their proofs and the
interfaces of the callees (`ismapped`, `kalloc`, `kfree`, `memset`, the
uncounted `mappages`, and `walk`).
-/
import Xv6.ProofVmfault

namespace Xv6

/-- `vmfault` meets its specification, given `ismapped`, `kalloc`, `kfree`,
`memset`, and the general `mappages` contract. -/
theorem Vmfault (IM : ISMAPPED) (KAL : KALLOC) (KF : KFREE) (MS : MEMSET)
    (MA : MAPPAGES_ANY) : VMFAULT :=
  vmfault_proof IM KAL KF MS MA

/-- `uvmclear` meets its specification, given non-allocating `walk`. -/
theorem Uvmclear (W : WALK_NOALLOC) : UVMCLEAR := uvmclear_proof W

end Xv6
