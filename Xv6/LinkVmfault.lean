/-
`vmfault`'s interface, from its proof and the interfaces of the callees
(`ismapped`, `kalloc`, `kfree`, `memset` and the uncounted `mappages`).
-/
import Xv6.ProofVmfault

namespace Xv6

/-- `vmfault` meets its specification, given `ismapped`, `kalloc`, `kfree`,
`memset`, and the general `mappages` contract. -/
theorem Vmfault (IM : ISMAPPED) (KAL : KALLOC) (KF : KFREE) (MS : MEMSET)
    (MA : MAPPAGES_ANY) : VMFAULT :=
  vmfault_proof IM KAL KF MS MA

end Xv6
