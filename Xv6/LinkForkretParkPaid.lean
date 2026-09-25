/-
Link the paid park (Rocq `LinkForkretParkPaid.v`: `ForkretParkProof
Forkret`): `ProofForkretPark.forkret_park_proof` at the linked forkret.
What `LinkUserinit` (and main) apply; open in the closed loop's link
parameters exactly as `LinkForkret` is.
-/
import Xv6.LinkForkret
import Xv6.ProofForkretPark

namespace Xv6

/-- The paid park at the proved forkret. -/
theorem ForkretParkPaid (RG : RELEASE_GEN) (RR : RELEASE_REFUTE) (RC : RELEASE_CANCEL) (KFF : KFREE_FREE)
    (FC : FILECLOSE) (VF : VMFAULT) : FORKRET_PARK_PAID :=
  forkret_park_proof (Forkret RG RR RC KFF FC VF)

end Xv6
