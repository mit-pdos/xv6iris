/-
Link the paid park (Rocq `LinkForkretParkPaid.v`: `ForkretParkProof
Forkret`): `ProofForkretPark.forkret_park_proof` at the linked forkret.
What `LinkUserinit` (and main) apply; CLOSED, as `LinkForkret` is.
-/
import Xv6.LinkForkret
import Xv6.ProofForkretPark

namespace Xv6

/-- The paid park at the proved forkret. -/
theorem ForkretParkPaid : FORKRET_PARK_PAID :=
  forkret_park_proof Forkret

end Xv6
