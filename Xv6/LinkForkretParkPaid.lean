/-
Link the paid park (Rocq `LinkForkretParkPaid.v`: `ForkretParkProof
Forkret`): `ProofForkretPark.forkret_park_proof` at the linked forkret.
What `LinkUserinit` (and main) apply; open in the closed loop exactly as
`LinkForkret` is.
-/
import Xv6.LinkForkret
import Xv6.ProofForkretPark

namespace Xv6

/-- The paid park at the proved forkret, given the closed trap loop. -/
theorem ForkretParkPaid (LOOP : FORKRET_LOOP) : FORKRET_PARK_PAID :=
  forkret_park_proof (Forkret LOOP)

end Xv6
