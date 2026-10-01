/-
Link `igetroot`: the proof instance clients import (Rocq `LinkIgetroot.v`:
`Module Igetroot := IgetrootProof Iget`).  Its one callee is the linked
`iget`.
-/
import Xv6.ProofIgetroot
import Xv6.LinkIget

namespace Xv6

/-- The proved `igetroot` interface. -/
theorem Igetroot : IGETROOT := igetroot_proof Iget

end Xv6
