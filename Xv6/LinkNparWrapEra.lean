/-
Link `nameiparent` at its ERA contract (Rocq `LinkNparWrapEra.v`:
`Module NparWrapEra := NparWrapEraProof NparEra`).  One callee, namex at its
nameiparent-side era contract; no panic of its own; closed up to `copyout`,
as `Xv6.Namex`.
-/
import Xv6.ProofNparWrapEra
import Xv6.LinkNparEra

namespace Xv6

/-- The proved `nameiparent` era interface, given `copyout`. -/
theorem NparWrapEra (CO : COPYOUT) : NPAR_WRAP_ERA := nparWrapEra_proof (NparEra CO)

end Xv6
