/-
Link `namei` at its ERA contract (Rocq `LinkNameiEra.v`: `Module NameiEra :=
NameiEraProof NamexEra`).  One callee, namex at its era contract; no panic of
its own; closed up to `copyout`, as `Xv6.Namex`.
-/
import Xv6.ProofNameiEra
import Xv6.LinkNamexEra

namespace Xv6

/-- The proved `namei` era interface, given `copyout`. -/
theorem NameiEra (CO : COPYOUT) : NAMEI_ERA := nameiEra_proof (NamexEra CO)

end Xv6
