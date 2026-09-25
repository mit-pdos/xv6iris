/-
Link `nameiparent` (Rocq `LinkNameiparent.v`: `Module Nameiparent :=
NameiparentProof Namex`).  One callee, namex; no panic of its own; closed up
to `copyout`, as `Xv6.Namex`.
-/
import Xv6.ProofNameiparent
import Xv6.LinkNamex

namespace Xv6

/-- The proved `nameiparent` interface, given `copyout` (as `Xv6.Namex`). -/
theorem Nameiparent (CO : COPYOUT) : NAMEIPARENT := nameiparent_proof (Namex CO)

end Xv6
