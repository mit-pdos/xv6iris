/-
`namecmp`'s interface, instantiated from its proof (Rocq `LinkNamecmp.v`).
strncmp is proved, so namecmp carries no caveat.
-/
import Xv6.ProofNamecmp
import Xv6.LinkStrncmp

namespace Xv6

theorem Namecmp : NAMECMP := namecmp_proof Strncmp

end Xv6
