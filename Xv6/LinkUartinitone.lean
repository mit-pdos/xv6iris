/-
`uartinitone`'s interface, instantiated from its proof.
-/
import Xv6.ProofUartinitone

namespace Xv6

theorem Uartinitone (IL : INITLOCK) : UARTINITONE := uartinitone_proof IL

end Xv6
