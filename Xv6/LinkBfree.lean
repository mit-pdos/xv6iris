/-
`bfree` meets its specification, closed with the proved `bread`,
`log_write` and `brelse` (Rocq `LinkBfree.v`).  bfree's own
`unreachable` arm is DEAD (refuted from the caller's byte run against the
free pool, `Xv6/BfreeMid.lean`), so no panic contract is instantiated
here beyond the one `bread` carries.
-/
import Xv6.ProofBfree
import Xv6.LinkBread
import Xv6.LinkLogWrite
import Xv6.LinkBrelse

namespace Xv6

theorem Bfree : BFREE := bfree_proof Bread LogWrite Brelse

end Xv6
