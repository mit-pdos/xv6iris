/-
`itrunc` meets its specification, closed with the proved `bread`, `bfree`,
`brelse` and `iupdate` (Rocq `LinkItrunc.v`, `ItruncProof Bread Bfree Brelse
Iupdate`).  itrunc has no panic arm of its own; the panic credentials it
takes are the ones its callees' `bread` carries.
-/
import Xv6.ProofItrunc
import Xv6.LinkBread
import Xv6.LinkBfree
import Xv6.LinkBrelse
import Xv6.LinkIupdate

namespace Xv6

theorem Itrunc : ITRUNC := itrunc_proof Bread Bfree Brelse Iupdate

end Xv6
