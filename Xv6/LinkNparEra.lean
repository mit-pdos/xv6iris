/-
Link `namex` at its ERA contract, nameiparent side (Rocq `LinkNparEra.v`:
`Module NparEra := NparEraProof Myproc Idup Iget Memmove Ilock Iunlock
Iunlockput Dirlookup Iput`): the same nine callees as `Xv6.Namex`, through
the same links; closed up to `copyout`, as `Xv6.Namex`.
-/
import Xv6.ProofNparEra
import Xv6.LinkIdup
import Xv6.LinkIlock
import Xv6.LinkIunlockput
import Xv6.LinkDirlookup

namespace Xv6

/-- The proved `namex` era interface (nameiparent side), given `copyout`. -/
theorem NparEra (CO : COPYOUT) : NPAR_ERA :=
  nparEra_proof Myproc (Idup Acquire ReleaseHook) Iget Memmove Ilock Iunlock Iunlockput
    (Dirlookup CO) Iput

end Xv6
