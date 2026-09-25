/-
`iunlockput` meets its specification (Rocq `LinkIunlockput.v`), closed with
the proved `iunlock` and `iput`.  No axiom.
-/
import Xv6.ProofIunlockput
import Xv6.LinkIunlock
import Xv6.LinkIput

namespace Xv6

/-- The proved `iunlockput` interface. -/
theorem Iunlockput : IUNLOCKPUT :=
  iunlockput_proof Iunlock Iput

end Xv6
