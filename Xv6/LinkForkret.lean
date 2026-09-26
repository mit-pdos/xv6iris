/-
Link `forkret` (Rocq `LinkForkret.v`: `ForkretProof Myproc Release
PrepareReturn Fsinit Kexec Panic UserretClosedD`): its six callees are the
proved interfaces and the CLOSED trap loop is `LinkUserretClosed`'s.  Nothing
stays a parameter.
-/
import Xv6.ProofForkret
import Xv6.LinkFsinit
import Xv6.LinkUserretClosed

namespace Xv6

/-- The proved `forkret` interface, CLOSED. -/
theorem Forkret : FORKRET :=
  forkret_proof Myproc Release PrepareReturn Fsinit Kexec Panic UserretClosed

end Xv6
