/-
Link `forkret` (Rocq `LinkForkret.v`: `ForkretProof Myproc Release
PrepareReturn Fsinit Kexec Panic UserretClosedD`): its six callees are the
proved interfaces; the CLOSED trap loop (`FORKRET_LOOP`, Rocq's
`UserretClosedD`) is W8-L's and stays a PARAMETER until its link lands
(ForkretLoop deviation 1).
-/
import Xv6.ProofForkret
import Xv6.LinkMyproc
import Xv6.LinkRelease
import Xv6.LinkPrepareReturn
import Xv6.LinkFsinit
import Xv6.LinkKexec
import Xv6.LinkPanic

namespace Xv6

/-- The proved `forkret` interface, given the closed trap loop. -/
theorem Forkret (LOOP : FORKRET_LOOP) : FORKRET :=
  forkret_proof Myproc Release PrepareReturn Fsinit Kexec Panic LOOP

end Xv6
