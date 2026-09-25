/-
Link `forkret` (Rocq `LinkForkret.v`: `ForkretProof Myproc Release
PrepareReturn Fsinit Kexec Panic UserretClosedD`): its six callees are the
proved interfaces and the CLOSED trap loop is `LinkUserretClosed`'s.  Left
as parameters, exactly as `LinkUserretClosed.UserretClosed` leaves them:
`LinkSyscall`'s four lock / allocator leaves, `fileclose` and `vmfault`.
-/
import Xv6.ProofForkret
import Xv6.LinkMyproc
import Xv6.LinkRelease
import Xv6.LinkPrepareReturn
import Xv6.LinkFsinit
import Xv6.LinkKexec
import Xv6.LinkPanic
import Xv6.LinkUserretClosed

namespace Xv6

/-- The proved `forkret` interface, given the closed loop's link parameters. -/
theorem Forkret (RG : RELEASE_GEN) (RR : RELEASE_REFUTE) (RC : RELEASE_CANCEL) (KFF : KFREE_FREE)
    (FC : FILECLOSE) (VF : VMFAULT) : FORKRET :=
  forkret_proof Myproc Release PrepareReturn Fsinit Kexec Panic (UserretClosed RG RR RC KFF FC VF)

end Xv6
