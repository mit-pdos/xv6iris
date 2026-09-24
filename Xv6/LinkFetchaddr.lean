/-
Link `fetchaddr`: the proof instance clients import.  It calls `myproc`
and `copyin`; those interfaces stay parameters here, so a client may close
them with the linked ones (`LinkMyproc`, `LinkCopyin`) or with its own.
-/
import Xv6.ProofFetchaddr

namespace Xv6

/-- The proved `fetchaddr` interface, given `myproc` and `copyin`. -/
theorem Fetchaddr (MP : MYPROC) (CI : COPYIN) : FETCHADDR :=
  fetchaddr_proof MP CI

end Xv6
