/-
Link `either_copyin`: the proof instance clients import.  It calls
`myproc`, `copyin` and `memmove`; those interfaces stay parameters here,
so a client may close them with the linked ones (`LinkMyproc`,
`LinkCopyin`, `LinkMemmove`) or with its own.
-/
import Xv6.ProofEitherCopyin

namespace Xv6

/-- The proved `either_copyin` interface, given `myproc`, `copyin` and `memmove`. -/
theorem EitherCopyin (MP : MYPROC) (CI : COPYIN) (MM : MEMMOVE) : EITHER_COPYIN :=
  either_copyin_proof MP CI MM

end Xv6
