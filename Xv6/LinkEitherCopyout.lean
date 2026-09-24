/-
Link `either_copyout`: the proof instance clients import.  It calls
`myproc`, `copyout` and `memmove`; those interfaces stay parameters here,
so a client may close them with the linked ones (`LinkMyproc`,
`LinkCopyout`, `LinkMemmove`) or with its own.
-/
import Xv6.ProofEitherCopyout

namespace Xv6

/-- The proved `either_copyout` interface, given `myproc`, `copyout` and `memmove`. -/
theorem EitherCopyout (MP : MYPROC) (CO : COPYOUT) (MM : MEMMOVE) : EITHER_COPYOUT :=
  either_copyout_proof MP CO MM

end Xv6
