/-
Link `proc_freepagetable`: the proof instance clients import.  It builds
on the user-memory functions of `vm.c`, whose interfaces stay parameters
here, so a client may close them with the linked ones or with its own.
-/
import Xv6.ProofProcFreepagetable

namespace Xv6

/-- `proc_freepagetable` meets its specification, given `uvmunmap`'s and
`uvmfree`'s. -/
theorem ProcFreepagetable (UM : UVMUNMAP) (UF : UVMFREE) : PROC_FREEPAGETABLE :=
  proc_freepagetable_proof UM UF

end Xv6
