/-
Link `proc_pagetable`: the proof instance clients import.  It builds on
the user-memory functions of `vm.c`, whose interfaces stay parameters
here, so a client may close them with the linked ones or with its own.
-/
import Xv6.ProofProcPagetable

namespace Xv6

/-- `proc_pagetable` meets its specification, given `uvmcreate`'s,
`mappages`' (uncounted), `uvmunmap`'s and `uvmfree`'s. -/
theorem ProcPagetable (UC : UVMCREATE) (MP : MAPPAGES_ANY) (UM : UVMUNMAP) (UF : UVMFREE) :
    PROC_PAGETABLE := proc_pagetable_proof UC MP UM UF

end Xv6
