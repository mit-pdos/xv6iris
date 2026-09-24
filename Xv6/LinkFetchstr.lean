/-
Link `fetchstr`: the proof instance clients import.  It calls `myproc`,
`copyinstr` and `strlen`; those interfaces stay parameters here, so a client
may close them with the linked ones (`LinkMyproc`, `LinkCopyinstr`,
`LinkStrlen`) or with its own.
-/
import Xv6.ProofFetchstr

namespace Xv6

/-- The proved `fetchstr` interface, given `myproc`, `copyinstr` and `strlen`. -/
theorem Fetchstr (MP : MYPROC) (CI : COPYINSTR) (SL : STRLEN) : FETCHSTR :=
  fetchstr_proof MP CI SL

end Xv6
