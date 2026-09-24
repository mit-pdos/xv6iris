/-
Link `prepare_return`: the sealed proof instance clients import.
`prepare_return` calls only `myproc`; its proof is closed with the linked
`Myproc`.
-/
import Xv6.ProofPrepareReturn
import Xv6.LinkMyproc

namespace Xv6

/-- The proved `prepare_return` interface. -/
theorem PrepareReturn : PREPARE_RETURN := prepare_return_proof Myproc

end Xv6
