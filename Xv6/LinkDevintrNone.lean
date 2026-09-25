/-
Link `devintr`'s third arm (`SpecDevintrNone`): no callees, nothing open.
-/
import Xv6.ProofDevintrNone

namespace Xv6

/-- The proved interface of `devintr` at a non-device cause. -/
theorem DevintrNone : DEVINTR_NONE := devintr_none_proof

end Xv6
