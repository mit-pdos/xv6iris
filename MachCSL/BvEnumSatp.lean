import MachCSL.URunRW

/-!
# One home for `bv_decide`'s `SATPMode` encoding

`bv_decide` encodes an enum it meets in a goal or hypothesis by adding an
auxiliary declaration `SATPMode.enumToBitVec` (and its lemmas) to the
environment. Two modules that each trigger it add the same name and then clash
when imported together. This file triggers it once; every module whose
`bv_decide` sees a `SATPMode` imports this file, and `bv_decide` reuses the
existing declaration.
-/

namespace MachCSL

theorem bvEnumSatp_refl (a b : LeanRV64D.SATPMode) (h : a = b) : b = a := by
  bv_decide

end MachCSL
