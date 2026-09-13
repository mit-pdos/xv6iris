/-
Link `kernelvec`: the proof instance clients import.  kernelvec calls
`kerneltrap`, whose interface (`KERNELTRAP`, stated in `SpecKerneltrap`)
remains a parameter until its cone (devintr, yield) is proved.
-/
import Xv6.ProofKernelvec

namespace Xv6

/-- The proved `kernelvec` handler contract, given `kerneltrap`. -/
theorem Kernelvec (KT : KERNELTRAP) : KERNELVEC := kernelvec_proof KT

end Xv6
