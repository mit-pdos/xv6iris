/-
**sync, linked**: main and start at one engine (Rocq's `UkSync` section closes
them together; DU10 split them one function per file).  The ecall leaves
(`UK_SYS_P`) are a parameter here, discharged by `UkSysPHolds.ukSysP_holds`
(drift SY2).
-/
import Xv6.ProofSyncMain
import Xv6.ProofSyncStart

namespace Xv6

/-- sync's `main` and `start`, at the engine `UL`. -/
theorem sync_linked (UL : UK_LEAVES) (HS : UK_SYS_P) : SYNC_MAIN ∧ SYNC_START :=
  have HM := syncMain_holds UL HS
  ⟨HM, syncStart_holds UL HM⟩

end Xv6
