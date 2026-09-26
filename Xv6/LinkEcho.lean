/-
**echo, linked**: the three walks at one engine (Rocq's `UkEcho` section
closes them together; DU10 split them one function per file).
-/
import Xv6.ProofEchoStrlen
import Xv6.ProofEchoMain
import Xv6.ProofEchoStart

namespace Xv6

/-- echo's `strlen`, `main` and `start`, at the engine `UL`. -/
theorem echo_linked (UL : UK_LEAVES) : ECHO_STRLEN ∧ ECHO_MAIN ∧ ECHO_START :=
  have HS := echoStrlen_holds UL
  have HM := echoMain_holds UL HS
  ⟨HS, HM, echoStart_holds UL HM⟩

end Xv6
