/-
`holdingsleep` meets its interface, given the interfaces of `acquire`,
`release` and `myproc`.
-/
import Xv6.ProofHoldingsleep

namespace Xv6

theorem Holdingsleep (AC : ACQUIRE) (RE : RELEASE) (MP : MYPROC) : HOLDINGSLEEP :=
  holdingsleep_proof AC RE MP

end Xv6
