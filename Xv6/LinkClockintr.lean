/-
`clockintr`'s interface, instantiated from its proof.
-/
import Xv6.ProofClockintr
import Xv6.LinkCpuid
import Xv6.LinkWakeup

namespace Xv6

theorem Clockintr : CLOCKINTR := clockintr_proof Cpuid Acquire Release Wakeup

end Xv6
