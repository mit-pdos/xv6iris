/-
`uartinit`'s interface, instantiated from its proof.
-/
import Xv6.ProofUartinit

namespace Xv6

theorem Uartinit (UI : UARTINITONE) : UARTINIT := uartinit_proof UI

end Xv6
