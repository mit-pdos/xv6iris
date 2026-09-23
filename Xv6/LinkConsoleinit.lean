/-
`consoleinit`'s interface, instantiated from its proof.
-/
import Xv6.ProofConsoleinit
import Xv6.LinkInitlock
import Xv6.LinkUartinit
import Xv6.LinkUartinitone

namespace Xv6

theorem Consoleinit : CONSOLEINIT := consoleinit_proof Initlock (Uartinit (Uartinitone Initlock))

end Xv6
