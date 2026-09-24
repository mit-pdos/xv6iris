/-
`stati`'s interface, instantiated from its proof.  stati is a LEAF (it calls
nothing), so the proof takes no callee interfaces (Rocq `LinkStati.v`).
-/
import Xv6.ProofStati

namespace Xv6

theorem Stati : STATI := stati_proof

end Xv6
