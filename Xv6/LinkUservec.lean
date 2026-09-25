/-
uservec, linked (Rocq `LinkUservec.v`, `Module Uservec := UservecProof`):
the trampoline's uservec meets its interface.  No parameter: the contract
ends at usertrap's entry (SpecUservec deviation 1), so neither `USERTRAP`
nor `USERRET` is needed here -- the closed loop chains them.
-/
import Xv6.ProofUservec

namespace Xv6

/-- **The uservec interface is inhabited.** -/
theorem uservec_link : USERVEC := uservec_proof

end Xv6
