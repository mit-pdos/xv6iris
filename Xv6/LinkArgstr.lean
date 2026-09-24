/-
Link `argstr`: the proof instance clients import.  argaddr is inlined in
the compiled `argstr`, so its callees are `argraw` and `fetchstr`; those
interfaces stay parameters here, so a client may close them with the linked
ones (`LinkArgraw`, `LinkFetchstr`) or with its own.
-/
import Xv6.ProofArgstr

namespace Xv6

/-- The proved `argstr` interface, given `argraw` and `fetchstr`. -/
theorem Argstr (AR : ARGRAW) (FS : FETCHSTR) : ARGSTR := argstr_proof AR FS

end Xv6
