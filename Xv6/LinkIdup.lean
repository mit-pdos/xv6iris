/-
`idup`'s interface, instantiated from its proof against its callees'
interfaces (Rocq `LinkIdup.v`: `IdupProof Acquire Release`).  Rocq's
`RELEASE` there carries the hooked form (`wp_release_hook_sconf`); in Lean
that is the separate `RELEASE_HOOK` interface.
-/
import Xv6.ProofIdup

namespace Xv6

theorem Idup (AC : ACQUIRE) (RE : RELEASE_HOOK) : IDUP := idup_proof AC RE

end Xv6
