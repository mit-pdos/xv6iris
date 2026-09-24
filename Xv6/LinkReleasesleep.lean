/-
`releasesleep` meets its interface, given the interfaces of `acquire`,
`release` and `wakeup`.
-/
import Xv6.ProofReleasesleep

namespace Xv6

/-- The HOOKED form (the primitive one): the payload is finished at the
inner spinlock's own stamped context. -/
theorem ReleasesleepHook (AC : ACQUIRE) (REH : RELEASE_HOOK) (WK : WAKEUP) : RELEASESLEEP_HOOK :=
  releasesleep_hook_proof AC REH WK

theorem Releasesleep (AC : ACQUIRE) (REH : RELEASE_HOOK) (WK : WAKEUP) : RELEASESLEEP :=
  (ReleasesleepHook AC REH WK).toRELEASESLEEP

end Xv6
