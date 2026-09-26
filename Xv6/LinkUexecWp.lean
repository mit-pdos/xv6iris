/-
Link the generic user-execution slot (Rocq `LinkUserinit.UG`, the module
`UexecGen (US : USER) : UEXEC_GEN` instantiated where the system theorem
reads it): `ProofUexecWp.uexecWp_gen` at the user-mode interface `USER`, the
one assumed interface of the system theorem (D24).  Its one reader is the
generic application's init-boot discharge (`SystemAdequacy.xv6Triv_initBoot`).
-/
import Xv6.ProofUexecWp

namespace Xv6

/-- The generic user-execution slot, at the user-mode interface. -/
theorem UexecGen (US : USER) : UEXEC_GEN := uexecWp_gen US

end Xv6
