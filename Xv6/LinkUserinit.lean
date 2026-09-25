/-
Link `userinit`: the proof instance clients import.  Rocq `LinkUserinit.v`:
`Module Userinit := UserinitProof Allocproc NameiRootBoot Release
ForkretParkPaid`.  `namei("/")` is the REAL root corner (`NameiRoot`, which
is also Rocq's `NameiRootBoot`, `Xv6/SpecNamei.lean`'s header; wave 7 W7-C
retired the assumed `FsEnv.nameiBoot`); the `allocproc` and `release`
interfaces stay PARAMETERS here, and so does Rocq's `ForkretParkPaid`
(`FORKRET_PARK_PAID`, whose `park_token_intro` the park spends): main's link
supplies `ProofForkretPark.forkret_park_proof` of the linked forkret.
-/
import Xv6.ProofUserinit
import Xv6.LinkNamei

namespace Xv6

/-- The `userinit` interface, given `allocproc`, `release` and the proved park. -/
theorem Userinit (AP : ALLOCPROC) (RE : RELEASE) (FP : FORKRET_PARK_PAID) : USERINIT :=
  userinit_proof AP RE NameiRoot FP

end Xv6
