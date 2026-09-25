/-
Link `userinit`: the proof instance clients import.  Rocq `LinkUserinit.v`:
`Module Userinit := UserinitProof Allocproc NameiRootBoot Release
ForkretParkPaid`.  `namei("/")` is the REAL root corner (`NameiRoot`, which
is also Rocq's `NameiRootBoot`, `Xv6/SpecNamei.lean`'s header; wave 7 W7-C
retired the assumed `FsEnv.nameiBoot`); the `allocproc` and `release`
interfaces stay PARAMETERS here.  Rocq's `ForkretParkPaid` is the assumed
`[ForkretIs]` of the contract (D8 / the trap path).
-/
import Xv6.ProofUserinit
import Xv6.LinkNamei

namespace Xv6

/-- The `userinit` interface, given `allocproc` and `release`. -/
theorem Userinit (AP : ALLOCPROC) (RE : RELEASE) : USERINIT := userinit_proof AP RE NameiRoot

end Xv6
