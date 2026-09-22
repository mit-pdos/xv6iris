/-
Link `userinit`: the proof instance clients import.  `userinit` calls
`allocproc`, `namei` (the boot arm of the file-system boundary, assumed as
`FsEnv.nameiBoot`) and `release`; the `allocproc` and `release` interfaces
stay PARAMETERS here, so a client may close them with the linked ones
(`LinkAllocproc`, `LinkRelease`) or with its own -- and this file needs no
`Link*` import of its own.
-/
import Xv6.ProofUserinit

namespace Xv6

/-- The `userinit` interface, given `allocproc` and `release`. -/
theorem Userinit (AP : ALLOCPROC) (RE : RELEASE) : USERINIT := userinit_proof AP RE

end Xv6
