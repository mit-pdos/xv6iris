/-
`pipealloc` meets its specification, given `filealloc`, `kalloc`, `initlock`,
`fileclose`, and (NI M3 quotas Q-0) `acquire`/`release` for `npipelock`.
-/
import Xv6.ProofPipealloc

namespace Xv6

theorem Pipealloc (FA : FILEALLOC) (KAL : KALLOC) (IL : INITLOCK) (FC : FILECLOSE)
    (AC : ACQUIRE) (RE : RELEASE) : PIPEALLOC :=
  pipealloc_proof FA KAL IL FC AC RE

end Xv6
