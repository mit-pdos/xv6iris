/-
`pipealloc` meets its specification, given `filealloc`, `kalloc`, `initlock`
and `fileclose`.
-/
import Xv6.ProofPipealloc

namespace Xv6

theorem Pipealloc (FA : FILEALLOC) (KAL : KALLOC) (IL : INITLOCK) (FC : FILECLOSE) : PIPEALLOC :=
  pipealloc_proof FA KAL IL FC

end Xv6
