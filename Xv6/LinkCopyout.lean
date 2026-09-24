/-
Link `copyout`: the proof instance clients import.  `copyout` copies bytes
from the kernel into a process's address space, walking its page table and
faulting in lazily-allocated pages on the way.  Its callees stay parameters
here, so a client may close them with the linked ones or with its own.
-/
import Xv6.ProofCopyout

namespace Xv6

/-- The proved `copyout` interface, given its callees. -/
theorem Copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) :
    COPYOUT :=
  copyout_proof WA VF W MM

end Xv6
