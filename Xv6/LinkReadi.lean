/-
Link `readi` (Rocq `LinkReadi.v`): the proof instance clients import.
bmap arrives through its NO-ALLOC contract (`LinkBmapNoalloc`), whose proof
never mentions balloc or log_write, so readi's cone stays out of the log.
`either_copyout` is closed with the linked `myproc` / `memmove`; `copyout`
stays a parameter, as in `LinkConsoleread` (its page-table walkers are
parameters of `LinkCopyout`).
-/
import Xv6.ProofReadi
import Xv6.LinkBmapNoalloc
import Xv6.LinkBread
import Xv6.LinkBrelse
import Xv6.LinkEitherCopyout
import Xv6.LinkMyproc
import Xv6.LinkMemmove

namespace Xv6

/-- The proved `readi` interface, given `copyout`. -/
theorem Readi (CO : COPYOUT) : READI :=
  readi_proof BmapNoalloc Bread Brelse (EitherCopyout Myproc CO Memmove)

end Xv6
