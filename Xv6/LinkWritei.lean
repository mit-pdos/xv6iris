/-
`writei` meets its specification, closed with the proved `bmap`, `bread`,
`brelse`, `log_write`, `either_copyin` and `iupdate` (Rocq `LinkWritei.v`,
`WriteiProof Bmap Bread Brelse LogWrite EitherCopyin Iupdate PrintkGen`;
the `PrintkGen` parameter is gone: writei calls no printk of its own).
`copyin` stays a parameter, as in `Xv6/LinkConsolewrite.lean` (it still
takes `walkaddr`/`vmfault`).
-/
import Xv6.ProofWritei
import Xv6.LinkBmap
import Xv6.LinkEitherCopyin
import Xv6.LinkIupdate

namespace Xv6

/-- The proved `writei` interface, given `copyin`. -/
theorem Writei (CI : COPYIN) : WRITEI :=
  writei_proof Bmap Bread Brelse LogWrite (EitherCopyin Myproc CI Memmove) Iupdate

end Xv6
