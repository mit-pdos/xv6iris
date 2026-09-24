/-
`iupdate` meets its specification, closed with the proved `bread`,
`memmove`, `log_write` and `brelse` (Rocq `LinkIupdate.v`).
-/
import Xv6.ProofIupdate
import Xv6.LinkBread
import Xv6.LinkMemmove
import Xv6.LinkLogWrite
import Xv6.LinkBrelse

namespace Xv6

theorem Iupdate : IUPDATE := iupdate_proof Bread Memmove LogWrite Brelse

end Xv6
