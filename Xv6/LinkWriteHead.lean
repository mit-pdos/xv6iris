/-
`write_head` meets its specification, closed with the proved `bread`,
`bwrite` and `brelse`.
-/
import Xv6.ProofWriteHead
import Xv6.LinkBread
import Xv6.LinkBwrite
import Xv6.LinkBrelse

namespace Xv6

theorem WriteHead : WRITE_HEAD := writeHead_proof Bread Bwrite Brelse

end Xv6
