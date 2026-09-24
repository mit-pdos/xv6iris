/-
`bmap`'s allocating interface, instantiated from its proof (Rocq
`LinkBmap.v`).  All four callees -- `balloc`, `bread`, `brelse`,
`log_write` -- are proven, so nothing here is assumed (Rocq's LinkBmap.v
comment calling balloc ASSUMED is stale).  The dead `unreachable` arm is
refuted inside the proof, and Rocq's `PrintkGen` argument is dropped: bmap
never calls printk (`Xv6/ProofBmap.lean` deviation 1).
-/
import Xv6.ProofBmap
import Xv6.LinkBalloc
import Xv6.LinkBread
import Xv6.LinkBrelse
import Xv6.LinkLogWrite

namespace Xv6

theorem Bmap : BMAP := bmap_proof Balloc Bread Brelse LogWrite

end Xv6
