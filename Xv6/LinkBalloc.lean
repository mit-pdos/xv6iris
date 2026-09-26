/-
`balloc`'s interface, instantiated from its proof (Rocq `LinkBalloc.v`).
All five callees -- `bread`, `log_write`, `brelse`, `memset` (the inlined
bzero's) and `printk` (the LIVE out-of-blocks arm's) -- are proven, so
nothing here is assumed.  balloc's two dead arms (`+0x12`, `+0x98`) are
refuted inside the proof, so no panic contract is instantiated.
-/
import Xv6.ProofBalloc
import Xv6.LinkBread
import Xv6.LinkLogWrite
import Xv6.LinkBrelse
import Xv6.LinkMemset

namespace Xv6

theorem Balloc : BALLOC := balloc_proof Bread LogWrite Brelse Memset Printk

end Xv6
