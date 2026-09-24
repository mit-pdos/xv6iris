/-
`bmap`'s NO-ALLOC interface, instantiated from its proof (Rocq
`LinkBmapNoalloc.v`).  Only `bread` and `brelse` are needed: the three
allocation arms are dead under the no-alloc premise, and the core takes
`BALLOC` / `LOG_WRITE` only as hypotheses gated on the kit, so readi's cone
does not reach balloc.  Rocq's `PrintkGen` argument is dropped (unused).
-/
import Xv6.ProofBmap
import Xv6.LinkBread
import Xv6.LinkBrelse

namespace Xv6

theorem BmapNoalloc : BMAP_NOALLOC := bmap_noalloc_proof Bread Brelse

end Xv6
