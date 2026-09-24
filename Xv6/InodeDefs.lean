/-
Pure inode vocabulary usable without the inode invariant.  A port of Rocq
`InodeDefs.v` (`/shared/xv6rocq/iris/InodeDefs.v`), whole.

No deviation from Rocq beyond the port's spellings: `file_byte` →
`fileByte`, stdpp's total lookup `!!!` → `l[i]!`, and `BSIZE` is the
existing `Xv6.BSIZE` of `Xv6/DiskDefs.lean` rather than Rocq's
`BioDefs.BSIZE`.
-/
import Xv6.DiskDefs

namespace Xv6

/-- The flat byte view of block-indexed file contents (Rocq's
`file_byte`): byte `k` of the file is byte `k % BSIZE` of block
`k / BSIZE`. -/
def fileByte (data : Nat → List (BitVec 8)) (k : Nat) : BitVec 8 :=
  (data (k / BSIZE))[k % BSIZE]!

end Xv6
