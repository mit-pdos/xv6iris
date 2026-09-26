/-
MachCSL: xv6's PMP configuration, as plain data.

The tables `start()` leaves (`pmpaddr0 := 0x3fffffffffffff`, `pmpcfg0 := 0xf`)
and the footprint condition under which its TOR entry 0 covers an access.
Kept apart from the CSR stage lemmas (`WpCsr`) and the PMP stage
(`WpPmpXv6`) so the S-mode configuration (`SConfDefs`) does not wait for them.
-/
import MachCSL.Platform

namespace MachCSL

/-- The PMP tables after `start()`: entry 0 is TOR up to `0x3fffffffffffff` (all
of physical memory), R/W/X, unlocked. -/
def xv6Pmpcfg : Vector (BitVec 8) 64 := Sail.vectorUpdate bootPmpcfg 0 0x0f#8
def xv6Pmpaddr : Vector (BitVec 64) 64 := Sail.vectorUpdate bootPmpaddr 0 0x3fffffffffffff#64
theorem xv6Pmpaddr_0 : xv6Pmpaddr[0]! = 0x3fffffffffffff#64 := by decide

/-- An access xv6's TOR entry 0 covers: the footprint lies below `2^56 - 4`
(every RAM access, and every device-window access). -/
def pmpOk (addr : BitVec 64) (width : Nat) : Prop :=
  0 < addr.toNat + width ∧ addr.toNat + width ≤ 72057594037927932 ∧ addr.toNat < 72057594037927932

end MachCSL
