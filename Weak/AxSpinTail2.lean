/-
Weak: **THEOREM 2 / P4: the text facts of the walk past the row end** — `AxSpinApA.tailText2`,
the three instructions a hart executes after the terminal store `c.sw a5,24(s1)` at
`allocproc + 0x9a` (the row end) before it stops (`notes/weak-lb-thm2-p4.md` §A.6, §B, Q-P4-3):

| pc | bytes | instruction | fact |
|---|---|---|---|
| `allocproc + 0x9c` = 0x80001c0e | `0xf71fe0ef` | `jal ra, kalloc` | `textAt4S` (2 mod 4, Q22) |
| `kalloc + 0` = 0x80000b7e | `0x1101` | `c.addi sp,sp,-32` | `textAtS` |
| `kalloc + 2` = 0x80000b80 | `0xec06` | `c.sdsp ra,24(sp)` | `textAtS` |

The `c.sdsp` is a store AT the row end — stuck (`AxSpinRowEnd.XxStEnd`) — so the walk stops at
`kalloc + 2` (Q-P4-3); no kalloc premise beyond these three words.

Lean-only (no Rocq source).  The bytes are this tree's kernel image (`Xv6/KernelImage.lean`:
`⟨0x80001c0e, 4, 0xf71fe0ef⟩`, `⟨0x80000b7e, 2, 0x1101⟩`, `⟨0x80000b80, 2, 0xec06⟩`); they are
certified on the capstone image `AxSpinT2c5.σX` in `AxSpinTail2X` (`AxSpinTail2X.tailText2X`).
Names: `AxSpinApA.tailText2` (the premise name of the design, `AxSpinApA` namespace) and the
file-qualified `AxSpinTail2.pka` / `AxSpinTail2.wJal`.  Reused: `pca` (AxSpinAp), `AxSpinE7.hw`,
`textAtS` / `textAt4S`.
-/
import Weak.AxSpinAp

namespace Weak

open MachCSL

/-- The address `kalloc + off`. -/
def AxSpinTail2.pka (off : Int) : BitVec 64 := BitVec.ofInt 64 ((KernelSyms.«kalloc» : Int) + off)

/-- `allocproc + 0x9c`: `jal ra, kalloc` (0xf71fe0ef). -/
def AxSpinTail2.wJal : BitVec 32 := 0xf71fe0ef#32

/-- The text facts of the three instructions past the row end (`allocproc + 0x9c`, `kalloc + 0`,
`kalloc + 2`). -/
def AxSpinApA.tailText2 (σi : ExecSt) (T : PTree) : Prop :=
  textAt4S σi T (pca 0x9c) AxSpinTail2.wJal ∧
  textAtS σi T (AxSpinTail2.pka 0) (AxSpinE7.hw 0x1101) ∧
  textAtS σi T (AxSpinTail2.pka 2) (AxSpinE7.hw 0xec06)

end Weak
