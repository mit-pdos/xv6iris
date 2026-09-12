/-
MachCSL: the points-to of a word.

`wordPointsTo pa n dq w` owns the `n` bytes of `w` at `pa` (`bytesPointsTo`)
together with the two facts a load or store of that word needs: the window is
in RAM and `pa` is `n`-aligned.  The facts travel with the ownership (the
Rocq prototype's `word_pointsto`), so an instruction rule takes the cell and
nothing else: no client proves RAM membership or alignment at a memory access.
-/
import MachCSL.Ctx
import MachCSL.PlatformFacts

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std

variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

/-- **The `n`-byte word `w` at `pa`**, owned at `dq`: its bytes, in RAM, at an
`n`-aligned address. -/
def wordPointsTo [CurCtx] (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) : IProp GF := iprop%
  ⌜inRam pa n ∧ pa.toNat % n = 0⌝ ∗ bytesPointsTo pa n dq w

/-- A byte window in RAM at an aligned address is a word. -/
theorem wordPointsTo_intro [CurCtx] (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n))
    (hram : inRam pa n) (hal : pa.toNat % n = 0) :
    bytesPointsTo (GF := GF) pa n dq w ⊢ wordPointsTo pa n dq w := by
  unfold wordPointsTo
  iintro H; iframe H; ipureintro; exact ⟨hram, hal⟩

/-- A word is its byte window, with the facts. -/
theorem wordPointsTo_cases [CurCtx] (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordPointsTo (GF := GF) pa n dq w ⊢ ⌜inRam pa n ∧ pa.toNat % n = 0⌝ ∗ bytesPointsTo pa n dq w := by
  unfold wordPointsTo
  iintro H; iexact H

/-- The facts of a word. -/
theorem wordPointsTo_facts [CurCtx] (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    wordPointsTo (GF := GF) pa n dq w ⊢ ⌜inRam pa n ∧ pa.toNat % n = 0⌝ ∗ wordPointsTo pa n dq w := by
  unfold wordPointsTo
  iintro ⟨%h, H⟩; iframe H; ipureintro; exact ⟨h, h⟩

instance [CurCtx] (pa : PAddr) (n : Nat) (dq : DFrac) (w : BitVec (8 * n)) :
    Timeless (PROP := IProp GF) (wordPointsTo pa n dq w) := by
  unfold wordPointsTo
  infer_instance

/-- The low four bytes of a doubleword window, as a window. -/
theorem bytesPointsTo_lo4_acc [CurCtx] (a : BitVec 64) (dq : DFrac) (w : BitVec 64) :
    bytesPointsTo (GF := GF) a 8 dq w ⊢
      bytesPointsTo a 4 dq (BitVec.extractLsb' 0 32 w) ∗
      (bytesPointsTo a 4 dq (BitVec.extractLsb' 0 32 w) -∗ bytesPointsTo a 8 dq w) := by
  have e0 : nthByte (n := 4) (BitVec.extractLsb' 0 32 w) 0 = nthByte (n := 8) w 0 := by unfold nthByte; bv_decide
  have e1 : nthByte (n := 4) (BitVec.extractLsb' 0 32 w) 1 = nthByte (n := 8) w 1 := by unfold nthByte; bv_decide
  have e2 : nthByte (n := 4) (BitVec.extractLsb' 0 32 w) 2 = nthByte (n := 8) w 2 := by unfold nthByte; bv_decide
  have e3 : nthByte (n := 4) (BitVec.extractLsb' 0 32 w) 3 = nthByte (n := 8) w 3 := by unfold nthByte; bv_decide
  unfold bytesPointsTo ctxBytes
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    Iris.Algebra.BigOpL.bigOpL_cons, Iris.Algebra.BigOpL.bigOpL_nil, BitVec.add_zero, e0, e1, e2, e3]
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, _⟩
  iframe H0 H1 H2 H3
  iintro ⟨H0, H1, H2, H3, _⟩
  iframe
  all_goals try iempintro

/-- The low half of a doubleword is a word (`lw` of an 8-byte cell). -/
theorem wordPointsTo_lo4_acc [CurCtx] (a : BitVec 64) (dq : DFrac) (w : BitVec 64) :
    wordPointsTo (GF := GF) a 8 dq w ⊢
      wordPointsTo a 4 dq (BitVec.extractLsb' 0 32 w) ∗
      (wordPointsTo a 4 dq (BitVec.extractLsb' 0 32 w) -∗ wordPointsTo a 8 dq w) := by
  unfold wordPointsTo
  iintro ⟨%⟨hram, hal⟩, H⟩
  have hram4 : inRam a 4 := by unfold inRam at *; omega
  have hal4 : a.toNat % 4 = 0 := by omega
  icases bytesPointsTo_lo4_acc a dq w $$ H with ⟨Hlo, Hclose⟩
  isplitl [Hlo]
  · iframe Hlo; ipureintro; exact ⟨hram4, hal4⟩
  · iintro ⟨_, Hlo⟩
    ihave H := Hclose $$ Hlo
    iframe H; ipureintro; exact ⟨hram, hal⟩

end MachCSL
