/-
MachCSL: word entries and word histories, the PURE layer (split out of
`MachCSL.WordHist` by W8-β′ so that the state interpretation's reserved-region
discipline, `MachCSL.Reserved`, can be stated below `MachCSL.Resources`).

Everything here is a definition or a pure lemma over `MachCSL.TsoMem`'s byte
histories; the resource `wordCell` and the read/heads lemmas stay in
`MachCSL.WordHist`, which imports this file.  Names unchanged.
-/
import MachCSL.TsoMem

namespace MachCSL

variable {n : Nat}

/-! ## Word entries -/

/-- An entry of a word's history: a whole-word store. -/
structure WEnt (n : Nat) where
  t : Nat
  tid : Agent
  v : BitVec (8 * n)

/-- The history of a word: latest first. -/
abbrev WordHist (n : Nat) := List (WEnt n)

/-- Byte `j` of an entry. -/
def WEnt.proj (j : Nat) (e : WEnt n) : HEnt := ⟨e.t, e.tid, nthByte e.v j⟩

/-- Visible to agent `h` at view `tv` (as `HEnt.visible`). -/
def WEnt.visible (h : Agent) (tv : Nat) (e : WEnt n) : Bool :=
  decide (e.t ≤ tv) || decide (e.tid = h)

theorem WEnt.proj_visible (j : Nat) (h : Agent) (tv : Nat) (e : WEnt n) :
    (e.proj j).visible h tv = e.visible h tv := rfl

/-- Visible to agent `h` at (landing) view `tv` (route P, as `HEnt.visibleP`): landed at or
below the view, or the agent's own. -/
def WEnt.visibleP (lp : LandPos) (h : Agent) (tv : Nat) (e : WEnt n) : Bool :=
  (lp e.t).any (· ≤ tv) || decide (e.tid = h)

theorem WEnt.proj_visibleP (j : Nat) (lp : LandPos) (h : Agent) (tv : Nat) (e : WEnt n) :
    (e.proj j).visibleP lp h tv = e.visibleP lp h tv := rfl

/-- Under eager landing a word entry landed at its own stamp is visible exactly when it is today. -/
theorem WEnt.visibleP_eager (lp : LandPos) (h : Agent) (tv : Nat) (e : WEnt n) (he : lp e.t = some e.t) :
    e.visibleP lp h tv = e.visible h tv := by
  simp [WEnt.visibleP, WEnt.visible, he]

/-- The read cases of a word history for a reader `h` at (landing) view `tvn` (route P, increment
P-M4c; `MachCSL.ReadCases`'s twin over `WEnt.visibleP`): the first visible entry's value, or the
initial value when none is visible. -/
abbrev ReadCasesP (lp : LandPos) (W : WordHist n) (h : Agent) (tvn : Nat) (v0 w : BitVec (8 * n)) : Prop :=
  (∃ W1 e W2, W = W1 ++ e :: W2 ∧ e.visibleP lp h tvn = true ∧ (∀ x ∈ W1, x.visibleP lp h tvn = false) ∧
    w = e.v) ∨
  ((∀ x ∈ W, x.visibleP lp h tvn = false) ∧ w = v0)

/-- The byte histories of the word: `W`'s projections over the tails. -/
def WordHist.hist (W : WordHist n) (Hold : Nat → Hist) (j : Nat) : Hist :=
  W.map (WEnt.proj j) ++ Hold j

/-- The tails: nonempty, heads spelling `v0` at EXACTLY the position `lo`
(`lo = 0` for a window never written since the image; the timestamp of the
one store that minted the word otherwise).  The exactness is what lets a
reader who authored the store at `lo` certify the head as visible. -/
def tailOk (n lo : Nat) (v0 : BitVec (8 * n)) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.v = nthByte v0 j ∧ e.t = lo

/-- The tails' heads spell `v0`, their positions left open: what the
value-level arguments (`read_cases`, `heads_eq`) need of a tail. -/
def tailVals (n : Nat) (v0 : BitVec (8 * n)) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.v = nthByte v0 j

/-- The tails with a position PER BYTE: nonempty, byte `j`'s head spelling
byte `j` of `v0` at EXACTLY the position `ts j`.  A word zeroed by a byte
loop (`memset`) has eight different positions, one per store; `tailOk n lo`
is the constant case. -/
def tailOkT (n : Nat) (ts : Nat → Nat) (v0 : BitVec (8 * n)) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.v = nthByte v0 j ∧ e.t = ts j

theorem tailOk_vals {n lo : Nat} {v0 : BitVec (8 * n)} {Hold : Nat → Hist}
    (h : tailOk n lo v0 Hold) : tailVals n v0 Hold :=
  fun j hj => let ⟨e, H, h1, h2, _⟩ := h j hj; ⟨e, H, h1, h2⟩

theorem tailOkT_vals {n : Nat} {ts : Nat → Nat} {v0 : BitVec (8 * n)} {Hold : Nat → Hist}
    (h : tailOkT n ts v0 Hold) : tailVals n v0 Hold :=
  fun j hj => let ⟨e, H, h1, h2, _⟩ := h j hj; ⟨e, H, h1, h2⟩

/-- The head of a tail: its value and its (exact) per-byte position. -/
theorem tailOkT_head {n : Nat} {ts : Nat → Nat} {v0 : BitVec (8 * n)} {Hold : Nat → Hist}
    (htail : tailOkT n ts v0 Hold) (j : Nat) (hj : j < n) (e : HEnt) (H : Hist)
    (hH : Hold j = e :: H) : e.v = nthByte v0 j ∧ e.t = ts j := by
  obtain ⟨e', H', hH', hv, ht⟩ := htail j hj
  rw [hH] at hH'
  simp only [List.cons.injEq] at hH'
  obtain ⟨rfl, rfl⟩ := hH'
  exact ⟨hv, ht⟩

/-- The head of a tail: its value and its (exact) position. -/
theorem tailOk_head {n lo : Nat} {v0 : BitVec (8 * n)} {Hold : Nat → Hist}
    (htail : tailOk n lo v0 Hold) (j : Nat) (hj : j < n) (e : HEnt) (H : Hist)
    (hH : Hold j = e :: H) : e.v = nthByte v0 j ∧ e.t = lo := by
  obtain ⟨e', H', hH', hv, ht⟩ := htail j hj
  rw [hH] at hH'
  simp only [List.cons.injEq] at hH'
  obtain ⟨rfl, rfl⟩ := hH'
  exact ⟨hv, ht⟩

/-- The current value of the word. -/
def curVal (W : WordHist n) (v0 : BitVec (8 * n)) : BitVec (8 * n) :=
  match W with
  | e :: _ => e.v
  | [] => v0


end MachCSL
