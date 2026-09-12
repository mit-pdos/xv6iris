/-
MachCSL: word histories.

The byte histories of an aligned word written only by whole-word stores
share their timestamps and authors: they are the projections of ONE list of
word entries.  `wordCell pa n lo v0 W` owns the `n` byte histories of the
window at `pa` as `W`'s projections on top of an arbitrary tail whose head
entries (the value `v0`, at positions at most `lo`) are what the window
held before it was placed under a word discipline.

What this buys: a racy plain load of the window by any hart at any view
past `lo` returns a WHOLE entry of `W` -- the first one visible to the
reader -- or `v0` (`WordHist.read_cases`), because visibility depends only
on the timestamp and the author, which the bytes share.  The value-set and
"not my own pointer" arguments of the spinlock kit are word-level
arguments over `W`.
-/
import MachCSL.WpAtomic

namespace MachCSL

open Iris Iris.BI Iris.ProofMode Std

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

/-- The byte histories of the word: `W`'s projections over the tails. -/
def WordHist.hist (W : WordHist n) (Hold : Nat → Hist) (j : Nat) : Hist :=
  W.map (WEnt.proj j) ++ Hold j

/-- The tails: nonempty, heads spelling `v0` at positions at most `lo`. -/
def tailOk (n lo : Nat) (v0 : BitVec (8 * n)) (Hold : Nat → Hist) : Prop :=
  ∀ j, j < n → ∃ e H, Hold j = e :: H ∧ e.v = nthByte v0 j ∧ e.t ≤ lo

/-- The current value of the word. -/
def curVal (W : WordHist n) (v0 : BitVec (8 * n)) : BitVec (8 * n) :=
  match W with
  | e :: _ => e.v
  | [] => v0

theorem WordHist.hist_ne_nil (W : WordHist n) (Hold : Nat → Hist) {lo : Nat} {v0 : BitVec (8 * n)}
    (htail : tailOk n lo v0 Hold) (j : Nat) (hj : j < n) : W.hist Hold j ≠ [] := by
  obtain ⟨e, H, hH, _, _⟩ := htail j hj
  unfold WordHist.hist
  rw [hH]
  simp

theorem WordHist.hist_push (W : WordHist n) (Hold : Nat → Hist) (t : Nat) (h : Agent)
    (w : BitVec (8 * n)) : pushed (W.hist Hold) t h w = WordHist.hist (⟨t, h, w⟩ :: W) Hold := by
  funext j
  simp [pushed, WordHist.hist, WEnt.proj]

theorem WordHist.find?_hist (W : WordHist n) (Hold : Nat → Hist) (h : Agent) (tv j : Nat) :
    (W.hist Hold j).find? (HEnt.visible h tv) =
      ((W.find? (WEnt.visible h tv)).map (WEnt.proj j)).or ((Hold j).find? (HEnt.visible h tv)) := by
  unfold WordHist.hist
  rw [List.find?_append, List.find?_map]
  rfl

/-- A plain read of the window past `lo` returns the first visible entry of
`W`, or the tail's `v0` if none is visible. -/
theorem WordHist.read_cases (W : WordHist n) (Hold : Nat → Hist) (h : Agent) (tvn lo : Nat)
    (v0 w : BitVec (8 * n)) (hn : 0 < n) (htail : tailOk n lo v0 Hold) (hlo : lo ≤ tvn)
    (hrd : readsAre h tvn (W.hist Hold) n w) :
    (∃ W1 e W2, W = W1 ++ e :: W2 ∧ e.visible h tvn = true ∧ (∀ x ∈ W1, x.visible h tvn = false) ∧
      w = e.v) ∨
    ((∀ x ∈ W, x.visible h tvn = false) ∧ w = v0) := by
  cases hf : W.find? (WEnt.visible h tvn) with
  | some e =>
    left
    obtain ⟨hvis, W1, W2, hW, hW1⟩ := List.find?_eq_some_iff_append.1 hf
    refine ⟨W1, e, W2, hW, hvis, fun x hx => by simpa using hW1 x hx, ?_⟩
    apply bv_eq_of_bytes
    intro j hj
    have := hrd j hj
    unfold Hist.read at this
    rw [WordHist.find?_hist, hf] at this
    simp only [Option.map_some, Option.some_or, WEnt.proj, Option.some.injEq] at this
    exact this.symm
  | none =>
    right
    have hnone := List.find?_eq_none.1 hf
    refine ⟨fun x hx => by simpa using hnone x hx, ?_⟩
    apply bv_eq_of_bytes
    intro j hj
    have := hrd j hj
    obtain ⟨e, H, hH, hev, het⟩ := htail j hj
    unfold Hist.read at this
    have hvis : HEnt.visible h tvn e = true := HEnt.visible_of_le h tvn e (by omega)
    rw [WordHist.find?_hist, hf, Option.map_none, Option.none_or, hH] at this
    simp only [List.find?_cons, hvis, Option.map_some, Option.some.injEq] at this
    rw [← this, hev]

/-- The heads of the window spell the current value. -/
theorem WordHist.heads_eq (W : WordHist n) (Hold : Nat → Hist) {lo : Nat} (v0 w : BitVec (8 * n))
    (htail : tailOk n lo v0 Hold) (hh : headsAre (W.hist Hold) n w) : w = curVal W v0 := by
  apply bv_eq_of_bytes
  intro j hj
  have := hh j hj
  cases W with
  | nil =>
    obtain ⟨e, H, hH, hev, _⟩ := htail j hj
    simp only [WordHist.hist, List.map_nil, List.nil_append, hH, List.head?_cons, Option.map_some,
      Option.some.injEq] at this
    simp only [curVal]
    rw [← this, hev]
  | cons e W =>
    simp only [WordHist.hist, List.map_cons, List.cons_append, List.head?_cons, Option.map_some,
      WEnt.proj, Option.some.injEq] at this
    simp only [curVal]
    exact this.symm

/-! ## The resource -/

section res
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]

instance histBytes_timeless (pa : PAddr) (n : Nat) (dqs : Nat → DFrac) (Hs : Nat → Hist) :
    Timeless (histBytes (GF := GF) pa n dqs Hs) := by
  unfold histBytes
  exact BigSepL.bigSepL_timeless (fun _ => inferInstance)

/-- The word window at `pa`: `W`'s projections over tails spelling `v0` at
positions at most `lo`. -/
def wordCell (pa : PAddr) (n lo : Nat) (v0 : BitVec (8 * n)) (W : WordHist n) : IProp GF := iprop%
  ∃ Hold : Nat → Hist, histBytes pa n (fun _ => DFrac.own 1) (W.hist Hold) ∗ ⌜tailOk n lo v0 Hold⌝

instance wordCell_timeless (pa : PAddr) (n lo : Nat) (v0 : BitVec (8 * n)) (W : WordHist n) :
    Timeless (wordCell (GF := GF) pa n lo v0 W) := by
  unfold wordCell
  infer_instance

theorem wordCell_cases (pa : PAddr) (n lo : Nat) (v0 : BitVec (8 * n)) (W : WordHist n) :
    wordCell (GF := GF) pa n lo v0 W ⊢
      ∃ Hold : Nat → Hist, histBytes pa n (fun _ => DFrac.own 1) (W.hist Hold) ∗ ⌜tailOk n lo v0 Hold⌝ := by
  unfold wordCell
  iintro H
  iexact H

theorem wordCell_intro (pa : PAddr) (n lo : Nat) (v0 : BitVec (8 * n)) (W : WordHist n) (Hold : Nat → Hist)
    (htail : tailOk n lo v0 Hold) :
    histBytes (GF := GF) pa n (fun _ => DFrac.own 1) (W.hist Hold) ⊢ wordCell pa n lo v0 W := by
  unfold wordCell
  iintro H
  iexists Hold
  iframe H
  ipureintro
  exact htail

/-- After a whole-word store at `t` by `h`: the entry joins `W`. -/
theorem wordCell_push (pa : PAddr) (n lo : Nat) (v0 : BitVec (8 * n)) (W : WordHist n) (Hold : Nat → Hist)
    (htail : tailOk n lo v0 Hold) (t : Nat) (h : Agent) (w : BitVec (8 * n)) :
    histBytes (GF := GF) pa n (fun _ => DFrac.own 1) (pushed (W.hist Hold) t h w) ⊢
      wordCell pa n lo v0 (⟨t, h, w⟩ :: W) := by
  rw [WordHist.hist_push]
  exact wordCell_intro pa n lo v0 _ Hold htail

/-- A window never written since the image is a word cell at floor `0`. -/
theorem WordHist.hist_nil (Hold : Nat → Hist) : WordHist.hist ([] : WordHist n) Hold = Hold := by
  funext j
  simp [WordHist.hist]

theorem wordCell_of_fresh (pa : PAddr) (n : Nat) (v0 : BitVec (8 * n)) (tids : Nat → Agent) :
    histBytes (GF := GF) pa n (fun _ => DFrac.own 1) (fun j => [⟨0, tids j, nthByte v0 j⟩]) ⊢
      wordCell pa n 0 v0 [] := by
  have htail : tailOk n 0 v0 (fun j => [⟨0, tids j, nthByte v0 j⟩]) := fun j _ => ⟨_, _, rfl, rfl, le_refl _⟩
  have e := wordCell_intro (GF := GF) pa n 0 v0 [] _ htail
  rw [WordHist.hist_nil] at e
  exact e

end res

end MachCSL
