/-
Weak: **PREFIX ROW SHAPES** (pure) — the `Ritem`-level prefix match `RowShP` that the
Theorem 2 STAGE 2 P-form compositions (E8, PO1–PO6, Hd*, Aq*, Rl*, Ap9) state their row premises
over.  Stage-2 design `notes/weak-lb-thm2-stage2.md` §A ("Row family") and §B ("Prefix
tolerance"); orchestrator layering ruling (2026-10-08): the predicate lives LOW, importing only
`Weak.AxSpinPOr` (where `Ritem`/`ishape`/`RowSh` live), so every P-form file can use it.  NEW Lean
file (no Rocq source; Rocq's ID-8 prefix family is the model).

## What this file provides

`RowShP k row sh`: every item `sh[j]` whose row position `k + j` is PRESENT in the row
(`k + j < row.length`) is matched there (`ishape`).  Positions past the row end are
unconstrained, so a row that stops anywhere inside the window — at ANY row position, each of
which is an instruction boundary under Stage C (items are memory events; fetches and warm-TLB
walks emit none) — still matches.  `RowSh` is the special case `k + sh.length ≤ row.length`.

API (all `theorem`s, no premises beyond the displayed ones):
  `rowShPOfSh`   : `RowSh k row sh → RowShP k row sh`
  `rowShOfP`     : `RowShP k row sh → k + sh.length ≤ row.length → RowSh k row sh`
  `rowShPAppL`   : `RowShP k row (s1 ++ s2) → RowShP k row s1`
  `rowShPAppR`   : `RowShP k row (s1 ++ s2) → RowShP (k + s1.length) row s2`
  `rowShPApp`    : `RowShP k row s1 → RowShP (k + s1.length) row s2 → RowShP k row (s1 ++ s2)`
  `rowShPAt`     : `RowShP k row sh → sh[j]? = some it → k + j < row.length →
                    ∃ lb, row[k + j]? = some lb ∧ ishape it lb`
  `rowShPShort`  : `row.length ≤ k → RowShP k row sh`   (a window past the row end is vacuous)
  `rowShPNil`    : `RowShP k row []`
  `rowShPCongr`  : `RowShP k row sh → k = k' → RowShP k' row sh`
  `rowShPIff`    : `k + sh.length ≤ row.length → (RowShP k row sh ↔ RowSh k row sh)`

HONESTY.  Definitions and list arithmetic only.

**Reused:** `Ritem`, `ishape`, `RowSh` (AxSpinPOr).  New short names `RowShP`, `rowShP*`,
`rowShOfP` grepped absent from the tree.
-/
import Weak.AxSpinPOr

namespace Weak

open MachCSL MachCSL.Stdpp

/-- PREFIX shape match: every item whose row position is present in the row is matched there. -/
def RowShP (k : Nat) (row : List Lbl) (sh : List Ritem) : Prop :=
  ∀ j it, sh[j]? = some it → k + j < row.length → ∃ lb, row[k + j]? = some lb ∧ ishape it lb

theorem rowShPOfSh {k : Nat} {row : List Lbl} {sh : List Ritem} :
    RowSh k row sh → RowShP k row sh :=
  fun H j it Hj _ => H j it Hj

theorem rowShOfP {k : Nat} {row : List Lbl} {sh : List Ritem} :
    RowShP k row sh → k + sh.length ≤ row.length → RowSh k row sh := by
  intro H Hl j it Hj
  have : j < sh.length := (List.getElem?_eq_some_iff.1 Hj).1
  exact H j it Hj (by omega)

theorem rowShPIff {k : Nat} {row : List Lbl} {sh : List Ritem}
    (Hl : k + sh.length ≤ row.length) : RowShP k row sh ↔ RowSh k row sh :=
  ⟨fun H => rowShOfP H Hl, rowShPOfSh⟩

theorem rowShPAppL {k : Nat} {row : List Lbl} {s1 s2 : List Ritem} :
    RowShP k row (s1 ++ s2) → RowShP k row s1 :=
  fun H j it Hj Hk => H j it (lookup_app_l_Some Hj) Hk

theorem rowShPAppR {k : Nat} {row : List Lbl} {s1 s2 : List Ritem} :
    RowShP k row (s1 ++ s2) → RowShP (k + s1.length) row s2 := by
  intro H j it Hj Hk
  obtain ⟨lb, Hlb, Hs⟩ := H (s1.length + j) it (by
    rw [List.getElem?_append_right (by omega), show s1.length + j - s1.length = j by omega]
    exact Hj) (by omega)
  exact ⟨lb, by rw [show k + s1.length + j = k + (s1.length + j) by omega]; exact Hlb, Hs⟩

theorem rowShPApp {k : Nat} {row : List Lbl} {s1 s2 : List Ritem} :
    RowShP k row s1 → RowShP (k + s1.length) row s2 → RowShP k row (s1 ++ s2) := by
  intro H1 H2 j it Hj Hk
  by_cases hj : j < s1.length
  · rw [List.getElem?_append_left hj] at Hj
    exact H1 j it Hj Hk
  · rw [List.getElem?_append_right (by omega)] at Hj
    obtain ⟨lb, Hlb, Hs⟩ := H2 (j - s1.length) it Hj (by omega)
    exact ⟨lb, by rw [show k + s1.length + (j - s1.length) = k + j by omega] at Hlb; exact Hlb, Hs⟩

theorem rowShPAt {k : Nat} {row : List Lbl} {sh : List Ritem} {j : Nat} {it : Ritem} :
    RowShP k row sh → sh[j]? = some it → k + j < row.length →
      ∃ lb, row[k + j]? = some lb ∧ ishape it lb :=
  fun H Hj Hk => H j it Hj Hk

theorem rowShPShort {k : Nat} {row : List Lbl} {sh : List Ritem} :
    row.length ≤ k → RowShP k row sh :=
  fun Hl _ _ _ Hk => absurd Hk (by omega)

theorem rowShPNil {k : Nat} {row : List Lbl} : RowShP k row [] :=
  fun _ _ Hj => by simp at Hj

theorem rowShPCongr {k k' : Nat} {row : List Lbl} {sh : List Ritem} :
    RowShP k row sh → k = k' → RowShP k' row sh := fun H e => e ▸ H

end Weak
