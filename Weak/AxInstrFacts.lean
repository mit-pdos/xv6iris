/-
Weak: **discharging the instruction-layer hypotheses** `Hwdat_spec`/`Hdata_tot`/`Hrdat_spec`
(and the n-byte `Hrdatn_spec`) from the graph/emission definitions, where they hold by
construction.

Rocq: `iris/AxInstrFacts.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxProtCov3`/`AxProtGate`(`N`) take, as section hypotheses over a fixed `GD : Gdexec`, a write
datum `wdat` with `Hwdat_spec` (a write's byte footprint is exactly `wdat w`), `Hdata_tot` (a
write has graph data) and a read datum `rdat` with `Hrdat_spec`.  This file supplies the data
and proves the facts off `graphData`/`graphValue`/`lblData`/`lblValue` (AxWp/AxOpsem),
`gwritesByte`/`greadsByte`/`gisW`/`gxLbl` (WeakRvwmoGraph) and the `Lbl` alphabet
(WeakAxiomatic).
- `hdataTotOfGraph`: unconditional (`lblData` is defined on exactly the `gisW` labels).
- `hwdatSpecOfGraph`: needs `gwfWr1` (every write is single-byte) — `gwf` only says a write's
  bytes are nonempty, and a multi-byte write makes the `↔` false.
- `hrdatSpecOfGraph`: needs `gwfRd1` (single-byte reads) AND a corrected domain (an actual read,
  `gxLbl … = some l ∧ lbIsR l`): Rocq's literal `gisW r = false` domain also contains fences and
  absent events, where the statement is false.
- `hrdatnSpecOfGraph` (n-byte): same corrected domain, off `gwf` alone (its label-shape clause
  gives `vs.length = ts.length`, so `zip` pairs the footprint losslessly).

Fetches: nothing here depends on how fetches are represented — the lemmas are about the label
alphabet `Lbl` (which has no fetch constructor) and `lbIsR`/`lbIsW`, whatever events carry them.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); no duplicated Rocq names, no Lean-only helpers.
2. `bv_0 8` ↦ `0#8`; `Z` ↦ `Int`; `l !! j` ↦ `l[j]?`; `l.*2` ↦ `l.map Prod.snd`.  `rdat`'s
   `Z * nat * bv 8` (left-nested) is Lean's right-nested `Int × Nat × BitVec 8`: Rocq
   `.1.1`/`.1.2`/`.2` ↦ `.1`/`.2.1`/`.2.2`.
3. Section parameters become explicit arguments, taken only where used (as Rocq's sections do):
   `wdatOf GD`, `hwdatSpecOfGraph GD Hw1`, `rdatOf GD`, `hrdatSpecOfGraph GD Hr1`,
   `rdatnOf GD`, `hrdatnSpecOfGraph GD Hgwf`.

## Name map (Rocq → Lean)

`hdata_tot_of_graph` ↦ `hdataTotOfGraph`, `gwf_wr1` ↦ `gwfWr1`, `wdat_of` ↦ `wdatOf`,
`hwdat_spec_of_graph` ↦ `hwdatSpecOfGraph`, `gwf_rd1` ↦ `gwfRd1`, `rdat_of` ↦ `rdatOf`,
`hrdat_spec_of_graph` ↦ `hrdatSpecOfGraph`, `rdatn_of` ↦ `rdatnOf`,
`hrdatn_spec_of_graph` ↦ `hrdatnSpecOfGraph`.

## Dropped

None.
-/
import Weak.AxWp

namespace Weak

open Lbl

/-! # 1. `Hdata_tot`: unconditional -/

theorem hdataTotOfGraph (GD : Gdexec) (w : Geid) :
    gisW GD.gdG w = true → ∃ data, graphData GD w = some data := by
  unfold gisW graphData
  intro hisw
  cases hl : gxLbl GD.gdG w with
  | none => rw [hl] at hisw; cases hisw
  | some l =>
    rw [hl] at hisw
    cases l with
    | LLoad => simp [lbIsW] at hisw
    | LStore rl base vs k => exact ⟨vs, rfl⟩
    | LFence => simp [lbIsW] at hisw
    | LRmw aq rl base ts rvs wvs k => exact ⟨wvs, rfl⟩
    | LIo => simp [lbIsW] at hisw

/-! # 2. `Hwdat_spec`: under `gwfWr1` -/

/-- The missing well-formedness fact: every write event's byte footprint is a SINGLETON. -/
def gwfWr1 (G : Gexec) : Prop :=
  ∀ (w : Geid) (l : Lbl) (base : Int) (vs : List (BitVec 8)),
    gxLbl G w = some l → lbWr l = some (base, vs) → ∃ v, vs = [v]

def wdatOf (GD : Gdexec) (w : Geid) : Int × BitVec 8 :=
  match gxLbl GD.gdG w with
  | some l =>
      match lbWr l with
      | some (base, v :: _) => (base, v)
      | _ => (0, 0#8)
  | none => (0, 0#8)

theorem hwdatSpecOfGraph (GD : Gdexec) (Hw1 : gwfWr1 GD.gdG) (w : Geid) (a : Int)
    (v : BitVec 8) :
    gisW GD.gdG w = true →
    (gwritesByte GD.gdG w a v ↔ (a, v) = wdatOf GD w) := by
  unfold gisW
  intro hisw
  cases hl : gxLbl GD.gdG w with
  | none => rw [hl] at hisw; cases hisw
  | some l =>
    rw [hl] at hisw
    obtain ⟨base, vs, hwr⟩ := lbIsWWr l hisw
    obtain ⟨v0, rfl⟩ := Hw1 w l base vs hl hwr
    have hwdat : wdatOf GD w = (base, v0) := by
      unfold wdatOf; rw [hl]; simp only []; rw [hwr]
    rw [hwdat]
    unfold gwritesByte
    constructor
    · rintro ⟨l', base', vs', j, hl', hwr', hj, ha⟩
      rw [hl] at hl'
      cases hl'
      rw [hwr] at hwr'
      cases hwr'
      cases j with
      | zero =>
        simp at hj
        subst hj
        unfold accAddr at ha
        simp at ha
        rw [ha]
      | succ j' => simp at hj
    · intro heq
      cases heq
      exact ⟨l, a, [v], 0, hl, hwr, rfl, by unfold accAddr; simp⟩

/-! # 3. `Hrdat_spec`: under `gwfRd1`, over the corrected (read-only) domain -/

/-- The missing well-formedness fact: every read event's byte footprint is a SINGLETON. -/
def gwfRd1 (G : Gexec) : Prop :=
  ∀ (r : Geid) (l : Lbl) (base : Int) (ts : List Nat) (vs : List (BitVec 8)),
    gxLbl G r = some l → lbRd l = some (base, ts, vs) →
    ∃ t v, ts = [t] ∧ vs = [v]

def rdatOf (GD : Gdexec) (r : Geid) : Int × Nat × BitVec 8 :=
  match gxLbl GD.gdG r with
  | some l =>
      match lbRd l with
      | some (base, t :: _, v :: _) => (base, t, v)
      | _ => (0, 0, 0#8)
  | none => (0, 0, 0#8)

/-- Corrected domain: `r` is an ACTUAL read (its label satisfies `lbIsR`), not merely
`gisW r = false` (see the header). -/
theorem hrdatSpecOfGraph (GD : Gdexec) (Hr1 : gwfRd1 GD.gdG) (r : Geid) (l : Lbl)
    (Hl : gxLbl GD.gdG r = some l) (Hisr : lbIsR l = true) :
    graphValue GD r = some [(rdatOf GD r).2.2] ∧
    greadsByte GD.gdG r (rdatOf GD r).1 (rdatOf GD r).2.1 (rdatOf GD r).2.2 := by
  obtain ⟨base, ts, vs, hrd⟩ := lbIsRRd l Hisr
  obtain ⟨t0, v0, rfl, rfl⟩ := Hr1 r l base ts vs Hl hrd
  have hrdat : rdatOf GD r = (base, t0, v0) := by
    unfold rdatOf; rw [Hl]; simp only []; rw [hrd]
  rw [hrdat]
  refine ⟨?_, ?_⟩
  · unfold graphValue
    rw [Hl]
    cases l with
    | LLoad aq b ts vs => simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd; obtain ⟨_, _, rfl⟩ := hrd; rfl
    | LStore => simp [lbRd] at hrd
    | LFence => simp [lbRd] at hrd
    | LIo => simp [lbRd] at hrd
    | LRmw aq rl b ts rvs wvs k =>
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd; obtain ⟨_, _, rfl⟩ := hrd; rfl
  · exact ⟨l, base, [t0], [v0], 0, Hl, hrd, rfl, rfl, by unfold accAddr; simp⟩

/-! # 4. `Hrdatn_spec` (n-byte, `AxProtGateN`'s corrected domain): from `gwf` alone -/

def rdatnOf (GD : Gdexec) (r : Geid) : Int × List (Nat × BitVec 8) :=
  match gxLbl GD.gdG r with
  | some l =>
      match lbRd l with
      | some (base, ts, vs) => (base, ts.zip vs)
      | none => (0, [])
  | none => (0, [])

theorem hrdatnSpecOfGraph (GD : Gdexec) (Hgwf : gwf GD.gdG) (r : Geid) (l : Lbl)
    (Hl : gxLbl GD.gdG r = some l) (Hisr : lbIsR l = true) :
    graphValue GD r = some ((rdatnOf GD r).2.map Prod.snd) ∧
    ∀ (j : Nat) t v, (rdatnOf GD r).2[j]? = some (t, v) →
      greadsByte GD.gdG r ((rdatnOf GD r).1 + (j : Int)) t v := by
  obtain ⟨base, ts, vs, hrd⟩ := lbIsRRd l Hisr
  have hshape := gwfLblShape GD.gdG r l Hgwf Hl
  have hlen : vs.length = ts.length := by
    cases l with
    | LLoad aq b ts' vs' =>
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨_, rfl, rfl⟩ := hrd; exact hshape
    | LStore => simp [lbRd] at hrd
    | LFence => simp [lbRd] at hrd
    | LIo => simp [lbRd] at hrd
    | LRmw aq rl b ts' rvs' wvs' k =>
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd
      obtain ⟨_, rfl, rfl⟩ := hrd; exact hshape.2.2
  have hrdatn : rdatnOf GD r = (base, ts.zip vs) := by
    unfold rdatnOf; rw [Hl]; simp only []; rw [hrd]
  rw [hrdatn]
  have hsnd : (ts.zip vs).map Prod.snd = vs := List.map_snd_zip (by omega)
  refine ⟨?_, ?_⟩
  · unfold graphValue
    rw [Hl, hsnd]
    cases l with
    | LLoad aq b ts' vs' =>
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd; obtain ⟨_, _, rfl⟩ := hrd; rfl
    | LStore => simp [lbRd] at hrd
    | LFence => simp [lbRd] at hrd
    | LIo => simp [lbRd] at hrd
    | LRmw aq rl b ts' rvs' wvs' k =>
      simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at hrd; obtain ⟨_, _, rfl⟩ := hrd; rfl
  · intro j t v hj
    simp only [] at hj
    rw [List.getElem?_zip_eq_some] at hj
    obtain ⟨ht, hv⟩ := hj
    exact ⟨l, base, ts, vs, j, Hl, hrd, ht, hv, rfl⟩

end Weak
