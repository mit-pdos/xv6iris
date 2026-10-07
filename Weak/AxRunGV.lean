/-
Weak: **`runAtGraphValues GD i s0 s1`** (milestone A2, design §7.A) — the per-hart RUN PREMISE of
Tier A adequacy: a multi-step run of the athread semantics (`AxOpsem`) from `s0` to `s1` in which
every read step reads exactly `graphValue GD (i, s.atK)` (the GRAPH's value for that event, not
an angelic one) and every emitted event matches row `AxOpsem.grow GD i` at its index.  Built on
`rowEmittedFromRun` (AxRowConf) by pinning its read case's value.

Rocq: `iris/AxRunGV.v` @ xxvzwolszwmp.

## What this file proves

1. `runAtGraphValuesRefl`/`runAtGraphValuesTrans`: reflexive and closed under concatenation.
2. `runAtGraphValuesRowEmitted`: forgetting the value pinning recovers `rowEmittedFromRun`;
   `runAtGraphValuesSound`: hence an `astepOwn`-labelled `rtc`.
3. `runAtGraphValuesCoverage`/`runAtGraphValuesVisits`: a run from `⟨p, 0⟩` to row-length
   position visits every index `k < (grow GD i).length` (`coverageOfRow`/`consumed`).
4. `runAtGraphValuesNfGv`: the run unfolds to an `rtc` of `astepAnyNfGv` steps (AxWpDSteps).

## Deviations from Rocq

1. O2 STAGE C (AxRowConf deviation 1): no `T`/`img` oracle parameters anywhere —
   `astep_own_any_incl`, `run_at_graph_values_row_emitted`, `_sound`, `_coverage` lose them
   (`astepOwn`/`astepAny`/`consumed`/`rowEmittedFromRun` have none).  Rocq's fetch discussion
   (the omitted `RowEmitFetch` arm) is moot: a fetch is an `lbAdmin true (LIFetch ..)` label, so
   it is a `RunGVAdmin` step.
2. OWNER Q8 (AxAdequacy deviation 2): `astepAnyNfGv`'s program arm is `astepProgNf … img`,
   which carries the boot-image pin `WeakAxRealize.fetchPin GD.gdG.gxImg l` in place of Rocq's
   `wlabel_is_fetch l = false`.  Write/fence labels are pinned trivially (`fetchPin` is `True`
   off `LIFetch`), but an ADMIN step may now be a fetch, so `runAtGraphValuesNfGv` takes the
   extra premise `hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
   WeakAxRealize.fetchPin GD.gdG.gxImg l` (the admin steps of the program LTS are pinned; the
   graph tier's LTS `pstepPin img pstepEv` supplies it, cf. `AxAdequacy.astepProgNfOfPinned`).
   No Rocq file uses `run_at_graph_values_nf_gv`.
3. NAMES: camelCase; `S k` ↦ `k + 1`; `l !! k` ↦ `l[k]?`; `at_k` ↦ `.atK`; `AThread p k` ↦
   `⟨p, k⟩`.  `runAtGraphValuesVisits` uses the `coverage` lemma directly (no dummy `T`/`img`).

## Rocq → Lean name map

`astep_own_any_incl` `astepOwnAnyIncl`, `run_at_graph_values` `runAtGraphValues` (constructors
`RunGVDone/RunGVWrite/RunGVFence/RunGVAdmin/RunGVRead`), `run_at_graph_values_refl`
`runAtGraphValuesRefl`, `run_at_graph_values_trans` `runAtGraphValuesTrans`,
`run_at_graph_values_row_emitted` `runAtGraphValuesRowEmitted`, `run_at_graph_values_sound`
`runAtGraphValuesSound`, `run_at_graph_values_coverage` `runAtGraphValuesCoverage`,
`run_at_graph_values_visits` `runAtGraphValuesVisits`, `run_at_graph_values_nf_gv`
`runAtGraphValuesNfGv`.

**Dropped:** only the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxRowConf
import Weak.AxWpDSteps

namespace Weak

open MachCSL MachCSL.Stdpp
open Wlabel

/-! # 1. `runAtGraphValues` -/

/-- `astepOwn` is included in `astepAny`. -/
theorem astepOwnAnyIncl (row : List Lbl) (s s' : Athread) :
    astepOwn row s s' → astepAny row s s' :=
  fun h => (astepAnyOwn row s s').2 (.inl h)

section RunGV
variable (GD : Gdexec) (i : Agent)

/-- The run whose reads read the graph's values and whose events match the row. -/
inductive runAtGraphValues : Athread → Athread → Prop where
  | RunGVDone (t : Athread) : runAtGraphValues t t
  | RunGVWrite (p : Pexv6) (k : Nat) (d : Efab) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (lb : Lbl) (p' : Pexv6) (d' : Efab)
      (t' : Athread) :
      (AxOpsem.grow GD i)[k]? = some lb →
      aident lb = .IWrite rl base data.length →
      data = AxRowConf.lblWdata lb →
      pstepProg p d (LStore rl base data asrc vsrc) p' d' →
      runAtGraphValues ⟨p', k + 1⟩ t' →
      runAtGraphValues ⟨p, k⟩ t'
  | RunGVFence (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (lb : Lbl) (p' : Pexv6)
      (d' : Efab) (t' : Athread) :
      (AxOpsem.grow GD i)[k]? = some lb →
      (wlFence l).isSome = true →
      wlFence l = aidentFence (aident lb) →
      pstepProg p d l p' d' →
      runAtGraphValues ⟨p', k + 1⟩ t' →
      runAtGraphValues ⟨p, k⟩ t'
  | RunGVAdmin (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
      (t' : Athread) :
      lbAdmin true l →
      pstepProg p d l p' d' →
      runAtGraphValues ⟨p', k⟩ t' →
      runAtGraphValues ⟨p, k⟩ t'
  | RunGVRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread)
      (vs : List (BitVec 8)) (t' : Athread) :
      areadStep (AxOpsem.grow GD i) s id K →
      vs.length = aidentN id →
      graphValue GD (i, s.atK) = some vs →
      runAtGraphValues (K vs) t' →
      runAtGraphValues s t'

/-! ## 1.1 Reflexivity / transitivity -/

theorem runAtGraphValuesRefl (s : Athread) : runAtGraphValues GD i s s := .RunGVDone s

theorem runAtGraphValuesTrans (s1 s2 s3 : Athread) :
    runAtGraphValues GD i s1 s2 → runAtGraphValues GD i s2 s3 →
    runAtGraphValues GD i s1 s3 := by
  intro h12
  induction h12 with
  | RunGVDone t => exact id
  | RunGVWrite p k d rl base data asrc vsrc lb p' d' t' hrow hid hdata hstep _ ih =>
    exact fun h23 => .RunGVWrite p k d rl base data asrc vsrc lb p' d' s3 hrow hid hdata hstep
      (ih h23)
  | RunGVFence p k d l lb p' d' t' hrow hsome hidf hstep _ ih =>
    exact fun h23 => .RunGVFence p k d l lb p' d' s3 hrow hsome hidf hstep (ih h23)
  | RunGVAdmin p k d l p' d' t' hadm hstep _ ih =>
    exact fun h23 => .RunGVAdmin p k d l p' d' s3 hadm hstep (ih h23)
  | RunGVRead s id K vs t' hrd hlen hgv _ ih =>
    exact fun h23 => .RunGVRead s id K vs s3 hrd hlen hgv (ih h23)

/-! ## 1.2 Forgetting the pinning -/

theorem runAtGraphValuesRowEmitted (s t' : Athread) :
    runAtGraphValues GD i s t' → rowEmittedFromRun (AxOpsem.grow GD i) s t' := by
  intro h
  induction h with
  | RunGVDone t => exact .RowEmitDone t
  | RunGVWrite p k d rl base data asrc vsrc lb p' d' t' hrow hid hdata hstep _ ih =>
    exact .RowEmitWrite p k d rl base data asrc vsrc lb p' d' t' hrow hid hdata hstep ih
  | RunGVFence p k d l lb p' d' t' hrow hsome hidf hstep _ ih =>
    exact .RowEmitFence p k d l lb p' d' t' hrow hsome hidf hstep ih
  | RunGVAdmin p k d l p' d' t' hadm hstep _ ih =>
    exact .RowEmitAdmin p k d l p' d' t' hadm hstep ih
  | RunGVRead s id K vs t' hrd hlen _ _ ih =>
    exact .RowEmitRead s id K vs t' hrd hlen ih

/-- `runAtGraphValues` really is a run. -/
theorem runAtGraphValuesSound (s t' : Athread) :
    runAtGraphValues GD i s t' → rtc (astepOwn (AxOpsem.grow GD i)) s t' :=
  fun h => rowEmittedFromRunSound _ s t' (runAtGraphValuesRowEmitted GD i s t' h)

/-! ## 1.3 Coverage -/

theorem runAtGraphValuesCoverage (p p' : Pexv6) :
    runAtGraphValues GD i ⟨p, 0⟩ ⟨p', (AxOpsem.grow GD i).length⟩ →
    ∀ k, consumed (AxOpsem.grow GD i) ⟨p, 0⟩ ⟨p', (AxOpsem.grow GD i).length⟩ k ↔
      k < (AxOpsem.grow GD i).length := by
  intro hrun
  apply coverageOfRow
  exact rtc_subrel (astepOwnAnyIncl _) (runAtGraphValuesSound GD i _ _ hrun)

/-- Every row index is VISITED: some intermediate state sits exactly at `k`. -/
theorem runAtGraphValuesVisits (p p' : Pexv6) (k : Nat) :
    runAtGraphValues GD i ⟨p, 0⟩ ⟨p', (AxOpsem.grow GD i).length⟩ →
    k < (AxOpsem.grow GD i).length →
    ∃ s : Athread, s.atK = k := by
  intro hrun hk
  obtain ⟨s1, _, _, _, _, hk1, _⟩ := (runAtGraphValuesCoverage GD i p p' hrun k).2 hk
  exact ⟨s1, hk1⟩

end RunGV

/-! # 2. Relating to `astepAnyNfGv` (AxWpDSteps) -/

/-- The run unfolds to an `rtc` of graph-pinned single steps (deviation 2: the admin steps of the
program LTS are image-pinned, `hpin`). -/
theorem runAtGraphValuesNfGv (GD : Gdexec) (i : Agent)
    (hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l →
      WeakAxRealize.fetchPin GD.gdG.gxImg l)
    (s t' : Athread) :
    runAtGraphValues GD i s t' → rtc (astepAnyNfGv GD i) s t' := by
  intro h
  induction h with
  | RunGVDone t => exact rtc_refl _
  | RunGVWrite p k d rl base data asrc vsrc lb p' d' t' hrow hid hdata hstep _ ih =>
    refine rtc_l (.ANFGVProg _ _ ⟨LStore rl base data asrc vsrc, ?_, trivial⟩) ih
    have hwl : wlWr (LStore rl base data asrc vsrc) = aidentWr (aident lb) := by
      rw [hid]; rfl
    have hwd : wlWdata (LStore rl base data asrc vsrc) = lblData lb := by
      cases lb with
      | LStore rl' base' vs' k' =>
        simp only [AxRowConf.lblWdata] at hdata
        simp only [wlWdata, lblData, hdata]
      | LLoad => simp [aident] at hid
      | LFence => simp [aident] at hid
      | LRmw => simp [aident] at hid
    exact .AStepWrite p k d _ lb p' d' hrow rfl hwl hwd hstep
  | RunGVFence p k d l lb p' d' t' hrow hsome hidf hstep _ ih =>
    refine rtc_l (.ANFGVProg _ _ ⟨l, .AStepFence p k d l lb p' d' hrow hsome hidf hstep, ?_⟩) ih
    cases l <;> simp_all [wlFence, WeakAxRealize.fetchPin]
  | RunGVAdmin p k d l p' d' t' hadm hstep _ ih =>
    exact rtc_l (.ANFGVProg _ _ ⟨l, .AStepAdmin p k d l p' d' hadm hstep,
      hpin p d l p' d' hstep hadm⟩) ih
  | RunGVRead s id K vs t' hrd hlen hgv _ ih =>
    exact rtc_l (.ANFGVRead s id K vs hrd hgv hlen) ih

end Weak
