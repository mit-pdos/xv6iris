/-
Weak: **row conformance as one inductive predicate** — `rowEmittedFromRun row s t'`: "the row
IS exactly the sequence of labels emitted by the hart's opax run from `s` to `t'`" (LB/AxSL
epilogue hardening, step 1a).

Rocq: `iris/AxRowConf.v` @ xxvzwolszwmp.

## What this file proves

The predicate is built from `AxOpsem`'s own step relations (`pstepProg`, `AxOpsem.astepProg`'s
premises, `areadStep`).  Its WRITE case carries the store's bytes (`data = AxRowConf.lblWdata
lb`), which `AxOpsem.astepProg.AStepWrite` also checks (`wlWdata l = lblData lb`).  The PLIC
wire is deliberately NOT a case (a row records the program's emissions, not interrupt
delivery; `astepOwn` excludes it too).
- `rowEmittedFromRunSound`: the predicate really is a run — an `astepOwn`-labelled `rtc`.
- `rowLookupAgree`: `row[k]?` is a partial function of `k` (the trick behind the extraction
  lemmas: no `pstepProg` determinism is needed).
- `rowEmittedHVsvs(Gen)`: given a WRITE identity at the start position and a run that leaves
  it, the run performs a matching `LStore` step whose bytes are the row's recorded payload.
- `rowEmittedShapes(Gen)`: the same for a FENCE identity.

As in Rocq, `epilogue_consecutive_ret_conf` (step 1b) is NOT proved here.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; `AxOpsem` deviation 2): Rocq's constructor
   `RowEmitFetch` (a fetch consuming the row's `LLoad false …` item, answered by the oracle
   `fetch_answers T img`) is DROPPED, and with it the section parameters `T`/`img` (deleted
   from `astepOwn` by Q-C2).  A fetch is now an administrative label (`AxOpsem.lbAdminAx true (LIFetch
   ..)`), so a run's fetches are `RowEmitAdmin` steps; no row item is consumed.  The
   extraction lemmas lose their (contradictory) fetch case.
2. NAMES: camelCase; `l !! k` ↦ `l[k]?`; `S k` ↦ `k + 1`; `is_Some o` ↦ `o.isSome = true`;
   `at_k` ↦ `.atK`; `bv 8` ↦ `BitVec 8`.  `lbl_wdata` is a duplicated Rocq name (AxPair has a
   Wlabel one): declared as `AxRowConf.lblWdata`.

## Rocq → Lean name map

`lbl_wdata` `AxRowConf.lblWdata`, `row_emitted_from_run` `rowEmittedFromRun` (constructors
`RowEmitDone/RowEmitWrite/RowEmitFence/RowEmitAdmin/RowEmitRead`), `row_emitted_from_run_sound`
`rowEmittedFromRunSound`, `row_lookup_agree` `rowLookupAgree`, `row_emitted_HVsvs_gen`
`rowEmittedHVsvsGen`, `row_emitted_HVsvs` `rowEmittedHVsvs`, `row_emitted_shapes_gen`
`rowEmittedShapesGen`, `row_emitted_shapes` `rowEmittedShapes`.

**Dropped:** the constructor `RowEmitFetch` (deviation 1).  Nothing else.
-/
import Weak.AxOpsem

namespace Weak

open MachCSL
open Wlabel

section RowConf
variable (row : List Lbl)

/-- The row's own recorded WRITE bytes at a label. -/
def AxRowConf.lblWdata (lb : Lbl) : List (BitVec 8) :=
  match lb with
  | .LStore _ _ vs _ => vs
  | _ => []

/-- "The row is exactly the run's emission" (deviation 1: no fetch case). -/
inductive rowEmittedFromRun : Athread → Athread → Prop where
  | RowEmitDone (t : Athread) : rowEmittedFromRun t t
  | RowEmitWrite (p : Pexv6) (k : Nat) (d : Efab) (rl : Bool) (base : Int)
      (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (lb : Lbl) (p' : Pexv6) (d' : Efab)
      (t' : Athread) :
      row[k]? = some lb →
      aident lb = .IWrite rl base data.length →
      data = AxRowConf.lblWdata lb →
      pstepProg p d (LStore rl base data asrc vsrc) p' d' →
      rowEmittedFromRun ⟨p', k + 1⟩ t' →
      rowEmittedFromRun ⟨p, k⟩ t'
  | RowEmitFence (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (lb : Lbl) (p' : Pexv6)
      (d' : Efab) (t' : Athread) :
      row[k]? = some lb →
      (wlFence l).isSome = true →
      wlFence l = aidentFence (aident lb) →
      pstepProg p d l p' d' →
      rowEmittedFromRun ⟨p', k + 1⟩ t' →
      rowEmittedFromRun ⟨p, k⟩ t'
  | RowEmitAdmin (p : Pexv6) (k : Nat) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab)
      (t' : Athread) :
      AxOpsem.lbAdminAx true l →
      pstepProg p d l p' d' →
      rowEmittedFromRun ⟨p', k⟩ t' →
      rowEmittedFromRun ⟨p, k⟩ t'
  | RowEmitRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread)
      (vs : List (BitVec 8)) (t' : Athread) :
      areadStep row s id K →
      vs.length = aidentN id →
      rowEmittedFromRun (K vs) t' →
      rowEmittedFromRun s t'

/-- `rowEmittedFromRun` really is a run: an `astepOwn`-labelled `rtc`. -/
theorem rowEmittedFromRunSound (t1 t2 : Athread) :
    rowEmittedFromRun row t1 t2 → rtc (astepOwn row) t1 t2 := by
  intro h
  induction h with
  | RowEmitDone t => exact rtc_refl _
  | RowEmitWrite p k d rl base data asrc vsrc lb p' d' t' hrow hid hdata hstep _ ih =>
    refine rtc_l (Or.inl ⟨LStore rl base data asrc vsrc, ?_⟩) ih
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
      | LIo => simp [aident] at hid
    exact .AStepWrite p k d _ lb p' d' hrow rfl hwl hwd hstep
  | RowEmitFence p k d l lb p' d' t' hrow hsome hidf hstep _ ih =>
    exact rtc_l (Or.inl ⟨_, .AStepFence p k d l lb p' d' hrow hsome hidf hstep⟩) ih
  | RowEmitAdmin p k d l p' d' t' hadm hstep _ ih =>
    exact rtc_l (Or.inl ⟨_, .AStepAdmin p k d l p' d' hadm hstep⟩) ih
  | RowEmitRead s id K vs t' hrd hlen _ ih =>
    exact rtc_l (Or.inr ⟨id, K, vs, hrd, hlen, rfl⟩) ih

/-- Two row entries at the SAME position agree. -/
theorem rowLookupAgree (k : Nat) (lb lb0 : Lbl) :
    row[k]? = some lb → row[k]? = some lb0 → lb = lb0 := by
  intro h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

theorem rowEmittedHVsvsGen (s t' : Athread) :
    rowEmittedFromRun row s t' →
    ∀ lb rl base n,
      row[s.atK]? = some lb → aident lb = .IWrite rl base n → t'.atK ≠ s.atK →
      ∃ (p0 : Pexv6) (d : Efab) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : Pexv6)
        (d' : Efab),
        pstepProg p0 d (LStore rl base data asrc vsrc) p' d' ∧
        data.length = n ∧ data = AxRowConf.lblWdata lb := by
  intro h
  induction h with
  | RowEmitDone t =>
    intro lb rl base n _ _ hne
    exact absurd rfl hne
  | RowEmitWrite p k d rl0 base0 data0 asrc0 vsrc0 lb0 p' d' t' hrow0 hid0 hdata0 hstep0 _ _ =>
    intro lb rl base n hrow hid _
    have heq := rowLookupAgree row k lb lb0 hrow hrow0
    subst heq
    rw [hid0] at hid
    injection hid with hrl hbase hn
    subst hrl hbase
    exact ⟨p, d, data0, asrc0, vsrc0, p', d', hstep0, hn, hdata0⟩
  | RowEmitFence p k d l0 lb0 p' d' t' hrow0 hsome0 hidf0 hstep0 _ _ =>
    intro lb rl base n hrow hid _
    have heq := rowLookupAgree row k lb lb0 hrow hrow0
    subst heq
    rw [hid] at hidf0
    simp only [aidentFence] at hidf0
    rw [hidf0] at hsome0
    exact absurd hsome0 (by simp)
  | RowEmitAdmin p k d l0 p' d' t' _ _ _ ih =>
    intro lb rl base n hrow hid hne
    exact ih lb rl base n hrow hid hne
  | RowEmitRead s0 id0 K0 vs0 t' hrd0 _ _ _ =>
    intro lb rl base n hrow hid _
    obtain ⟨lb1, hrow1, hid1, hsome1, _⟩ := hrd0
    have heq := rowLookupAgree row s0.atK lb lb1 hrow hrow1
    subst heq
    rw [hid] at hid1
    subst hid1
    simp [aidentRd] at hsome1

theorem rowEmittedHVsvs (p : Pexv6) (k : Nat) (lb : Lbl) (rl : Bool) (base : Int) (n : Nat)
    (t' : Athread) :
    row[k]? = some lb → aident lb = .IWrite rl base n → t'.atK ≠ k →
    rowEmittedFromRun row ⟨p, k⟩ t' →
    ∃ (p0 : Pexv6) (d : Efab) (data : List (BitVec 8)) (asrc vsrc : List Dsrc) (p' : Pexv6)
      (d' : Efab),
      pstepProg p0 d (LStore rl base data asrc vsrc) p' d' ∧
      data.length = n ∧ data = AxRowConf.lblWdata lb :=
  fun hrow hid hne hconf => rowEmittedHVsvsGen row ⟨p, k⟩ t' hconf lb rl base n hrow hid hne

/-- The symmetric extraction for a FENCE-shaped row entry. -/
theorem rowEmittedShapesGen (s t' : Athread) :
    rowEmittedFromRun row s t' →
    ∀ lb pr pw sr sw,
      row[s.atK]? = some lb → aident lb = .IFence pr pw sr sw → t'.atK ≠ s.atK →
      ∃ (p0 : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab),
        wlFence l = some (pr, pw, sr, sw) ∧ pstepProg p0 d l p' d' := by
  intro h
  induction h with
  | RowEmitDone t =>
    intro lb pr pw sr sw _ _ hne
    exact absurd rfl hne
  | RowEmitWrite p k d rl0 base0 data0 asrc0 vsrc0 lb0 p' d' t' hrow0 hid0 _ _ _ _ =>
    intro lb pr pw sr sw hrow hid _
    have heq := rowLookupAgree row k lb lb0 hrow hrow0
    subst heq
    rw [hid0] at hid
    cases hid
  | RowEmitFence p k d l0 lb0 p' d' t' hrow0 _ hidf0 hstep0 _ _ =>
    intro lb pr pw sr sw hrow hid _
    have heq := rowLookupAgree row k lb lb0 hrow hrow0
    subst heq
    rw [hid] at hidf0
    exact ⟨p, d, l0, p', d', hidf0, hstep0⟩
  | RowEmitAdmin p k d l0 p' d' t' _ _ _ ih =>
    intro lb pr pw sr sw hrow hid hne
    exact ih lb pr pw sr sw hrow hid hne
  | RowEmitRead s0 id0 K0 vs0 t' hrd0 _ _ _ =>
    intro lb pr pw sr sw hrow hid _
    obtain ⟨lb1, hrow1, hid1, hsome1, _⟩ := hrd0
    have heq := rowLookupAgree row s0.atK lb lb1 hrow hrow1
    subst heq
    rw [hid] at hid1
    subst hid1
    simp [aidentRd] at hsome1

theorem rowEmittedShapes (p : Pexv6) (k : Nat) (lb : Lbl) (pr pw sr sw : Bool) (t' : Athread) :
    row[k]? = some lb → aident lb = .IFence pr pw sr sw → t'.atK ≠ k →
    rowEmittedFromRun row ⟨p, k⟩ t' →
    ∃ (p0 : Pexv6) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab),
      wlFence l = some (pr, pw, sr, sw) ∧ pstepProg p0 d l p' d' :=
  fun hrow hid hne hconf => rowEmittedShapesGen row ⟨p, k⟩ t' hconf lb pr pw sr sw hrow hid hne

end RowConf

end Weak
