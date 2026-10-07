/-
Weak: **THE gco-IMMEDIATE PREDECESSOR** `axprotImmpred` (C6 coverage, continued from
`Weak.AxProtInst`).

Rocq: `iris/AxProtCov.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The twin induction that would close `AxCov.classEpochGmoMono` for the real run-shared ghost name
needs, for each write `w` to a byte, its gco-IMMEDIATE predecessor `w0`: `na !! w` holds the
persistent `histSnap` (plus the data fact), `ea !! w` the exclusive `tokTie` keyed at `w0` — both
built from the SAME `protInvWriteStep` call (`AxProtInst.flowEqOwnedWriteChainSnap`, §4 there).
This file builds the "which `w0`" bookkeeping once:

§1 `axprotImmpred GD e`: the LAST element of `gxGmo` satisfying `axprotPred`'s filter (`none` iff
`e` is the first write to its byte); `axprotImmpredPred` (it is a predecessor) and
`axprotImmpredTop` (every other predecessor is gmo-before it).
§2 The remaining gap (Rocq header, recorded, nothing proved): (a) ASSEMBLY of `na`/`ea` as
functions of `GD` and the per-event line of `AxAdequacyL.ordEaTodoL` (continued in AxProtCov2/3);
(b) the independent C9 blocker — `LPredClosedFlow GD proc` for a real scheduler run is open
(AxAdequacyL §6), so over `L := gxGmo` alone the coverage corollary is content-free.

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below); none of the three names is duplicated in the Rocq tree.
2. VOCABULARY (as `AxProtInst` deviation 2): `last l` ↦ `l.getLast?`, `filter` ↦ `List.filter`,
   `gd_g GD` ↦ `GD.gdG`, `NoDup` ↦ `List.Nodup`.
3. Lean-only helper `AxProtCov.lastFilterSome` (stdpp `last_filter_Some`, absent from the Lean
   shims), file-qualified.

**Rocq → Lean name map.**  `axprot_immpred` `axprotImmpred`, `axprot_immpred_pred`
`axprotImmpredPred`, `axprot_immpred_top` `axprotImmpredTop`; stdpp `last_filter_Some`
`AxProtCov.lastFilterSome`.

**Not ported:** the §3 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtInst

namespace Weak

open MachCSL MachCSL.Stdpp

/-! # 1. `axprotImmpred`: THE gco-IMMEDIATE PREDECESSOR -/

/-- `w`'s gco-immediate predecessor: the LAST (gmo-latest) element of `gxGmo` satisfying
`axprotPred`'s filter — `none` iff `w` is the first write to its byte. -/
def axprotImmpred (GD : Gdexec) (e : Geid) : Option Geid :=
  (GD.gdG.gxGmo.filter (fun w => gcoB GD.gdG w e)).getLast?

/-- stdpp `last_filter_Some`: the last element satisfying `p` splits the list, with nothing after
it satisfying `p`. -/
theorem AxProtCov.lastFilterSome {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (x : α), (l.filter p).getLast? = some x →
      ∃ l1 l2, l = l1 ++ x :: l2 ∧ ∀ y ∈ l2, p y = false
  | [], x, h => by simp at h
  | a :: t, x, h => by
    by_cases ht : t.filter p = []
    · have hx : p a = true ∧ a = x := by
        cases hpa : p a <;> simp [hpa, ht] at h
        exact ⟨rfl, h⟩
      obtain ⟨_, rfl⟩ := hx
      refine ⟨[], t, rfl, fun y hy => ?_⟩
      rw [List.filter_eq_nil_iff] at ht
      simpa using ht y hy
    · have h' : (t.filter p).getLast? = some x := by
        cases hpa : p a
        · simpa [List.filter_cons, hpa] using h
        · rw [List.filter_cons, hpa, if_pos rfl, List.getLast?_cons] at h
          obtain ⟨z, hz⟩ : ∃ z, (t.filter p).getLast? = some z := by
            cases hg : (t.filter p).getLast? with
            | none => exact absurd (List.getLast?_eq_none_iff.mp hg) ht
            | some z => exact ⟨z, rfl⟩
          rw [hz] at h; simp at h; rw [hz, h]
      obtain ⟨l1, l2, heq, hafter⟩ := AxProtCov.lastFilterSome p t x h'
      exact ⟨a :: l1, l2, by rw [heq]; rfl, hafter⟩

/-- `axprotImmpred` really does pick a member of `axprotPred`. -/
theorem axprotImmpredPred (GD : Gdexec) (e w0 : Geid) :
    axprotImmpred GD e = some w0 → w0 ∈ axprotPred GD e := by
  intro hl
  rw [axprotPred, elemOfListToSet]
  exact List.mem_of_getLast? hl

/-- `axprotImmpred` really is the IMMEDIATE one: every OTHER predecessor of `e` is gmo-before it. -/
theorem axprotImmpredTop (GD : Gdexec) (Hnd : GD.gdG.gxGmo.Nodup) (e w0 w' : Geid) :
    axprotImmpred GD e = some w0 → w' ∈ axprotPred GD e → w' ≠ w0 →
      gmoLt GD.gdG w' w0 := by
  intro hl hin' hne
  obtain ⟨l1, l2, heq, hafter⟩ := AxProtCov.lastFilterSome _ _ _ hl
  rw [axprotPred, elemOfListToSet, List.mem_filter] at hin'
  obtain ⟨hmem, hp⟩ := hin'
  rw [heq, List.mem_append] at hmem
  rcases hmem with hin1 | hin2
  · obtain ⟨i, hi⟩ := elem_of_list_lookup_1 hin1
    have hilt : i < l1.length := lookup_lt_Some hi
    have hgx : GD.gdG.gxGmo[i]? = some w' := by
      rw [heq, List.getElem?_append_left hilt]; exact hi
    have hgx0 : GD.gdG.gxGmo[l1.length]? = some w0 := by
      rw [heq]; exact list_lookup_middle rfl
    have hposw' := gposOfLookup _ _ _ Hnd hgx
    have hposw0 := gposOfLookup _ _ _ Hnd hgx0
    refine ⟨elem_of_list_lookup_2 hgx, elem_of_list_lookup_2 hgx0, ?_⟩
    rw [hposw', hposw0]; exact hilt
  · rcases List.mem_cons.mp hin2 with h | hin2
    · exact absurd h hne
    · rw [hafter w' hin2] at hp; cases hp

end Weak
