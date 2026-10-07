/-
Weak: **`epiReloadTrivial1hart`: with ONE hart, `epiReloadSound`'s conclusion follows from its
PURE premises alone** (no WPd, no `Hrun`, no protocol, no adequacy).

Rocq: `iris/AxEpiTrivial.v` @ xxvzwolszwmp.

Argument (per byte `j < 8` of the reload `(0,1)`, which reads `a + j` at timestamp `t` with
value `v`):
- `Hok_ld`'s history clause gives `gwritesByte (0,0) (a+j) (sdData[j])`, and `(0,0)` is
  po-before `(0,1)`, hence VISIBLE (`gvisible` includes `gpo`); `gloadValue`'s maximality gives
  `1 ≤ gwix (0,0) ≤ t`, so the read is not from the image;
- so `t = t' + 1` and the rf-write `w` is a write in `gxGmo`; `Hharts` puts it on hart 0,
  `Hlen` bounds its index by 2, and the reload `(0,1)` is a non-write (`Hok_ld`), so
  `w = (0,0)`;
- `Hw_sd` then pins `v = sdData[j]`.

So `epiReloadSound` is a pipeline milestone, not a separation result: ownership is not needed
to get its conclusion with one hart.

## Deviations from Rocq

1. O2 STAGE C (fetches are not graph events; as `AxEpiAdeq` deviation 1): the row is
   `[SD @(0,0); LD @(0,1)]` (Rocq `[F0; SD; F1; LD]`).  So `sd_write_ok GD 0 1 a` ↦
   `sdWriteOk GD 0 0 a`, `ldsp_own_ok GD 0 3 (0,1) a (writen_hist (0,1) …)` ↦
   `ldspOwnOk GD 0 1 (0,0) a (writenHist (0,0) …)`, `length (grow GD 0) = 4` ↦ `= 2`, and the
   conclusion is at `(0,1)` (Rocq `(0,3)`).  The fetch-event premises `Hnw_sd`/`Hnw_ld`
   (`gis_w` of `(0,0)`/`(0,2)`) are DROPPED (no fetch events); the reload's own non-write fact
   (in `ldspOwnOk`) excludes the one remaining non-spill position.
2. TYPES: `Z.of_nat j` ↦ `(j : Int)`; `` `{!axpol} `` ↦ `[Axpol]`.

**Rocq → Lean name map.**  `epi_reload_trivial_1hart` `epiReloadTrivial1hart` (not in the
duplicated-name table).

**Dropped:** nothing (Rocq 1 lemma; Lean 1).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxEpiAdeq
import Weak.WeakRvwmoLock

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std

/-- Same names as `epiReloadSound`'s premises; only the pure ones, and not even all of them.
Stated for ANY policy (`ldspOwnOk` mentions `lobp`/`sPol`, but the proof uses none of the policy
clauses); `epiReloadSound` uses `epiPol`. -/
theorem epiReloadTrivial1hart [Axpol] (GD : Gdexec) (a : Int)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hok_ld : ldspOwnOk GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2) :
    graphValue GD (0, 1) = some sdData := by
  obtain ⟨Hwf, _, Hlv, _⟩ := Hcons
  obtain ⟨_, _, _, Hr_nw, _, ⟨aq, ts0, vs0, Hlbl, Hts, Hvs⟩, Hwr, _, _, Hpo⟩ := Hok_ld
  obtain ⟨_, Hsd_bytes, _⟩ := Hw_sd
  have Hsd_len : sdData.length = 8 := rfl
  rw [graphValue, Hlbl]
  simp only [Option.bind_some, lblValue]
  congr 1
  apply List.ext_getElem?
  intro j
  by_cases Hj : j < 8
  · obtain ⟨t, Ht⟩ : ∃ t, ts0[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, Hv⟩ : ∃ v, vs0[j]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨vd, Hvd⟩ : ∃ v, sdData[j]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Hv, Hvd]
    -- the spill writes `a + j` with `vd`
    have HH : (writenHist (0, 0) sdData epiHs0)[j]? = some [((0, 0), vd)] := by
      rw [gsdldHs1, List.getElem?_map, Hvd]; rfl
    have Hw1 : gwritesByte GD.gdG (0, 0) (a + (j : Int)) vd :=
      Hwr j _ HH ((0, 0), vd) (List.mem_singleton.2 rfl)
    -- the reload reads `a + j` at `t` with `v`
    have Hrd : greadsByte GD.gdG (0, 1) (a + (j : Int)) t v :=
      ⟨_, a, ts0, vs0, j, Hlbl, rfl, Ht, Hv, rfl⟩
    obtain ⟨Hrf, Hmax⟩ := Hlv _ _ _ _ Hrd
    -- the spill is po-before, hence visible: `1 ≤ gwix (0,0) ≤ t`
    have Hle := Hmax _ _ Hw1 (Or.inr Hpo)
    have Hpos := WeakRvwmoGraph.gwixPos _ _ (gwritesByteGwrites _ _ _ _ Hwf Hw1)
    cases t with
    | zero => omega
    | succ t' =>
      obtain ⟨w, Hat, Hwb, _⟩ := Hrf
      obtain ⟨Hw_in, _⟩ := gwriteAtInv _ _ _ Hwf.1 Hat
      have Hw_gmo : w ∈ GD.gdG.gxGmo := (List.mem_filter.1 Hw_in).1
      have Hw0 := Hharts _ Hw_gmo
      obtain ⟨wi, wk⟩ := w
      simp only at Hw0
      subst Hw0
      -- the rf-write is a hart-0 event within the 2-event row: it is the spill
      have Hwk : wk < 2 := by
        obtain ⟨l, _, _, _, hl, _⟩ := Hwb
        rw [← Hlen]
        unfold gxLbl at hl
        unfold AxOpsem.grow growG
        cases hp : GD.gdG.gxProg[0]? with
        | none => rw [hp] at hl; cases hl
        | some p =>
          rw [hp] at hl
          simp only [Option.bind_some] at hl
          exact (List.getElem?_eq_some_iff.1 hl).1
      match wk, Hwk, Hwb with
      | 0, _, Hwb =>
        obtain ⟨j', Hj', Hj'a⟩ := Hsd_bytes _ _ Hwb
        have : j' = j := by omega
        subst this
        rw [Hvd] at Hj'
        exact Hj'.symm
      | 1, _, Hwb =>
        have := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ Hwb
        rw [Hr_nw] at this
        cases this
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end Weak
