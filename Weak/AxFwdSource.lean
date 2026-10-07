/-
Weak: **PURE store forwarding under the cat model** — `rfiFwdSource` and its epilogue instance
`epiReloadFwd`.

Rocq: `iris/AxFwdSource.v` @ xxvzwolszwmp.

## What this file proves

`rfiFwdSource`: let `r` be an n-byte load of hart `i` at `a..a+n-1`, and `w` a store of hart
`i`, po-before `r`, writing EVERY byte `a..a+n-1` (full coverage), with no same-hart write to any
of those bytes po-between `w` and `r` (po-latest).  If `gmoLt r w` (the FORWARDING arm: the load
is performed before the store is globally visible), then every byte's rf-source is `w` and `r`
reads `w`'s data.

Argument (per byte `a + j`): `gloadValue` names a source `w''` that is `gvisible` and
gwix-maximal among visible same-byte writes.  `w` itself is visible (po), so `gwix w ≤ t`.  The
source is gmo-before-or-equal `w`: by `gmoLt r w` in the gmo arm; in the po arm (`w'' ≠ w`)
po-latest forces `gpo w'' w` and ppo RULE 1 (`gppo1`, an arm of `gppoCatGmo`) orders it.
`gmoGwixLt` turns gmo into write indices, and `gwixInj` gives `w'' = w`.

NOT covered (as Rocq): the non-forwarding arm `gmoLt w r`.

`epiReloadFwd`: the epilogue shape — spill `(0,0)` (`sdWriteOk`), 8-byte reload `(0,1)` at `a`,
`gmoLt (0,1) (0,0)` ⇒ `graphValue GD (0,1) = some sdData`.  Any number of harts.
`epiFwdSat`: NON-VACUITY — `gsdldFwd` is `gsdld` (AxEpiSdLdSat) with the spill moved gmo-LAST;
all premises hold (cat consistency by `decide +kernel`).  Pure graph facts: no ownership.

## Deviations from Rocq

1. O2 STAGE C (AxEpiSat deviation 1 / AxEpiSdLdSat deviation 1): the epilogue row is
   `[SD; LD]` (no fetch items).  So in `epiReloadFwd`/`gsdldFwdSdWriteOk`/`epiFwdSat` the spill
   is at `(0,0)` (Rocq `(0,1)`) and the reload at `(0,1)` (Rocq `(0,3)`); Rocq's premise
   `Hnw_ld : gis_w (gd_g GD) (0,2) = false` (the fetch `(0,2)` between them is not a write) has
   no counterpart — nothing lies po-between `(0,0)` and `(0,1)` — and is DROPPED, as is the
   matching conjunct `gis_w … (0,2) = false` of `epiFwdSat`.  `sd_write_ok GD 0 1 a` ↦
   `sdWriteOk GD 0 0 a`.  `gsdldFwd`'s gmo is `[eLD, eSD]` (Rocq `[eF0; eF1; eLD; eSD]`).
2. VOCABULARY: `Z` ↦ `Int`, `l !! j` ↦ `l[j]?`, `gd_g` ↦ `.gdG`, `vm_compute` ↦
   `decide +kernel`; Rocq `gpo` ↦ `WeakRvwmoGraph.gpo`.  The `Print Assumptions` audits are not
   ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `rfi_fwd_source_g` `rfiFwdSourceG`, `rfi_fwd_source`
`rfiFwdSource`, `epi_reload_fwd` `epiReloadFwd`, `gsdld_fwd` `gsdldFwd`, `gsdld_fwd_cat`
`gsdldFwdCat`, `gsdld_fwd_sd_write_ok` `gsdldFwdSdWriteOk`, `epi_fwd_sat` `epiFwdSat`.

**Dropped:** none.  Rocq 7 declarations; Lean 7.
-/
import Weak.AxEpiOwned
import Weak.AxEpiSdLdSat
import Weak.AxGraphCat
import Weak.AxGraphDec
import Weak.WeakRvwmoLock

namespace Weak

open Lbl

/-! # 1. The graph-level lemma (only rule 1 of ppo is used) -/

theorem rfiFwdSourceG (G : Gexec) (r w : Geid) (aq : Bool) (a : Int)
    (ts : List Nat) (vs data : List (BitVec 8))
    (Hwf : gwf G)
    (Hppo1 : ∀ e1 e2, gppo1 G e1 e2 → gmoLt G e1 e2)
    (Hlv : gloadValue G)
    (Hr : gxLbl G r = some (LLoad aq a ts vs))
    (Hlen : data.length = vs.length)
    (Hcov : ∀ (j : Nat) v, data[j]? = some v → gwritesByte G w (a + (j : Int)) v)
    (Hpo : WeakRvwmoGraph.gpo G w r)
    (Hlatest : ∀ w' (j : Nat) v', j < vs.length →
        gwritesByte G w' (a + (j : Int)) v' → WeakRvwmoGraph.gpo G w w' →
        WeakRvwmoGraph.gpo G w' r → False)
    (Hfwd : gmoLt G r w) :
    vs = data ∧ (∀ j, j < vs.length → ts[j]? = some (gwix G w)) := by
  have Hts : vs.length = ts.length := gwfLblShape G r _ Hwf Hr
  have Hbyte : ∀ (j t : Nat) (v : BitVec 8), ts[j]? = some t → vs[j]? = some v →
      t = gwix G w ∧ data[j]? = some v := by
    intro j t v Ht Hv
    have Hj : j < vs.length := (List.getElem?_eq_some_iff.1 Hv).1
    obtain ⟨d, Hd⟩ : ∃ d, data[j]? = some d :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hwd := Hcov _ _ Hd
    have Hw_in := gwritesByteGwrites _ _ _ _ Hwf Hwd
    have Hrd : greadsByte G r (a + (j : Int)) t v := ⟨_, a, ts, vs, j, Hr, rfl, Ht, Hv, rfl⟩
    obtain ⟨Hsrc, Hmax⟩ := Hlv _ _ _ _ Hrd
    have Hle := Hmax _ _ Hwd (Or.inr Hpo)
    cases t with
    | zero =>
      have := WeakRvwmoGraph.gwixPos _ _ Hw_in
      omega
    | succ t' =>
      obtain ⟨w'', Hat, Hw''b, Hvis⟩ := Hsrc
      obtain ⟨Hw''_in, Hix⟩ := gwriteAtInv _ _ _ Hwf.1 Hat
      have Hle2 : gwix G w'' ≤ gwix G w := by
        rcases Hvis with Hgmo | Hpo''
        · have := gmoGwixLt G w'' w Hwf Hw''_in Hw_in (gmoLtTrans _ _ _ _ Hgmo Hfwd)
          omega
        · by_cases Hne : w'' = w
          · rw [Hne]
            exact Nat.le_refl _
          · have Hpo2 : WeakRvwmoGraph.gpo G w'' w := by
              obtain ⟨Hh1, Hk1, Hs1, Hs2⟩ := Hpo''
              obtain ⟨Hh2, Hk2, Hs3, Hs4⟩ := Hpo
              by_cases Hlt : w''.2 < w.2
              · exact ⟨by omega, Hlt, Hs1, Hs3⟩
              · by_cases Heq : w''.2 = w.2
                · exact absurd (Prod.ext (by omega) Heq) Hne
                · exact (Hlatest w'' j v Hj Hw''b ⟨by omega, by omega, Hs3, Hs1⟩
                    ⟨Hh1, Hk1, Hs1, Hs2⟩).elim
            have Hg : gmoLt G w'' w := Hppo1 _ _ ⟨Hpo2, _, Or.inl ⟨_, Hw''b⟩, _, Hwd⟩
            have := gmoGwixLt G w'' w Hwf Hw''_in Hw_in Hg
            omega
      have Heq : w'' = w := gwixInj G _ _ Hwf.1 Hw''_in Hw_in (by omega)
      subst Heq
      refine ⟨by omega, ?_⟩
      rw [Hd, gwritesByteDet G w'' _ _ _ Hwd Hw''b]
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem?
    intro j
    cases Hv : vs[j]? with
    | some v =>
      have hj := (List.getElem?_eq_some_iff.1 Hv).1
      obtain ⟨t, Ht⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [(Hbyte _ _ _ Ht Hv).2]
    | none =>
      have := List.getElem?_eq_none_iff.1 Hv
      rw [List.getElem?_eq_none_iff.2 (by omega)]
  · intro j Hj
    obtain ⟨t, Ht⟩ : ∃ t, ts[j]? = some t := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, Hv⟩ : ∃ v, vs[j]? = some v := ⟨_, List.getElem?_eq_getElem Hj⟩
    rw [Ht, (Hbyte _ _ _ Ht Hv).1]

/-! # 2. Under the cat model -/

theorem rfiFwdSource (GD : Gdexec) (r w : Geid) (aq : Bool) (a : Int)
    (ts : List Nat) (vs data : List (BitVec 8))
    (Hcons : rvwmoCatConsistent GD)
    (Hr : gxLbl GD.gdG r = some (LLoad aq a ts vs))
    (Hlen : data.length = vs.length)
    (Hcov : ∀ (j : Nat) v, data[j]? = some v → gwritesByte GD.gdG w (a + (j : Int)) v)
    (Hpo : WeakRvwmoGraph.gpo GD.gdG w r)
    (Hlatest : ∀ w' (j : Nat) v', j < vs.length →
        gwritesByte GD.gdG w' (a + (j : Int)) v' →
        WeakRvwmoGraph.gpo GD.gdG w w' → WeakRvwmoGraph.gpo GD.gdG w' r → False)
    (Hfwd : gmoLt GD.gdG r w) :
    graphValue GD r = some data ∧
    (∀ j, j < vs.length →
       ts[j]? = some (gwix GD.gdG w) ∧
       gwriteAt GD.gdG (gwix GD.gdG w) = some w) := by
  obtain ⟨Hwf, Hppo, Hlv, _⟩ := Hcons
  have Hppo1 : ∀ e1 e2, gppo1 GD.gdG e1 e2 → gmoLt GD.gdG e1 e2 :=
    fun e1 e2 H => Hppo e1 e2 (Or.inl (Or.inl H))
  obtain ⟨Heq, Hts⟩ :=
    rfiFwdSourceG _ _ _ _ _ _ _ _ Hwf Hppo1 Hlv Hr Hlen Hcov Hpo Hlatest Hfwd
  subst Heq
  refine ⟨by rw [graphValue, Hr]; rfl, fun j Hj => ⟨Hts j Hj, ?_⟩⟩
  apply gwriteAtGwix
  obtain ⟨d, Hd⟩ : ∃ d, vs[j]? = some d := ⟨_, List.getElem?_eq_getElem Hj⟩
  exact gwritesByteGwrites _ _ _ _ Hwf (Hcov _ _ Hd)

/-! # 3. The epilogue instance: spill `(0,0)`, reload `(0,1)` (Stage C positions) -/

theorem epiReloadFwd (GD : Gdexec) (a : Int) (aq : Bool)
    (ts : List Nat) (vs : List (BitVec 8))
    (Hcons : rvwmoCatConsistent GD)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hr : gxLbl GD.gdG (0, 1) = some (LLoad aq a ts vs))
    (Hlen : vs.length = 8)
    (Hfwd : gmoLt GD.gdG (0, 1) (0, 0)) :
    graphValue GD (0, 1) = some sdData := by
  obtain ⟨_, Hfoot, Hdata⟩ := Hw_sd
  unfold graphData at Hdata
  cases Hl : gxLbl GD.gdG (0, 0) with
  | none => rw [Hl] at Hdata; simp at Hdata
  | some l =>
    rw [Hl] at Hdata
    obtain ⟨base, Hwr⟩ : ∃ base, lbWr l = some (base, sdData) := by
      cases l with
      | LLoad _ _ _ _ => simp [lblData] at Hdata
      | LStore _ b vs' _ =>
        simp only [Option.bind_some, lblData, Option.some.injEq] at Hdata
        exact ⟨b, by rw [← Hdata]; rfl⟩
      | LFence _ _ _ _ => simp [lblData] at Hdata
      | LRmw _ _ b _ _ wvs _ =>
        simp only [Option.bind_some, lblData, Option.some.injEq] at Hdata
        exact ⟨b, by rw [← Hdata]; rfl⟩
    have Hcov0 : ∀ (j : Nat) v, sdData[j]? = some v →
        gwritesByte GD.gdG (0, 0) (base + (j : Int)) v :=
      fun j v Hv => ⟨l, base, sdData, j, Hl, Hwr, Hv, rfl⟩
    -- the footprint pins `base = a` (bytes 0 and 7)
    have Hba : base = a := by
      obtain ⟨v0, Hv0⟩ : ∃ v, sdData[0]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [sdDataLength]; omega)⟩
      obtain ⟨v7, Hv7⟩ : ∃ v, sdData[7]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [sdDataLength]; omega)⟩
      obtain ⟨j0, Hj0, E0⟩ := Hfoot _ _ (Hcov0 _ _ Hv0)
      obtain ⟨j7, Hj7, E7⟩ := Hfoot _ _ (Hcov0 _ _ Hv7)
      have h0 := (List.getElem?_eq_some_iff.1 Hj0).1
      have h7 := (List.getElem?_eq_some_iff.1 Hj7).1
      rw [sdDataLength] at h0 h7
      omega
    subst Hba
    refine (rfiFwdSource GD (0, 1) (0, 0) aq base ts vs sdData Hcons Hr ?_ Hcov0 ?_ ?_ Hfwd).1
    · rw [sdDataLength, Hlen]
    · exact ⟨rfl, by decide, by rw [Hl]; rfl, by rw [Hr]; rfl⟩
    · intro w' j v' _ _ H1 H2
      obtain ⟨_, Hk1, _⟩ := H1
      obtain ⟨_, Hk2, _⟩ := H2
      dsimp only at Hk1 Hk2
      omega

/-! # 4. NON-VACUITY: the premises of `epiReloadFwd` on a concrete graph -/

/-- `gsdld` with the spill moved gmo-LAST. -/
def gsdldFwd : Gdexec :=
  ⟨⟨sdldImg, [AxEpiSdLdSat.row], [AxEpiSdLdSat.eLD, AxEpiSdLdSat.eSD]⟩, []⟩

theorem gsdldFwdCat : rvwmoCatConsistent gsdldFwd :=
  catConsistentBSound _ (by decide +kernel)

theorem gsdldFwdSdWriteOk : sdWriteOk gsdldFwd 0 0 ldAddr := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  rintro a' v' ⟨l, base, vs, j, Hl, Hw, Hv, Ha⟩
  have Hl0 : gxLbl gsdldFwd.gdG (0, 0) = some (LStore false sdAddr sdData .WCplain) := rfl
  rw [Hl0, Option.some.injEq] at Hl
  subst Hl
  simp only [lbWr, Option.some.injEq, Prod.mk.injEq] at Hw
  obtain ⟨rfl, rfl⟩ := Hw
  refine ⟨j, Hv, ?_⟩
  rw [← Ha]
  unfold accAddr sdAddr ldAddr
  omega

theorem epiFwdSat :
    rvwmoCatConsistent gsdldFwd ∧
    sdWriteOk gsdldFwd 0 0 ldAddr ∧
    (∃ aq ts vs, gxLbl gsdldFwd.gdG (0, 1) = some (LLoad aq ldAddr ts vs) ∧
                 vs.length = 8) ∧
    gmoLt gsdldFwd.gdG (0, 1) (0, 0) ∧
    graphValue gsdldFwd (0, 1) = some sdData :=
  ⟨gsdldFwdCat, gsdldFwdSdWriteOk, ⟨false, _, _, rfl, rfl⟩,
   (gmoLtBSpec _ _ _).1 (by decide +kernel), rfl⟩

end Weak
