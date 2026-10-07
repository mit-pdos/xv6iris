/-
Weak: **THE PURE `deferredSnapAvail` DISCHARGE, THE PER-BYTE WRITE CHAIN `hOf`, AND THE COVERAGE
COROLLARY WITHOUT `Hdefer`** (C6/C9, continued from `Weak.AxProtCov`).

Rocq: `iris/AxProtCov2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxProtInst.axprotSchedProcAdequate` already carries no policy hypotheses, only `Hdefer`. This file:

§1 (item 3) `deferredSnapAvail GD everD r` is a bare, ghost-free Prop, so a witness history is a
plain value built from the graph: `axprotcovHist GD wl v` = every gco-predecessor of `wl` (gmo
order) then `wl`, all tagged `v`. `deferredReadCovPure` (coverage by the co-maximality argument,
pure gwix/gpos arithmetic) and `deferredSnapAvailPure` (unconditional for any read with SOME real,
non-image write source; a pure-image read has no `wl`, so `deferredSnapAvail` is unsatisfiable for
it — the corollary names that side condition `Hreal`).

§2 (items 1/2) Given a single-byte write-data function `wdat` with `HwdatSpec`: the immediate
predecessor keeps the byte (`axprotImmpredByte`), is gmo-earlier (`axprotImmpredGposLt`), and is
the immediate predecessor of at most one write (`axprotImmpredInj`, the pigeonhole that makes a
singleton `ea` deposit the right shape); `hOf GD wdat w`, the per-byte write chain through `w`, by
fuel-bounded recursion on `axprotImmpred` (fuel = `gpos`), with the unfolding equations,
fuel-stability, and the chain equation `hOf w = hOf w0 ++ [(w, (wdat w).2)]`.

§3 `axprotSchedProcAdequateCov`: `axprotSchedProcAdequate` with `Hdefer` replaced by `Hreal`.
`na`/`ea` are still parameters; their concrete assembly (the list-to-map lookup, the first-write
`histAlloc` distribution, the per-write `flowEqEa`, the non-write case) is Rocq's named remaining
gap (continued in AxProtCov3).

**Fetches.** Graph events only (Stage C); nothing here mentions fetches.

## Deviations from Rocq

1. NAMES: camelCase (map below); none is duplicated in the Rocq tree. Rocq `H_of*` ↦ `hOf*`.
2. VOCABULARY (as `AxProtInst` deviation 2): `gd_g GD` ↦ `GD.gdG`, `filter` ↦ `List.filter`,
   `<$>` ↦ `List.map`, `.*1` ↦ `List.map Prod.fst`, `last` ↦ `List.getLast?`, `bv 8` ↦ `BitVec 8`.
3. SECTION `chain`: Rocq's `Context (GD) (Hcons) (wdat) (Hwdat_spec)` become explicit arguments,
   each lemma taking exactly the ones its Rocq proof uses (Rocq's section-closing generalization),
   in the Rocq order `GD Hcons wdat HwdatSpec`.
4. §3 is generic in `hlc` (Rocq: `HasNoLc`), as `AxProtInst.axprotSchedProcAdequate` already is;
   its policy is the global `axprotPol` instance (`Axpol.lobp GD e0 = axprotPred GD e0`).
5. Lean-only helper `AxProtCov2.immpredGco` (file-qualified): the `gco` witness unpacked from
   `axprotImmpred GD w = some w0` — the step Rocq repeats inline in its three §2 proofs.

**Rocq → Lean name map.**  `axprotcov_predl` `axprotcovPredl`, `axprotcov_hist` `axprotcovHist`,
`axprotcov_hist_last` `axprotcovHistLast`, `fmap_fst_pair_const` `fmapFstPairConst`,
`axprotcov_hist_fst` `axprotcovHistFst`, `deferred_read_cov_pure` `deferredReadCovPure`,
`deferred_snap_avail_pure` `deferredSnapAvailPure`, `axprot_immpred_byte` `axprotImmpredByte`,
`axprot_immpred_gpos_lt` `axprotImmpredGposLt`, `axprot_immpred_inj` `axprotImmpredInj`,
`H_of_fuel` `hOfFuel`, `H_of` `hOf`, `H_of_fuel_S_eq` `hOfFuelSEq`, `H_of_fuel_none_eq`
`hOfFuelNoneEq`, `H_of_fuel_stable` `hOfFuelStable`, `H_of_first` `hOfFirst`, `H_of_chain`
`hOfChain`, `H_of_last` `hOfLast`, `axprot_sched_proc_adequate_cov` `axprotSchedProcAdequateCov`.

**Not ported:** the §5 `Print Assumptions` audit (the lint's axiom check covers it).
-/
import Weak.AxProtCov

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. ITEM (3): `deferredSnapAvail`, PURELY, WITH NO `Hdefer`/GHOST -/

/-- `w`'s gco-predecessors as a LIST (gmo order) — `axprotPred`'s filter, kept as a list. -/
def axprotcovPredl (GD : Gdexec) (w : Geid) : List Geid :=
  GD.gdG.gxGmo.filter (fun w' => gcoB GD.gdG w' w)

/-- A COMPUTABLE witness history for `w`: every gco-predecessor, then `w`, all tagged `v`. -/
def axprotcovHist (GD : Gdexec) (w : Geid) (v : BitVec 8) : List Hent :=
  (axprotcovPredl GD w).map (fun w' => (w', v)) ++ [(w, v)]

theorem axprotcovHistLast (GD : Gdexec) (w : Geid) (v : BitVec 8) :
    (axprotcovHist GD w v).getLast? = some (w, v) := by
  simp [axprotcovHist]

theorem fmapFstPairConst {A B : Type _} (l : List A) (v : B) :
    (l.map (fun x => (x, v))).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, ih]

theorem axprotcovHistFst (GD : Gdexec) (w : Geid) (v : BitVec 8) :
    (axprotcovHist GD w v).map Prod.fst = axprotcovPredl GD w ++ [w] := by
  rw [axprotcovHist, List.map_append, fmapFstPairConst]
  rfl

/-- THE COVERAGE LEMMA, PURE: every gmo-before-`r` write to `wl`'s byte is in the history. -/
theorem deferredReadCovPure (GD : Gdexec) (Hwf : gwf GD.gdG)
    (r wl : Geid) (a : Int) (vl : BitVec 8) :
    gwritesByte GD.gdG wl a vl →
    (∀ w v, gwritesByte GD.gdG w a v → gmoLt GD.gdG w r →
      gwix GD.gdG w ≤ gwix GD.gdG wl) →
    deferredReadCov GD a r (axprotcovHist GD wl vl) := by
  intro hwlwb hmax
  unfold deferredReadCov
  rw [axprotcovHistFst]
  intro w v hwb hmo
  by_cases hne : w = wl
  · subst hne; simp
  · apply List.mem_append_left
    rw [axprotcovPredl, List.mem_filter]
    have hww := gwritesByteGwrites _ _ _ _ Hwf hwb
    have hwlw := gwritesByteGwrites _ _ _ _ Hwf hwlwb
    refine ⟨((gwritesElemOf _ _).1 hww).1, (gcoBSpec _ _ _).2 ⟨a, v, vl, hwb, hwlwb, ?_⟩⟩
    have hle := hmax w v hwb hmo
    have hneq : gwix GD.gdG w ≠ gwix GD.gdG wl := fun heq =>
      hne (gwixInj _ _ _ Hwf.1 hww hwlw heq)
    omega

/-- THE MAIN RESULT: `deferredSnapAvail` holds for every read with SOME real write source. -/
theorem deferredSnapAvailPure (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (everD : GSet Geid) (r : Geid) (a : Int) (t : Nat) (vr : BitVec 8) (wl : Geid) :
    greadsByte GD.gdG r a t vr →
    gwriteAt GD.gdG t = some wl →
    deferredSnapAvail GD everD r := by
  intro hrd hwrat _
  obtain ⟨hwf, _, hgv, _⟩ := Hcons
  obtain ⟨hsrc, hmaxg⟩ := hgv r a t vr hrd
  cases t with
  | zero => simp [gwriteAt] at hwrat
  | succ t' =>
    obtain ⟨w0, hwat0, hwb0, hvis0⟩ := hsrc
    rw [hwrat, Option.some.injEq] at hwat0
    subst hwat0
    refine ⟨a, axprotcovHist GD wl vr, wl, vr, axprotcovHistLast GD wl vr, hvis0, ?_⟩
    apply deferredReadCovPure GD hwf r wl a vr hwb0
    intro w v hwb hmo
    have hwix := (gwriteAtInv GD.gdG (t' + 1) wl hwf.1 hwrat).2
    rw [hwix]
    exact hmaxg w v hwb (Or.inl hmo)

/-! # 2. ITEMS (1)+(2): THE CHAIN INFRASTRUCTURE, GIVEN A SINGLE-BYTE WRITE-DATA FUNCTION `wdat`

Rocq's section `chain` context `(GD) (Hcons) (wdat) (Hwdat_spec)` is passed explicitly (deviation 3);
`HwdatSpec` is `∀ w a v, gisW GD.gdG w = true → (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w)`. -/

/-- Unpacking `axprotImmpred GD w = some w0` into the `gco` witness. -/
theorem AxProtCov2.immpredGco (GD : Gdexec) (w w0 : Geid) (h : axprotImmpred GD w = some w0) :
    ∃ a v v', gwritesByte GD.gdG w0 a v ∧ gwritesByte GD.gdG w a v' ∧
      gwix GD.gdG w0 < gwix GD.gdG w := by
  have hin := axprotImmpredPred GD w w0 h
  rw [axprotPred, elemOfListToSet, List.mem_filter] at hin
  exact (gcoBSpec _ _ _).1 hin.2

/-- `w`'s immediate gco-predecessor never changes byte. -/
theorem axprotImmpredByte (GD : Gdexec) (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (w w0 : Geid) :
    axprotImmpred GD w = some w0 → (wdat w0).1 = (wdat w).1 := by
  intro himm
  obtain ⟨a, v, v', hwb0, hwbw, _⟩ := AxProtCov2.immpredGco GD w w0 himm
  have hisw0 := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwb0
  have hisww := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwbw
  have e1 := (HwdatSpec w0 a v hisw0).1 hwb0
  have e2 := (HwdatSpec w a v' hisww).1 hwbw
  rw [← e1, ← e2]

/-- The chain's strictly-decreasing measure: an immediate predecessor is gmo-strictly-earlier. -/
theorem axprotImmpredGposLt (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (w w0 : Geid) :
    axprotImmpred GD w = some w0 → gpos GD.gdG w0 < gpos GD.gdG w := by
  intro himm
  obtain ⟨a, v, v', hwb0, hwb, hgwix⟩ := AxProtCov2.immpredGco GD w w0 himm
  have hw0 := gwritesByteGwrites _ _ _ _ Hcons.1 hwb0
  have hw := gwritesByteGwrites _ _ _ _ Hcons.1 hwb
  exact (gwixGposLt GD.gdG w0 w Hcons.1.1 hw0 hw).1 hgwix

/-- THE PIGEONHOLE: at most one write names `p` as its immediate predecessor. -/
theorem axprotImmpredInj (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8)
    (HwdatSpec : ∀ w a v, gisW GD.gdG w = true →
      (gwritesByte GD.gdG w a v ↔ (a, v) = wdat w))
    (p w1 w2 : Geid) :
    axprotImmpred GD w1 = some p → axprotImmpred GD w2 = some p → w1 = w2 := by
  intro h1 h2
  by_cases hne : w1 = w2
  · exact hne
  exfalso
  have hwf := Hcons.1
  have hlt1 := axprotImmpredGposLt GD Hcons w1 p h1
  have hlt2 := axprotImmpredGposLt GD Hcons w2 p h2
  obtain ⟨a1, vp1, v1, hwbp1, hwb1, _⟩ := AxProtCov2.immpredGco GD w1 p h1
  obtain ⟨a2, vp2, v2, hwbp2, hwb2, _⟩ := AxProtCov2.immpredGco GD w2 p h2
  have hisp := WeakRvwmoGraph.gwritesByteGisW _ _ _ _ hwbp1
  have e1 := (HwdatSpec p a1 vp1 hisp).1 hwbp1
  have e2 := (HwdatSpec p a2 vp2 hisp).1 hwbp2
  have hpp : (a1, vp1) = (a2, vp2) := by rw [e1, ← e2]
  have ha : a1 = a2 := (Prod.mk.injEq _ _ _ _ ▸ hpp).1
  subst ha
  have hw1w := gwritesByteGwrites _ _ _ _ hwf hwb1
  have hw2w := gwritesByteGwrites _ _ _ _ hwf hwb2
  have hmem1 := ((gwritesElemOf _ _).1 hw1w).1
  have hmem2 := ((gwritesElemOf _ _).1 hw2w).1
  rcases Nat.lt_trichotomy (gpos GD.gdG w1) (gpos GD.gdG w2) with hlt12 | heqp | hlt21
  · have hgwix12 := (gwixGposLt GD.gdG w1 w2 hwf.1 hw1w hw2w).2 hlt12
    have hpred : w1 ∈ axprotPred GD w2 := by
      rw [axprotPred, elemOfListToSet, List.mem_filter]
      exact ⟨hmem1, (gcoBSpec _ _ _).2 ⟨a1, v1, v2, hwb1, hwb2, hgwix12⟩⟩
    by_cases hnep : w1 = p
    · subst hnep; omega
    · have ⟨_, _, hlt⟩ := axprotImmpredTop GD hwf.1 w2 p w1 h2 hpred hnep
      omega
  · exact hne (gposInj GD.gdG w1 w2 hwf.1 hmem1 hmem2 heqp)
  · have hgwix21 := (gwixGposLt GD.gdG w2 w1 hwf.1 hw2w hw1w).2 hlt21
    have hpred : w2 ∈ axprotPred GD w1 := by
      rw [axprotPred, elemOfListToSet, List.mem_filter]
      exact ⟨hmem2, (gcoBSpec _ _ _).2 ⟨a1, v2, v1, hwb2, hwb1, hgwix21⟩⟩
    by_cases hnep : w2 = p
    · subst hnep; omega
    · have ⟨_, _, hlt⟩ := axprotImmpredTop GD hwf.1 w1 p w2 h1 hpred hnep
      omega

/-- `hOfFuel`: the per-byte write chain up through `w`, by fuel-bounded recursion on
`axprotImmpred` (fuel = `gpos`). -/
def hOfFuel (GD : Gdexec) (wdat : Geid → Int × BitVec 8) : Nat → Geid → List Hent
  | fuel, w =>
    match axprotImmpred GD w with
    | none => [(w, (wdat w).2)]
    | some w0 =>
      match fuel with
      | 0 => [(w, (wdat w).2)]
      | n + 1 => hOfFuel GD wdat n w0 ++ [(w, (wdat w).2)]

def hOf (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) : List Hent :=
  hOfFuel GD wdat (gpos GD.gdG w) w

theorem hOfFuelSEq (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat) (w w0 : Geid) :
    axprotImmpred GD w = some w0 →
    hOfFuel GD wdat (f + 1) w = hOfFuel GD wdat f w0 ++ [(w, (wdat w).2)] := by
  intro himm
  rw [hOfFuel, himm]

theorem hOfFuelNoneEq (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (f : Nat) (w : Geid) :
    axprotImmpred GD w = none → hOfFuel GD wdat f w = [(w, (wdat w).2)] := by
  intro himm
  rw [hOfFuel, himm]

/-- Extra fuel changes nothing, as long as there is already enough. -/
theorem hOfFuelStable (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) :
    ∀ f w, gpos GD.gdG w ≤ f →
      ∀ f', gpos GD.gdG w ≤ f' → hOfFuel GD wdat f w = hOfFuel GD wdat f' w := by
  intro f
  induction f with
  | zero =>
    intro w hf f' _
    cases himm : axprotImmpred GD w with
    | some w0 =>
      have := axprotImmpredGposLt GD Hcons w w0 himm
      omega
    | none => rw [hOfFuelNoneEq GD wdat 0 w himm, hOfFuelNoneEq GD wdat f' w himm]
  | succ f ih =>
    intro w hf f' hf'
    cases himm : axprotImmpred GD w with
    | some w0 =>
      have hlt := axprotImmpredGposLt GD Hcons w w0 himm
      cases f' with
      | zero => omega
      | succ f'' =>
        rw [hOfFuelSEq GD wdat f w w0 himm, hOfFuelSEq GD wdat f'' w w0 himm,
          ih w0 (by omega) f'' (by omega)]
    | none => rw [hOfFuelNoneEq GD wdat (f + 1) w himm, hOfFuelNoneEq GD wdat f' w himm]

theorem hOfFirst (GD : Gdexec) (wdat : Geid → Int × BitVec 8) (w : Geid) :
    axprotImmpred GD w = none → hOf GD wdat w = [(w, (wdat w).2)] :=
  fun himm => hOfFuelNoneEq GD wdat (gpos GD.gdG w) w himm

/-- THE CHAIN EQUATION: `hOf` telescopes across one gco-step. -/
theorem hOfChain (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (w w0 : Geid) :
    axprotImmpred GD w = some w0 → hOf GD wdat w = hOf GD wdat w0 ++ [(w, (wdat w).2)] := by
  intro himm
  have hlt := axprotImmpredGposLt GD Hcons w w0 himm
  unfold hOf
  obtain ⟨f, hf⟩ : ∃ f, gpos GD.gdG w = f + 1 := ⟨gpos GD.gdG w - 1, by omega⟩
  rw [hf, hOfFuelSEq GD wdat f w w0 himm,
    hOfFuelStable GD Hcons wdat f w0 (by omega) (gpos GD.gdG w0) (Nat.le_refl _)]

theorem hOfLast (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (wdat : Geid → Int × BitVec 8) (w : Geid) :
    (hOf GD wdat w).getLast? = some (w, (wdat w).2) := by
  cases himm : axprotImmpred GD w with
  | some w0 => rw [hOfChain GD Hcons wdat w w0 himm]; simp
  | none => rw [hOfFirst GD wdat w himm]; rfl

/-! # 3. THE COROLLARY: `axprotSchedProcAdequate` WITH NO `Hdefer` HYPOTHESIS -/

section AdequateCov
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF]

theorem axprotSchedProcAdequateCov (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (na : Mea GF) (ea : Sra GF)
    (HdomEq : (FiniteMap.dom_set ea : GSet Geid) = FiniteMap.dom_set na)
    (Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆ FiniteMap.dom_set na)
    (HeaLob : ∀ e0 gm, get? ea e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ Axpol.lobp GD e0)
    (Hreal : ∀ r, r ∈ st.sEverD →
      ∃ a t vr wl, greadsByte GD.gdG r a t vr ∧ gwriteAt GD.gdG t = some wl)
    (σ0 : AxirisG.obSt GF) :
    ⊢ ordEaTodoL GD ea na st.sProc 0 -∗
      AxirisG.obStInterp GD σ0 ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : AxirisG.obSt GF),
          AxirisG.obStInterp GD σ (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? na e0) :=
  axprotSchedProcAdequate GD Hcons st Hrun Hfull Hdone na ea HdomEq Hdom HeaLob
    (fun r hin => by
      obtain ⟨a, t, vr, wl, hrd, hwrat⟩ := Hreal r hin
      exact deferredSnapAvailPure GD Hcons st.sEverD r a t vr wl hrd hwrat hin)
    σ0

end AdequateCov

end Weak
