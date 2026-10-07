/-
Weak: **THE FIX for `AxLockN.lockNSound`'s VACUITY** (AxSL tier; LB/AxSL lock slice).

Rocq: `iris/AxLockN2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxLockN.naVal'` deposits, at an `x`-write `e`, a FULL `tokTie GD γ x H {[e := 1]}` as `e`'s own
established fact, while `AxLockN.eaVal`'s `isRelL` branch separately demands the same write
deposit a second, disjoint full tie to its release — both unfold to `histAuth γ x 1 _`, refuted
by `ownedWriteExcluded` (`AxLockN.lockNPremiseRefutedLock3s`).  `eaVal` also never gives an
`isWx` event anything.

THE FIX, additively (AxLockN is not modified):
- `naVal''` at `isWx` = the PURE FACTS ONLY (no `tokTie`) — `AxLockAdeq`'s `na0` convention.
- `eaVal''` is `AxLockN.eaVal` verbatim at the `isRelL`/`isAcqL` branches, PLUS a new `isWx`
  branch: the write receives, keyed by its own predecessor `AxLockN.xwPredO GD L e`, a single
  `∃ H, histAuth γ x 1 H`; a co-first write (`xwPredO = none`) gets it from `HflowInit''`'s
  externally supplied initial `histAuth γ x 1 []` instead.
So exactly ONE token travels acq → w → … → rel → acq' → …, never duplicated.

`lockAdequateGhost''`/`lockDiscGeneric''`/`lockNSound''` are `AxLockN`'s `lockAdequateGhost'`/
`lockDiscGeneric`/`lockNSound` restated verbatim over `naOf''`/`eaOf''`/`axGn2Inst` (a fresh
copy of `AxLockN.axGnInst`).  Every generic graph-flow helper (`isRelL`/`isAcqL`/`isWx`/
`xwPredO`/`relPredO`/`acqPredO`/`optSingleton`/`lockPred`/`axlocknPol`/`xwIsCsWrite`/
`gmoPermOfRun`/`lgMapOfFunLookupSome`/`None`/`axlocknPredSubFlowSpol`/`Lobp`) is REUSED from
`AxLockN`, as are the Lean-only `AxLockN.obInitLock`/`AxLockN.bytesIntro`.

**Ghost state allocated** (inside the soundness continuation, by
`AxLockAdeq2.lockInitialAlloc`): the history log (`AxlogG GF Hent`, name `γ`) at `x` and `L`
with empty histories and the claimed-set authority (`AxLockG GF`, name `γc`) at `∅`.

**Fetches / Q8.** No fetch content (graph labels only).

NOTE (downstream, Rocq `AxLockN3.v`): `HflowInit''` is still not certifiable for `lock3s` with
this `eaVal''` (release/acquire branch shapes); AxLockN3 changes those two branches.

## Deviations from Rocq

1. NAMES: camelCase (map below).  No name of this file is in the duplicated-name table.
   Lean-only helper (file-qualified): `AxLockN2.naBagCs` (the final bag projection of
   `lockDiscGeneric''`, as `AxLockN.naBagCs`).
2. VOCABULARY and SECTION VARIABLES as `AxLockN` deviations 2/3: section variables are explicit
   leading arguments (`GD L x Hxl Hcons HrelFence HacqRead HacqAq`, then `γ γc`); Rocq's
   section-local `Local Instance axlockn_pol_inst2` is not a declaration — `axlocknPol GD L x`
   is passed explicitly; `axGn2Inst` (Rocq `Instance AxGn2_inst`) is a reducible def passed
   explicitly; `AxirisG` has no `ax_text` field (Stage C).
3. `lockAdequateGhost''` is stated at `[InvGS_gen hlc GF]` for any `hlc` (Rocq `HasNoLc`), as
   `AxLockN.lockAdequateGhost'`; wand chains as `⊢ A -∗ B -∗ C -∗ D`, `HflowInit''` as `A ⊢ B`.
4. `lockDiscGeneric''`: as `AxLockN.lockDiscGeneric` (`∃ k, length = k + 1`, the step-fupd
   unfolded once around the `imod` of `lockInitialAlloc`).

**Rocq → Lean name map.**  `na_val''` `naVal''`, `ea_val''` `eaVal''`, `na_of''` `naOf''`,
`ea_of''` `eaOf''`, `na_of''_dom` `naOf''Dom`, `ea_of''_dom` `eaOf''Dom`, `na_ea_dom_eq''`
`naEaDomEq''`, `Hea_lob0''` `HeaLob0''`, `Hea_lob0_lobp''` `HeaLob0Lobp''`,
`axlockn_pol_inst2` (folded, deviation 2), `AxGn2_inst` `axGn2Inst`,
`AxGn2_ob_st_interp_unfold` `axGn2ObStInterpUnfold`, `lock_adequate_ghost''`
`lockAdequateGhost''`, `lock_disc_generic''` `lockDiscGeneric''`, `lockN_sound''`
`lockNSound''`.

**Dropped:** nothing.
-/
import Weak.AxLockN

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `naVal''`/`eaVal''`/`naOf''`/`eaOf''` -/

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- At `isWx`: the pure facts only (no token). -/
def naVal'' (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : IProp GF :=
  if AxLockN.isWx GD x e then
    iprop(∃ (v : BitVec 8) (data : List (BitVec 8)),
      ⌜gwritesByte GD.gdG e x v⌝ ∗ ⌜graphData GD e = some data⌝ ∗ ⌜AxLockN.xwIsCsWrite GD L e⌝)
  else if AxLockN.isRelL GD L e then
    iprop(∃ (H_L : List Hent), histSnap γ L H_L)
  else iprop(emp)

/-- `AxLockN.eaVal` plus the `isWx` branch: the write receives the full `x`-history. -/
def eaVal'' (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : Mea GF :=
  if AxLockN.isRelL GD L e then
    match AxLockN.relPredO GD L x e with
    | some p => {[p := iprop(∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else if AxLockN.isAcqL GD L e then
    match AxLockN.acqPredO GD e with
    | some p => {[p := iprop(⌜gwritesByte GD.gdG p L b0⌝ ∗
                  ∃ (H : List Hent), tokTie GD γ x H {[e := (1 : Qp)]})]}
    | none => ∅
  else if AxLockN.isWx GD x e then
    match AxLockN.xwPredO GD L e with
    | some p => {[p := iprop(∃ (H : List Hent), histAuth γ x 1 H)]}
    | none => ∅
  else ∅

def naOf'' (GD : Gdexec) (L x : Int) (γ : GName) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, naVal'' GD L x γ e))

def eaOf'' (GD : Gdexec) (L x : Int) (γ : GName) : Sra GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, eaVal'' GD L x γ e))

theorem naOf''Dom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (naOf'' (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold naOf'' at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold naOf''
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem eaOf''Dom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (eaOf'' (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold eaOf'' at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold eaOf''
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem naEaDomEq'' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (eaOf'' (GF := GF) GD L x γ) : GSet Geid) =
      FiniteMap.dom_set (naOf'' (GF := GF) GD L x γ) := by
  rw [eaOf''Dom GD Hcons L x, naOf''Dom GD Hcons L x]

theorem HeaLob0'' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (eaOf'' (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ AxLockN.lockPred GD L x e0 := by
  have Hnd := (schedHGwf GD Hcons).1
  intro e0 gm Hea
  by_cases Hin : e0 ∈ GD.gdG.gxGmo
  · unfold eaOf'' at Hea
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e0 Hin] at Hea
    cases Option.some.inj Hea
    unfold eaVal'' AxLockN.lockPred
    cases Hrel : AxLockN.isRelL GD L e0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases Hacq : AxLockN.isAcqL GD L e0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases Hwx : AxLockN.isWx GD x e0
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [domEmpty]
        · simp only [↓reduceIte]
          unfold AxLockN.optSingleton
          cases AxLockN.xwPredO GD L e0 with
          | none => rw [domEmpty]
          | some p => rw [domSingleton]
      · simp only [↓reduceIte]
        unfold AxLockN.optSingleton
        cases AxLockN.acqPredO GD e0 with
        | none => rw [domEmpty]
        | some p => rw [domSingleton]
    · simp only [↓reduceIte]
      unfold AxLockN.optSingleton
      cases AxLockN.relPredO GD L x e0 with
      | none => rw [domEmpty]
      | some p => rw [domSingleton]
  · unfold eaOf'' at Hea
    rw [AxLockN.lgMapOfFunLookupNone _ _ e0 Hin] at Hea
    cases Hea

/-- Restated at the literal `lobp` projection. -/
theorem HeaLob0Lobp'' (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (eaOf'' (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ @Axpol.lobp (axlocknPol GD L x) GD e0 :=
  HeaLob0'' GD Hcons L x Hxl HrelFence HacqRead HacqAq γ

end annot

/-! # 2. The fixed concrete instance and `lockAdequateGhost''` -/

section fixedInst

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- Rocq `AxGn2_inst` (a fresh copy of `AxLockN.axGnInst`): `obStInterp` IS `protInvLock'`. -/
@[reducible] def axGn2Inst (L x : Int) (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD0 σ s => protInvLock' L x γ γc GD0 s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem axGn2ObStInterpUnfold (L x : Int) (γ γc : GName) (GD0 : Gdexec)
    (σ : GSet Geid × GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := axGn2Inst (GF := GF) L x γ γc) GD0 σ s ⊣⊢
      protInvLock' L x γ γc GD0 s σ.1 σ.2 :=
  ⟨.rfl, .rfl⟩

end fixedInst

section adequate

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxlogG GF Hent] [AxLockG GF]

theorem lockAdequateGhost'' (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ γc : GName)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit'' :
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) hlc GF _ (axGn2Inst L x γ γc) GD
          (eaOf'' GD L x γ) (naOf'' GD L x γ) GD.gdG.gxGmo 0) :
    ⊢ histAuth (GF := GF) γ x 1 ([] : List Hent) -∗ histAuth γ L 1 ([] : List Hent) -∗
      claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := axGn2Inst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf'' GD L x γ) e0) := by
  have Hperm := gmoPermOfRun GD Hcons st Hrun Hfull Hdone
  have Htodo : ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) ⊢
      @ordEaTodoL (axlocknPol GD L x) hlc GF _ (axGn2Inst L x γ γc) GD
        (eaOf'' GD L x γ) (naOf'' GD L x γ) st.sProc 0 := by
    refine HflowInit''.trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    exact (BigSepL.bigSepL_perm Hperm.symm).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (naOf'' (GF := GF) GD L x γ) := by
    rw [naOf''Dom GD Hcons L x]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact Hperm.mem_iff.1 He'
  have Had : ⊢ @ordEaTodoL (axlocknPol GD L x) hlc GF _ (axGn2Inst L x γ γc) GD
        (eaOf'' GD L x γ) (naOf'' GD L x γ) st.sProc 0 -∗
      AxirisG.obStInterp (self := axGn2Inst L x γ γc) GD
        ((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := axGn2Inst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf'' GD L x γ) e0) :=
    @schedProcAdequate hlc GF _ (axGn2Inst L x γ γc) (axlocknPol GD L x)
      GD Hcons st Hrun Hfull Hdone
      (axlocknPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
      (axlocknPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq)
      (naOf'' GD L x γ) (eaOf'' GD L x γ)
      (naEaDomEq'' GD Hcons L x γ) Hdom
      (HeaLob0Lobp'' GD Hcons L x Hxl HrelFence HacqRead HacqAq γ) Hdefer
      ((∅, ∅) : GSet Geid × GMapF Geid (List Hent))
  have Hob0 : claimedAuth γc (∅ : GSet Geid) ⊢
      AxirisG.obStInterp (self := axGn2Inst (GF := GF) L x γ γc) GD
        ((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) ∅ :=
    AxLockN.obInitLock L x γ γc GD
  iintro Hx HL Hc
  ihave Hb := AxLockN.bytesIntro x L Hxl γ $$ [Hx HL]
  · isplitl [Hx]
    · iexact Hx
    · iexact HL
  ihave Ht := Htodo $$ Hb
  ihave Hob := Hob0 $$ Hc
  iapply Had $$ Ht Hob

end adequate

/-! # 3. `lockDiscGeneric''` — the Prop-level extraction -/

section disc

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- Lean-only: the final bag entry at an `x`-write yields the discipline fact. -/
theorem AxLockN2.naBagCs (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName)
    (w : Geid) (vw : BitVec 8) (Hw : gwritesByte GD.gdG w x vw) :
    AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf'' (GF := GF) GD L x γ) w) ⊢
      ⌜AxLockN.xwIsCsWrite GD L w⌝ := by
  have Hnd := (schedHGwf GD Hcons).1
  have HinGmo : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (schedHGwf GD Hcons) Hw
  have Hisx : AxLockN.isWx GD x w = true := (gwaBSpec _ _ _).2 ⟨vw, Hw⟩
  unfold naOf''
  rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd w HinGmo]
  simp only [AxWp.fromOption]
  unfold naVal''
  rw [if_pos Hisx]
  iintro ⟨%v, %data, -, -, %Hcs⟩
  ipureintro
  exact Hcs

end disc

theorem lockDiscGeneric'' {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit'' : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (axGn2Inst L x γ γc) GD
          (eaOf'' GD L x γ) (naOf'' GD L x γ) GD.gdG.gxGmo 0)
    (w : Geid) (vw : BitVec 8) :
    gwritesByte GD.gdG w x vw → AxLockN.xwIsCsWrite GD L w := by
  intro Hw
  have Hperm := gmoPermOfRun GD Hcons st Hrun Hfull Hdone
  have HinGmo : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (schedHGwf GD Hcons) Hw
  have HinProc : w ∈ st.sProc := Hperm.mem_iff.2 HinGmo
  obtain ⟨k, hk⟩ : ∃ k, st.sProc.length = k + 1 := by
    cases h : st.sProc with
    | nil => rw [h] at HinProc; cases HinProc
    | cons a l => exact ⟨l.length, rfl⟩
  have Hin : w ∈ (LawfulSet.ofList st.sProc : GSet Geid) := elemOfListToSet.2 HinProc
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := HasLC.hasNoLC)
    (P := iprop(⌜AxLockN.xwIsCsWrite GD L w⌝)) (k + 1) 0 ?_
  intro Hinv
  iintro _
  have hs : ∀ (P : IProp GF),
      iprop(|={⊤}[∅]▷=>^[k + 1] P) = iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[k] P) := fun _ => rfl
  rw [hs]
  imod lockInitialAlloc (GF := GF) x L Hxl with ⟨%γ, %γc, Hx, HL, Hc⟩
  rw [← hs]
  have Hfinal := lockAdequateGhost'' (hlc := .hasNoLC) GD L x Hxl Hcons HrelFence HacqRead
    HacqAq γ γc st Hrun Hfull Hdone Hdefer (HflowInit'' Hinv γ γc)
  rw [hk] at Hfinal
  ihave Hfin := Hfinal $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfin
  iintro ⟨%σ, -, Hbag⟩
  ihave Hw' := BigSepS.bigSepS_elem_of (Φ := fun e0 =>
    AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf'' (GF := GF) GD L x γ) e0))
    Hin $$ Hbag
  iapply AxLockN2.naBagCs GD Hcons L x γ w vw Hw $$ Hw'

/-! # 4. `lockNSound''` — composing (3) with `AxLockSerial.csHandoffLast` -/

theorem lockNSound'' {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit'' : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (axGn2Inst L x γ γc) GD
          (eaOf'' GD L x γ) (naOf'' GD L x γ) GD.gdG.gxGmo 0)
    (acqA relA acqB relB w_x r_x : Geid) (vx v v0 : BitVec 8) (t_B t : Nat)
    (Hpat : lockPattern GD.gdG L) (Hpair : lockPaired GD.gdG L)
    (HcsA : lockCs GD.gdG L acqA relA) (HaqA : glblIs GD.gdG acqA lbAq)
    (Hwx : gwritesByte GD.gdG w_x x vx)
    (Hwx_po : WeakRvwmoGraph.gpo GD.gdG acqA w_x) (Hcov_wx : gppoCat GD w_x relA)
    (HcsB : lockCs GD.gdG L acqB relB) (HaqB : glblIs GD.gdG acqB lbAq)
    (Hharts : acqA.1 ≠ acqB.1)
    (Hrd_acqB : greadsByte GD.gdG acqB L t_B v0)
    (Hsrc_acqB : gwriteAt GD.gdG t_B = some relA)
    (Hacq_po : WeakRvwmoGraph.gpo GD.gdG acqB r_x) (Hrd : greadsByte GD.gdG r_x x t v)
    (Hcov_rx : gppoCat GD r_x relB)
    (Hscope : ∀ w vw, w ≠ w_x → gwritesByte GD.gdG w x vw →
      ∀ acqk relk, lockCs GD.gdG L acqk relk → glblIs GD.gdG acqk lbAq →
        WeakRvwmoGraph.gpo GD.gdG acqk w → gppoCat GD w relk →
        acqk.1 ≠ acqA.1 ∧ acqk.1 ≠ acqB.1) :
    WeakRvwmoAcyc.grf GD.gdG w_x r_x ∧ v = vx := by
  have Hdisc_x : ∀ w vw, gwritesByte GD.gdG w x vw → w = w_x ∨
      (∃ acqk relk, lockCs GD.gdG L acqk relk ∧ glblIs GD.gdG acqk lbAq ∧
        acqk.1 ≠ acqA.1 ∧ acqk.1 ≠ acqB.1 ∧
        WeakRvwmoGraph.gpo GD.gdG acqk w ∧ gppoCat GD w relk) := by
    intro w vw Hw
    by_cases Hne : w = w_x
    · exact Or.inl Hne
    · right
      obtain ⟨acqk, relk, Hcsk, Haqk, Hpok, Hcovk⟩ :=
        lockDiscGeneric'' GD L x Hxl Hcons HrelFence HacqRead HacqAq st Hrun Hfull Hdone Hdefer
          HflowInit'' w vw Hw
      obtain ⟨HneA, HneB⟩ := Hscope w vw Hne Hw acqk relk Hcsk Haqk Hpok Hcovk
      exact ⟨acqk, relk, Hcsk, Haqk, HneA, HneB, Hpok, Hcovk⟩
  exact csHandoffLast GD L x acqA relA acqB relB w_x r_x vx v v0 t_B t
    Hcons Hpat Hpair HcsA HaqA Hwx Hwx_po Hcov_wx HcsB HaqB Hharts
    Hrd_acqB Hsrc_acqB Hacq_po Hrd Hcov_rx Hdisc_x

end Weak
