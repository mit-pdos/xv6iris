/-
Weak: **THE FIX for `AxLockN2`'s `HflowInit''` BLOCKER** (AxSL tier; LB/AxSL lock slice).

Rocq: `iris/AxLockN3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`HflowInit''` is not certifiable for `lock3s`: (1) `eaVal''`'s `isRelL` branch deposits, at the
release's predecessor `p := relPredO`, a tie already tied to the release itself, whereas
`AxLockAdeq.flowEqReleaseWx` expects a tie on `p` (it re-ties it along `gobCat p r` itself);
(2) `eaVal''`'s `isAcqL` branch hands the acquire an `x`-tie, whereas
`AxLockAdeq.flowEqAmoswapAqWl` wants the LOCK's history `histAuth γ L 1 H_L`; (3) the first-ever
acquire has no predecessor (`eaVal'' = ∅` there) but its `L`-RMW still needs an `L`-history.

THE FIX (item (a)): `eaVal3` changes exactly those two branches (`{[e := 1]}` ↦ `{[p := 1]}`;
the acquire slot is `∃ H_L, histAuth γ L 1 H_L`); `isWx` and `AxLockN2.naVal''` are unchanged.
Every dom-only generic lemma carries over verbatim (`naOf3`/`eaOf3`/`HeaLob03`/
`lockAdequateGhost3`/`lockDiscGeneric3`/`lockNSound3`).  Item (b): `flowEqAmoswapAqInit`, the
first acquire's rule — an `L`-RMW writing `b1` consuming the initial `histAuth γ L 1 []`, with a
vacuous own `ΦLock'` slot (`b1 ≠ b0`).  Rocq's item (c) (`HflowInit3` for `lock3s`) was not
completed in Rocq (PAUSE 2026-09-27) and is not here either.

**Ghost state allocated** (inside the soundness continuation of `lockDiscGeneric3`, by
`AxLockAdeq2.lockInitialAlloc`): the history log (`AxlogG GF Hent`, name `γ`) at `x` and `L`
with empty histories and the claimed-set authority (`AxLockG GF`, name `γc`) at `∅`.

**Fetches / Q8.** No fetch content (graph labels only).

## Deviations from Rocq

1. NAMES: camelCase (map below).  `AxGn3_inst` is a duplicated Rocq name (AxLockN, AxLockN3):
   `AxLockN3.axGn3Inst`.  Lean-only helper (file-qualified): `AxLockN3.naBagCs` (the final bag
   projection of `lockDiscGeneric3`, as `AxLockN2.naBagCs`, restated at `naOf3`).
2. VOCABULARY and SECTION VARIABLES as `AxLockN2` deviations 2–4: section variables are explicit
   leading arguments (`GD L x Hxl Hcons HrelFence HacqRead HacqAq`, then `γ γc`); Rocq's
   section-local `Local Instance axlockn_pol_inst3` is not a declaration — `axlocknPol GD L x`
   is passed explicitly; `AxLockN3.axGn3Inst` is a reducible def passed explicitly; `AxirisG`
   has no `ax_text` field (Stage C); `lockAdequateGhost3` at `[InvGS_gen hlc GF]` for any
   `hlc` (Rocq `HasNoLc`); wand chains as `⊢ A -∗ B -∗ C -∗ D`, `HflowInit3` as `A ⊢ B`;
   `lockDiscGeneric3` destructs the step count as `∃ k, length = k + 1`.
3. `flowEqAmoswapAqInit` is stated at `[InvGS_gen hlc GF]` for any `hlc` (Rocq `HasNoLc`); its
   Rocq section context (`ob_D ob_hm mk_ob' Hmk_ob'_D Hmk_ob'_hm Hob_eq'`, `γ γc L x`) are
   explicit leading arguments, as in `AxLockAdeq`; the `AxirisG`/`Axpol` are instance
   arguments; the wand is `A ⊢ B`.

**Rocq → Lean name map.**  `ea_val3` `eaVal3`, `na_of3` `naOf3`, `ea_of3` `eaOf3`,
`na_of3_dom` `naOf3Dom`, `ea_of3_dom` `eaOf3Dom`, `na_ea_dom_eq3` `naEaDomEq3`, `Hea_lob0_3`
`HeaLob03`, `Hea_lob0_lobp_3` `HeaLob0Lobp3`, `axlockn_pol_inst3` (folded, deviation 2),
`AxGn3_inst` `AxLockN3.axGn3Inst`, `AxGn3_ob_st_interp_unfold` `axGn3ObStInterpUnfold`,
`lock_adequate_ghost3` `lockAdequateGhost3`, `lock_disc_generic3` `lockDiscGeneric3`,
`lockN_sound3` `lockNSound3`, `flow_eq_amoswap_aq_init` `flowEqAmoswapAqInit`.

**Dropped:** nothing.
-/
import Weak.AxLockN2
import Weak.AxLockAdeq

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. `eaVal3`/`naOf3`/`eaOf3` (`naVal''` reused from AxLockN2) -/

section annot

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- THE FIX: `eaVal3` with the `isRelL` tie keyed and tied at the predecessor `p`, and the
`isAcqL` slot carrying the lock's own history `∃ H_L, histAuth γ L 1 H_L`. -/
def eaVal3 (GD : Gdexec) (L x : Int) (γ : GName) (e : Geid) : Mea GF :=
  if AxLockN.isRelL GD L e then
    match AxLockN.relPredO GD L x e with
    | some p => {[p := iprop(∃ (H : List Hent), tokTie GD γ x H {[p := (1 : Qp)]})]}
    | none => ∅
  else if AxLockN.isAcqL GD L e then
    match AxLockN.acqPredO GD e with
    | some p => {[p := iprop(∃ (H_L : List Hent), histAuth γ L 1 H_L)]}
    | none => ∅
  else if AxLockN.isWx GD x e then
    match AxLockN.xwPredO GD L e with
    | some p => {[p := iprop(∃ (H : List Hent), histAuth γ x 1 H)]}
    | none => ∅
  else ∅

def naOf3 (GD : Gdexec) (L x : Int) (γ : GName) : Mea GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, naVal'' GD L x γ e))

def eaOf3 (GD : Gdexec) (L x : Int) (γ : GName) : Sra GF :=
  PartialMap.ofList (GD.gdG.gxGmo.map fun e => (e, eaVal3 GD L x γ e))

theorem naOf3Dom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (naOf3 (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold naOf3 at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold naOf3
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem eaOf3Dom (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (eaOf3 (GF := GF) GD L x γ) : GSet Geid) =
      LawfulSet.ofList GD.gdG.gxGmo := by
  have Hnd := (schedHGwf GD Hcons).1
  rw [setEq]
  intro e
  rw [elemOfDom, elemOfListToSet]
  constructor
  · intro Hv
    by_cases Hin : e ∈ GD.gdG.gxGmo
    · exact Hin
    · unfold eaOf3 at Hv
      rw [AxLockN.lgMapOfFunLookupNone _ _ e Hin] at Hv
      exact absurd Hv Bool.false_ne_true
  · intro Hin
    unfold eaOf3
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e Hin]
    rfl

theorem naEaDomEq3 (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName) :
    (FiniteMap.dom_set (eaOf3 (GF := GF) GD L x γ) : GSet Geid) =
      FiniteMap.dom_set (naOf3 (GF := GF) GD L x γ) := by
  rw [eaOf3Dom GD Hcons L x, naOf3Dom GD Hcons L x]

theorem HeaLob03 (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (eaOf3 (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ AxLockN.lockPred GD L x e0 := by
  have Hnd := (schedHGwf GD Hcons).1
  intro e0 gm Hea
  by_cases Hin : e0 ∈ GD.gdG.gxGmo
  · unfold eaOf3 at Hea
    rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd e0 Hin] at Hea
    cases Option.some.inj Hea
    unfold eaVal3 AxLockN.lockPred
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
  · unfold eaOf3 at Hea
    rw [AxLockN.lgMapOfFunLookupNone _ _ e0 Hin] at Hea
    cases Hea

/-- Restated at the literal `lobp` projection. -/
theorem HeaLob0Lobp3 (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (Hxl : x ≠ L)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ : GName) :
    ∀ e0 gm, get? (eaOf3 (GF := GF) GD L x γ) e0 = some gm →
      (FiniteMap.dom_set gm : GSet Geid) ⊆ @Axpol.lobp (axlocknPol GD L x) GD e0 :=
  HeaLob03 GD Hcons L x Hxl HrelFence HacqRead HacqAq γ

end annot

/-! # 2. The fixed concrete instance and `lockAdequateGhost3` -/

section fixedInst

variable {GF : BundledGFunctors} [AxlogG GF Hent] [AxLockG GF]

/-- Rocq `AxGn3_inst` (a fresh copy of `axGn2Inst`): `obStInterp` IS `protInvLock'`. -/
@[reducible] def AxLockN3.axGn3Inst (L x : Int) (γ γc : GName) : AxirisG GF where
  annotInterp := fun _ => iprop(True)
  gconstInterp := fun _ => iprop(True)
  obSt := GSet Geid × GMapF Geid (List Hent)
  obStInterp := fun GD0 σ s => protInvLock' L x γ γc GD0 s σ.1 σ.2
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem axGn3ObStInterpUnfold (L x : Int) (γ γc : GName) (GD0 : Gdexec)
    (σ : GSet Geid × GMapF Geid (List Hent)) (s : GSet Geid) :
    AxirisG.obStInterp (self := AxLockN3.axGn3Inst (GF := GF) L x γ γc) GD0 σ s ⊣⊢
      protInvLock' L x γ γc GD0 s σ.1 σ.2 :=
  ⟨.rfl, .rfl⟩

end fixedInst

section adequate

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxlogG GF Hent] [AxLockG GF]

theorem lockAdequateGhost3 (GD : Gdexec) (L x : Int) (Hxl : x ≠ L)
    (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (γ γc : GName)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit3 :
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN3.axGn3Inst L x γ γc) GD
          (eaOf3 GD L x γ) (naOf3 GD L x γ) GD.gdG.gxGmo 0) :
    ⊢ histAuth (GF := GF) γ x 1 ([] : List Hent) -∗ histAuth γ L 1 ([] : List Hent) -∗
      claimedAuth γc (∅ : GSet Geid) -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := AxLockN3.axGn3Inst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf3 GD L x γ) e0) := by
  have Hperm := gmoPermOfRun GD Hcons st Hrun Hfull Hdone
  have Htodo : ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 []) ⊢
      @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN3.axGn3Inst L x γ γc) GD
        (eaOf3 GD L x γ) (naOf3 GD L x γ) st.sProc 0 := by
    refine HflowInit3.trans ?_
    unfold ordEaTodoL
    simp only [List.drop_zero]
    exact (BigSepL.bigSepL_perm Hperm.symm).1
  have Hdom : (LawfulSet.ofList st.sProc : GSet Geid) ⊆
      FiniteMap.dom_set (naOf3 (GF := GF) GD L x γ) := by
    rw [naOf3Dom GD Hcons L x]
    intro e' He'
    rw [elemOfListToSet] at He' ⊢
    exact Hperm.mem_iff.1 He'
  have Had : ⊢ @ordEaTodoL (axlocknPol GD L x) hlc GF _ (AxLockN3.axGn3Inst L x γ γc) GD
        (eaOf3 GD L x γ) (naOf3 GD L x γ) st.sProc 0 -∗
      AxirisG.obStInterp (self := AxLockN3.axGn3Inst L x γ γc) GD
        ((∅, ∅) : GSet Geid × GMapF Geid (List Hent)) ∅ -∗
      |={⊤}[∅]▷=>^[st.sProc.length]
        ∃ (σ : GSet Geid × GMapF Geid (List Hent)),
          AxirisG.obStInterp (self := AxLockN3.axGn3Inst L x γ γc) GD σ
            (LawfulSet.ofList st.sProc) ∗
          [∗set] e0 ∈ (LawfulSet.ofList st.sProc : GSet Geid),
            AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf3 GD L x γ) e0) :=
    @schedProcAdequate hlc GF _ (AxLockN3.axGn3Inst L x γ γc) (axlocknPol GD L x)
      GD Hcons st Hrun Hfull Hdone
      (axlocknPredSubFlowSpol GD L x Hxl HrelFence HacqRead HacqAq)
      (axlocknPredSubFlowLobp GD L x Hxl HrelFence HacqRead HacqAq)
      (naOf3 GD L x γ) (eaOf3 GD L x γ)
      (naEaDomEq3 GD Hcons L x γ) Hdom
      (HeaLob0Lobp3 GD Hcons L x Hxl HrelFence HacqRead HacqAq γ) Hdefer
      ((∅, ∅) : GSet Geid × GMapF Geid (List Hent))
  have Hob0 : claimedAuth γc (∅ : GSet Geid) ⊢
      AxirisG.obStInterp (self := AxLockN3.axGn3Inst (GF := GF) L x γ γc) GD
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

/-! # 3. `lockDiscGeneric3` — the Prop-level extraction -/


section disc

variable {GF : BundledGFunctors} [AxlogG GF Hent]

/-- Lean-only: the final bag entry at an `x`-write yields the discipline fact. -/
theorem AxLockN3.naBagCs (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) (L x : Int) (γ : GName)
    (w : Geid) (vw : BitVec 8) (Hw : gwritesByte GD.gdG w x vw) :
    AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf3 (GF := GF) GD L x γ) w) ⊢
      ⌜AxLockN.xwIsCsWrite GD L w⌝ := by
  have Hnd := (schedHGwf GD Hcons).1
  have HinGmo : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (schedHGwf GD Hcons) Hw
  have Hisx : AxLockN.isWx GD x w = true := (gwaBSpec _ _ _).2 ⟨vw, Hw⟩
  unfold naOf3
  rw [AxLockN.lgMapOfFunLookupSome _ _ Hnd w HinGmo]
  simp only [AxWp.fromOption]
  unfold naVal''
  rw [if_pos Hisx]
  iintro ⟨%v, %data, -, -, %Hcs⟩
  ipureintro
  exact Hcs

end disc

theorem lockDiscGeneric3 {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit3 : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (AxLockN3.axGn3Inst L x γ γc) GD
          (eaOf3 GD L x γ) (naOf3 GD L x γ) GD.gdG.gxGmo 0)
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
  have Hfinal := lockAdequateGhost3 (hlc := .hasNoLC) GD L x Hxl Hcons HrelFence HacqRead
    HacqAq γ γc st Hrun Hfull Hdone Hdefer (HflowInit3 Hinv γ γc)
  rw [hk] at Hfinal
  ihave Hfin := Hfinal $$ Hx HL Hc
  iapply step_fupdN_wand $$ Hfin
  iintro ⟨%σ, -, Hbag⟩
  ihave Hw' := BigSepS.bigSepS_elem_of (Φ := fun e0 =>
    AxWp.fromOption (fun P => P) iprop(emp) (get? (naOf3 (GF := GF) GD L x γ) e0))
    Hin $$ Hbag
  iapply AxLockN3.naBagCs GD Hcons L x γ w vw Hw $$ Hw'

/-! # 4. `lockNSound3` — composing (3) with `AxLockSerial.csHandoffLast` -/

theorem lockNSound3 {GF : BundledGFunctors} [InvGpreS GF] [AxlogG GF Hent] [AxLockG GF]
    (GD : Gdexec) (L x : Int) (Hxl : x ≠ L) (Hcons : rvwmoCatConsistent GD)
    (HrelFence : ∀ e p, AxLockN.isRelL GD L e = true → AxLockN.relPredO GD L x e = some p →
      gobCatFlow GD p e)
    (HacqRead : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbIsR)
    (HacqAq : ∀ e', AxLockN.isAcqL GD L e' = true → glblIs GD.gdG e' lbAq)
    (st : Sstate) (Hrun : rtc (schedStep GD.gdG) sst0 st)
    (Hfull : st.sN = GD.gdG.gxGmo.length) (Hdone : st.sD = ∅)
    (Hdefer : ∀ r, deferredSnapAvail GD st.sEverD r)
    (HflowInit3 : ∀ (Hinv : InvGS_gen .hasNoLC GF) (γ γc : GName),
      ([∗set] a ∈ (({x} : GSet Int) ∪ {L}), histAuth (GF := GF) γ a 1 ([] : List Hent)) ⊢
        @ordEaTodoL (axlocknPol GD L x) .hasNoLC GF Hinv (AxLockN3.axGn3Inst L x γ γc) GD
          (eaOf3 GD L x γ) (naOf3 GD L x γ) GD.gdG.gxGmo 0)
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
        lockDiscGeneric3 GD L x Hxl Hcons HrelFence HacqRead HacqAq st Hrun Hfull Hdone Hdefer
          HflowInit3 w vw Hw
      obtain ⟨HneA, HneB⟩ := Hscope w vw Hne Hw acqk relk Hcsk Haqk Hpok Hcovk
      exact ⟨acqk, relk, Hcsk, Haqk, HneA, HneB, Hpok, Hcovk⟩
  exact csHandoffLast GD L x acqA relA acqB relB w_x r_x vx v v0 t_B t
    Hcons Hpat Hpair HcsA HaqA Hwx Hwx_po Hcov_wx HcsB HaqB Hharts
    Hrd_acqB Hsrc_acqB Hacq_po Hrd Hcov_rx Hdisc_x

/-! # 5. THE INITIAL-ACQUIRE FLOW RULE (Rocq §4, item (b)) -/

section initAcq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [axG : AxirisG GF] [Axpol]
  [AxlogG GF Hent] [AxLockG GF]
variable (γ γc : GName) (L x : Int)
variable (ob_D : AxirisG.obSt GF → GSet Geid) (ob_hm : AxirisG.obSt GF → GMapF Geid (List Hent))
  (mk_ob' : GSet Geid → GMapF Geid (List Hent) → AxirisG.obSt GF)
  (Hmk_ob'_D : ∀ D hm, ob_D (mk_ob' D hm) = D)
  (Hmk_ob'_hm : ∀ D hm, ob_hm (mk_ob' D hm) = hm)
  (Hob_eq' : ∀ (GD : Gdexec) (σ : AxirisG.obSt GF) (s : GSet Geid),
    AxirisG.obStInterp GD σ s ⊣⊢ protInvLock' L x γ γc GD s (ob_D σ) (ob_hm σ))

include Hmk_ob'_D Hmk_ob'_hm Hob_eq'

/-- The FIRST acquire's own step: an `L`-RMW writing `b1` with no predecessor — takes
`histAuth γ L 1 []` directly, discards the fresh tie; its own `ΦLock'` slot is vacuous
(`b1 ≠ b0`). -/
theorem flowEqAmoswapAqInit (GD : Gdexec) (i : Agent) (k : Nat)
    (Hwb1 : gwritesByte GD.gdG (i, k) L b1)
    (Hsingle : ∀ a' v', gwritesByte GD.gdG (i, k) a' v' → a' = L) :
    histAuth γ L 1 ([] : List Hent) ⊢
      flowEqDyn GD (i, k) (Axpol.sPol GD (i, k)) (∅ : Mea GF) iprop(emp) := by
  iintro HaL
  unfold flowEqDyn
  iintro %σ %sOb %Hsub %Hnin Hob -
  ihave Hob := (Hob_eq' GD σ sOb).1 $$ Hob
  icases (protInvLockUnfold' L x γ γc GD sOb (ob_D σ) (ob_hm σ)).1 $$ Hob
    with ⟨Hc, Hpo, Hlocks⟩
  imod protInvWriteStep γ GD sOb (i, k) L b1 [] Hnin Hwb1 Hsingle $$ [$Hpo $HaL]
    with ⟨Hpo', -⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  inext
  imod Hclose
  imodintro
  iexists mk_ob' (ob_D σ) (ob_hm σ)
  isplitl [Hc Hpo' Hlocks]
  · iapply (Hob_eq' GD (mk_ob' (ob_D σ) (ob_hm σ)) (({(i, k)} : GSet Geid) ∪ sOb)).2
    rw [Hmk_ob'_D, Hmk_ob'_hm]
    iapply (protInvLockUnfold' L x γ γc GD (({(i, k)} : GSet Geid) ∪ sOb) (ob_D σ)
      (ob_hm σ)).2
    isplitl [Hc]
    · iexact Hc
    isplitl [Hpo']
    · iexact Hpo'
    iapply (AxProtLock.bigSepSUnionSingleton
      (Φ := fun e => ΦLock' L x γ γc GD e ((get? (ob_hm σ) e).getD [])) Hnin).2
    isplitl []
    · iapply AxProtLock.ΦLock'Vacuous L x γ γc GD (i, k) _
        (fun hbad => b0NeB1 (gwritesByteDet _ _ _ _ _ hbad Hwb1))
    · iexact Hlocks
  · iempintro

end initAcq

end Weak
