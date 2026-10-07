/-
Weak: **`WPd` THREADED ACROSS A RUN** (AxSL tier; design §7.A, milestone A3: the single step
`wpdStepAnnotM`, the multi-step `wpdNstepsM`/`wpdStepsM`).

Rocq: `iris/AxWpDSteps.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxAdequacy.stepAnnot` needs a SHADOW state `sw` (same position as the external target `s'`,
otherwise unrelated) because `AxWp.wp`'s read arm is angelic.  `wpdM`'s read arm is PINNED to the
graph value, so for a REAL step whose read (if any) reads `graphValue GD (i, s.atK)` there is no
value to guess: `wpdStepAnnotM`'s target is literally `s'`.  §1: the graph-pinned step relation
`astepAnyNfGv` — `AxAdequacy.astepAnyNf` with the read arm's free value replaced by the graph's
value.  §1.5: domain-pinning helpers — only hart `i`'s own slice of `na`'s domain ever moves, so a
second hart's `naAtProgress … 0` survives the run.  §2: the single step (write/fence/admin/wire
arms as `stepAnnot`; the read arm without the shadow).  §3: `wpdStepsN n P`, `n` copies of
`|==> ▷` capped by `|==>` (always `|==>`-headed, so per-step composition is one
`imod`/`imodintro`/`inext` chain); `wpdNstepsM` over `nsteps`, `wpdStepsM` over `rtc`, and the
embedding `wpdStepsNStepFupdN` into the iterated step-fupd.

## Deviations from Rocq

1. NAMES: camelCase (map below); `S k` ↦ `k + 1`; `dom` ↦ `FiniteMap.dom_set … : GSet Geid`,
   `filter (λ e, e.1 ≠ i)` ↦ `FiniteSet.filter (fun e => decide (e.1 ≠ i))`, map unions ↦
   `PartialMap.union` (AxWp/AxAdequacy conventions); `|={⊤}[∅]▷=>^n` ↦ `|={⊤}[∅]▷=>^[n]`.
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`.  Wand chains are stated
   `⊢ A -∗ B -∗ …` (AxWp deviation 7).
2. O2 STAGE C: no fetch arm and no `ax_text` oracle — `astepAnyNfGv`'s program arm is
   `astepProgNf (AxOpsem.grow GD i) GD.gdG.gxImg` (Q8: the step carries the boot-image pin
   `WeakAxRealize.fetchPin`, Rocq's `gx_img (gd_g GD)` argument; `wpdStepAnnotM`'s program arm
   hands it to `wpdMPreStepDef`'s step clause), `astepAnyNfGvNf` lands in
   `astepAnyNf (AxOpsem.grow GD i) GD.gdG.gxImg`, and the fence arm calls `astepProgNodataFenceGmem` without
   the `wlabel_is_fetch` premise (AxAdequacy deviation 2).
3. `wpdStepsN` is defined by two equations (`0`, `n + 1`), each `|==>`-headed; Rocq's single
   `|==> match …` body is `wpdStepsNUnfold` (stated with the `match`).  The `|==>` elimination
   under an abstract `n` uses the Lean-only `AxWpDSteps.bupdWpdStepsN` instead of Rocq's
   `rewrite wpdStepsN_unfold`/`-wpdStepsN_unfold` round trip.
4. Lean-only helpers (file-qualified): `AxWpDSteps.evCase`/`AxWpDSteps.skipCase` (the annotated /
   unannotated arms of `wpdStepAnnotM`, as `AxAdequacy.evCase`/`skipCase`), `AxWpDSteps.nstepsSuccInv`
   (head inversion of `nsteps`, which is tail-built in Lean), `AxWpDSteps.bupdWpdStepsN`.
   `naDomGrowFull`'s set arguments are stated as the three `dom`s it is applied to.
5. The old-name `Definition`s (`wpd_step_annot`, `wpd_nsteps`, `wpd_steps`) are theorems with
   their statements spelled out at `rvwmoCatConsistent`.

**Rocq → Lean name map.**  `astep_any_nf_gv` `astepAnyNfGv` (`ANFGVProg`/`ANFGVWire`/
`ANFGVRead`), `astep_any_nf_gv_nf` `astepAnyNfGvNf`, `na_dom_pin_refl` `naDomPinRefl`,
`na_dom_pin_refl_iprop` `naDomPinReflIprop`, `na_dom_grow_full` `naDomGrowFull`,
`na_dom_other_stable` `naDomOtherStable`, `wpd_step_annotM` `wpdStepAnnotM`, `wpd_step_annot`
`wpdStepAnnot`, `wpd_stepsN` `wpdStepsN`, `wpd_stepsN_O` `wpdStepsNO`, `wpd_stepsN_S`
`wpdStepsNS`, `wpd_stepsN_unfold` `wpdStepsNUnfold`, `wpd_stepsN_mono` `wpdStepsNMono`,
`wpd_nstepsM` `wpdNstepsM`, `wpd_stepsM` `wpdStepsM`, `wpd_stepsN_step_fupdN`
`wpdStepsNStepFupdN`, `wpd_nsteps` `wpdNsteps`, `wpd_steps` `wpdSteps`.

**Dropped:** only the §4 `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWpD
import Weak.AxAdequacy

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The graph-pinned step relation -/

section astepGv

/-- `astepAnyNf` with the read arm's free value replaced by the GRAPH's value at the position. -/
inductive astepAnyNfGv (GD : Gdexec) (i : Agent) : Athread → Athread → Prop where
  | ANFGVProg (s s' : Athread) :
      astepProgNf (AxOpsem.grow GD i) GD.gdG.gxImg s s' → astepAnyNfGv GD i s s'
  | ANFGVWire (s s' : Athread) : awire s s' → astepAnyNfGv GD i s s'
  | ANFGVRead (s : Athread) (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
      areadStep (AxOpsem.grow GD i) s id K →
      graphValue GD (i, s.atK) = some v →
      v.length = aidentN id →
      astepAnyNfGv GD i s (K v)

/-- Every graph-pinned step is an `astepAnyNf` step. -/
theorem astepAnyNfGvNf (GD : Gdexec) (i : Agent) (s s' : Athread) :
    astepAnyNfGv GD i s s' → astepAnyNf (AxOpsem.grow GD i) GD.gdG.gxImg s s'
  | .ANFGVProg _ _ h => .ANFProg _ _ h
  | .ANFGVWire _ _ h => .ANFWire _ _ h
  | .ANFGVRead _ id K v hrd _ hlen => .ANFRead _ id K v hrd hlen

end astepGv

/-! # 1.5. Domain-pinning helpers -/

/-- The partition of a whole domain into hart `i`'s slice and the rest. -/
theorem naDomPinRefl (i : Agent) (X : GSet Geid) (GD : Gdexec) (k : Nat) :
    FiniteSet.filter (fun e : Geid => decide (e.1 = i)) X = eidsBefore GD i k →
    X = FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) X ∪ eidsBefore GD i k := by
  intro Hna
  rw [← Hna, setEq]
  intro e
  simp only [elemOfUnion, elemOfFilter, decide_eq_true_eq]
  constructor
  · intro He
    by_cases h : e.1 = i
    · exact .inr ⟨h, He⟩
    · exact .inl ⟨h, He⟩
  · rintro (⟨_, He⟩ | ⟨_, He⟩) <;> exact He

theorem naDomPinReflIprop {GF : BundledGFunctors} (GD : Gdexec) (i : Agent) (na : Mea GF)
    (k : Nat) :
    naAtProgress GD i k na ⊢
      ⌜(FiniteMap.dom_set na : GSet Geid) =
        FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
          eidsBefore GD i k⌝ := by
  unfold naAtProgress
  iintro %Hna
  ipureintro
  exact naDomPinRefl i _ GD k Hna

/-- `naDomGrow`'s FULL-domain strengthening: the whole domain grows by exactly `(i,k)`. -/
theorem naDomGrowFull [Axpol] (Hwf : axpolWf) (i : Agent) (Xna Xnu Xnuu : GSet Geid)
    (GD : Gdexec) (k : Nat) :
    FiniteSet.filter (fun e : Geid => decide (e.1 = i)) Xna = eidsBefore GD i k →
    Xnu ⊆ Axpol.lobp GD (i, k) → Xnu = Xnuu →
    gmemB GD.gdG (i, k) = true →
    ({(i, k)} : GSet Geid) ∪ Xnuu ∪ Xna =
      FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) Xna ∪ eidsBefore GD i (k + 1) := by
  intro Hna Hsub Heq Hgmem
  have HnuNa : ∀ x, x ∈ Xnuu → x ∈ Xna := by
    intro x hx
    rw [← Heq] at hx
    exact lobpSubDom Hwf GD i k _ Hna x (Hsub x hx)
  rw [eidsBeforeSMem GD i k Hgmem, ← Hna, setEq]
  intro x
  simp only [elemOfUnion, elemOfSingleton, elemOfFilter, decide_eq_true_eq]
  constructor
  · rintro ((rfl | hx) | hx)
    · exact .inr (.inl rfl)
    · have hx' := HnuNa x hx
      by_cases h : x.1 = i
      · exact .inr (.inr ⟨h, hx'⟩)
      · exact .inl ⟨h, hx'⟩
    · by_cases h : x.1 = i
      · exact .inr (.inr ⟨h, hx⟩)
      · exact .inl ⟨h, hx⟩
  · rintro (⟨_, hx⟩ | rfl | ⟨_, hx⟩)
    · exact .inr hx
    · exact .inl (.inl rfl)
    · exact .inr hx

/-- The non-`i` slice of a pinned domain is the starting domain's non-`i` slice. -/
theorem naDomOtherStable (i : Agent) (X Y : GSet Geid) (GD : Gdexec) (k : Nat) :
    Y = FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) X ∪ eidsBefore GD i k →
    FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) Y =
      FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) X := by
  intro HY
  subst HY
  rw [setEq]
  intro e
  simp only [elemOfFilter, elemOfUnion, decide_eq_true_eq, elemOfEidsBefore]
  constructor
  · rintro ⟨hne, ⟨_, hx⟩ | ⟨heq, _⟩⟩
    · exact ⟨hne, hx⟩
    · exact absurd heq hne
  · rintro ⟨hne, hx⟩
    exact ⟨hne, .inl ⟨hne, hx⟩⟩

/-! # 2. The single step -/

section wpdStep
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Lean-only: the annotated arms (write; pinned read). -/
theorem AxWpDSteps.evCase (Hwf : axpolWf) (GD : Gdexec) (Hgwf : gwf GD.gdG) (i : Agent)
    (k : Nat) (Hgmem : gmemB GD.gdG (i, k) = true) (ok val : Unit → Prop) (k' : Nat)
    (hk' : k' = k + 1) (na : Mea GF) (ea : Sra GF) (W : IProp GF)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k) :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗
      wpEvStep GD i k ok val (fun _ => k') (fun _ => W) -∗
      |==> ▷ |==> ∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i k' na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i k'⌝ ∗
        AxirisG.annotInterp na' ∗ eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i k' ls' ∗ W := by
  subst hk'
  iintro Hannot Hea Hb
  iunfold wpEvStep at Hb
  ihave Hpre : naAtProgress GD i k na $$ []
  · iunfold naAtProgress
    ipureintro
    exact Hna
  imod Hb $$ %na [$Hpre $Hannot] with Hb
  imodintro
  inext
  imod Hb with ⟨%a, %R, %nu, %nuu, %ls', %_, #Hsplit, Hfe, Hannot', Hloc', HΨ⟩
  ihave %Hd := naSplittingWfDom (Axpol.lobp GD (i, k)) na nu nuu $$ Hsplit
  ihave Hfe' := AxAdequacy.flowEqDynDropPure GD (i, k) (Axpol.sPol GD (i, k)) nu R (val a) $$ Hfe
  ihave Hea' := eaLocalWfEvStep Hwf GD i k na ea nu nuu R Hgwf Hgmem Hna $$ Hsplit Hea Hfe'
  imodintro
  iexists PartialMap.union (PartialMap.union {[(i, k) := R]} nuu) na,
    PartialMap.union {[(i, k) := nu]} ea, ls'
  isplitr
  · iunfold naAtProgress
    ipureintro
    exact naDomGrow Hwf GD i k na nu nuu R Hna Hd.1 Hd.2 Hgmem
  isplitr
  · ipureintro
    rw [AxLifting.domUnionG, AxLifting.domUnionG, domSingleton]
    exact naDomGrowFull Hwf i _ _ _ GD k Hna Hd.1 Hd.2 Hgmem
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea']
  · iexact Hea'
  isplitl [Hloc']
  · iexact Hloc'
  · iexact HΨ

/-- Lean-only: the unannotated arms (fence/admin, wire, RMW read half). -/
theorem AxWpDSteps.skipCase (GD : Gdexec) (i : Agent) (k k' : Nat) (na : Mea GF) (ea : Sra GF)
    (W : IProp GF)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k)
    (Heq : eidsBefore GD i k = eidsBefore GD i k') :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗ wpSkipStep GD i k' W -∗
      |==> ▷ |==> ∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i k' na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i k'⌝ ∗
        AxirisG.annotInterp na' ∗ eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i k' ls' ∗ W := by
  iintro Hannot Hea Hb
  iunfold wpSkipStep at Hb
  imod Hb $$ %na Hannot with Hb
  imodintro
  inext
  imod Hb with ⟨%ls', Hannot', Hloc', HΨ⟩
  imodintro
  iexists na, ea, ls'
  isplitr
  · iunfold naAtProgress
    ipureintro
    rw [← Heq]
    exact Hna
  isplitr
  · ipureintro
    rw [← Heq]
    exact naDomPinRefl i _ GD k Hna
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea]
  · iexact Hea
  isplitl [Hloc']
  · iexact Hloc'
  · iexact HΨ

variable (M : Gdexec → Prop) [GModel M]

/-- THE SINGLE STEP: the target is the external step's own `s'` (no shadow). -/
theorem wpdStepAnnotM (GD : Gdexec) (Hwf : axpolWf) (Hcons : M GD) (i : Agent)
    (st : Stuckness) (s s' : Athread) (Hstep : astepAnyNfGv GD i s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpdM M st i s Φ -∗
      |==> ▷ |==> ∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpdM M st i s' Φ := by
  have Hgwf := gmGwf GD Hcons
  iintro Hnap Hannot Hea Hloc #Hgconst H
  iunfold naAtProgress at Hnap
  icases Hnap with %Hna
  ihave H := (AxWpD.wpdMUnfoldStep M st i s Φ).1 $$ H
  icases H with ⟨-, H⟩
  iunfold wpdMPreStepDef at H
  ihave Hpre : (⌜M GD⌝ ∗ □ AxirisG.gconstInterp GD ∗
      AxirisG.localInterp GD i s.atK ls) $$ [Hloc]
  · isplitr
    · ipureintro
      exact Hcons
    · isplitr
      · imodintro
        iexact Hgconst
      · iexact Hloc
  ihave Habc := H $$ %GD %ls Hpre
  cases Hstep with
  | ANFGVProg _ Hprog =>
    obtain ⟨l, Hap, Hpin⟩ := Hprog
    icases Habc with ⟨-, Hb, -⟩
    ihave Hb := Hb $$ %l %s' %Hap %Hpin
    cases hwd : wlWdata l with
    | some data =>
      have Hgmem := astepProgWdataGmem GD i s l s' data Hap hwd
      have Hk := astepProgWdataSk _ s l s' data Hap hwd
      try isimp only [] at Hb
      iapply AxWpDSteps.evCase Hwf GD Hgwf i s.atK Hgmem (fun _ => True)
        (fun _ => graphData GD (i, s.atK) = some data) s'.atK Hk na ea (wpdM M st i s' Φ) Hna
        $$ Hannot Hea Hb
    | none =>
      have Heq : eidsBefore GD i s.atK = eidsBefore GD i s'.atK := by
        rcases astepProgNodataK _ s l s' Hap hwd with hk | hk
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK (.inl hk)
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK
            (.inr ⟨hk, astepProgNodataFenceGmem GD i s l s' Hap hwd hk⟩)
      try isimp only [] at Hb
      iapply AxWpDSteps.skipCase GD i s.atK s'.atK na ea (wpdM M st i s' Φ) Hna Heq
        $$ Hannot Hea Hb
  | ANFGVWire _ Hw =>
    icases Habc with ⟨-, -, Hc, -⟩
    ihave Hc := Hc $$ %s' %Hw
    iapply AxWpDSteps.skipCase GD i s.atK s'.atK na ea (wpdM M st i s' Φ) Hna (by rw [Hw.1])
      $$ Hannot Hea Hc
  | ANFGVRead id K v Hrd Hgv Hlenv =>
    icases Habc with ⟨Ha, -⟩
    ihave Ha := Ha $$ %id %K %Hrd
    by_cases Hadv : aidentAdvRd id = 1
    · isimp only [if_pos Hadv] at Ha
      ihave Ha := Ha $$ %v %Hgv %Hlenv
      have Hgmem := areadStepGmem GD i s id K Hrd
      iapply AxWpDSteps.evCase Hwf GD Hgwf i s.atK Hgmem (fun _ => True)
        (fun _ => graphValue GD (i, s.atK) = some v) (K v).atK
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, Hadv]) na ea (wpdM M st i (K v) Φ) Hna
        $$ Hannot Hea Ha
    · have Hadv0 := aidentAdvRdNot1 id Hadv
      isimp only [if_neg Hadv] at Ha
      ihave Ha := Ha $$ %v %Hgv %Hlenv
      iapply AxWpDSteps.skipCase GD i s.atK (K v).atK na ea (wpdM M st i (K v) Φ) Hna
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, Hadv0, Nat.add_zero]) $$ Hannot Hea Ha

end wpdStep

section wpdCatStep
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `wpd_step_annot` (the riscv.cat instance). -/
theorem wpdStepAnnot (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD) (i : Agent)
    (st : Stuckness) (s s' : Athread) (Hstep : astepAnyNfGv GD i s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpd st i s Φ -∗
      |==> ▷ |==> ∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpd st i s' Φ :=
  wpdStepAnnotM rvwmoCatConsistent GD Hwf Hcons i st s s' Hstep na ea ls Φ

end wpdCatStep

/-! # 3. The multi-step lemma -/

section wpdStepsN
variable {GF : BundledGFunctors}

/-- `n` copies of `|==> ▷`, capped by a final `|==>` (deviation 3). -/
def wpdStepsN : Nat → IProp GF → IProp GF
  | 0, P => iprop(|==> P)
  | n + 1, P => iprop(|==> ▷ wpdStepsN n P)

theorem wpdStepsNO (P : IProp GF) : wpdStepsN 0 P ⊣⊢ iprop(|==> P) := .rfl

theorem wpdStepsNS (n : Nat) (P : IProp GF) :
    wpdStepsN (n + 1) P ⊣⊢ iprop(|==> ▷ wpdStepsN n P) := .rfl

/-- The generic unfold, at a variable `n`. -/
theorem wpdStepsNUnfold (n : Nat) (P : IProp GF) :
    wpdStepsN n P ⊣⊢ iprop(|==> (match n with | 0 => P | n' + 1 => iprop(▷ wpdStepsN n' P))) := by
  cases n <;> exact .rfl

/-- Lean-only: `wpdStepsN n` absorbs a leading `|==>` (at a variable `n`). -/
theorem AxWpDSteps.bupdWpdStepsN (n : Nat) (P : IProp GF) :
    iprop(|==> wpdStepsN n P) ⊢ wpdStepsN n P := by
  cases n with
  | zero =>
    simp only [wpdStepsN]
    iintro H
    imod H
    iexact H
  | succ n =>
    simp only [wpdStepsN]
    iintro H
    imod H
    iexact H

theorem wpdStepsNMono (n : Nat) (P Q : IProp GF) :
    iprop(P -∗ Q) ⊢ wpdStepsN n P -∗ wpdStepsN n Q := by
  induction n with
  | zero =>
    simp only [wpdStepsN]
    iintro HPQ H
    imod H
    imodintro
    iapply HPQ $$ H
  | succ n ih =>
    simp only [wpdStepsN]
    iintro HPQ H
    imod H
    imodintro
    inext
    iapply ih $$ HPQ H

/-- Embedding into the iterated step-fupd. -/
theorem wpdStepsNStepFupdN {hlc : HasLC} [InvGS_gen hlc GF] (n : Nat) (P : IProp GF) :
    wpdStepsN n P ⊢ iprop(|={⊤}[∅]▷=>^[n] |={⊤}=> P) := by
  induction n with
  | zero =>
    show iprop(|==> P) ⊢ iprop(|={⊤}=> P)
    iintro H
    imod H
    imodintro
    iexact H
  | succ n ih =>
    show iprop(|==> ▷ wpdStepsN n P) ⊢ iprop(|={⊤}[∅]▷=> |={⊤}[∅]▷=>^[n] |={⊤}=> P)
    iintro H
    imod H
    iapply (step_fupd_intro LawfulSet.empty_subset)
    inext
    iapply ih $$ H

end wpdStepsN

/-- Lean-only: head inversion of `nsteps` (tail-built in Lean). -/
theorem AxWpDSteps.nstepsSuccInv {A : Type _} {R : A → A → Prop} {n : Nat} {x z : A}
    (h : nsteps R (n + 1) x z) : ∃ y, R x y ∧ nsteps R n y z := by
  induction n generalizing z with
  | zero =>
    cases h with
    | tail y h1 h2 =>
      cases h1 with
      | rfl => exact ⟨z, h2, nsteps_O z⟩
  | succ m ih =>
    cases h with
    | tail y h1 h2 =>
      obtain ⟨w, hxw, hwy⟩ := ih h1
      exact ⟨w, hxw, nsteps_r hwy h2⟩

section wpdSteps
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop) [GModel M]

/-- The workhorse, over `nsteps` (supplies the step count). -/
theorem wpdNstepsM (GD : Gdexec) (Hwf : axpolWf) (Hcons : M GD) (i : Agent) (st : Stuckness)
    (n : Nat) :
    ∀ (s s' : Athread), nsteps (astepAnyNfGv GD i) n s s' →
    ∀ (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF),
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpdM M st i s Φ -∗
      wpdStepsN n iprop(∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpdM M st i s' Φ) := by
  induction n with
  | zero =>
    intro s s' Hsteps na ea ls Φ
    cases Hsteps
    iintro Hna Hannot Hea Hloc #_ H
    ihave %Hdom := naDomPinReflIprop GD i na s.atK $$ Hna
    simp only [wpdStepsN]
    imodintro
    iexists na, ea, ls
    isplitl [Hna]
    · iexact Hna
    isplitr
    · ipureintro
      exact Hdom
    isplitl [Hannot]
    · iexact Hannot
    isplitl [Hea]
    · iexact Hea
    isplitl [Hloc]
    · iexact Hloc
    · iexact H
  | succ n IHn =>
    intro s s' Hsteps na ea ls Φ
    obtain ⟨y, Hxy, Hyz⟩ := AxWpDSteps.nstepsSuccInv Hsteps
    iintro Hna Hannot Hea Hloc #Hgconst H
    ihave H := wpdStepAnnotM M GD Hwf Hcons i st s y Hxy na ea ls Φ
      $$ Hna Hannot Hea Hloc Hgconst H
    simp only [wpdStepsN]
    imod H
    imodintro
    inext
    iapply AxWpDSteps.bupdWpdStepsN
    imod H with ⟨%na1, %ea1, %ls1, Hna1, %Hdom1, Hannot1, Hea1, Hloc1, H⟩
    imodintro
    ihave Hrec := IHn y s' Hyz na1 ea1 ls1 Φ $$ Hna1 Hannot1 Hea1 Hloc1 Hgconst H
    iapply wpdStepsNMono $$ [] Hrec
    iintro ⟨%na', %ea', %ls', Hna', %Hdom2, Hannot', Hea', Hloc', HΦ⟩
    iexists na', ea', ls'
    isplitl [Hna']
    · iexact Hna'
    isplitr
    · ipureintro
      rw [naDomOtherStable i _ _ GD y.atK Hdom1] at Hdom2
      exact Hdom2
    isplitl [Hannot']
    · iexact Hannot'
    isplitl [Hea']
    · iexact Hea'
    isplitl [Hloc']
    · iexact Hloc'
    · iexact HΦ

/-- The `rtc`-phrased form (existential step count). -/
theorem wpdStepsM (GD : Gdexec) (Hwf : axpolWf) (Hcons : M GD) (i : Agent) (st : Stuckness)
    (s s' : Athread) (Hsteps : rtc (astepAnyNfGv GD i) s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpdM M st i s Φ -∗
      ∃ n, wpdStepsN n iprop(∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpdM M st i s' Φ) := by
  obtain ⟨n, Hn⟩ := rtc_nsteps_1 Hsteps
  iintro Hna Hannot Hea Hloc #Hgconst H
  iexists n
  iapply wpdNstepsM M GD Hwf Hcons i st n s s' Hn na ea ls Φ $$ Hna Hannot Hea Hloc Hgconst H

end wpdSteps

section wpdCatSteps
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `wpd_nsteps` (the riscv.cat instance). -/
theorem wpdNsteps (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD) (i : Agent)
    (st : Stuckness) (n : Nat) :
    ∀ (s s' : Athread), nsteps (astepAnyNfGv GD i) n s s' →
    ∀ (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF),
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpd st i s Φ -∗
      wpdStepsN n iprop(∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpd st i s' Φ) :=
  wpdNstepsM rvwmoCatConsistent GD Hwf Hcons i st n

/-- Rocq `wpd_steps` (the riscv.cat instance). -/
theorem wpdSteps (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD) (i : Agent)
    (st : Stuckness) (s s' : Athread) (Hsteps : rtc (astepAnyNfGv GD i) s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpd st i s Φ -∗
      ∃ n, wpdStepsN n iprop(∃ (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        naAtProgress GD i s'.atK na' ∗
        ⌜(FiniteMap.dom_set na' : GSet Geid) =
          FiniteSet.filter (fun e : Geid => decide (e.1 ≠ i)) (FiniteMap.dom_set na : GSet Geid) ∪
            eidsBefore GD i s'.atK⌝ ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i s'.atK ls' ∗
        wpd st i s' Φ) :=
  wpdStepsM rvwmoCatConsistent GD Hwf Hcons i st s s' Hsteps na ea ls Φ

end wpdCatSteps

end Weak
