/-
Weak: **CHECKPOINT ADEQUACY** (AxSL tier): `wpc`'s per-hart T4 obligation (design §0's
"chkp i s" clause of `xv6_rvwmo_safe_ax`), a port of AxSL's `low/adequacy_chk.v` over
`AxAdequacy`'s single-hart phase-1 machinery (`stepAnnot`, `expectedRun`).

Rocq: `iris/AxAdequacyChk.v` @ xxvzwolszwmp.

## The Rocq header, in substance

AxSL's `adequacy_chk.v` recipe ("copy phases 1/2 of `adequacy.v` with `Φ` replaced by
`Psi_chk tid Φ`") needs AxSL's multi-step phase 1 (`wp_steps`), which `AxAdequacy` does NOT
deliver (its §4 multi-step finding: angelic reads make the external run and `wp`'s shadow run
agree only in row position).  Phase 2 (`adequacyOrd`) IS delivered, but needs full gmo coverage,
whose derivation needs the same run-pairing / fresh-construction machinery.  So this file
delivers only what needs neither:
§1 `psiChk`/`chkPure`/`postLiftingPsiChk`/`psiChkPure` — the composite postcondition and its
   meta-extractability (`isTerminated s = false` always, so `psiChk i Φ` is extensionally
   `chk i`; the terminated half is kept for fidelity).
§2 `stepChkAnnot` — the `wpc` analogue of `AxAdequacy.stepAnnot`: `wpPreStepDef` is parametric
   in its continuation, so `stepAnnot`'s argument transports with `AxWp.wp st i` replaced by
   `wpc st i`, after peeling `wpc` to its step obligation (`wpcUnfoldStep`).  The base case, not
   its iteration (same multi-step gap as `stepAnnot`).
§3 `adequate`/`adequateChk` — PER-HART `Prop` records (quantified over every state the hart's
   `expectedRun` reaches) and `adequateChkAdequate` (forget the checkpoint half).

NOT DELIVERED (as in Rocq): `wpc_adequacy`, `wp_adequacy_of_wpc`,
`adequacy_pure_partial_of_chk` and the LB non-vacuity artifact `lb_stack_nonvacuous` — Rocq
states them in prose only (no declarations), blocked on the multi-step composition (a).

## Deviations from Rocq

1. NAMES camelCase (map below); `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`;
   wand chains stated `⊢ A -∗ B -∗ …` (AxWp deviations 6/7); `WPc s @ st; i {{ Φ }}` ↦
   `wpc st i s Φ`.
2. O2 STAGE C: `astep_any_nf`, `not_stuck_gd`, `expected_run` lose the oracle parameter
   `ax_text` (AxAdequacy deviation 2; Q8: the image `img` is back on `astepAnyNf`, fixed at
   `GD.gdG.gxImg` as Rocq's `gx_img (gd_g GD)`), so the records need no `AxirisG` instance
   (Rocq's section context `axirisG Σ` is dropped there).
3. STEP-CLAUSE HANDLING LOCALIZED.  The Lean `AxAdequacy.stepAnnot` (and its helpers
   `AxAdequacy.evCase`/`skipCase`) is stated at the fixed continuation `AxWp.wp st i`, so it
   cannot be instantiated at `wpc st i`.  This file re-proves it ONCE, generic in the
   continuation `wpF : Athread → (Athread → IProp GF) → IProp GF`, as the Lean-only
   `AxAdequacyChk.stepAnnotGen` (with `AxAdequacyChk.evCaseGen`/`skipCaseGen`); `stepChkAnnot`
   is `wpcUnfoldStep` + `stepAnnotGen (wpc st i)`.  Every dependency on `wpPreStepDef`'s step
   clauses lives in `stepAnnotGen`; under Q8 it hands the step's `WeakAxRealize.fetchPin` (from
   `astepProgNf` at `GD.gdG.gxImg`) to the clause, as `AxAdequacy.stepAnnot` does.
4. `wpc_unfold_step` here is Rocq's one-way peel; the iff `AxWp.wpcUnfoldStep` (AxWp2) is a
   different, Lean-only lemma.  The two names coexist (`Weak.wpcUnfoldStep` vs
   `Weak.AxWp.wpcUnfoldStep`).
5. Record fields: Rocq record projections ↦ Lean structure fields with the same camelCase names;
   Rocq's `AThread pfin kfin` ↦ `⟨pfin, kfin⟩`.

**Rocq → Lean name map.**  `Psi_chk` `psiChk`, `chk_pure` `chkPure`, `post_lifting_Psi_chk`
`postLiftingPsiChk`, `Psi_chk_pure` `psiChkPure`, `wpc_unfold_step` `wpcUnfoldStep`,
`step_chk_annot` `stepChkAnnot`, `adequate` `adequate` (`adequate_not_stuck` `adequateNotStuck`,
`adequate_result` `adequateResult`), `adequate_chk` `adequateChk` (`adequate_chk_not_stuck`
`adequateChkNotStuck`, `adequate_chk_result` `adequateChkResult`), `adequate_chk_adequate`
`adequateChkAdequate`.  Lean-only: `AxAdequacyChk.skipCaseGen`, `AxAdequacyChk.evCaseGen`,
`AxAdequacyChk.stepAnnotGen`.

**Dropped:** only the §4 `Print Assumptions` block (the lint's axiom check covers it).  No premise
is carried beyond Rocq's own.
-/
import Weak.AxAdequacy

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The composite postcondition `psiChk` -/

section psiChk
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
  [AxirisGChk GF]

/-- At a terminated state, the user's postcondition; otherwise the checkpoint. -/
def psiChk (i : Agent) (Φ : Athread → IProp GF) : Athread → IProp GF :=
  fun s => if isTerminated s then Φ s else AxirisGChk.chk i s

/-- `chk` is extractable at the meta level. -/
def chkPure (chkp : Agent → Athread → Prop) : Prop :=
  ∀ i s, AxirisGChk.chk (GF := GF) i s ⊢ iprop(⌜chkp i s⌝)

/-- `wpc`'s per-step disjunction is literally `postLifting (psiChk i Φ) i s`. -/
theorem postLiftingPsiChk (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    (if isTerminated s then postLifting Φ i s else postLifting (AxirisGChk.chk i) i s)
      = postLifting (psiChk i Φ) i s := by
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `psiChk` at a pure postcondition is pure, given `chkPure`. -/
theorem psiChkPure (chkp : Agent → Athread → Prop) (Hchkp : chkPure (GF := GF) chkp)
    (i : Agent) (Φp : Athread → Prop) (s : Athread) :
    psiChk (GF := GF) i (fun v => iprop(⌜Φp v⌝)) s ⊢
      iprop(⌜(terminated s → Φp s) ∧ (¬ terminated s → chkp i s)⌝) := by
  unfold psiChk
  cases Hterm : isTerminated s with
  | true =>
    simp only [↓reduceIte]
    have Hts := (isTerminatedTerminated s).1 Hterm
    refine pure_mono ?_
    intro HΦ
    exact ⟨fun _ => HΦ, fun Hnt => absurd Hts Hnt⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (Hchkp i s).trans (pure_mono ?_)
    intro Hc
    refine ⟨fun Ht => ?_, fun _ => Hc⟩
    have := (isTerminatedTerminated s).2 Ht
    rw [Hterm] at this
    exact absurd this Bool.false_ne_true

end psiChk

/-! # 2. The single `wpc` step -/

section stepChk
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Lean-only: `AxAdequacy.skipCase` at an arbitrary continuation `wpF`. -/
theorem AxAdequacyChk.skipCaseGen (wpF : Athread → (Athread → IProp GF) → IProp GF)
    (GD : Gdexec) (i : Agent) (k : Nat)
    (sw s' : Athread) (na : Mea GF) (ea : Sra GF) (Φ : Athread → IProp GF)
    (hk : sw.atK = s'.atK)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k)
    (Heq : eidsBefore GD i k = eidsBefore GD i sw.atK) :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗
      wpSkipStep GD i sw.atK (wpF sw Φ) -∗
      |==> ▷ |==> ∃ (sw' : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw'.atK = s'.atK⌝ ∗ naAtProgress GD i sw'.atK na' ∗ AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i sw'.atK ls' ∗ wpF sw' Φ := by
  iintro Hannot Hea Hb
  iunfold wpSkipStep at Hb
  imod Hb $$ %na Hannot with Hb
  imodintro
  inext
  imod Hb with ⟨%ls', Hannot', Hloc', HΨ⟩
  imodintro
  iexists sw, na, ea, ls'
  isplitr
  · ipureintro
    exact hk
  isplitr
  · iunfold naAtProgress
    ipureintro
    rw [← Heq]
    exact Hna
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea]
  · iexact Hea
  isplitl [Hloc']
  · iexact Hloc'
  · iexact HΨ

/-- Lean-only: `AxAdequacy.evCase` at an arbitrary continuation `wpF`. -/
theorem AxAdequacyChk.evCaseGen {A : Type} (wpF : Athread → (Athread → IProp GF) → IProp GF)
    (Hwf : axpolWf) (GD : Gdexec) (Hgwf : gwf GD.gdG)
    (i : Agent) (k : Nat) (Hgmem : gmemB GD.gdG (i, k) = true)
    (ok val : A → Prop) (kf : A → Nat) (Kf : A → Athread) (hK : ∀ a, kf a = (Kf a).atK)
    (s' : Athread) (hpos : ∀ a, ok a → (Kf a).atK = s'.atK ∧ kf a = k + 1)
    (na : Mea GF) (ea : Sra GF) (Φ : Athread → IProp GF)
    (Hna : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set na : GSet Geid) = eidsBefore GD i k) :
    ⊢ AxirisG.annotInterp na -∗ eaLocalWf GD ea na -∗
      wpEvStep GD i k ok val kf (fun a => wpF (Kf a) Φ) -∗
      |==> ▷ |==> ∃ (sw' : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw'.atK = s'.atK⌝ ∗ naAtProgress GD i sw'.atK na' ∗ AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗ AxirisG.localInterp GD i sw'.atK ls' ∗ wpF sw' Φ := by
  iintro Hannot Hea Hb
  iunfold wpEvStep at Hb
  ihave Hpre : naAtProgress GD i k na $$ []
  · iunfold naAtProgress
    ipureintro
    exact Hna
  imod Hb $$ %na [$Hpre $Hannot] with Hb
  imodintro
  inext
  imod Hb with ⟨%a, %R, %nu, %nuu, %ls', %Hok, #Hsplit, Hfe, Hannot', Hloc', HΨ⟩
  ihave %Hd := naSplittingWfDom (Axpol.lobp GD (i, k)) na nu nuu $$ Hsplit
  ihave Hfe' := AxAdequacy.flowEqDynDropPure GD (i, k) (Axpol.sPol GD (i, k)) nu R (val a) $$ Hfe
  ihave Hea' := eaLocalWfEvStep Hwf GD i k na ea nu nuu R Hgwf Hgmem Hna $$ Hsplit Hea Hfe'
  imodintro
  obtain ⟨h1, h2⟩ := hpos a Hok
  iexists Kf a, PartialMap.union (PartialMap.union {[(i, k) := R]} nuu) na,
    PartialMap.union {[(i, k) := nu]} ea, ls'
  isplitr
  · ipureintro
    exact h1
  isplitr
  · iunfold naAtProgress
    ipureintro
    rw [← hK a, h2]
    exact naDomGrow Hwf GD i k na nu nuu R Hna Hd.1 Hd.2 Hgmem
  isplitl [Hannot']
  · iexact Hannot'
  isplitl [Hea']
  · iexact Hea'
  isplitl [Hloc']
  · rw [← hK a]
    iexact Hloc'
  · iexact HΨ

/-- Lean-only: `AxAdequacy.stepAnnot` at an arbitrary continuation `wpF` (the single place this
file inspects `wpPreStepDef`'s step clauses; deviation 3). -/
theorem AxAdequacyChk.stepAnnotGen (wpF : Athread → (Athread → IProp GF) → IProp GF)
    (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (i : Agent) (s s' : Athread)
    (Hstep : astepAnyNf (AxOpsem.grow GD i) GD.gdG.gxImg s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpPreStepDef i wpF s Φ -∗
      |==> ▷ |==> ∃ (sw : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw.atK = s'.atK⌝ ∗
        naAtProgress GD i sw.atK na' ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i sw.atK ls' ∗
        wpF sw Φ := by
  have Hgwf := Hcons.1
  iintro Hnap Hannot Hea Hloc #Hgconst H
  iunfold naAtProgress at Hnap
  icases Hnap with %Hna
  iunfold wpPreStepDef at H
  ihave Hpre : (⌜rvwmoCatConsistent GD⌝ ∗ □ AxirisG.gconstInterp GD ∗
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
  | ANFProg _ Hprog =>
    obtain ⟨l, Hap, Hpin⟩ := Hprog
    ihave Hb := (and_elim_r.trans and_elim_l) $$ Habc
    ihave Hb := Hb $$ %l %s' %Hap %Hpin
    cases hwd : wlWdata l with
    | some data =>
      have Hgmem := astepProgWdataGmem GD i s l s' data Hap hwd
      have Hk := astepProgWdataSk _ s l s' data Hap hwd
      try isimp only [] at Hb
      iapply AxAdequacyChk.evCaseGen (A := Unit) wpF Hwf GD Hgwf i s.atK Hgmem (fun _ => True)
        (fun _ => graphData GD (i, s.atK) = some data) (fun _ => s'.atK) (fun _ => s')
        (fun _ => rfl) s' (fun _ _ => ⟨rfl, Hk⟩) na ea Φ Hna $$ Hannot Hea Hb
    | none =>
      have Heq : eidsBefore GD i s.atK = eidsBefore GD i s'.atK := by
        rcases astepProgNodataK _ s l s' Hap hwd with hk | hk
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK (.inl hk)
        · exact eidsBeforeKOrSkip GD i s.atK s'.atK
            (.inr ⟨hk, astepProgNodataFenceGmem GD i s l s' Hap hwd hk⟩)
      try isimp only [] at Hb
      iapply AxAdequacyChk.skipCaseGen wpF GD i s.atK s' s' na ea Φ rfl Hna Heq $$ Hannot Hea Hb
  | ANFWire _ Hw =>
    ihave Hc := (and_elim_r.trans and_elim_r) $$ Habc
    ihave Hc := Hc $$ %s' %Hw
    iapply AxAdequacyChk.skipCaseGen wpF GD i s.atK s' s' na ea Φ rfl Hna (by rw [Hw.1])
      $$ Hannot Hea Hc
  | ANFRead id K vs Hrd Hlen =>
    ihave Ha := and_elim_l $$ Habc
    ihave Ha := Ha $$ %id %K %Hrd
    by_cases Hadv : aidentAdvRd id = 1
    · isimp only [if_pos Hadv] at Ha
      have Hgmem := areadStepGmem GD i s id K Hrd
      iapply AxAdequacyChk.evCaseGen (A := List (BitVec 8)) wpF Hwf GD Hgwf i s.atK Hgmem
        (fun v => v.length = aidentN id) (fun v => graphValue GD (i, s.atK) = some v)
        (fun v => (K v).atK) K (fun _ => rfl) (K vs)
        (fun a hok => ⟨by rw [areadStepPos _ _ _ _ _ Hrd hok, areadStepPos _ _ _ _ _ Hrd Hlen],
          by rw [areadStepPos _ _ _ _ _ Hrd hok, Hadv]⟩) na ea Φ Hna $$ Hannot Hea Ha
    · have Hadv0 := aidentAdvRdNot1 id Hadv
      obtain ⟨v, Hgv, Hlenv⟩ := areadStepRmwValue GD i s id K Hgwf Hrd Hadv0
      isimp only [if_neg Hadv] at Ha
      ihave Ha := Ha $$ %v %Hgv %Hlenv
      iapply AxAdequacyChk.skipCaseGen wpF GD i s.atK (K v) (K vs) na ea Φ
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, areadStepPos _ _ _ _ _ Hrd Hlen]) Hna
        (by rw [areadStepPos _ _ _ _ _ Hrd Hlenv, Hadv0, Nat.add_zero]) $$ Hannot Hea Ha

variable [AxirisGChk GF]

/-- Peel `wpc` down to its step obligation (Rocq `wpc_unfold_step`). -/
theorem wpcUnfoldStep (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpc st i s Φ ⊢ wpPreStepDef i (wpc st i) s Φ :=
  (AxWp.wpcUnfoldStep st i s Φ).1.trans (and_elim_r.trans and_elim_r)

/-- THE `wpc` ANALOGUE OF `AxAdequacy.stepAnnot`: same five resources in, same five out; `wpc`'s
own fixpoint re-supplies the checkpoint at `sw`. -/
theorem stepChkAnnot (GD : Gdexec) (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (i : Agent) (st : Stuckness) (s s' : Athread)
    (Hstep : astepAnyNf (AxOpsem.grow GD i) GD.gdG.gxImg s s')
    (na : Mea GF) (ea : Sra GF) (ls : AxirisG.logTsT GF) (Φ : Athread → IProp GF) :
    ⊢ naAtProgress GD i s.atK na -∗
      AxirisG.annotInterp na -∗
      eaLocalWf GD ea na -∗
      AxirisG.localInterp GD i s.atK ls -∗
      □ AxirisG.gconstInterp GD -∗
      wpc st i s Φ -∗
      |==> ▷ |==> ∃ (sw : Athread) (na' : Mea GF) (ea' : Sra GF) (ls' : AxirisG.logTsT GF),
        ⌜sw.atK = s'.atK⌝ ∗
        naAtProgress GD i sw.atK na' ∗
        AxirisG.annotInterp na' ∗
        eaLocalWf GD ea' na' ∗
        AxirisG.localInterp GD i sw.atK ls' ∗
        wpc st i sw Φ := by
  iintro Hna Hannot Hea Hloc #Hgconst Hwpc
  ihave H := wpcUnfoldStep st i s Φ $$ Hwpc
  iapply AxAdequacyChk.stepAnnotGen (wpc st i) GD Hwf Hcons i s s' Hstep na ea ls Φ
    $$ Hna Hannot Hea Hloc Hgconst H

end stepChk

/-! # 3. The adequacy records (per hart) -/

/-- Upstream's `adequate`, specialized to one hart and its expected run from `p0`. -/
structure adequate (st : Stuckness) (GD : Gdexec) (i : Agent) (p0 : Pexv6)
    (Φp : Athread → Prop) : Prop where
  adequateNotStuck : ∀ pfin kfin,
    st = .NotStuck → expectedRun GD i p0 pfin kfin → notStuckGd GD i ⟨pfin, kfin⟩
  adequateResult : ∀ pfin kfin,
    expectedRun GD i p0 pfin kfin → terminated ⟨pfin, kfin⟩ → Φp ⟨pfin, kfin⟩

/-- `adequate` plus the CHECKPOINT half at every non-terminated state reached. -/
structure adequateChk (st : Stuckness) (GD : Gdexec) (i : Agent) (p0 : Pexv6)
    (Φp : Athread → Prop) (chkp : Agent → Athread → Prop) : Prop where
  adequateChkNotStuck : ∀ pfin kfin,
    st = .NotStuck → expectedRun GD i p0 pfin kfin → notStuckGd GD i ⟨pfin, kfin⟩
  adequateChkResult : ∀ pfin kfin,
    expectedRun GD i p0 pfin kfin →
      (terminated ⟨pfin, kfin⟩ → Φp ⟨pfin, kfin⟩) ∧
      (¬ terminated ⟨pfin, kfin⟩ → chkp i ⟨pfin, kfin⟩)

/-- `adequateChk` subsumes `adequate`: forget the checkpoint half. -/
theorem adequateChkAdequate (st : Stuckness) (GD : Gdexec) (i : Agent) (p0 : Pexv6)
    (Φp : Athread → Prop) (chkp : Agent → Athread → Prop) :
    adequateChk st GD i p0 Φp chkp → adequate st GD i p0 Φp := by
  intro ⟨Hns, Hres⟩
  exact ⟨Hns, fun pfin kfin Hrun Hterm => (Hres pfin kfin Hrun).1 Hterm⟩

end Weak
