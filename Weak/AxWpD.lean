/-
Weak: **`WPd`, THE DEMONIC-READ VARIANT OF `AxWp.wp`** (AxSL tier), parametric in the
graph-consistency model.

Rocq: `iris/AxWpD.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxWp.wp`'s read arm (a) is `∃ a, …`: adequacy learns the witness only in phase 2, so a phase-1
expected-run replay cannot match it against the run's row (design §7.A FINDING).  `wpdM M`
pins arm (a) to the graph value — `∀ v, ⌜graphValue GD (i, s.atK) = some v⌝ -∗ …`, with
`wpEvStep` called at the trivial witness type `Unit` — exactly as `wp`'s RMW read-half sub-arm
already is; arms (b) (every other program step) and (c) (the PLIC wire) are `wp`'s, verbatim;
a new clause (d) hands out the postcondition at the end of the hart's own row
(`s.atK = (AxOpsem.grow GD i).length`), since `isTerminated` is always `false`.
§0: the consistency model `M` is a parameter, `GModel M` (all the model-generic proofs use of
`M`: the graph is well formed), instance `catGmodel`.  §1: `wpdMPreStepDef`, its mono/bupd/iupd
laws (the mono combinator takes ONE `∧`-combined resource, so a single non-persistent
`∀ k, Φ1 k ==∗ Φ2 k` justifies both the continuation and clause (d)), `wpdMPre`, the fixpoint
`wpdM`.  The riscv.cat instance under the old names `wpd*` (`M := rvwmoCatConsistent`).
§2: structural lemmas (unfold, value, post at row end, strong mono, mono, bupd, iupd).
§3: `wpdMWp` — `wpdM M ⊢ AxWp.wp` when cat ⊆ `M`, by Löb, instantiating `wp`'s read
existential at the graph's own value (`areadStepGraphValue`); clause (d) is dropped.
§4: `wpdMReadStepAllWand`, the demonic read rule at `wpdM`'s pinned arm (`AxReadAll`'s
`wpReadAllWand` at `A := Unit`).

The file is generic in the read: it speaks of `areadStep` and the `aidentAdvRd id = 1` arm only
(through `areadStepGraphValue`), never of instruction fetches, so it does not depend on whether
fetches are graph read events.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below); `bv 8` ↦ `BitVec 8`; `agent` ↦ `Agent`; `mea Σ` ↦
   `Mea GF`; map unions ↦ `PartialMap.union` (left-nested as `AxWp`'s `wpEvStep`).
   Lean-only helpers, file-qualified: `AxWpD.wpdMPreStepDefDist` (non-expansiveness of the step
   case, for contractiveness) and `AxWpD.wpdMUnfoldStep` (the unfolding at a hart state: harts
   never terminate).
2. `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for an arbitrary `hlc` (as `AxWp`, deviation 6).
3. SEALS / NOTATIONS: `wpdM` is a plain `fixpoint` (no seal; `wpdM_eq` has no counterpart);
   the `WPd …` notations are not provided (`wpd st i s Φ`).  Rocq's `Notation`s
   `wpd_pre_step_def`/`wpd_pre`/`wpd_def`/`wpd` are `abbrev`s at `rvwmoCatConsistent`
   (`wpd_def` and `wpd` coincide: `wpd`); `wpd_pre_contractive` is an instance.  The old-name
   `Definition`s (`wpd_unfold` …) are theorems with their statements spelled out at the
   instance.
4. STATEMENT SHAPES (as `AxWp`): Rocq's wand chains `A -∗ B -∗ C` ↦ `⊢ A -∗ B -∗ C`; `P ⊢ Q`
   stays; pure premises are `→`.  `GModel` is a `Prop`-valued class with field `gmWf`.

**Rocq → Lean name map.**  §0: `GModel` `GModel` (`gm_wf` `GModel.gmWf`), `cat_gmodel`
`catGmodel`, `gm_gwf` `gmGwf`.  §1: `post_lifting_bupd` `postLiftingBupd`,
`wpdM_pre_step_def` `wpdMPreStepDef`, `wpdM_pre_step_def_mono/bupd/iupd`
`wpdMPreStepDefMono/Bupd/Iupd`, `wpdM_pre` `wpdMPre`, `wpdM_pre_contractive`
`wpdMPreContractive`, `wpdM(_def)` `wpdM`, `wpd_pre_step_def` `wpdPreStepDef`, `wpd_pre`
`wpdPre`, `wpd(_def)` `wpd`, `wpd_pre_step_def_mono/bupd/iupd` `wpdPreStepDefMono/Bupd/Iupd`,
`wpd_pre_contractive` `wpdPreContractive`.  §2: `wpdM_unfold` `wpdMUnfold`, `wpdM_value`
`wpdMValue`, `wpdM_post_at_row_end` `wpdMPostAtRowEnd`, `wpdM_strong_mono` `wpdMStrongMono`,
`wpdM_mono` `wpdMMono`, `bupd_wpdM` `bupdWpdM`, `iupd_wpdM` `iupdWpdM`; old names `wpd_unfold`
`wpdUnfold`, `wpd_value` `wpdValue`, `wpd_post_at_row_end` `wpdPostAtRowEnd`,
`wpd_strong_mono` `wpdStrongMono`, `wpd_mono` `wpdMono`, `bupd_wpd` `bupdWpd`, `iupd_wpd`
`iupdWpd`.  §3: `wpdM_wp` `wpdMWp`, `wpd_wp` `wpdWp`.  §4: `wpdM_read_step_all_wand`
`wpdMReadStepAllWand`, `wpd_read_step_all_wand` `wpdReadStepAllWand`.

**Not ported:** `wpdM_aux`/`wpdM_eq` (seal; deviation 3) and the §5 `Print Assumptions` block
(the lint's axiom check covers it).
-/
import Weak.AxReadAll

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 0. The graph-consistency model is a parameter -/

/-- EVERYTHING the model-generic proofs use of the consistency model `M`. -/
class GModel (M : Gdexec → Prop) : Prop where
  gmWf : ∀ GD, M GD → gwf GD.gdG

instance catGmodel : GModel rvwmoCatConsistent := ⟨fun _ H => H.1⟩

/-- The field, at an inferred instance. -/
theorem gmGwf {M : Gdexec → Prop} [GModel M] (GD : Gdexec) : M GD → gwf GD.gdG :=
  fun H => GModel.gmWf GD H

/-! # 1. `wpdMPreStepDef` and the fixpoint -/

section wpdDef
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)

omit [Axpol] in
/-- `postLifting` under a bare `|==>`, for clause (d)'s bupd combinator. -/
theorem postLiftingBupd (Φ : Athread → IProp GF) (i : Agent) (s : Athread) :
    iprop(|==> postLifting Φ i s) ⊢ postLifting Φ i s := by
  unfold postLifting
  iintro H %na Hna
  imod H
  iapply H $$ %na Hna

/-- THE STEP CASE of `WPd`: (a) the read, PINNED to the graph value at every branch; (b) every
other program step, demonic (verbatim `wpPreStepDef`); (c) the PLIC wire (verbatim); (d) the
post at row end. -/
def wpdMPreStepDef (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF) (s : Athread)
    (Φ : Athread → IProp GF) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
    ⌜M GD⌝ ∗ □ AxirisG.gconstInterp GD ∗ AxirisG.localInterp GD i s.atK ls -∗
    (∀ (id : AidentT) (K : List (BitVec 8) → Athread),
       ⌜areadStep (AxOpsem.grow GD i) s id K⌝ -∗
       if aidentAdvRd id = 1 then
         ∀ v, ⌜graphValue GD (i, s.atK) = some v⌝ -∗ ⌜v.length = aidentN id⌝ -∗
           wpEvStep GD i s.atK
             (fun _ : Unit => True) (fun _ : Unit => graphValue GD (i, s.atK) = some v)
             (fun _ => (K v).atK) (fun _ => wpd (K v) Φ)
       else
         ∀ v, ⌜graphValue GD (i, s.atK) = some v⌝ -∗ ⌜v.length = aidentN id⌝ -∗
           wpSkipStep GD i (K v).atK (wpd (K v) Φ)) ∧
    (∀ (l : Wlabel) (s' : Athread),
       ⌜AxOpsem.astepProg (AxOpsem.grow GD i) s l s'⌝ -∗
       match wlWdata l with
       | some data =>
           wpEvStep GD i s.atK
             (fun _ : Unit => True) (fun _ => graphData GD (i, s.atK) = some data)
             (fun _ => s'.atK) (fun _ => wpd s' Φ)
       | none => wpSkipStep GD i s'.atK (wpd s' Φ)) ∧
    (∀ s', ⌜awire s s'⌝ -∗ wpSkipStep GD i s'.atK (wpd s' Φ)) ∧
    (⌜s.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s))

/-- The MONO combinator takes ONE combined resource (`∧`, not `∗`); each branch keeps only the
half it needs. -/
theorem wpdMPreStepDefMono (i : Agent) (wpd1 wpd2 : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ1 Φ2 : Athread → IProp GF) :
    ⊢ (▷ (∀ s', wpd1 s' Φ1 -∗ wpd2 s' Φ2) ∧ (∀ k, Φ1 k ==∗ Φ2 k)) -∗
      wpdMPreStepDef M i wpd1 s Φ1 -∗ wpdMPreStepDef M i wpd2 s Φ2 := by
  unfold wpdMPreStepDef
  iintro Hmono H %GD %ls Hpre
  ihave H := H $$ %GD %ls Hpre
  isplit
  · icases H with ⟨H, -⟩
    iintro %id %K %Hstep
    ihave H := H $$ %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      ihave H := H $$ %v %Hv %Hlen
      icases Hmono with ⟨Hcont, -⟩
      iapply wpEvStepMono $$ [Hcont] H
      inext
      iintro %_ Hw
      iapply Hcont $$ Hw
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      ihave H := H $$ %v %Hv %Hlen
      icases Hmono with ⟨Hcont, -⟩
      iapply wpSkipStepMono $$ [Hcont] H
      inext
      iintro Hw
      iapply Hcont $$ Hw
  isplit
  · icases H with ⟨-, H, -⟩
    iintro %l %s' %Hstep
    ihave H := H $$ %l %s' %Hstep
    icases Hmono with ⟨Hcont, -⟩
    cases wlWdata l with
    | some data =>
      iapply wpEvStepMono $$ [Hcont] H
      inext
      iintro %_ Hw
      iapply Hcont $$ Hw
    | none =>
      iapply wpSkipStepMono $$ [Hcont] H
      inext
      iintro Hw
      iapply Hcont $$ Hw
  isplit
  · icases H with ⟨-, -, H, -⟩
    iintro %s' %Hstep
    ihave H := H $$ %s' %Hstep
    icases Hmono with ⟨Hcont, -⟩
    iapply wpSkipStepMono $$ [Hcont] H
    inext
    iintro Hw
    iapply Hcont $$ Hw
  · icases H with ⟨-, -, -, H⟩
    iintro %Heq
    ihave H := H $$ %Heq
    icases Hmono with ⟨-, HΦ⟩
    iapply postLiftingStrongMono $$ H HΦ

theorem wpdMPreStepDefBupd (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpdMPreStepDef M i wpd s Φ) ⊢ wpdMPreStepDef M i wpd s Φ := by
  unfold wpdMPreStepDef
  iintro H %GD %ls Hpre
  isplit
  · iintro %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpEvStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpSkipStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
  isplit
  · iintro %l %s' %Hstep
    cases hl : wlWdata l with
    | some data =>
      iapply wpEvStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep
      rw [hl]
      iexact H
    | none =>
      iapply wpSkipStepBupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep
      rw [hl]
      iexact H
  isplit
  · iintro %s' %Hstep
    iapply wpSkipStepBupd
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, H, -⟩
    iapply H $$ %s' %Hstep
  · iintro %Heq
    iapply postLiftingBupd
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, -, H⟩
    iapply H $$ %Heq

theorem wpdMPreStepDefIupd (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpdMPreStepDef M i wpd s Φ) ⊢ wpdMPreStepDef M i wpd s Φ := by
  unfold wpdMPreStepDef
  iintro H %GD %ls Hpre
  isplit
  · iintro %id %K %Hstep
    by_cases hadv : aidentAdvRd id = 1
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpEvStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
    · simp only [hadv, ↓reduceIte]
      iintro %v %Hv %Hlen
      iapply wpSkipStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨H, -⟩
      ihave H := H $$ %id %K %Hstep
      simp only [hadv, ↓reduceIte]
      iapply H $$ %v %Hv %Hlen
  isplit
  · iintro %l %s' %Hstep
    cases hl : wlWdata l with
    | some data =>
      iapply wpEvStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep
      rw [hl]
      iexact H
    | none =>
      iapply wpSkipStepIupd
      imod H
      imodintro
      icases H $$ %GD %ls Hpre with ⟨-, H, -⟩
      ihave H := H $$ %l %s' %Hstep
      rw [hl]
      iexact H
  isplit
  · iintro %s' %Hstep
    iapply wpSkipStepIupd
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, H, -⟩
    iapply H $$ %s' %Hstep
  · iintro %Heq
    iapply postLiftingInterpMod
    imod H
    imodintro
    icases H $$ %GD %ls Hpre with ⟨-, -, -, H⟩
    iapply H $$ %Heq

/-- Non-expansiveness of the step case in the continuation (Lean-only). -/
theorem AxWpD.wpdMPreStepDefDist (i : Agent)
    (wpd1 wpd2 : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) (n : Nat)
    (h : ∀ m, m < n → ∀ s', wpd1 s' Φ ≡{m}≡ wpd2 s' Φ) :
    wpdMPreStepDef M i wpd1 s Φ ≡{n}≡ wpdMPreStepDef M i wpd2 s Φ := by
  unfold wpdMPreStepDef
  refine BI.forall_ne (fun GD => ?_)
  refine BI.forall_ne (fun ls => ?_)
  refine BI.wand_ne.ne .rfl ?_
  refine BI.and_ne.ne ?_ (BI.and_ne.ne ?_ (BI.and_ne.ne ?_ .rfl))
  · refine BI.forall_ne (fun id => ?_)
    refine BI.forall_ne (fun K => ?_)
    refine BI.wand_ne.ne .rfl ?_
    split
    · refine BI.forall_ne (fun v => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      exact AxWp.wpEvStepDist _ _ _ _ _ _ _ _ n (fun m hm _ => h m hm (K v))
    · refine BI.forall_ne (fun v => ?_)
      refine BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl ?_
      exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm (K v))
  · refine BI.forall_ne (fun l => ?_)
    refine BI.forall_ne (fun s' => ?_)
    refine BI.wand_ne.ne .rfl ?_
    split
    · exact AxWp.wpEvStepDist _ _ _ _ _ _ _ _ n (fun m hm _ => h m hm s')
    · exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm s')
  · refine BI.forall_ne (fun s' => ?_)
    refine BI.wand_ne.ne .rfl ?_
    exact AxWp.wpSkipStepDist _ _ _ _ _ n (fun m hm => h m hm s')

/-- Rocq `wpdM_pre`. -/
def wpdMPre (st : Stuckness) (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF) :
    Athread → (Athread → IProp GF) → IProp GF :=
  fun s Φ =>
    if isTerminated s then postLifting Φ i s
    else iprop(progressObl st i s ∧ wpdMPreStepDef M i wpd s Φ)

instance wpdMPreContractive (st : Stuckness) (i : Agent) :
    OFE.Contractive (wpdMPre (GF := GF) M st i) where
  distLater_dist {n wpd wpd'} Hwpd := by
    intro s Φ
    unfold wpdMPre
    simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
    refine BI.and_ne.ne .rfl ?_
    exact AxWpD.wpdMPreStepDefDist M i wpd wpd' s Φ n (fun m hm s' => Hwpd m hm s' Φ)

/-- Rocq `wpdM`: the fixpoint of `wpdMPre`. -/
def wpdM (st : Stuckness) (i : Agent) : Athread → (Athread → IProp GF) → IProp GF :=
  fixpoint (wpdMPre (GF := GF) M st i)

end wpdDef

/-! ## The riscv.cat instance under the old names -/

section wpdCatPre
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- Rocq `Notation wpd_pre_step_def`. -/
abbrev wpdPreStepDef (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) : IProp GF :=
  wpdMPreStepDef rvwmoCatConsistent i wpd s Φ

/-- Rocq `Notation wpd_pre`. -/
abbrev wpdPre (st : Stuckness) (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF) :
    Athread → (Athread → IProp GF) → IProp GF :=
  wpdMPre rvwmoCatConsistent st i wpd

/-- Rocq `Notation wpd` (and `wpd_def`). -/
abbrev wpd (st : Stuckness) (i : Agent) : Athread → (Athread → IProp GF) → IProp GF :=
  wpdM rvwmoCatConsistent st i

theorem wpdPreStepDefMono (i : Agent) (wpd1 wpd2 : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ1 Φ2 : Athread → IProp GF) :
    ⊢ (▷ (∀ s', wpd1 s' Φ1 -∗ wpd2 s' Φ2) ∧ (∀ k, Φ1 k ==∗ Φ2 k)) -∗
      wpdPreStepDef i wpd1 s Φ1 -∗ wpdPreStepDef i wpd2 s Φ2 :=
  wpdMPreStepDefMono rvwmoCatConsistent i wpd1 wpd2 s Φ1 Φ2

theorem wpdPreStepDefBupd (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpdPreStepDef i wpd s Φ) ⊢ wpdPreStepDef i wpd s Φ :=
  wpdMPreStepDefBupd rvwmoCatConsistent i wpd s Φ

theorem wpdPreStepDefIupd (i : Agent) (wpd : Athread → (Athread → IProp GF) → IProp GF)
    (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpdPreStepDef i wpd s Φ) ⊢ wpdPreStepDef i wpd s Φ :=
  wpdMPreStepDefIupd rvwmoCatConsistent i wpd s Φ

instance wpdPreContractive (st : Stuckness) (i : Agent) :
    OFE.Contractive (wpdPre (GF := GF) st i) :=
  wpdMPreContractive rvwmoCatConsistent st i

end wpdCatPre

/-! # 2. Structural lemmas -/

section wpdLaws
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)

theorem wpdMUnfold (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpdM M st i s Φ ⊣⊢ wpdMPre M st i (wpdM M st i) s Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wpdMPre (GF := GF) M st i).toContractiveHom)).dist s Φ

/-- The unfolding at a hart state: harts never terminate (Lean-only). -/
theorem AxWpD.wpdMUnfoldStep (st : Stuckness) (i : Agent) (s : Athread)
    (Φ : Athread → IProp GF) :
    wpdM M st i s Φ ⊣⊢ iprop(progressObl st i s ∧ wpdMPreStepDef M i (wpdM M st i) s Φ) := by
  refine (wpdMUnfold M st i s Φ).trans ?_
  unfold wpdMPre
  simp only [isTerminated, Bool.false_eq_true, ↓reduceIte]
  exact .rfl

variable (st : Stuckness)

/-- The terminated arm — vacuous (`isTerminated` is constantly `false`). -/
theorem wpdMValue (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → postLifting Φ i s ⊢ wpdM M st i s Φ := by
  intro Hs
  simp [isTerminated] at Hs

/-- At the end of hart `i`'s own row, `WPd` hands out the postcondition. -/
theorem wpdMPostAtRowEnd (i : Agent) (s : Athread) (Φ : Athread → IProp GF) (GD : Gdexec)
    (ls : AxirisG.logTsT GF) (Heq : s.atK = (AxOpsem.grow GD i).length) (Hcons : M GD) :
    ⊢ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i s.atK ls -∗
      wpdM M st i s Φ -∗ postLifting Φ i s := by
  iintro #Hgconst Hloc H
  rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq]
  icases H with ⟨-, H⟩
  unfold wpdMPreStepDef
  ihave H := H $$ %GD %ls [Hloc]
  · isplitr
    · ipureintro
      exact Hcons
    isplitr
    · iexact Hgconst
    iexact Hloc
  icases H with ⟨-, -, -, H⟩
  iapply H
  ipureintro
  exact Heq

theorem wpdMStrongMono (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ wpdM M st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ wpdM M st i s Ψ := by
  have h : ⊢ ∀ s (Φ Ψ : Athread → IProp GF),
      wpdM M st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ wpdM M st i s Ψ := by
    iloeb as IH
    iintro %s %Φ %Ψ H HΦ
    rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq, (AxWpD.wpdMUnfoldStep M st i s Ψ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    · icases H with ⟨-, H⟩
      iapply wpdMPreStepDefMono $$ [HΦ] H
      isplit
      · inext
        iintro %s' H'
        iapply IH $$ %s' %Φ %Ψ H' HΦ
      · iexact HΦ
  iintro H HΦ
  iapply h $$ %s %Φ %Ψ H HΦ

theorem wpdMMono (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF)
    (HΦ : ∀ k, Φ k ⊢ Ψ k) : wpdM M st i s Φ ⊢ wpdM M st i s Ψ := by
  iintro H
  iapply wpdMStrongMono $$ H
  iintro %v H
  imodintro
  iapply HΦ v
  iexact H

theorem bupdWpdM (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpdM M st i s Φ) ⊢ wpdM M st i s Φ := by
  rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq]
  iintro H
  isplit
  · iapply progressOblBupd
    imod H
    imodintro
    icases H with ⟨H, -⟩
    iexact H
  · iapply wpdMPreStepDefBupd
    imod H
    imodintro
    icases H with ⟨-, H⟩
    iexact H

theorem iupdWpdM (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpdM M st i s Φ) ⊢ wpdM M st i s Φ := by
  rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq]
  iintro H
  isplit
  · iapply progressOblIupd
    iapply interpModMono $$ [] H
    iintro ⟨H, -⟩
    iexact H
  · iapply wpdMPreStepDefIupd
    iapply interpModMono $$ [] H
    iintro ⟨-, H⟩
    iexact H

end wpdLaws

section wpdCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdUnfold (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpd st i s Φ ⊣⊢ wpdPre st i (wpd st i) s Φ :=
  wpdMUnfold rvwmoCatConsistent st i s Φ

theorem wpdValue (st : Stuckness) (i : Agent) (Φ : Athread → IProp GF) (s : Athread) :
    isTerminated s = true → postLifting Φ i s ⊢ wpd st i s Φ :=
  wpdMValue rvwmoCatConsistent st i Φ s

theorem wpdPostAtRowEnd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF)
    (GD : Gdexec) (ls : AxirisG.logTsT GF) (Heq : s.atK = (AxOpsem.grow GD i).length)
    (Hcons : rvwmoCatConsistent GD) :
    ⊢ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i s.atK ls -∗
      wpd st i s Φ -∗ postLifting Φ i s :=
  wpdMPostAtRowEnd rvwmoCatConsistent st i s Φ GD ls Heq Hcons

theorem wpdStrongMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF) :
    ⊢ wpd st i s Φ -∗ (∀ k, Φ k ==∗ Ψ k) -∗ wpd st i s Ψ :=
  wpdMStrongMono rvwmoCatConsistent st i s Φ Ψ

theorem wpdMono (st : Stuckness) (i : Agent) (s : Athread) (Φ Ψ : Athread → IProp GF)
    (HΦ : ∀ k, Φ k ⊢ Ψ k) : wpd st i s Φ ⊢ wpd st i s Ψ :=
  wpdMMono rvwmoCatConsistent st i s Φ Ψ HΦ

theorem bupdWpd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    iprop(|==> wpd st i s Φ) ⊢ wpd st i s Φ :=
  bupdWpdM rvwmoCatConsistent st i s Φ

theorem iupdWpd (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    interpMod (wpd st i s Φ) ⊢ wpd st i s Φ :=
  iupdWpdM rvwmoCatConsistent st i s Φ

end wpdCat

/-! # 3. `wpdMWp`: `WPd` entails `WP` (when cat ⊆ `M`) -/

section wpdWp
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)

/-- RISCV.CAT-BOUND: `AxWp.wp`'s own graph premise is `rvwmoCatConsistent`, so `wpdM M ⊢ wp`
needs cat ⊆ `M`.  Clause (d) is dropped (`wp` has no terminal arm to route it to). -/
theorem wpdMWp (Hsub : ∀ GD, rvwmoCatConsistent GD → M GD) (st : Stuckness) (i : Agent)
    (s : Athread) (Φ : Athread → IProp GF) :
    wpdM M st i s Φ ⊢ AxWp.wp st i s Φ := by
  have h : ⊢ ∀ s (Φ : Athread → IProp GF), wpdM M st i s Φ -∗ AxWp.wp st i s Φ := by
    iloeb as IH
    iintro %s %Φ H
    rw [(AxWpD.wpdMUnfoldStep M st i s Φ).to_eq, (wpUnfoldStep st i s Φ).to_eq]
    isplit
    · icases H with ⟨H, -⟩
      iexact H
    icases H with ⟨-, H⟩
    unfold wpdMPreStepDef wpPreStepDef
    iintro %GD %ls ⟨%Hc, #Hg, Hl⟩
    ihave H := H $$ %GD %ls [Hl]
    · isplitr
      · ipureintro
        exact Hsub GD Hc
      isplitr
      · iexact Hg
      iexact Hl
    isplit
    · -- (a) the read: instantiate wp's ∃ at the graph value.
      icases H with ⟨H, -⟩
      iintro %id %K %Hstep
      ihave H := H $$ %id %K %Hstep
      by_cases hadv : aidentAdvRd id = 1
      · simp only [hadv, ↓reduceIte]
        obtain ⟨v0, Hgv, Hlenimp⟩ := areadStepGraphValue GD i s id K Hstep
        have Hlen0 := Hlenimp hadv
        ihave H := H $$ %v0 %Hgv %Hlen0
        unfold wpEvStep
        iintro %na Hpg
        imod H $$ %na Hpg with H
        imodintro
        inext
        imod H with ⟨%a, %R, %nu, %nuu, %ls', -, Hsplit, Hfe, Hna, Hloc, Hc⟩
        imodintro
        iexists v0, R, nu, nuu, ls'
        isplitr
        · ipureintro
          exact Hlen0
        iframe Hsplit Hfe Hna Hloc
        iapply IH $$ %(K v0) %Φ Hc
      · simp only [hadv, ↓reduceIte]
        iintro %v %Hv %Hlen
        ihave H := H $$ %v %Hv %Hlen
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hc
        iapply IH $$ %(K v) %Φ Hc
    isplit
    · icases H with ⟨-, H, -⟩
      iintro %l %s' %Hstep
      ihave H := H $$ %l %s' %Hstep
      cases wlWdata l with
      | some data =>
        iapply wpEvStepMono $$ [] H
        inext
        iintro %_ Hc
        iapply IH $$ %s' %Φ Hc
      | none =>
        iapply wpSkipStepMono $$ [] H
        inext
        iintro Hc
        iapply IH $$ %s' %Φ Hc
    · -- (c); clause (d) is dropped.
      icases H with ⟨-, -, H, -⟩
      iintro %s' %Hstep
      ihave H := H $$ %s' %Hstep
      iapply wpSkipStepMono $$ [] H
      inext
      iintro Hc
      iapply IH $$ %s' %Φ Hc
  iintro H
  iapply h $$ %s %Φ H

end wpdWp

theorem wpdWp {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (st : Stuckness) (i : Agent) (s : Athread) (Φ : Athread → IProp GF) :
    wpd st i s Φ ⊢ AxWp.wp st i s Φ :=
  wpdMWp rvwmoCatConsistent (fun _ H => H) st i s Φ

/-! # 4. The demonic read rule, at `wpdM`'s pinned arm -/

section wpdReadAll
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)

theorem wpdMReadStepAllWand (st : Stuckness) (GD : Gdexec) (i : Agent) (s : Athread)
    (id : AidentT) (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF)
    (v : List (BitVec 8)) (_Hlen : v.length = aidentN id)
    (Hflow : ⊢ ∀ na, naAtProgress GD i s.atK na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, s.atK)) na naUsed naUnused ∗
         flowEqDyn GD (i, s.atK) (Axpol.sPol GD (i, s.atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, s.atK) = some v⌝) ∗
         AxirisG.annotInterp
           (PartialMap.union (PartialMap.union {[(i, s.atK) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (K v).atK ls') :
    wpdM M st i (K v) Φ ⊢
      wpEvStep GD i s.atK (fun _ : Unit => True)
        (fun _ : Unit => graphValue GD (i, s.atK) = some v)
        (fun _ => (K v).atK) (fun _ => wpdM M st i (K v) Φ) := by
  iintro Hc
  iapply (wpReadAllWand GD i s.atK (fun _ : Unit => True)
    (fun _ : Unit => graphValue GD (i, s.atK) = some v) (fun _ => (K v).atK)
    (fun _ => wpdM M st i (K v) Φ) () trivial Hflow)
  iintro %_ %_
  iexact Hc

end wpdReadAll

theorem wpdReadStepAllWand {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF]
    [AxirisG GF] [Axpol] (st : Stuckness) (GD : Gdexec) (i : Agent) (s : Athread)
    (id : AidentT) (K : List (BitVec 8) → Athread) (Φ : Athread → IProp GF)
    (v : List (BitVec 8)) (Hlen : v.length = aidentN id)
    (Hflow : ⊢ ∀ na, naAtProgress GD i s.atK na ∗ AxirisG.annotInterp na -∗ |==> ▷ |==>
       ∃ (R : IProp GF) (naUsed naUnused : Mea GF) (ls' : AxirisG.logTsT GF),
         naSplittingWf (Axpol.lobp GD (i, s.atK)) na naUsed naUnused ∗
         flowEqDyn GD (i, s.atK) (Axpol.sPol GD (i, s.atK)) naUsed
           iprop(R ∗ ⌜graphValue GD (i, s.atK) = some v⌝) ∗
         AxirisG.annotInterp
           (PartialMap.union (PartialMap.union {[(i, s.atK) := R]} naUnused) na) ∗
         AxirisG.localInterp GD i (K v).atK ls') :
    wpd st i (K v) Φ ⊢
      wpEvStep GD i s.atK (fun _ : Unit => True)
        (fun _ : Unit => graphValue GD (i, s.atK) = some v)
        (fun _ => (K v).atK) (fun _ => wpd st i (K v) Φ) :=
  wpdMReadStepAllWand rvwmoCatConsistent st GD i s id K Φ v Hlen Hflow

end Weak

