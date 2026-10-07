/-
Weak: **`tierAAdequacy`** — a GATE-FREE, graph-generic Prop-level adequacy theorem for `wpd`
(AxSL tier), composing `wpdNsteps` (one hart's whole run) with `wpdPostAtRowEnd` (clause (d) at
row end) and `postLifting`, closed by `step_fupdN_soundness_close`/`Iris.pure_soundness` (the
AxLockRace3 soundness idiom).

Rocq: `iris/AxTierA.v` @ xxvzwolszwmp.

## The Rocq header, in substance

TRIVIALITY (coordinator, 2026-09-27): this is NOT the Tier A target.  The fixed record `axGA`
has no protocol (`obStInterp := True`) and the post is read off `postLifting` at `na := ∅`, so
the client's `Φ` receives NO annotation: the theorem only says "posts provable from the pure run
alone hold".  Kept as a compositional skeleton (soundness chaining over `wpdNsteps`).

§1 THE FIXED RECORD `AxTierA.axGA GD`: `Hwp` is stated against ONE FIXED `AxirisG` instance
(quantifying over every instance makes the premise unsatisfiable).  `obSt := Unit`,
`obStInterp := True`, `logTsT := Unit`, `localInterp := True`, `gconstInterp GD0 := ⌜GD0 = GD⌝`,
`annotInterp na := [∗map] e ↦ R ∈ na, R` (so `annotInterp ∅ ⊣⊢ emp`, no ghost allocation).
Phase 2 / the scheduler is not needed: `postLifting` is universally quantified over `na`, so it
is instantiated at `∅`, whose resource obligation is `emp`.  ONE HART AT A TIME: each hart's run
is threaded from `na := ea := ∅`; `harts.Nodup` is kept only for interface fidelity.
§3 the non-vacuity sanity check at `harts := []` over the empty graph.

## Deviations from Rocq

1. O2 STAGE C: `AxirisG` has no `ax_text` field, so `axGA` (and everything below) drops the
   oracle parameter `T : Z → Prop`; the sanity check correspondingly drops its `(λ _, True)`.
2. NAMES: camelCase; `AxGA` (a Rocq `Local Instance`) is the reducible def `AxTierA.axGA GD`,
   passed explicitly (`@wpd .hasNoLC GF Hinv (AxTierA.axGA GD) _ …` in `Hwp`; `letI` in proofs).
   `invGS_gen HasNoLc Σ` ↦ `InvGS_gen .hasNoLC GF`; `invGpreS Σ` ↦ `[InvGpreS GF]`;
   `at_k` ↦ `.atK`; `grow` ↦ `AxOpsem.grow`; `MaybeStuck` ↦ `Stuckness.MaybeStuck`.
   `tier_A_trivial_axpol` (a Rocq `Instance`) is the def `tierATrivialAxpol`, passed explicitly.
3. The §3 graph-axiom lemmas (`tierAEmptyGwf` … `tierAEmptyGdepsGmo`) are proved by the
   `AxGraphDec` checkers (`decide +kernel`) instead of Rocq's by-hand case analysis; statements
   unchanged.  `tierAEmptyGxlblNone` is `rfl`.
4. Hwp's `∀ \`{Hinv : !invGS_gen HasNoLc Σ}` ↦ `∀ [Hinv : InvGS_gen .hasNoLC GF]`.

**Rocq → Lean name map.**  `AxGA` `AxTierA.axGA`, `AxGA_annot_empty` `AxGAAnnotEmpty`,
`AxGA_gconst` `AxGAGconst`, `AxGA_local` `AxGALocal`, `tierA_adequacy` `tierAAdequacy`,
`tierA_empty_gexec` `tierAEmptyGexec`, `tierA_empty_GD` `tierAEmptyGD`,
`tierA_empty_gxlbl_none` `tierAEmptyGxlblNone`, `tierA_empty_gwf` `tierAEmptyGwf`,
`tierA_empty_gppo_cat_gmo` `tierAEmptyGppoCatGmo`, `tierA_empty_gload_value`
`tierAEmptyGloadValue`, `tierA_empty_gatomicity` `tierAEmptyGatomicity`, `tierA_empty_gdeps_wf`
`tierAEmptyGdepsWf`, `tierA_empty_gdeps_gmo` `tierAEmptyGdepsGmo`, `tierA_empty_consistent`
`tierAEmptyConsistent`, `tierA_trivial_axpol` `tierATrivialAxpol`, `tierA_trivial_axpol_wf`
`tierATrivialAxpolWf`, `tierA_dummy_athread` `tierADummyAthread`, `tierA_adequacy_sanity`
`tierAAdequacySanity`.  Lean-only (file-qualified): `AxTierA.gconstBox`.

**Dropped:** only the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxWpDHarts
import Weak.AxGraphDec

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The fixed `AxirisG` instance -/

section TierAInst
variable {GF : BundledGFunctors} (GD : Gdexec)

/-- Rocq `AxGA`: the fixed record (no protocol; the graph pinned to `GD`). -/
@[reducible] def AxTierA.axGA : AxirisG GF where
  annotInterp := fun na => iprop([∗map] _e ↦ R ∈ na, R)
  gconstInterp := fun GD0 => iprop(⌜GD0 = GD⌝)
  obSt := Unit
  obStInterp := fun _ _ _ => iprop(True)
  logTsT := Unit
  localInterp := fun _ _ _ _ => iprop(True)

theorem AxGAAnnotEmpty : ⊢ @AxirisG.annotInterp GF (AxTierA.axGA GD) (∅ : Mea GF) :=
  (BigSepM.bigSepM_empty (Φ := fun (_ : Geid) (R : IProp GF) => R)).2

theorem AxGAGconst : ⊢ @AxirisG.gconstInterp GF (AxTierA.axGA GD) GD :=
  BI.pure_intro rfl

theorem AxGALocal (i : Agent) (k : Nat) : ⊢ @AxirisG.localInterp GF (AxTierA.axGA GD) GD i k () :=
  BI.true_intro

/-- Lean-only: the graph pin, boxed. -/
theorem AxTierA.gconstBox : ⊢ □ @AxirisG.gconstInterp GF (AxTierA.axGA GD) GD := by
  show ⊢ iprop(□ ⌜GD = GD⌝)
  imodintro
  ipureintro
  rfl

/-! # 2. `tierAAdequacy` -/

theorem tierAAdequacy [Axpol] [InvGpreS GF] (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (harts : List Agent) (_Hnd : harts.Nodup)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ i, i ∈ harts → nsteps (astepAnyNfGv GD i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ harts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ harts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp : ∀ [Hinv : InvGS_gen .hasNoLC GF],
      ⊢ [∗list] i ∈ harts,
          @wpd .hasNoLC GF Hinv (AxTierA.axGA GD) _ .MaybeStuck i (s0 i)
            (fun s => iprop(⌜post i s⌝))) :
    ∀ i, i ∈ harts → post i (sN i) := by
  intro i Hi
  apply Iris.pure_soundness (PROP := IProp GF)
  refine step_fupdN_soundness_close (hlc := .hasNoLC) (n i + 1) 0 (fun Hinv => ?_)
  letI : AxirisG GF := AxTierA.axGA GD
  have Hna0 : FiniteSet.filter (fun e : Geid => decide (e.1 = i))
      (FiniteMap.dom_set (∅ : Mea GF) : GSet Geid) = eidsBefore GD i (s0 i).atK := by
    rw [domEmpty, filterEmpty, Hk0 i Hi, eidsBefore0]
  have Hnap : ⊢ naAtProgress GD i (s0 i).atK (∅ : Mea GF) := BI.pure_intro Hna0
  iintro _
  ihave Hall := @Hwp Hinv
  icases (BigSepL.bigSepL_mem_acc
    (Φ := fun j => @wpd .hasNoLC GF Hinv (AxTierA.axGA GD) _ .MaybeStuck j (s0 j)
      (fun s => iprop(⌜post j s⌝))) Hi) $$ Hall with ⟨HWPi, -⟩
  ihave Hannot0 := AxGAAnnotEmpty (GF := GF) GD
  ihave Hea0 := eaLocalWfEmpty (GF := GF) GD
  ihave Hloc0 := AxGALocal (GF := GF) GD i (s0 i).atK
  ihave #Hgc := AxTierA.gconstBox (GF := GF) GD
  ihave Hnap := Hnap
  ihave Hstep := wpdNsteps GD Hwf Hcons i .MaybeStuck (n i) (s0 i) (sN i) (Hrun i Hi)
    (∅ : Mea GF) (∅ : Sra GF) () (fun s => iprop(⌜post i s⌝))
    $$ Hnap Hannot0 Hea0 Hloc0 Hgc HWPi
  ihave Hfupd := wpdStepsNStepFupdN (n i) _ $$ Hstep
  rw [step_fupdN_add.to_eq, AxAdequacy.stepFupdNSucc, AxAdequacy.stepFupdNZero]
  iapply step_fupdN_wand $$ Hfupd
  iintro H
  imod H with ⟨%na', %ea', %ls', -, -, -, -, Hloc', HWPN⟩
  ihave Hpl := wpdPostAtRowEnd .MaybeStuck i (sN i) (fun s => iprop(⌜post i s⌝)) GD ls'
    (Hend i Hi) Hcons $$ Hgc Hloc' HWPN
  iunfold postLifting at Hpl
  ihave Hannot00 := AxGAAnnotEmpty (GF := GF) GD
  imod Hpl $$ %(∅ : Mea GF) Hannot00 with ⟨-, Hwand⟩
  ihave Hemp := (BigSepM.bigSepM_empty (Φ := fun (e : Geid) (R : IProp GF) =>
    if e.1 = i then R else iprop(True))).2 $$ []
  · itrivial
  ihave HΦ := Hwand $$ Hemp
  iapply (step_fupd_intro LawfulSet.empty_subset)
  inext
  imod HΦ with %Hp
  ipureintro
  exact Hp

end TierAInst

/-! # 3. Non-vacuity sanity check: `harts := []` discharges every premise -/

section Sanity

def tierAEmptyGexec : Gexec := { gxImg := fun _ : Int => none, gxProg := [], gxGmo := [] }
def tierAEmptyGD : Gdexec := { gdG := tierAEmptyGexec, gdDeps := [] }

theorem tierAEmptyGxlblNone (e : Geid) : gxLbl tierAEmptyGexec e = none := rfl

theorem tierAEmptyGwf : gwf tierAEmptyGexec :=
  gwfBSound _ (by decide +kernel)

theorem tierAEmptyGppoCatGmo : gppoCatGmo tierAEmptyGD :=
  gppoCatGmoBSound _ (gdepsWfBSound _ _ (by decide +kernel)) (by decide +kernel)

theorem tierAEmptyGloadValue : gloadValue tierAEmptyGexec :=
  gloadValueBSound _ (by decide +kernel)

theorem tierAEmptyGatomicity : gatomicity tierAEmptyGexec :=
  gatomBSound _ (by decide +kernel)

theorem tierAEmptyGdepsWf : gdepsWf tierAEmptyGexec [] :=
  gdepsWfBSound _ _ (by decide +kernel)

theorem tierAEmptyGdepsGmo : gdepsGmo tierAEmptyGexec [] :=
  gdepsGmoBSound _ _ (by decide +kernel)

theorem tierAEmptyConsistent : rvwmoCatConsistent tierAEmptyGD :=
  ⟨tierAEmptyGwf, tierAEmptyGppoCatGmo, tierAEmptyGloadValue, tierAEmptyGatomicity,
    tierAEmptyGdepsWf, tierAEmptyGdepsGmo⟩

/-- Rocq `tierA_trivial_axpol` (an `Instance` there; passed explicitly here). -/
@[reducible] def tierATrivialAxpol : Axpol where
  sPol := fun _ _ => (∅ : GSet Geid)
  lobp := fun _ _ => (∅ : GSet Geid)

theorem tierATrivialAxpolWf : @axpolWf tierATrivialAxpol :=
  fun _ _ _ _ h => (notElemOfEmpty h).elim

def tierADummyAthread : Athread := .AThread (.PDisk none) 0

theorem tierAAdequacySanity {GF : BundledGFunctors} [InvGpreS GF] :
    ∀ i, i ∈ ([] : List Agent) → True :=
  @tierAAdequacy GF tierAEmptyGD tierATrivialAxpol _ tierATrivialAxpolWf tierAEmptyConsistent
    [] List.nodup_nil (fun _ => tierADummyAthread) (fun _ => tierADummyAthread) (fun _ => 0)
    (fun _ Hi => (List.not_mem_nil Hi).elim) (fun _ Hi => (List.not_mem_nil Hi).elim)
    (fun _ Hi => (List.not_mem_nil Hi).elim) (fun _ _ => True)
    (fun {_} => BigSepL.bigSepL_nil.2)

end Sanity

end Weak
