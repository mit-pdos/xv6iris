/-
Weak: **A GENERIC LIFTER** building `wpd st i s Φ` (Rocq `WPd s @ st; i {{ Φ }}`) for a hart
segment with NO memory events, from a PURE invariant (spike S2).

Rocq: `iris/AxWpdLift.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`wpdOfClosedRun` (§1) is proved by Löb over `AxWpD.wpdMUnfoldStep`, carrying a single
`∧`-shaped resource `exit ∧ rowend`: at each unfolding exactly one of `wpdPreStepDef`'s four
`∧`-clauses is proved, and each consumes at most one half of it, so the resource need not be
persistent.
- clause (a) (reads): excluded by the pure premise `Hnord` (no `areadStep` from a `P`-state);
- clause (b) (all program steps, DEMONIC): the closure premise `Hclos` — every successor has no
  write data, keeps `atK` (so the pre `localInterp` is reused verbatim for `wpSkipStep`), and
  lands in `P` (recurse, IH) or `Q` (exit resource).  Keeping `atK` forces the step to be
  `AStepAdmin` (every other constructor advances `k`);
- clause (c) (PLIC wire): its own closure premise `Hwire`; `awire` keeps `atK` by definition;
- clause (d) (row end): the `rowend` half of the resource;
- `progressObl`: premise `Hprog` (trivial at `MaybeStuck`, `wpdOfClosedRunMaybe`).
§2 `closedOfDetRun`: how a determinism premise plus an ∃-run discharges a closure premise for
the invariant "strictly before the run's end".

## Deviations from Rocq

1. O2 STAGE C (fetch = admin step).  Rocq's header notes that a FETCH is realised through
   clause (a) as an ordinary read, so a segment covered by the lemma must START AFTER the
   instruction's fetch.  In Lean (AxOpsem deviation 2) a fetch is an `AStepAdmin` step at
   `lbAdmin true (LIFetch ..)`: no row item, `wlWdata = none`, `atK` kept.  So `Hnord` no longer
   speaks of fetches at all, and a fetch inside the segment is simply one more `Hclos` step
   (clause (b)); the "start after the fetch" side condition is vacuous.  Statements unchanged.
2. NAMES: camelCase (map below); `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` for any `hlc`
   (as AxWp/AxWpD); `astep_prog (grow GD i) ax_text (gx_img (gd_g GD))` ↦
   `AxOpsem.astepProg (AxOpsem.grow GD i)` (the oracle parameters are deleted, AxOpsem Q-C2);
   wand chains `A -∗ B` ↦ `⊢ A -∗ B`.
3. Lean-only helper, file-qualified: `AxWpdLift.tcInvL` (head inversion of the library's
   tail-style `tc`, MachCSL.Rel).

**Rocq → Lean name map.** `wpd_of_closed_run` `wpdOfClosedRun`, `wpd_of_closed_run_maybe`
`wpdOfClosedRunMaybe`, `closed_of_det_run` `closedOfDetRun`.

**Not ported:** the `Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxWpD

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp

/-! # 1. The lifter -/

section wpdLift
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfClosedRun (st : Stuckness) (i : Agent) (P Q : Athread → Prop)
    (Φ : Athread → IProp GF)
    (Hprog : ∀ s1, P s1 → ⊢ progressObl (GF := GF) st i s1)
    (Hnord : ∀ GD s1 id K, P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K)
    (Hclos : ∀ GD s1 l s2, P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
       wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ Q s2))
    (Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ Q s2) :
    ⊢ ∀ s, ⌜P s⌝ -∗
      ((∀ s2, ⌜Q s2⌝ -∗ wpd st i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜P s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd st i s Φ := by
  iloeb as IH
  iintro %s %HP R
  iapply (AxWpD.wpdMUnfoldStep rvwmoCatConsistent st i s Φ).2
  isplit
  · iapply (Hprog s HP)
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  isplit
  · iintro %id %K %Hst
    exact (Hnord GD s id K HP Hst).elim
  isplit
  · iintro %l %s' %Hst
    obtain ⟨Hw, Hk, HPQ⟩ := Hclos GD s l s' HP Hst
    simp only [Hw]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    rw [Hk]
    iframe Hna Hloc
    cases HPQ with
    | inl HP' => iapply IH $$ %s' %HP' R
    | inr HQ' =>
      icases R with ⟨R, -⟩
      iapply R $$ %s' %HQ'
  isplit
  · iintro %s' %Hst
    have HPQ := Hwire s s' HP Hst
    have Hk : s'.atK = s.atK := Hst.1
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    rw [Hk]
    iframe Hna Hloc
    cases HPQ with
    | inl HP' => iapply IH $$ %s' %HP' R
    | inr HQ' =>
      icases R with ⟨R, -⟩
      iapply R $$ %s' %HQ'
  · iintro %Heq
    icases R with ⟨-, R⟩
    iapply R $$ %GD %s %HP %Heq

/-- The `MaybeStuck` specialisation (the stuckness `AxTierA2.tierA_adequacy_ann` uses), with
clause (d) discharged by the pure premise "no `P`-state sits at its row's end". -/
theorem wpdOfClosedRunMaybe (i : Agent) (P Q : Athread → Prop) (Φ : Athread → IProp GF)
    (s : Athread)
    (Hnord : ∀ GD s1 id K, P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K)
    (Hclos : ∀ GD s1 l s2, P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
       wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ Q s2))
    (Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ Q s2)
    (Hend : ∀ (GD : Gdexec) s1, P s1 → s1.atK ≠ (AxOpsem.grow GD i).length)
    (HP : P s) :
    ⊢ (∀ s2, ⌜Q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗ wpd .MaybeStuck i s Φ := by
  iintro Hexit
  iapply (wpdOfClosedRun .MaybeStuck i P Q Φ
    (fun s1 _ => (progressOblMaybestuck (GF := GF) i s1).2) Hnord Hclos Hwire) $$ %s %HP
  isplit
  · iexact Hexit
  · iintro %GD %s1 %HP1 %Heq
    exact (Hend GD s1 HP1 Heq).elim

end wpdLift

/-! # 2. `closedOfDetRun` — closure from determinism + an ∃-run

`step` is abstract; the intended instance is the row-uniform program step
`fun s1 s2 => ∃ GD l, AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2` (for `atK`-preserving
segments this is `AStepAdmin` only, whose premise does not mention the row).  The invariant is
"strictly before `q` along `step`, inside the deterministic region `R`"; the exit is `q`
itself.  Using `tc` (not `rtc ∧ ≠`) avoids needing decidable equality on `Athread`. -/

/-- (Lean-only) head inversion of the library's tail-style `tc`. -/
theorem AxWpdLift.tcInvL {A : Type _} {R : A → A → Prop} {x z : A} (h : tc R x z) :
    R x z ∨ ∃ y, R x y ∧ tc R y z := by
  induction h with
  | single h => exact .inl h
  | tail _ h2 ih =>
    rcases ih with h1 | ⟨y', h1, h1'⟩
    · exact .inr ⟨_, h1, tc_once h2⟩
    · exact .inr ⟨y', h1, tc_r h1' h2⟩

theorem closedOfDetRun (step : Athread → Athread → Prop) (R : Athread → Prop) (q : Athread)
    (Hdet : ∀ s1 s2 s3, R s1 → step s1 s2 → step s1 s3 → s2 = s3)
    (HR : ∀ s1 s2, R s1 → step s1 s2 → R s2) :
    ∀ s1 s2, (R s1 ∧ tc step s1 q) → step s1 s2 →
      (R s2 ∧ tc step s2 q) ∨ s2 = q := by
  intro s1 s2 ⟨HR1, Htc⟩ Hst
  rcases AxWpdLift.tcInvL Htc with Hq | ⟨s', Hs', Htc'⟩
  · exact .inr (Hdet s1 s2 q HR1 Hst Hq)
  · rw [Hdet s1 s2 s' HR1 Hst Hs']
    exact .inl ⟨HR s1 s' HR1 Hs', Htc'⟩

end Weak
