/-
Weak/Prom: **A0 = `PF.adequacy`** (stage S2; plan rev 7 §0 "Top-level theorem shapes" and §2 "Adequacy A0").

```
theorem PF.adequacy {img M run} (π : Proto) (prog : Hart → P) (Φ : Hart → Val → Prop) (Ψ : Hart → List PEv → Prop) :
    PO_img π img → PO_ad π img M → (∀ h, Ψ h []) → devFreeProg pstep prog →
    (∀ h, ⊢ wpPF π M h (prog h) (Ψ h) (fun v => ∃ V, ⟦V⟧⌜Φ h v⌝)) → PF.validRun img prog M run →
    (i) ∧ (ii) ∧ (iii) ∧ (iii') ∧ (iv) ∧ (v) ∧ (vi)
```

Lean rendering (`adequacy` below), with these presentational choices:
* the hart domain is explicit ([R7.s3]): hart `h` runs `ps[h]`; the per-hart premise is for every `h` with
  `ps[h]? = some p`; harts outside the domain have the empty trace and are covered by `Ψ h []`;
* the program half `pstep` (with the fabric type `D` and initial fabric `d0`, [R7.s2]) and the value map `pdone`
  (what "hart `h` reached the value `v`" means, A0 (i)) are explicit; `wpPF`'s world is `⟨pstep, pdone, img, M, h⟩`;
* the wp premise holds in every invariant world (`∀ [InvGS_gen hlc GF]`), for any `GF` with the invariant and
  ghost-variable functors — the usual form of an Iris adequacy premise;
* `∃!` is `exU` (CoreDefs.lean).
No named assumption, no extra premise.  `devFreeProg` is kept as the plan states it; the proof does not need it,
because the per-hart wp is proved against EVERY fabric answer (`anyFab`, CoreRun.lean), so each hart's state-phase
run already depends only on `M` and its own state.

Proof (plan §0 "Proof:"): `validRun_soloD` (which uses the PROVED promises-first factorization `validRun_factorL`,
NA-12b, through `validRun_statePhase`) gives every hart a solo run against `M` with the given run's trace; every
prefix of it is an iris-lean thread run (`solo_nsteps`), so `wp_strong_adequacy_gen` gives the step invariant
`hartFacts` at every prefix (`hart_adequate`): the guarded `Ψ` and the `protoOk` of every fulfil; at the end, the
value step gives the guarded `Φ`.  `validInduction` with the partition (iii) gives (iv); (iv) removes the guards of
(i) and (ii).  (iii), (v) are CoreRun.lean's machine lemmas; (vi) is `adExact_all` (no A/D class in v2).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreWp
import Iris.ProgramLogic.Adequacy

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

variable {P D V : Type}

/-! ## 1. Solo runs are thread runs -/

theorem solo_nsteps {w : HW P D V} :
    ∀ {x y : P × PState × GSet Nat} {tr : Trace}, soloSteps (anyFab w.pstep) w.img w.M w.h x tr y →
      ∀ (τ0 : Trace) (n : Nat) (κ : List Unit) (ρ : List (HExpr P D V) × HSt),
        NSteps n ([HExpr.run w y.1], (y.2.1, y.2.2, τ0 ++ tr)) κ ρ →
        NSteps (tr.length + n) ([HExpr.run w x.1], (x.2.1, x.2.2, τ0)) κ ρ := by
  intro x y tr h
  induction h with
  | refl x => intro τ0 n κ ρ hn; simpa using hn
  | step x l ots p' ws' prom' tr y hp hm hrest ih =>
    intro τ0 n κ ρ hn
    obtain ⟨d, d', hp⟩ := hp
    have hs : hstep (HExpr.run w x.1, (x.2.1, x.2.2, τ0)) []
        (HExpr.run w p', (ws', prom', τ0 ++ [(l, ots)]), []) :=
      .lab w x.1 x.2.1 x.2.2 τ0 l ots p' ws' prom' d d' hp hm
    have hS : Language.Step ([HExpr.run w x.1], (x.2.1, x.2.2, τ0)) []
        ([HExpr.run w p'], (ws', prom', τ0 ++ [(l, ots)])) := by
      simpa using Language.Step.atomic (Λ := (inferInstance : Language (HExpr P D V) HSt Unit V)) hs [] []
    have := ih (τ0 ++ [(l, ots)]) n κ ρ (by simpa using hn)
    have h2 := NSteps.cons hS this
    simp only [List.nil_append] at h2
    rw [show (l, ots) :: tr = [(l, ots)] ++ tr from rfl, List.length_append]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h2

/-! ## 2. Per-hart adequacy -/

section adeq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]

/-- **PER-HART ADEQUACY**: after any thread run from the hart's initial state, the step invariant holds of the
reached state, and a reached value meets the (pure) postcondition. -/
theorem hart_adequate {π : Proto} {w : HW P D V} {Ψ : Trace → Prop} {s0 : P} {Q : V → Prop} {P0 : GSet Nat}
    (hP0 : ∀ t, t ∈ P0 ↔ 0 < t ∧ ownTs w.M w.h t) (hΨ0 : Ψ [])
    (hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} wpPF π w Ψ s0 (fun v => iprop(⌜Q v⌝)))
    {n : Nat} {κs : List Unit} {es : List (HExpr P D V)} {σ : HSt}
    (hsteps : NSteps n ([HExpr.run w s0], (psInit, P0, [])) κs (es, σ)) :
    hartFacts π w.img w.M Ψ σ ∧ ∀ v, es = [HExpr.ret v] → Q v := by
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck [HExpr.run w s0]
    (psInit, P0, []) n κs es σ _ (fun _ => 0) ?_ hsteps
  intro Hinv
  have hw := @hwp Hinv
  iintro
  imod ghost_var_alloc ((psInit, P0, []) : HSt) with ⟨%γ, H⟩
  have hs := ghost_var_split (GF := GF) γ ((psInit, P0, []) : HSt) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  ihave ⟨H1, H2⟩ := hs $$ H
  imodintro
  iexists (fun σ _ _ _ => hartInterp (GF := GF) γ π w.img w.M Ψ σ), [fun v => iprop(⌜Q v⌝)],
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [H1]
  · unfold hartInterp
    iframe H1
    ipureintro
    exact ⟨⟨0, fun _ => hΨ0⟩, fun e he => (by cases he), Nat.le_refl _,
      fun a tf vf h => (by rw [show psInit.wFwd = ∅ from rfl, lookupEmpty] at h; cases h)⟩
  isplitl [H2]
  · iapply BigSepL2.bigSepL2_singleton.2
    ihave Hw := hw
    unfold wpPF
    ihave Hw := Hw $$ %γ %P0 %hP0
    unfold hartSt
    ihave Hw := Hw $$ H2
    dsimp only [wpH]
    iexact Hw
  iintro %es' %t2' %Heq %Hlen %_ Hσ Hpost _
  unfold hartInterp
  icases Hσ with ⟨_, %Hf⟩
  obtain ⟨e, rfl⟩ : ∃ e, es' = [e] := List.length_eq_one_iff.1 (by simpa using Hlen)
  ihave Hpost := BigSepL2.bigSepL2_singleton.1 $$ Hpost
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  cases e with
  | run w' s' =>
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp at hv
  | ret v0 =>
    dsimp only [ToVal.toVal, HExpr.toV, Option.elim]
    icases Hpost with %Hq
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp only [List.cons_append, List.nil_append, List.cons.injEq, HExpr.ret.injEq] at hv
    rw [← hv.1]; exact Hq

end adeq

/-! ## 3. A0 -/

/-- **A0 = `PF.adequacy`** (plan §0, rev 7; see the header for the Lean rendering).  Exports: (i) termination,
(ii) the trace part at every prefix of every hart, (iii) the partition (both parts), (iv) `Valid`, (v) `traceWf`,
(vi) `adExact`. -/
theorem adequacy {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]
    {pstep : P → D → PLabel → P → D → Prop} {pdone : P → Option V} {img : Image} {d0 : D} {ps : List P}
    {M : List PMsg} {run : PFRun P D}
    (π : Proto) (Φ : Nat → V → Prop) (Ψ : Nat → Trace → Prop) :
    PO_img π img →
    PO_ad π img M →
    (∀ h, Ψ h []) →
    devFreeProg pstep ps →
    (∀ h p, ps[h]? = some p → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wpPF π ⟨pstep, pdone, img, M, h⟩ (Ψ h) p (fun v => iprop(⌜∃ V, grd π img M V (Φ h v)⌝))) →
    validRun pstep img d0 ps M run →
      (∀ h v, run.done pdone h v → Φ h v)
    ∧ (∀ h k, Ψ h ((run.trace h).take k))
    ∧ (∀ t, 1 ≤ t → t ≤ M.length → exU (fun h => t ∈ run.fulfils h ∧ tidAt M t = some h))
    ∧ (∀ h, (run.fulfils h).Nodup)
    ∧ Valid π img M M.length
    ∧ run.traceWf M
    ∧ adExact img M := by
  intro himg had hΨ0 _ hwp hrun
  obtain ⟨hpart, hnd⟩ := validRun_partition hrun
  have htwf := validRun_traceWf hrun
  obtain ⟨hv, hM⟩ := hrun
  -- per-hart facts at every prefix
  have hfacts : ∀ h p, ps[h]? = some p → ∀ k, ∃ σ : HSt, σ.2.2 = (run.trace h).take k ∧
      hartFacts π img M (Ψ h) σ := by
    intro h p hp k
    obtain ⟨ag, _, P0, hP0, hs⟩ := validRun_soloD hv h p hp
    rw [hM] at hP0 hs
    obtain ⟨z, hz, _⟩ := soloSteps_take hs k
    have hn := solo_nsteps (w := ⟨pstep, pdone, img, M, h⟩) hz [] 0 [] _ (.refl _)
    have := hart_adequate (hlc := hlc) (GF := GF) (w := ⟨pstep, pdone, img, M, h⟩) (Q := fun v =>
      ∃ V, grd π img M V (Φ h v)) hP0 (hΨ0 h) (fun {_} => hwp h p hp) hn
    exact ⟨_, by simp [PFRun.trace], this.1⟩
  -- (iv)
  have hValid : Valid π img M M.length := by
    refine validInduction (fun t h1 h2 _ => ?_) himg had (adExact_all img M)
    obtain ⟨h, ⟨hin, htid⟩, _⟩ := hpart t h1 h2
    have hdom : ∃ p, ps[h]? = some p := by
      cases hq : ps[h]? with
      | some p => exact ⟨p, rfl⟩
      | none =>
        have : run.fulfils h = [] := by
          unfold PFRun.fulfils fulfilsOf; rw [validRun_traceNone hv hq]; rfl
        rw [this] at hin; cases hin
    obtain ⟨p, hp⟩ := hdom
    obtain ⟨σ, hτ, hf⟩ := hfacts h p hp (run.trace h).length
    rw [List.take_length] at hτ
    unfold PFRun.fulfils fulfilsOf at hin
    obtain ⟨e, he, het⟩ := List.mem_filterMap.1 hin
    exact hf.2.1 e (by rw [hτ]; exact he) t het
  refine ⟨fun h v hd => ?_, fun h k => ?_, hpart, hnd, hValid, htwf, adExact_all img M⟩
  · -- (i)
    obtain ⟨ag, hag, hdv⟩ := hd
    have hdom : ∃ p, ps[h]? = some p := by
      cases hq : ps[h]? with
      | some p => exact ⟨p, rfl⟩
      | none =>
        have hl := validRun_len hv
        have : h ≥ run.cfg.pcAgs.length := by
          rw [hl]; exact List.getElem?_eq_none_iff.1 hq
        rw [List.getElem?_eq_none_iff.2 this] at hag; cases hag
    obtain ⟨p, hp⟩ := hdom
    obtain ⟨ag', hag', P0, hP0, hs⟩ := validRun_soloD hv h p hp
    rw [hag] at hag'; cases hag'
    rw [hM] at hP0 hs
    have hfin : hstep (HExpr.run (⟨pstep, pdone, img, M, h⟩ : HW P D V) ag.paSt,
        ((ag.paWs, ag.paProm, [] ++ traceOf h run.evs) : HSt)) [] (HExpr.ret v, _, []) :=
      .fin _ _ _ v hdv
    have hS : Language.Step ([HExpr.run (⟨pstep, pdone, img, M, h⟩ : HW P D V) ag.paSt],
        ((ag.paWs, ag.paProm, [] ++ traceOf h run.evs) : HSt)) []
        ([HExpr.ret v], ((ag.paWs, ag.paProm, [] ++ traceOf h run.evs) : HSt)) := by
      simpa using Language.Step.atomic (Λ := (inferInstance : Language (HExpr P D V) HSt Unit V)) hfin [] []
    have hn := solo_nsteps (w := ⟨pstep, pdone, img, M, h⟩) hs [] 1 [] _
      (by simpa using NSteps.cons hS (.refl _))
    have := hart_adequate (hlc := hlc) (GF := GF) (w := ⟨pstep, pdone, img, M, h⟩) (Q := fun v =>
      ∃ V, grd π img M V (Φ h v)) hP0 (hΨ0 h) (fun {_} => hwp h p hp) hn
    obtain ⟨V', hg⟩ := this.2 v rfl
    exact grd_elim hValid hg
  · -- (ii)
    cases hq : ps[h]? with
    | none =>
      unfold PFRun.trace; rw [validRun_traceNone hv hq]; simpa using hΨ0 h
    | some p =>
      obtain ⟨σ, hτ, hf⟩ := hfacts h p hq k
      obtain ⟨V', hg⟩ := hf.1
      rw [hτ] at hg
      exact grd_elim hValid hg

end Weak.Prom.PF
