/-
Weak/Mini: **`mini_adequacy` — the soundness theorem of MiniLogic, in A0 shape** (mini plan rev 4 §2 L3, a VETTED
statement [R2]; the full stack's template is `Weak/Prom/CoreAdeq.lean`, `PF.adequacy`, plan rev 7 §0 A0).

```
theorem mini_adequacy (hrun : mSteps P (mInit P) evs c) (hnp : noProm c) (Ψ Φ) (hΨ0 : ∀ h, Ψ h [])
    (hwp : ∀ h hs, (mInit P).hs[h]? = some hs → ⊢ wp P c.log h (Ψ h) hs.fr (fun f => ⌜Φ h f⌝)) :
    (ii) Ψ at every prefix of every hart's trace ∧ (i) Φ of every finished hart ∧
    (iii) hart h fulfils exactly its own messages of the final log, each once ∧ (v) every trace entry is well-formed
```
Stated over a run `mSteps P (mInit P) evs c` with no outstanding promise at the end (P1 gate review §5: the final
configuration of `miniValidRun` is existential; this names it).  The trivial protocol only: A0 (iv) `Valid` and
(vi) `adExact` are vacuous and not stated; A0's `PO_img`/`PO_ad`/`devFreeProg` premises have nothing to say.
The wp premise holds in every invariant world (`∀ [InvGS_gen hlc GF]`), for any `GF` with the invariant and
ghost-variable functors (the usual form of an Iris adequacy premise).

Proof (as CoreAdeq.lean): `mSteps_solo` (Run.lean) gives every hart a solo run against the final log with its
trace; every prefix of it is a run of the hart's thread (`solo_nsteps`), so `wp_strong_adequacy_gen` gives `Ψ` at
every prefix (`hart_adequate`); a finished hart takes the value step, giving `Φ`.  (iii) is `mSteps_partition`,
(v) `solo_wf` (Run.lean).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Logic
import Iris.ProgramLogic.Adequacy

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Iris.ProgramLogic.Language Iris.ProgramLogic.Language.Notation

/-! ## 1. Solo runs are thread runs -/

theorem solo_nsteps {w : HW} :
    ∀ {f : MFront} {ws : MSt} {τ : Trace} {f' : MFront} {ws' : MSt}, solo w.P w.M w.h f ws τ f' ws' →
      ∀ (τ0 : Trace) (n : Nat) (κ : List Unit) (ρ : List HE × HSt),
        NSteps n ([HE.run w f'], (ws', τ0 ++ τ)) κ ρ → NSteps (τ.length + n) ([HE.run w f], (ws, τ0)) κ ρ := by
  intro f ws τ f' ws' h
  induction h with
  | refl f ws => intro τ0 n κ ρ hn; simpa using hn
  | step f ws l ots f1 ws1 pr pr' τ f2 ws2 hn hm _ ih =>
    intro τ0 n κ ρ hns
    have hs : hstep (HE.run w f, (ws, τ0)) [] (HE.run w f1, (ws1, τ0 ++ [(l, ots)]), []) :=
      .lab w f ws τ0 l ots f1 ws1 pr pr' hn hm
    have hS : Language.Step ([HE.run w f], (ws, τ0)) [] ([HE.run w f1], (ws1, τ0 ++ [(l, ots)])) := by
      simpa using Language.Step.atomic (Λ := (inferInstance : Language HE HSt Unit MFront)) hs [] []
    have := ih (τ0 ++ [(l, ots)]) n κ ρ (by simpa using hns)
    have h2 := NSteps.cons hS this
    simp only [List.nil_append] at h2
    rw [show (l, ots) :: τ = [(l, ots)] ++ τ from rfl, List.length_append]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h2

/-! ## 2. Per-hart adequacy -/

section adeq

variable {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]

/-- **PER-HART ADEQUACY**: after any thread run from the hart's initial state, the trace invariant holds of the
reached trace, and a reached value meets the (pure) postcondition. -/
theorem hart_adequate {P : MProg} {M : List MMsg} {h : Nat} {Ψ : Trace → Prop} {f0 : MFront} {Q : MFront → Prop}
    (hΨ0 : Ψ []) (hwp : ∀ [InvGS_gen hlc GF], ⊢@{IProp GF} wp P M h Ψ f0 (fun v => iprop(⌜Q v⌝)))
    {n : Nat} {κs : List Unit} {es : List HE} {σ : HSt}
    (hsteps : NSteps n ([HE.run ⟨P, M, h⟩ f0], (msInit, [])) κs (es, σ)) :
    Ψ σ.2 ∧ ∀ v, es = [HE.ret v] → Q v := by
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.MaybeStuck [HE.run ⟨P, M, h⟩ f0]
    (msInit, []) n κs es σ _ (fun _ => 0) ?_ hsteps
  intro Hinv
  have hw := @hwp Hinv
  iintro
  imod ghost_var_alloc ((msInit, []) : HSt) with ⟨%γ, H⟩
  have hs := ghost_var_split (GF := GF) γ ((msInit, []) : HSt) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hs
  ihave ⟨H1, H2⟩ := hs $$ H
  imodintro
  iexists (fun σ _ _ _ => hartInterp (GF := GF) γ Ψ σ), [fun v => iprop(⌜Q v⌝)],
    (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [H1]
  · unfold hartInterp
    iframe H1
    ipureintro
    exact hΨ0
  isplitl [H2]
  · iapply BigSepL2.bigSepL2_singleton.2
    ihave Hw := hw
    unfold wp
    ihave Hw := Hw $$ %γ
    unfold hartSt
    ihave Hw := Hw $$ H2
    dsimp only [wpH]
    iexact Hw
  iintro %es' %t2' %Heq %Hlen %_ Hσ Hpost _
  unfold hartInterp
  icases Hσ with ⟨_, %Hf⟩
  obtain ⟨e, rfl⟩ : ∃ e, es' = [e] := List.length_eq_one_iff.1 (by simpa using Hlen)
  ihave Hpost := BigSepL2.bigSepL2_singleton.1 $$ Hpost
  iapply fupd_mask_intro_discard Iris.Std.LawfulSet.empty_subset
  cases e with
  | run w' f' =>
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp at hv
  | ret v0 =>
    dsimp only [ToVal.toVal, HE.toV, Option.elim]
    icases Hpost with %Hq
    ipureintro
    refine ⟨Hf, fun v hv => ?_⟩
    rw [Heq] at hv
    simp only [List.cons_append, List.nil_append, List.cons.injEq, HE.ret.injEq] at hv
    rw [← hv.1]; exact Hq

end adeq

/-! ## 3. A0 for MiniLogic -/

/-- **`mini_adequacy`** (A0 shape; see the header).  Over a MiniMach run of `P` from its initial configuration
with no outstanding promise at the end, given every hart's wp against the run's final log `c.log`:
(ii) `Ψ h` holds of every prefix of every hart's trace; (i) a FINISHED hart's final front-end state meets `Φ h`;
(iii) hart `h` fulfils exactly its own messages of `c.log` (the partition), and (iii') none twice; (v) every
trace entry is well-formed against `c.log` (loads read what they return, stores fulfil their own word). -/
theorem mini_adequacy {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]
    {P : MProg} {evs : List MEvt} {c : MCfg} (hrun : mSteps P (mInit P) evs c) (hnp : noProm c)
    (Ψ : Nat → Trace → Prop) (Φ : Nat → MFront → Prop) (hΨ0 : ∀ h, Ψ h [])
    (hwp : ∀ (h : Nat) (hs : MHart), (mInit P).hs[h]? = some hs → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wp P c.log h (Ψ h) hs.fr (fun f => iprop(⌜Φ h f⌝))) :
      (∀ h k, Ψ h ((traceOf h evs).take k))
    ∧ (∀ h (hs : MHart), c.hs[h]? = some hs → mDone P h hs.fr → Φ h hs.fr)
    ∧ (∀ h t, t ∈ fulfilsOf h evs ↔ 0 < t ∧ ownAt c.log h t)
    ∧ (∀ h, (fulfilsOf h evs).Nodup)
    ∧ (∀ h, ∀ e ∈ traceOf h evs, entryWf P c.log h e) := by
  have hsolo := mSteps_solo hrun (mInit_ok P)
  obtain ⟨hpart, hnd⟩ := mSteps_partition hrun hnp
  refine ⟨fun h k => ?_, fun h hs hh hd => ?_, hpart, hnd, fun h e he => ?_⟩
  · -- (ii)
    cases h0 : (mInit P).hs[h]? with
    | none => rw [mSteps_none hrun h0]; simpa using hΨ0 h
    | some hs0 =>
      obtain ⟨hs', _, hs⟩ := hsolo h hs0 h0
      obtain ⟨f'', ws'', hk⟩ := solo_take hs k
      have hn := solo_nsteps (w := ⟨P, c.log, h⟩) hk [] 0 [] _ (.refl _)
      have e := (mInit_get h0).2
      subst e
      have := hart_adequate (hlc := hlc) (GF := GF) (hΨ0 h) (fun {_} => hwp h _ h0) (Q := Φ h) hn
      simpa using this.1
  · -- (i)
    have hlt : h < (mInit P).hs.length := by
      rw [← mSteps_len hrun]; exact (List.getElem?_eq_some_iff.1 hh).1
    obtain ⟨hs0, h0⟩ : ∃ hs0, (mInit P).hs[h]? = some hs0 := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨hs', hh', hs1⟩ := hsolo h hs0 h0
    rw [hh] at hh'
    cases hh'
    have hfin : hstep (HE.run (⟨P, c.log, h⟩ : HW) hs.fr, ((hs.ws, [] ++ traceOf h evs) : HSt)) []
        (HE.ret hs.fr, ((hs.ws, [] ++ traceOf h evs) : HSt), []) := .fin _ _ _ hd
    have hS : Language.Step ([HE.run (⟨P, c.log, h⟩ : HW) hs.fr], ((hs.ws, [] ++ traceOf h evs) : HSt)) []
        ([HE.ret hs.fr], ((hs.ws, [] ++ traceOf h evs) : HSt)) := by
      simpa using Language.Step.atomic (Λ := (inferInstance : Language HE HSt Unit MFront)) hfin [] []
    have hn := solo_nsteps (w := ⟨P, c.log, h⟩) hs1 [] 1 [] _ (by simpa using NSteps.cons hS (.refl _))
    have e := (mInit_get h0).2
    subst e
    exact (hart_adequate (hlc := hlc) (GF := GF) (hΨ0 h) (fun {_} => hwp h _ h0) (Q := Φ h) hn).2 _ rfl
  · -- (v)
    cases h0 : (mInit P).hs[h]? with
    | none => rw [mSteps_none hrun h0] at he; cases he
    | some hs0 =>
      obtain ⟨hs', _, hs⟩ := hsolo h hs0 h0
      exact solo_wf hs e he

end Weak.Mini.Logic
