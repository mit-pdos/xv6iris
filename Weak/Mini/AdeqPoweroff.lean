/-
Weak/Mini: **`mini_adequacy_poweroff` — soundness of MiniLogic for POWER-OFF runs**, a corollary of
`mini_adequacy` (Adeq.lean:123).

```
theorem mini_adequacy_poweroff (hpre : mSteps P (mInit P) evs₁ c₁) (hext : mSteps P c₁ evs₂ c) (hnp : noProm c)
    (Ψ Φ) (hΨ0 : ∀ h, Ψ h [])
    (hwp : ∀ h hs, (mInit P).hs[h]? = some hs → ⊢ wp P c.log h (Ψ h) hs.fr (fun f => ⌜Φ h f⌝)) :
    ∀ h k, Ψ h ((traceOf h evs₁).take k)
```
A POWER-OFF run is a run prefix `evs₁` (stopped at `c₁`, possibly with outstanding promises) that SOME continuation
`evs₂` extends to a run with no outstanding promise.  The existential is over machine runs (the step relation
`mSteps`), not over program text.  It is a premise: supplied either by hand (an explicit continuation `hext`) or by
the reference chain (the prefix lemma `mini_prefix` + `mini_complete` give a whole valid run, which may be split at
any point).

The wp premise is checked against the COMPLETION's log `c.log`.  A run extends the log by appending only
(`mSteps_log`, Run.lean), so `c.log` extends `c₁.log` and every timestamp in the prefix's trace names the same
message in both.  The premises are satisfiable whenever `mini_adequacy`'s are (take `evs₂ = []`).

Proof: join the two runs (`mSteps_append`, local: the composition lemma of CmpHart.lean is in the completeness
development and is not imported here), apply `mini_adequacy` (ii) at `min k (traceOf h evs₁).length`, and cut the
completion's trace back with `traceOf_append`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.Adeq

namespace Weak.Mini.Logic

open Weak.Mini Weak.Mini.Mach
open Iris Iris.ProgramLogic Iris.BI

/-- Runs compose. -/
theorem mSteps_append {P : MProg} {c c1 c2 : MCfg} {es1 es2 : List MEvt}
    (h1 : mSteps P c es1 c1) (h2 : mSteps P c1 es2 c2) : mSteps P c (es1 ++ es2) c2 := by
  induction h1 with
  | refl => exact h2
  | step _ _ _ _ _ hs _ ih => exact .step _ _ _ _ _ hs (ih h2)

/-- **`mini_adequacy_poweroff`** (see the header).  Over a MiniMach run prefix `evs₁` of `P` from its initial
configuration that some continuation `evs₂` extends to a run with no outstanding promise, given every hart's wp
against the completion's final log `c.log`: `Ψ h` holds of every prefix of every hart's trace in `evs₁`. -/
theorem mini_adequacy_poweroff {hlc : HasLC} {GF : BundledGFunctors} [InvGpreS GF] [GhostVarG GF HSt]
    {P : MProg} {evs₁ evs₂ : List MEvt} {c₁ c : MCfg}
    (hpre : mSteps P (mInit P) evs₁ c₁) (hext : mSteps P c₁ evs₂ c) (hnp : noProm c)
    (Ψ : Nat → Trace → Prop) (Φ : Nat → MFront → Prop) (hΨ0 : ∀ h, Ψ h [])
    (hwp : ∀ (h : Nat) (hs : MHart), (mInit P).hs[h]? = some hs → ∀ [InvGS_gen hlc GF],
      ⊢@{IProp GF} wp P c.log h (Ψ h) hs.fr (fun f => iprop(⌜Φ h f⌝))) :
    ∀ h k, Ψ h ((traceOf h evs₁).take k) := by
  intro h k
  have hii := (mini_adequacy (hlc := hlc) (GF := GF) (mSteps_append hpre hext) hnp Ψ Φ hΨ0 hwp).1
    h (min k (traceOf h evs₁).length)
  rwa [traceOf_append, List.take_append_of_le_length (Nat.min_le_right _ _), ← List.take_take,
    List.take_of_length_le (l := traceOf h evs₁) (Nat.le_refl _)] at hii

end Weak.Mini.Logic
