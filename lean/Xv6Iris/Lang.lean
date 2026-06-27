/-
The Iris `Language` instance over the Sail free monad — the analog of Rocq's
`RiscvLang.riscv_lang`.

Like Rocq's `riscv_lang`, the language is concrete (one machine): a single
`Loop` expression whose primitive step runs `step` (the model's `try_step`) once
via `exec`. No values (`Val = Empty`), no observations, no forks — exactly the
Rocq shape (`mval := Empty_set`).

Here it's instantiated on a *demo* machine (one GPR-ish state, a `PC := PC+4`
tick) to exercise the iris-lean `Language`/`PrimStep`/`ToVal` typeclasses end to
end. The real port replaces `DemoReg`/`step` with the generated model's
`Register`/`try_step`, following the identical pattern.
-/
module

public import Xv6Iris.Interp
public import Iris.ProgramLogic.Language

@[expose] public section

namespace Xv6Iris.Demo

open Xv6Iris.Sail
open Iris.ProgramLogic

/-! ## A concrete demo machine -/

inductive DemoReg | PC | nextPC
  deriving DecidableEq

abbrev DemoRT : DemoReg → Type := fun _ => BitVec 64

/-- Demo exception type (empty: this machine never throws user exceptions). -/
inductive DemoExn

abbrev DState := MState DemoReg DemoRT

/-- The machine step (stands in for the model's `try_step 0 false`): `PC := PC+4`. -/
def step : Mon DemoReg DemoRT DemoExn Unit := do
  let pc ← readReg DemoReg.PC
  writeReg DemoReg.PC (pc + 4)

/-! ## The one-expression language -/

inductive RiscvExpr | Loop

instance : ToVal RiscvExpr Empty where
  toVal _ := none
  ofVal v := v.elim
  coe_of_toVal_eq_some {_ v} _ := v.elim
  toVal_coe v := v.elim

instance : PrimStep RiscvExpr DState (List Empty) where
  primStep
    | (e, σ), obs, (e', σ', efs) =>
      e = .Loop ∧ e' = .Loop ∧ obs = [] ∧ efs = [] ∧ ∃ r, exec step σ = some (r, σ')

instance : Language RiscvExpr DState Empty Empty where
  val_stuck _ := rfl

/-- Sanity check: a `Loop` step is exactly one `exec step`. -/
theorem primStep_iff {σ σ' : DState} :
    PrimStep.primStep (RiscvExpr.Loop, σ) ([] : List Empty) (RiscvExpr.Loop, σ', [])
      ↔ ∃ r, exec step σ = some (r, σ') := by
  constructor
  · rintro ⟨_, _, _, _, h⟩; exact h
  · intro h; exact ⟨rfl, rfl, rfl, rfl, h⟩

end Xv6Iris.Demo
