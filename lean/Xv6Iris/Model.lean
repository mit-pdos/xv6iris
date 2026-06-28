/-
The real machine — the Iris operational semantics over the *actual* generated
Sail RISC-V model's `try_step`, replacing the demo machine of `Lang.lean`.

This file is **non-module** Lean: it imports the generated model (`LeanRV64D`)
and the forked lean-sail (`Sail`), both of which are non-module, alongside
iris-lean (module). A `module` file cannot import a non-module one, but a
non-module file can import both — so the whole model-facing layer lives here.

The model's `try_step : SailM Bool` is now an interaction-monad program
(`PreSail.Mon Register RegisterType exception`), so the same interpreter design
as the demo (`exec`/`run` over the free monad) applies verbatim — only the
`Register` type and the `step` are the real ones.
-/
import Iris.ProgramLogic.Language
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.ProofMode
import Sail
import LeanRV64D

open Iris Iris.BI Iris.ProgramLogic Sail PreSail
open LeanRV64D.Defs (Register RegisterType exception)

namespace Xv6Iris.Model

/-- One real fetch–decode–execute cycle, as an interaction-monad program
(the analog of Rocq's `riscv_step := bind (try_step 0 false) (fun _ => returnm tt)`).
`try_step` comes straight from the generated model. -/
noncomputable def riscv_step : Mon Register RegisterType exception Unit :=
  Mon.bind (LeanRV64D.Functions.try_step 0 false) (fun _ => Mon.pure ())

/-- Machine state: the real register file (dependent `RegisterType`) + byte memory. -/
@[ext]
structure MState where
  regs : (r : Register) → Option (RegisterType r)
  mem : Nat → Option (BitVec 8)

namespace MState

def setReg (s : MState) (r : Register) (v : RegisterType r) : MState :=
  { s with regs := fun r' => if h : r' = r then some (h ▸ v) else s.regs r' }

def setMem (s : MState) (a : Nat) (b : BitVec 8) : MState :=
  { s with mem := fun a' => if a' = a then some b else s.mem a' }

end MState

/-- The functional interpreter of the model's interaction monad against `MState`.
Effects hit the register/byte maps; `choosePrim` is resolved deterministically by
`trivialChoiceSource` (matching the model's `SailM`). The Iris-side interpreter —
distinct from lean-sail's executable `Mon.run`. -/
def exec {α} : Mon Register RegisterType exception α → MState → Option (α × MState)
  | .pure a, s => some (a, s)
  | .throw _, _ => none
  | .vis o k, s =>
    match o with
    | .regRead r =>
        match s.regs r with
        | some v => exec (k v) s
        | none => none
    | .regWrite r v => exec (k ()) (s.setReg r v)
    | .readByte a =>
        match s.mem a with
        | some b => exec (k b) s
        | none => none
    | .writeByte a b => exec (k ()) (s.setMem a b)
    | .choosePrim p => exec (k (trivialChoiceSource.choose p ())) s

/-- Relational twin (graph of `exec`), for the Iris `primStep`. -/
def run {α} (m : Mon Register RegisterType exception α) (s : MState) (a : α) (s' : MState) : Prop :=
  exec m s = some (a, s')

theorem run_deterministic {α} {m : Mon Register RegisterType exception α} {s a₁ s₁ a₂ s₂}
    (h₁ : run m s a₁ s₁) (h₂ : run m s a₂ s₂) : a₁ = a₂ ∧ s₁ = s₂ := by
  unfold run at h₁ h₂; rw [h₁] at h₂
  exact ⟨congrArg Prod.fst (Option.some.inj h₂), congrArg Prod.snd (Option.some.inj h₂)⟩

/-! ## The Iris `Language` over the real model -/

inductive RiscvExpr | Loop

instance : ToVal RiscvExpr Empty where
  toVal _ := none
  ofVal v := v.elim
  coe_of_toVal_eq_some {_ v} _ := v.elim
  toVal_coe v := v.elim

instance : PrimStep RiscvExpr MState (List Empty) where
  primStep
    | (e, σ), obs, (e', σ', efs) =>
      e = .Loop ∧ e' = .Loop ∧ obs = [] ∧ efs = [] ∧ ∃ r, exec riscv_step σ = some (r, σ')

instance : Language RiscvExpr MState Empty Empty where
  val_stuck _ := rfl

end Xv6Iris.Model
