/-
Weak: **W-SCO (A) — the registry of footprint lemmas** (the `@[fp_reg]` attribute read by the
walker `SailCycleOrderFp.fp_step`, `Weak/SailCycleOrderFp.lean`) and of phase lemmas (`@[g_reg]`, read by
`good_walk`).  Lean-only, no theorem.

A lemma tagged `@[fp_reg]` concludes `SailCycleOrderFp.fpB b S (f args)` (or `fp`, `fpT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets (no failing unification against unrelated lemmas).
-/
import Lean

namespace Weak.SailCycleOrderFpReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize fpRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def fpRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.SailCycleOrderFp.fpT || c.isAppOf `Weak.SailCycleOrderFp.fp then c ← whnfR c
  unless c.isAppOf `Weak.SailCycleOrderFp.fpB do
    throwError "fp_reg: the conclusion is not an `fp` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "fp_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `fp_reg
  descr := "a footprint lemma for the W-SCO walker, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (fpRegHead info.type).run'
    fpRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def fpRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((fpRegExt.getState (← getEnv)).getD c #[]).reverse

/-! ## The registry of phase lemmas (`@[g_reg]`, read by `good_walk`, `Weak/SailCycleOrderGood.lean`)

A lemma tagged `@[g_reg]` concludes `SailCycleOrderK.good A R Q ph (f args)`; it is filed under `f`. -/

initialize gRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a phase lemma's tree. -/
def gRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let c := c.consumeMData
  unless c.isAppOfArity `Weak.SailCycleOrderK.good 6 do
    throwError "g_reg: the conclusion is not a `good` statement{indentExpr c}"
  let some n := c.appArg!.getAppFn.constName? | throwError "g_reg: no head constant{indentExpr c}"
  return n

initialize registerBuiltinAttribute {
  name := `g_reg
  descr := "a phase lemma for the W-SCO walker `good_walk`, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (gRegHead info.type).run'
    gRegExt.add (h, decl) kind
}

/-- The phase lemmas filed under `c`, latest first. -/
def gRegFind (c : Name) : CoreM (Array Name) := do
  return ((gRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.SailCycleOrderFpReg
