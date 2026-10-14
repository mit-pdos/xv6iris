/-
Weak: **W9a (B) B5 cycRun — the registry of `pfB` lemmas** (the `@[pf_reg]` attribute read by the
walker `pf_walk`, `Weak/PinCycRunFp.lean`; a copy of B1's `@[nw_reg]` registry,
`Weak/PinDataflowReg.lean`, for the predicate `PinCycRunFp.pfB`).  Lean-only, no theorem.

A lemma tagged `@[pf_reg]` concludes `PinCycRunFp.pfB b S (f args)` (or `pf`, `pfT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets.
-/
import Lean

namespace Weak.PinCycRunReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize pfRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def pfRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.PinCycRunFp.pfT || c.isAppOf `Weak.PinCycRunFp.pf then c ← whnfR c
  unless c.isAppOf `Weak.PinCycRunFp.pfB do
    throwError "pf_reg: the conclusion is not an `pf` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "pf_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `pf_reg
  descr := "a pfB lemma for the cycRun walker pf_walk, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (pfRegHead info.type).run'
    pfRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def pfRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((pfRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.PinCycRunReg
