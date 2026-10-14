/-
Weak: **W9a (B) B5 r2 — the registry of `xfB` lemmas** (the `@[xf_reg]` attribute read by the
walker `xf_walk`, `Weak/PinFetchPaFp.lean`; a copy of w1's `@[pf_reg]` registry,
`Weak/PinCycRunReg.lean`, for the predicate `PinFetchPaFp.xfB`).  Lean-only, no theorem.

A lemma tagged `@[xf_reg]` concludes `PinFetchPaFp.xfB b S (f args)` (or `xf`, `xfT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets.
-/
import Lean

namespace Weak.PinFetchPaReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize xfRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def xfRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.PinFetchPaFp.xfT || c.isAppOf `Weak.PinFetchPaFp.xf then c ← whnfR c
  unless c.isAppOf `Weak.PinFetchPaFp.xfB do
    throwError "xf_reg: the conclusion is not an `xf` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "xf_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `xf_reg
  descr := "a xfB lemma for the r2 walker xf_walk, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (xfRegHead info.type).run'
    xfRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def xfRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((xfRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.PinFetchPaReg
