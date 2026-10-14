/-
Weak: **W9a (B) B1 — the registry of `nwB` lemmas** (the `@[nw_reg]` attribute read by the walker
`nw_walk`, `Weak/PinDataflow.lean`; a copy of W-SCO's `@[fp_reg]` registry,
`Weak/SailCycleOrderFpReg.lean`, for the predicate `PinDataflow.nwB`).  Lean-only, no theorem.

A lemma tagged `@[nw_reg]` concludes `PinDataflow.nwB b S (f args)` (or `nw`, `nwT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets.
-/
import Lean

namespace Weak.PinDataflowReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize nwRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def nwRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.PinDataflow.nwT || c.isAppOf `Weak.PinDataflow.nw then c ← whnfR c
  unless c.isAppOf `Weak.PinDataflow.nwB do
    throwError "nw_reg: the conclusion is not an `nw` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "nw_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `nw_reg
  descr := "an nwB lemma for the W9a (B) walker nw_walk, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (nwRegHead info.type).run'
    nwRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def nwRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((nwRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.PinDataflowReg
