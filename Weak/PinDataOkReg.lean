/-
Weak: **`dataOkR` — the registry of `yfB` lemmas** (the `@[yf_reg]` attribute read by the
walker `yf_walk`, `Weak/PinDataOkFp.lean`; a copy of `Weak/PinFetchPaReg.lean`, for the predicate `PinDataOkFp.yfB`).  Lean-only, no theorem.

A lemma tagged `@[yf_reg]` concludes `PinDataOkFp.yfB b S (f args)` (or `yf`, `yfT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets.
-/
import Lean

namespace Weak.PinDataOkReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize yfRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def yfRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.PinDataOkFp.yfT || c.isAppOf `Weak.PinDataOkFp.yf then c ← whnfR c
  unless c.isAppOf `Weak.PinDataOkFp.yfB do
    throwError "yf_reg: the conclusion is not an `yf` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "yf_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `yf_reg
  descr := "a yfB lemma for the dataOkR walker yf_walk, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (yfRegHead info.type).run'
    yfRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def yfRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((yfRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.PinDataOkReg
