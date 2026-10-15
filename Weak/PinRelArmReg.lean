/-
Weak: **W11-C2′ (a3) relArmed — the registry of `zfB` lemmas** (the `@[zf_reg]` attribute read by the
walker `zf_walk`, `Weak/PinRelArmFp.lean`; a copy of B1's `@[nw_reg]` registry,
`Weak/PinDataflowReg.lean`, for the predicate `PinRelArmFp.zfB`).  Lean-only, no theorem.

A lemma tagged `@[zf_reg]` concludes `PinRelArmFp.zfB b S (f args)` (or `zf`, `zfT`, or the same on
`ExceptT.run (f args)`); it is filed under the head constant `f`, so the walker tries exactly the
lemmas of the head it meets.
-/
import Lean

namespace Weak.PinRelArmReg

open Lean Meta

/-- The registry: head constant ↦ the lemmas filed under it. -/
initialize zfRegExt : SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (k, v) => m.insert k ((m.getD k #[]).push v)
    initial := {}
  }

/-- The head constant of a footprint lemma's tree. -/
def zfRegHead (ty : Expr) : MetaM Name := forallTelescope ty fun _ c => do
  let mut c := c
  for _ in [0:3] do
    if c.isAppOf `Weak.PinRelArmFp.zfT || c.isAppOf `Weak.PinRelArmFp.zf then c ← whnfR c
  unless c.isAppOf `Weak.PinRelArmFp.zfB do
    throwError "zf_reg: the conclusion is not an `zf` statement{indentExpr c}"
  let m := c.appArg!
  let m := if m.isAppOf ``ExceptT.run then m.appArg! else m
  let some n := m.getAppFn.constName? | throwError "zf_reg: no head constant{indentExpr m}"
  return n

initialize registerBuiltinAttribute {
  name := `zf_reg
  descr := "a zfB lemma for the relArmed walker zf_walk, filed under its tree's head constant"
  add := fun decl _ kind => do
    let info ← getConstInfo decl
    let h ← (zfRegHead info.type).run'
    zfRegExt.add (h, decl) kind
}

/-- The lemmas filed under `c`, latest first. -/
def zfRegFind (c : Name) : CoreM (Array Name) := do
  -- the most recently registered (most specific) lemma first
  return ((zfRegExt.getState (← getEnv)).getD c #[]).reverse

end Weak.PinRelArmReg
