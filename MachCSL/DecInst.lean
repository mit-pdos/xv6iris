/-
MachCSL: re-synthesising the `Decidable` instances of `if`s (Lean ≥ 4.34).

Since Lean 4.34, `simp` rewrites inside the condition of an `if` by definitional
unfolding (of a definition, or of a `rfl` equation) WITHOUT rebuilding the
`Decidable` instance: `@ite α c inst t e` is left with `inst : Decidable c'`
where `c'` is the condition before the rewrite.  The term is still type-correct
(by delta), but `rw` then fails with "motive is not type correct" and `simp`
refuses the goal ("not type-correct under the `implicit` transparency level").
`fixDecInst` is a definitional simproc that replaces such an instance by a
freshly synthesised one, after checking that the two are definitionally equal;
the executor's normalisers include it, and `fix_dec` runs it on a goal.
-/
import Lean

namespace MachCSL

open Lean Meta Simp

/-- The core of `fixDecInst`: on `@ite α c inst t e` or `@dite α c inst t e`,
re-synthesise `inst` when its type is not reducibly `Decidable c`. -/
def fixDecInstCore (e : Expr) : SimpM DStep := do
  let args := e.getAppArgs
  -- `@ite α c inst t e`, `@dite α c inst t e`: the condition is argument 1, the instance 2;
  -- `@decide c inst`: 0 and 1
  let (ic, ii) ← match args.size with
    | 5 => pure (1, 2)
    | 2 => pure (0, 1)
    | _ => return .continue
  let c := args[ic]!
  let inst := args[ii]!
  let expected := mkApp (mkConst ``Decidable) c
  if ← withReducible (isDefEq (← inferType inst) expected) then return .continue
  let inst'? : Option Expr ← try pure (some (← synthInstance expected)) catch _ => pure none
  let some inst' := inst'? | return .continue
  -- a definitional step, so the two instances must be definitionally equal (`simp` runs at
  -- reducible transparency; the stale instance differs from the fresh one by a delta step)
  unless ← withDefault (isDefEq inst inst') do return .continue
  return .visit (mkAppN e.getAppFn (args.set! ii inst'))

dsimproc_decl fixDecInst (@ite _ _ _ _ _) := fixDecInstCore
dsimproc_decl fixDecInstD (@dite _ _ _ _ _) := fixDecInstCore
dsimproc_decl fixDecInstDecide (@decide _ _) := fixDecInstCore

/-- The core of `fixDiteBinders`: on `@dite α c inst t e`, a branch `fun h : c' => body` whose
binder type `c'` is not reducibly `c` (resp. `¬c`) and whose body does not use `h` gets the
binder type `c` (resp. `¬c`).  (A body that uses `h` only through `Eq.ndrec_symm` loses the use
by `MachCSL.ndrec_symm_const` first, since `simp` visits the branches before the `dite`.) -/
def fixDiteBindersCore (e : Expr) : SimpM DStep := do
  let args := e.getAppArgs
  unless args.size == 5 do return .continue
  let c := args[1]!
  let fixBranch (b : Expr) (ty : Expr) : MetaM (Option Expr) := do
    match b with
    | .lam n t body bi =>
      if ← withReducible (isDefEq t ty) then return none
      if body.hasLooseBVar 0 then return none
      return some (.lam n ty body bi)
    | _ => return none
  let t' ← fixBranch args[3]! c
  let e' ← fixBranch args[4]! (mkApp (mkConst ``Not) c)
  if t'.isNone && e'.isNone then return .continue
  return .visit (mkAppN e.getAppFn #[args[0]!, c, args[2]!, t'.getD args[3]!, e'.getD args[4]!])

dsimproc_decl fixDiteBinders (@dite _ _ _ _ _) := fixDiteBindersCore

/-- Repair the `Decidable` instances and branch binder types of the goal's `if`s (see the module
header). -/
macro "fix_dec" : tactic => `(tactic| (try simp only [fixDecInst, fixDecInstD, fixDecInstDecide, fixDiteBinders]))

end MachCSL
