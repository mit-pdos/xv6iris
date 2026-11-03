/-
Weak/Prom: **the Sail model as executable code, with the opaque reservation predicate as a PARAMETER** (S0-P part
(2), milestone 3).

The model's LR/SC reservation predicate `match_reservation` is the opaque constant
`LeanRV64D.Functions.xv6_resv_matches : physaddrbits → Bool` (model/Xv6Extras.lean: "an arbitrary but fixed
platform predicate … every proof that reads one must handle both answers"; plan D51).  Its compiled code is the
`Inhabited` default (`fun _ => false`: every SC fails before its memory write), so running the compiled model would
explore ONE platform only.

`subst_cone% c r` (below) makes every definition on a path from `r` to `c` (through definition bodies) a function of
`c`: for each such `f` it adds `f._rp : (P : type of c) → type of f` whose value is `fun P => (value of f)[c := P,
g := g._rp P for every such g]`, kernel-checked and compiled.  So `MachCSL.riscvStep._rp P` IS the model's
`riscvStep` with the predicate instantiated to `P` (`riscvStepP_opaque`: at `P := xv6_resv_matches` it is
`riscvStep`, by `rfl`), and the oracle can run every platform `P` — in particular both answers per address,
consistently (one `P` per run, shared by all harts: the predicate has no hart argument).

Everything else (the decoder cone, which the Sail backend emits `noncomputable`) gets its code from
`Vtest.Model`'s `compile_cone%` (`csimp` rules proved by `rfl`); nothing here is `implemented_by`.
-/
import Vtest.Model
import Weak.Prom.Emit

open Lean Meta Elab Command

namespace Weak.Prom.SailExec

/-- Only the model, the machine and the Sail library are traversed. -/
def ours (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    [`LeanRV64D, `MachCSL, `Sail, `Vtest].contains m.getRoot
  | none => true

/-- Does the body of definition `n` reach `target`?  Memoised; `order` collects the reaching definitions in
dependency order (callees first). -/
partial def reach (target : Name) (n : Name) : StateT (NameMap Bool × Array Name) MetaM Bool := do
  if n == target then return true
  if let some b := (← get).1.find? n then return b
  modify fun s => (s.1.insert n false, s.2)
  let env ← getEnv
  let some (.defnInfo dv) := env.find? n | return false
  if !ours env n then return false
  let mut r := false
  for c in dv.value.getUsedConstants do
    if ← reach target c then r := true
  for c in dv.type.getUsedConstants do
    if ← reach target c then r := true
  modify fun s => (s.1.insert n r, if r then s.2.push n else s.2)
  return r

def rpName (n : Name) : Name := n ++ `_rp

/-- Add `n._rp`. -/
def mkCopy (target : Name) (S : NameSet) (n : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.defnInfo dv) := env.find? n | throwError "subst_cone%: {n} is not a definition"
  let tinfo ← getConstInfo target
  withLocalDeclD `P tinfo.type fun P => do
    let f := fun (e : Expr) => match e with
      | .const c ls =>
        if c == target then some P
        else if S.contains c then some (mkApp (.const (rpName c) ls) P)
        else none
      | _ => none
    let nv ← mkLambdaFVars #[P] (dv.value.replace f)
    let nt ← mkForallFVars #[P] (dv.type.replace f)
    let d : DefinitionVal := { dv with name := rpName n, type := nt, value := nv, all := [rpName n] }
    addAndCompile (.defnDecl d)

/-- `subst_cone% c r`: see the file header. -/
elab "subst_cone% " tgt:ident root:ident : command => do
  let names ← liftTermElabM do
    let t ← realizeGlobalConstNoOverloadWithInfo tgt
    let r ← realizeGlobalConstNoOverloadWithInfo root
    let (ok, (_, order)) ← (reach t r).run ({}, #[])
    if !ok then throwError "subst_cone%: {r} does not reach {t}"
    let S : NameSet := order.foldl (fun s n => s.insert n) {}
    for n in order do mkCopy t S n
    return order
  logInfo m!"subst_cone%: {names.size} definition(s) made functions of the predicate: {names}"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
subst_cone% LeanRV64D.Functions.xv6_resv_matches MachCSL.riscvStep

end Weak.Prom.SailExec

namespace Weak.Prom

open Sail LeanRV64D

/-- THE MODEL'S CYCLE AT PLATFORM `P` (the reservation predicate's value at each physical address). -/
def riscvStepP (P : BitVec 64 → Bool) (tick : Bool) : SailM Unit := MachCSL.riscvStep._rp P tick

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- At the opaque predicate itself, `riscvStepP` is the model's `riscvStep`. -/
theorem riscvStepP_opaque : riscvStepP LeanRV64D.Functions.xv6_resv_matches = MachCSL.riscvStep := rfl

end Weak.Prom
