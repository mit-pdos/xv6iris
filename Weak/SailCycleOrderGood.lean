/-
Weak: **W-SCO (A) — the phase-aware walker** over the residual invariant
`SailCycleOrderK.good A Rboot Q ph m` (plan rev 36 §C W-SCO (A) (1)(c): the instruction-
independent cycle, the fetch's two-halfword arm).  Lean-only.

`good_walk` walks a `good` goal node by node like `fp_walk` (`Weak/SailCycleOrderFp.lean`), with
the phase rules of `good` (a RAM instruction-fetch read moves to phase `fetch`; an announce
requires phase `fetch` at an SFENCE.VMA word and moves to `instr` otherwise; a `Barrier_RISCV_i`
requires phase `instr`), and DELEGATES every bound computation it can to the footprint walker:
a registered footprint lemma, or a nested `fp_walk` of the bound tree (strict `fp` at any phase,
by `fpGood`; relaxed `fpB true` at phase `fetch`, by `fpGoodF`).  Only the phase-changing
stretches are walked in `good` itself.  Goals it cannot close are left to the caller.

Every helper is `Weak.SailCycleOrderGW.*`.
-/
import Weak.SailCycleOrderFp

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderGW
open SailCycleOrderK SailCycleOrderFp

variable {A : Int → BitVec 8 → Prop}

theorem gBindCF {X Y : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q : Ph → Y → Prop) (ph : Ph) (m : SailM X) (f : X → SailM Y)
    (h : good A R (fun ph' a => good A R Q ph' (f a)) ph m) : good A R Q ph (FreeM.bind m f) :=
  goodBind A R Q f m ph h

theorem gAssocF {X Y Z : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q : Ph → Z → Prop) (ph : Ph) (m : SailM X) (g : X → SailM Y) (f : Y → SailM Z)
    (h : good A R Q ph (FreeM.bind m (fun x => FreeM.bind (g x) f))) :
    good A R Q ph (FreeM.bind (FreeM.bind m g) f) := by
  rw [FreeMLemmas.bind_assoc]; exact h

theorem gIteF {X : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q : Ph → X → Prop) (ph : Ph) (c : Prop) [Decidable c] (a d : SailM X)
    (ha : c → good A R Q ph a) (hd : ¬ c → good A R Q ph d) : good A R Q ph (ite c a d) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hd h

theorem gDiteF {X : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q : Ph → X → Prop) (ph : Ph) (c : Prop) [Decidable c] (a : c → SailM X) (d : ¬ c → SailM X)
    (ha : ∀ h, good A R Q ph (a h)) (hd : ∀ h, good A R Q ph (d h)) : good A R Q ph (dite c a d) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hd h

theorem gEqRecF.{u} {X : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q : Ph → X → Prop) (ph : Ph) {α : Sort u} {a a' : α} {T : Type} (t : T) (h : a = a')
    (F : T → SailM X) (ht : good A R Q ph (F t)) :
    good A R Q ph (F (@Eq.rec α a (fun _ _ => T) t a' h)) := by
  cases h; exact ht

/-- Delegation of a bound computation to the strict footprint. -/
theorem gFpF {X Y : Type} (A : Int → BitVec 8 → Prop) (S : X → Prop) (Q : Ph → Y → Prop) (ph : Ph)
    (m : SailM X) (f : X → SailM Y) (hm : fp S m) (hf : ∀ a, S a → good A Rboot Q ph (f a)) :
    good A Rboot Q ph (FreeM.bind m f) :=
  goodBind A Rboot Q f m ph (fpGood A S m hm _ ph hf)

/-- Delegation of a bound computation to the relaxed footprint, at phase `fetch`. -/
theorem gFpRF {X Y : Type} (S : X → Prop) (Q : Ph → Y → Prop)
    (m : SailM X) (f : X → SailM Y) (hm : fpB true S m)
    (hf : ∀ a, S a → good (fun _ _ => True) Rboot Q .fetch (f a)) :
    good (fun _ _ => True) Rboot Q .fetch (FreeM.bind m f) :=
  goodBind _ Rboot Q f m .fetch (fpGoodF (fun _ _ => True) S m hm _ hf)

theorem gFpHeadF {X : Type} (A : Int → BitVec 8 → Prop) (S : X → Prop) (Q : Ph → X → Prop) (ph : Ph)
    (m : SailM X) (hm : fp S m) (hQ : ∀ a, S a → Q ph a) : good A Rboot Q ph m :=
  fpGood A S m hm Q ph hQ

theorem gFpRHeadF {X : Type} (S : X → Prop) (Q : Ph → X → Prop) (m : SailM X) (hm : fpB true S m)
    (hQ : ∀ a, S a → Q .fetch a) : good (fun _ _ => True) Rboot Q .fetch m :=
  fpGoodF (fun _ _ => True) S m hm Q hQ

theorem gMonoF {X : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (Q Q' : Ph → X → Prop) (ph : Ph) (m : SailM X) (h : good A R Q ph m)
    (hQ : ∀ ph a, Q ph a → Q' ph a) : good A R Q' ph m :=
  goodMono A A R Q Q' (fun _ _ h => h) hQ m ph h

/-- A bound computation with a registered phase lemma (`@[g_reg]`): through its post. -/
theorem gBindQF {X Y : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (S : Ph → X → Prop) (Q : Ph → Y → Prop) (ph : Ph) (m : SailM X) (f : X → SailM Y)
    (hm : good A R S ph m) (hf : ∀ p a, S p a → good A R Q p (f a)) :
    good A R Q ph (FreeM.bind m f) :=
  goodBind A R Q f m ph (goodMono A A R S _ (fun _ _ h => h) hf m ph hm)

/-- A head with a registered phase lemma: its post implies the goal's. -/
theorem gHeadQF {X : Type} (A : Int → BitVec 8 → Prop) (R : (r : Register) → RegisterType r → Prop)
    (S Q : Ph → X → Prop) (ph : Ph) (m : SailM X) (hm : good A R S ph m)
    (hQ : ∀ p a, S p a → Q p a) : good A R Q ph m :=
  goodMono A A R S Q (fun _ _ h => h) hQ m ph hm

/-- The device side of an instruction-fetch read at a RAM address is vacuous. -/
theorem vacIF (a b : Bool) (P : Prop) (ha : a = false) (hb : b = true) : (a = false → b = false) → P :=
  fun h => absurd (h ha) (by rw [hb]; decide)

namespace GWalk
open Lean Meta Elab Tactic
open Weak.SailCycleOrderFp.Walk

/-- Destructure a `good` goal: `(X, A, R, Q, ph, m)`. -/
def goodView? (t : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let t := t.consumeMData
  if t.isAppOfArity ``Weak.SailCycleOrderK.good 6 then
    let a := t.getAppArgs
    return some (a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!)
  return none

def mkGood (X A R Q ph m : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``Weak.SailCycleOrderK.good) #[X, A, R, Q, ph, m]

/-- Is `A` the trivial fetch filter `fun _ _ => True`? -/
def isTrivA (A : Lean.Expr) : Bool :=
  A.isLambda && A.bindingBody!.isLambda && A.bindingBody!.bindingBody!.consumeMData.isConstOf ``True

/-- Try to close the goal `fpB b S m` (fresh) by a nested footprint walk; returns the proof. -/
def tryFp (cx : Ctx) (b X m : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let post ← withLocalDeclD `a X fun a => mkLambdaFVars #[a] (mkConst ``True)
  let gm ← newGoal (mkFp b X post m)
  let s ← saveState
  try
    let left ← loop cx [gm.mvarId!]
    if left.isEmpty then return some (← instantiateMVars gm)
    s.restore; return none
  catch _ => s.restore; return none

/-- Instantiate the phase lemma `pf₀ : ∀ xs, good A' R' S ph' m'` at the goal's `A`, `R`, `ph`
and tree `m` (same head): the proof, its post, its leftover hypotheses. -/
def gInst (pf₀ ty₀ A R ph m : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr × List MVarId)) := do
  let (args, _, ty) ← forallMetaTelescope ty₀
  let some (_, A', R', S, ph', m') ← goodView? ty | return none
  unless m'.getAppFn.constName? == m.getAppFn.constName? do return none
  unless ← withTransparency .instances (isDefEq m' m) do return none
  unless ← isDefEq A' A do return none
  unless ← isDefEq R' R do return none
  unless ← isDefEq ph' ph do return none
  let hs ← argGoals args
  return some (← instantiateMVars (mkAppN pf₀ args), ← instantiateMVars S, hs)

/-- After introducing a value `a` and its post `ha`: substitute `ha` when it is an equation on
`a` (a post that pins the value; later `if`s/`match`es on it then reduce). -/
partial def substPost (g : MVarId) (ha : FVarId) : MetaM MVarId := g.withContext do
  let t ← whnfR (← instantiateMVars (← ha.getType))
  if t.isAppOfArity ``Eq 3 && ((t.getArg! 1).isFVar || (t.getArg! 2).isFVar) then
    return (← subst? g ha).getD g
  if t.isAppOfArity ``And 2 then
    let s ← saveState
    try
      let gs ← g.cases ha
      if h : gs.size = 1 then
        let sg := gs[0]
        let mut g' := sg.mvarId
        for f in sg.fields.reverse do
          if f.isFVar then
            -- the field may have been substituted away by an earlier one
            if (← g'.withContext do pure ((← getLCtx).contains f.fvarId!)) then
              g' ← substPost g' f.fvarId!
        return g'
      s.restore; return g
    catch _ => s.restore; return g
  return g

/-- Introduce `a`, `ha` and substitute an equational post. -/
def introPost (g : MVarId) : MetaM MVarId := do
  let (fvs, g') ← g.introN 2
  substPost g' fvs[1]!

/-- One `good` step. -/
partial def gstep (cx : Ctx) (g : MVarId) (X A R Q ph m0 : Lean.Expr) : TacticM (List MVarId) :=
  g.withContext do
  cx.gsteps.modify (· + 1)
  if (← cx.gsteps.get) > cx.glimit then throwError "good_walk: step limit"
  let m ← norm m0
  if cx.gDbg then
    let fmt ← ppExpr m
    let str := (toString fmt).take 300
    logInfo m!"gstep ph={ph} :: {str}"
  let fn := m.getAppFn
  let args := m.getAppArgs
  let C (n : Name) : Lean.Expr := mkConst n
  let replace (m' : Lean.Expr) : TacticM (List MVarId) := do
    let g' ← newGoal (mkGood X A R Q ph m')
    g.assign g'
    return [g'.mvarId!]
  let isRboot := R.isConstOf ``Weak.SailCycleOrderK.Rboot
  let isFetch := ph.isConstOf ``Weak.SailCycleOrderK.Ph.fetch
  -- a phase that is an `if` on a Boolean: decide it or case on it
  if ph.isAppOf ``ite then
    let ph' ← whnfD ph
    if ph' != ph && (ph'.isConst) then
      let g' ← newGoal (mkGood X A R Q ph' m); g.assign g'; return [g'.mvarId!]
    let cnd := ph.getArg! 1
    if let some (_, e, _) := cnd.eq? then
      let (fvs, g2) ← g.generalize #[{ expr := e, xName? := `sf, hName? := `hsf }]
      let gs ← g2.cases fvs[0]!
      return (gs.map (·.mvarId)).toList
  if let .letE _ _ v bd _ := m then return ← replace (bd.instantiate1 v)
  match fn with
  | .const c _ =>
    if c == ``FreeM.pure then
      let g' ← newGoal ((Q.beta #[ph, args[args.size - 1]!]).headBeta)
      g.assign g'; return [g'.mvarId!]
    if c == ``FreeM.impure then
      let call ← whnfR args[args.size - 2]!
      if call.isAppOf ``Except.error then g.assign (C ``True.intro); return []
      -- unfold `good` at the node: a conjunction / a ∀ the side handler splits
      let t ← whnfD (mkGood X A R Q ph m)
      -- an instruction-fetch read away from phase `fetch`: its RAM side is owed (a side goal
      -- `devAddr pa = false`), the device side is then vacuous
      if t.isAppOfArity ``And 2 && !isFetch then
        let c2 := t.getArg! 1
        if c2.isForall && !c2.bindingBody!.hasLooseBVars then
          let D := c2.bindingDomain!
          if D.isForall && !D.bindingBody!.hasLooseBVars then
            let hd := D.bindingDomain!
            let bE := D.bindingBody!
            if let (some (_, a, _), some (_, b, _)) := (hd.eq?, bE.eq?) then
              let bv ← withTransparency .all <| whnf b
              if bv.isConstOf ``Bool.true then
                let g1 ← newGoal (t.getArg! 0)
                let gd ← newGoal hd
                let hb ← mkExpectedTypeHint (← mkEqRefl (C ``Bool.true)) (← mkEq b (C ``Bool.true))
                let p2 := mkAppN (C ``Weak.SailCycleOrderGW.vacIF) #[a, b, c2.bindingBody!, gd, hb]
                g.assign (← mkAppM ``And.intro #[g1, p2])
                return [g1.mvarId!, gd.mvarId!]
      let g' ← newGoal t; g.assign g'
      return [g'.mvarId!]
    if c == ``FreeM.bind then
      let x ← norm args[args.size - 2]!
      let f := args[args.size - 1]!
      let α := (← whnf (← inferType f)).bindingDomain!
      if let .letE _ _ v bd _ := x then
        return ← replace (mkAppN fn (args.set! (args.size - 2) (bd.instantiate1 v)))
      if let .const xc _ := x.getAppFn then
        if xc == ``FreeM.pure then return ← replace (f.beta #[x.appArg!])
        if xc == ``FreeM.impure then
          let xa := x.getAppArgs
          let k := xa[xa.size - 1]!
          let k' ← withLocalDeclD `r (← inferType k).bindingDomain! fun r => do
            mkLambdaFVars #[r] (mkAppN fn (args.set! (args.size - 2) (k.beta #[r])))
          return ← replace (mkAppN x.getAppFn (xa.set! (xa.size - 1) k'))
        if xc == ``FreeM.bind then
          let xa := x.getAppArgs
          let y := xa[xa.size - 2]!; let gg := xa[xa.size - 1]!
          let γ := (← whnf (← inferType gg)).bindingDomain!
          let h ← withLocalDeclD `a γ fun a => do
            mkLambdaFVars #[a] (← mkAppM ``FreeM.bind #[gg.beta #[a], f])
          let inner ← mkAppM ``FreeM.bind #[y, h]
          let g' ← newGoal (mkGood X A R Q ph inner)
          g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gAssocF) #[γ, α, X, A, R, Q, ph, y, gg, f, g'])
          return [g'.mvarId!]
        -- a registered phase lemma (with its post)
        for L in ← Weak.SailCycleOrderFpReg.gRegFind xc do
          let s ← saveState
          let lc ← mkConstWithFreshMVarLevels L
          match ← gInst lc (← inferType lc) A R ph x with
          | some (pf, S, hs) =>
            let hk ← withLocalDeclD `p (C ``Weak.SailCycleOrderK.Ph) fun p => do
              withLocalDeclD `a α fun a => do
                withLocalDeclD `ha (S.beta #[p, a]) fun ha => do
                  mkForallFVars #[p, a, ha] (mkGood X A R Q p (f.beta #[a]))
            let gk ← newGoal hk
            g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gBindQF) #[α, X, A, R, S, Q, ph, x, f, pf, gk])
            let (fvs, gk') ← gk.mvarId!.introN 3
            return hs ++ [← substPost gk' fvs[2]!]
          | none => s.restore
        -- delegation: a registered footprint lemma (with its post)
        if isRboot then
          for L in ← Weak.SailCycleOrderFpReg.fpRegFind xc do
            let s ← saveState
            let lc ← mkConstWithFreshMVarLevels L
            match ← instAt lc (← inferType lc) x (C ``Bool.false) with
            | some (pf, b', S, hs) =>
              if b'.isConstOf ``Bool.false then
                let hk ← withLocalDeclD `a α fun a => do
                  withLocalDeclD `ha (S.beta #[a]) fun ha => do
                    mkForallFVars #[a, ha] (mkGood X A R Q ph (f.beta #[a]))
                let gk ← newGoal hk
                g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gFpF) #[α, X, A, S, Q, ph, x, f, pf, gk])
                return hs ++ [← introPost gk.mvarId!]
              s.restore
            | none => s.restore
      -- value mode: a bound `match`/`if` is walked under the continuation
      let xh := x.getAppFn.constName?
      let isBr ← match xh with
        | some n => do pure (n == ``ite || n == ``dite || (← isMatcher n))
        | none => pure false
      -- value mode: an `ExceptT` layer value (a `throw` the head normal form did not expose, a
      -- loop's early return) is walked, never delegated with an arbitrary result
      let isExc := (← whnfR α).isAppOf ``Except
      let isBr := isBr || (cx.gValue && isExc)
      -- delegation: a nested footprint walk (strict; relaxed at phase `fetch`)
      if isRboot && !(cx.gValue && isBr) then
        if let some pf ← tryFp cx (C ``Bool.false) α x then
          let S ← withLocalDeclD `a α fun a => mkLambdaFVars #[a] (C ``True)
          let hk ← withLocalDeclD `a α fun a => do
            withLocalDeclD `ha (C ``True) fun ha => do
              mkForallFVars #[a, ha] (mkGood X A R Q ph (f.beta #[a]))
          let gk ← newGoal hk
          g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gFpF) #[α, X, A, S, Q, ph, x, f, pf, gk])
          return [← introN' gk.mvarId! 2]
        if isFetch && isTrivA A then
          if let some pf ← tryFp cx (C ``Bool.true) α x then
            let S ← withLocalDeclD `a α fun a => mkLambdaFVars #[a] (C ``True)
            let hk ← withLocalDeclD `a α fun a => do
              withLocalDeclD `ha (C ``True) fun ha => do
                mkForallFVars #[a, ha] (mkGood X A R Q ph (f.beta #[a]))
            let gk ← newGoal hk
            g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gFpRF) #[α, X, S, Q, x, f, pf, gk])
            return [← introN' gk.mvarId! 2]
      -- continuation-passing
      let post ← withLocalDeclD `p (C ``Weak.SailCycleOrderK.Ph) fun p => do
        withLocalDeclD `a α fun a => do mkLambdaFVars #[p, a] (mkGood X A R Q p (f.beta #[a]))
      let g' ← newGoal (mkGood α A R post ph x)
      g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gBindCF) #[α, X, A, R, Q, ph, x, f, g'])
      return [g'.mvarId!]
    if c == ``ite || c == ``dite then
      let cnd := args[1]!; let inst := args[2]!; let a := args[3]!; let d := args[4]!
      if !cnd.hasFVar && !cnd.hasMVar then
        let dv ← withTransparency .all <| whnf (mkApp2 (C ``Decidable.decide) cnd inst)
        if dv.isConstOf ``Bool.true || dv.isConstOf ``Bool.false then
          let isT := dv.isConstOf ``Bool.true
          let br ← if c == ``ite then pure (if isT then a else d) else do
            let hEq ← mkEqRefl dv
            let pf ← if isT then mkAppOptM ``of_decide_eq_true #[cnd, inst, hEq]
              else mkAppOptM ``of_decide_eq_false #[cnd, inst, hEq]
            pure ((if isT then a else d).beta #[pf])
          -- the branch is the `if`'s value by computation
          let g' ← newGoal (mkGood X A R Q ph br)
          let eq ← mkEqRefl m
          discard <| pure eq
          g.assign g'
          return [g'.mvarId!]
      if c == ``ite then
        let ga ← newGoal (← mkArrow cnd (mkGood X A R Q ph a))
        let gb ← newGoal (← mkArrow (mkNot cnd) (mkGood X A R Q ph d))
        g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gIteF) #[X, A, R, Q, ph, cnd, inst, a, d, ga, gb])
        return [← introN' ga.mvarId! 1, ← introN' gb.mvarId! 1]
      let ta ← withLocalDeclD `h cnd fun h => do mkForallFVars #[h] (mkGood X A R Q ph (a.beta #[h]))
      let tb ← withLocalDeclD `h (mkNot cnd) fun h => do mkForallFVars #[h] (mkGood X A R Q ph (d.beta #[h]))
      let ga ← newGoal ta
      let gb ← newGoal tb
      g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gDiteF) #[X, A, R, Q, ph, cnd, inst, a, d, ga, gb])
      return [← introN' ga.mvarId! 1, ← introN' gb.mvarId! 1]
    if c == ``Eq.rec && args.size ≥ 6 then
      let motive := args[2]!
      let T? ← lambdaTelescope motive fun xs body => do
        let body ← Core.betaReduce body
        if xs.size == 2 && !body.hasAnyFVar (fun v => xs.contains (mkFVar v)) then pure (some body)
        else pure none
      if let some T := T? then
        let t := args[3]!; let h := args[5]!
        let extra := args.extract 6 args.size
        let F ← withLocalDeclD `z T fun z => do mkLambdaFVars #[z] (mkAppN z extra)
        let g' ← newGoal (mkGood X A R Q ph (F.beta #[t]))
        let lvl := match fn with | .const _ (u :: _) => u | _ => Level.zero
        g.assign (mkAppN (mkConst ``Weak.SailCycleOrderGW.gEqRecF [lvl])
          #[X, A, R, Q, ph, args[0]!, args[1]!, args[4]!, T, t, h, F, g'])
        return [g'.mvarId!]
    if ← isMatcher c then
      let some info ← getMatcherInfo? c | throwError "good_walk: no matcher info"
      let ds := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
      let g1 ← if m != m0 then do
          let g' ← newGoal (mkGood X A R Q ph m); g.assign g'; pure g'.mvarId!
        else pure g
      let ci ← getConstInfo c
      if ci.hasValue then
        let lvls := match m.getAppFn with | .const _ ls => ls | _ => []
        let v ← instantiateValueLevelParams ci lvls
        let m'' ← whnfCore (v.beta m.getAppArgs).headBeta
        let h := m''.getAppFn.constName?
        if h == some ``ite || h == some ``dite then
          let g' ← newGoal (mkGood X A R Q ph m''); g1.assign g'
          return [g'.mvarId!]
      if let some d := ds.find? (·.isFVar) then
        let ty ← whnfD (← inferType d)
        let lit := match ty.getAppFn.constName? with
          | some n => [``BitVec, ``Fin, ``Nat, ``Int].contains n | none => false
        if !lit then
          let gs ← g1.cases d.fvarId!
          return (gs.map (·.mvarId)).toList
      return ← Split.splitMatch g1 m
    -- a registered phase lemma at the head
    for L in ← Weak.SailCycleOrderFpReg.gRegFind c do
      let s ← saveState
      let lc ← mkConstWithFreshMVarLevels L
      match ← gInst lc (← inferType lc) A R ph m with
      | some (pf, S, hs) =>
        let hQ ← withLocalDeclD `p (C ``Weak.SailCycleOrderK.Ph) fun p => do
          withLocalDeclD `a X fun a => do
            withLocalDeclD `ha (S.beta #[p, a]) fun ha => do
              mkForallFVars #[p, a, ha] ((Q.beta #[p, a]).headBeta)
        let gQ ← newGoal hQ
        g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gHeadQF) #[X, A, R, S, Q, ph, m, pf, gQ])
        return hs ++ [← introN' gQ.mvarId! 3]
      | none => s.restore
    -- value mode: an `ExceptT` layer value is never delegated with an arbitrary result away from
    -- phase `fetch` (at `fetch` every post the walk meets holds of any value)
    let headExc := cx.gValue && (← whnfR X).isAppOf ``Except
    -- delegation at the head: a footprint walk with a trivial post (relaxed at phase `fetch`)
    if isRboot && isFetch && isTrivA A then
      if let some pf ← tryFp cx (C ``Bool.true) X m then
        let S ← withLocalDeclD `a X fun a => mkLambdaFVars #[a] (C ``True)
        let hQ ← withLocalDeclD `a X fun a => do
          withLocalDeclD `ha (C ``True) fun ha => do
            mkForallFVars #[a, ha] ((Q.beta #[C ``Weak.SailCycleOrderK.Ph.fetch, a]).headBeta)
        let gQ ← newGoal hQ
        g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gFpRHeadF) #[X, S, Q, m, pf, gQ])
        return [← introN' gQ.mvarId! 2]
    if isRboot && !headExc then
      if let some pf ← tryFp cx (C ``Bool.false) X m then
        let S ← withLocalDeclD `a X fun a => mkLambdaFVars #[a] (C ``True)
        let hQ ← withLocalDeclD `a X fun a => do
          withLocalDeclD `ha (C ``True) fun ha => do mkForallFVars #[a, ha] ((Q.beta #[ph, a]).headBeta)
        let gQ ← newGoal hQ
        g.assign (mkAppN (C ``Weak.SailCycleOrderGW.gFpHeadF) #[X, A, S, Q, ph, m, pf, gQ])
        return [← introN' gQ.mvarId! 2]
    -- unfold (delta, or the equation lemma of a recursive definition)
    let isRec ← isRecDef c
    let delta? ← if isRec then pure none else unfoldDefinition? m
    if let some m' := delta? then return ← replace m'
    let some eqn ← getUnfoldEqnFor? c (nonRec := true) |
      let m' ← withTransparency .instances <| whnf m
      if m' != m then return ← replace m'
      throwError "good_walk: cannot unfold {c}{indentExpr m}"
    let eqc ← mkConstWithFreshMVarLevels eqn
    let (eargs, _, ety) ← forallMetaTelescope (← inferType eqc)
    let some (_, lhs, rhs) := ety.eq? | throwError "good_walk: bad equation {eqn}"
    unless ← isDefEq lhs m do throwError "good_walk: equation {eqn} does not match{indentExpr m}"
    let pf ← instantiateMVars (mkAppN eqc eargs)
    let rhs ← instantiateMVars rhs
    let g' ← newGoal (mkGood X A R Q ph rhs)
    let eq ← mkCongrArg (mkAppN (C ``Weak.SailCycleOrderK.good) #[X, A, R, Q, ph]) pf
    g.assign (← mkEqMPR eq g')
    return [g'.mvarId!]
  | _ => throwError "good_walk: stuck{indentExpr m}"

/-- Close a side goal by a local hypothesis `h : ∀ xs, P₁ → … → G`, its equational premises by
`rfl` and the others by an assumption (the posts the walk carries: `ha _ rfl`, `ha hsf`). -/
def hypClose (g : MVarId) : MetaM Bool := g.withContext do
  let gt ← instantiateMVars (← g.getType)
  let lctx ← getLCtx
  for ld in lctx.decls.toList.reverse do
    let some ld := ld | continue
    if ld.isImplementationDetail then continue
    let s ← saveState
    try
      let (args, _, body) ← forallMetaTelescopeReducing ld.type
      if args.isEmpty then s.restore; continue
      unless ← isDefEq body gt do s.restore; continue
      let mut ok := true
      for a in args do
        let a ← instantiateMVars a
        unless a.isMVar do continue
        let t ← instantiateMVars (← inferType a)
        unless ← isProp t do continue
        let mut done := false
        if let some (_, l, r) := t.eq? then
          if ← isDefEq l r then
            a.mvarId!.assign (← mkEqRefl l); done := true
        unless done do
          for ld' in lctx do
            if ld'.isImplementationDetail then continue
            if ← isDefEq ld'.type t then
              a.mvarId!.assign ld'.toExpr; done := true; break
        unless done do ok := false; break
      let pf ← instantiateMVars (mkAppN ld.toExpr args)
      if ok && !pf.hasMVar then
        g.assign pf; return true
      s.restore
    catch _ => s.restore
  return false

/-- The loop: `good` goals by `gstep`, footprint goals by the footprint walker, side goals by its
side handler. -/
partial def gloop (cx : Ctx) (start : List MVarId) : TacticM (List MVarId) := do
  let mut stack := start
  let mut left : List MVarId := []
  while true do
    match stack with
    | [] => break
    | g :: rest =>
      if ← g.isAssigned then stack := rest; continue
      let ty ← instantiateMVars (← g.getType)
      if let some (X, A, R, Q, ph, m) ← goodView? ty then
        let gs ← gstep cx g X A R Q ph m
        stack := gs ++ rest
      else if (← fpView? ty).isSome then
        let l ← loop cx [g]
        left := left ++ l; stack := rest
      else
        let gs ← side g
        if gs == [g] then
          if ← hypClose g then stack := rest
          else left := left ++ [g]; stack := rest
        else stack := gs ++ rest
  return left

end GWalk

/-- Run the phase-aware walker on the main goal. -/
def GWalk.run (gValue : Bool) (gDbg : Bool := false) : Lean.Elab.Tactic.TacticM Unit := do
  let jps ← IO.mkRef {}
  let spineJps ← IO.mkRef {}
  let memo ← IO.mkRef {}
  let tab ← IO.mkRef {}
  let steps ← IO.mkRef 0
  let gsteps ← IO.mkRef 0
  let cx : Weak.SailCycleOrderFp.Walk.Ctx :=
    { jps, spineJps, memo, stats := false, tab, steps, limit := 10000000, gValue, gsteps, gDbg }
  let left ← GWalk.gloop cx [← Lean.Elab.Tactic.getMainGoal]
  Lean.Elab.Tactic.replaceMainGoal left

/-- **The phase-aware walker** (header). -/
elab "good_walk" : tactic => GWalk.run false

/-- The phase-aware walker in VALUE MODE: every bound `match`/`if` is walked under the
continuation (no footprint delegation), so the branches see the matched values. -/
elab "good_walk_v" : tactic => GWalk.run true

/-- `good_walk_v` logging every step (development aid). -/
elab "good_walk_dbg" : tactic => GWalk.run true true

end SailCycleOrderGW
end Weak
