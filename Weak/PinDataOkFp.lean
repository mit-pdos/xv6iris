/-
Weak: **`dataOkR` (4c) — the "no cause-register write" footprint `yfB` and its walker**
(`PROGRESS-dataOk.md`).  Lean-only (no Rocq source).

`PinDataOkFp.yfB b P m` is `PinFetchPaFp.xfB` (itself w1's `PinCycRunFp.pfB`) with the PROTECTED set
replaced by the trap handler's cause registers `scause`/`mcause` (`yfProt`): a tree satisfying
`yfB` writes neither, so it passes no stop of the filtered cycle predicate `PinDataOk.cyDB`.  The
walker `yf_walk` is `xf_walk` copied VERBATIM but for the predicate's constant names and the
protected set; its registry is `@[yf_reg]` (`Weak/PinDataOkReg.lean`).

Every helper is `Weak.PinDataOkFp.*`.
-/
import Weak.SailCycleOrderK
import Weak.WeakEvLang
import Weak.PinDataOkReg
import MachCSL.WpPmpDefs

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOkFp
open SailCycleOrderK

/-- The read-kind side condition of a memory read: anything when instruction fetches are allowed
(`b = true`, the relaxed footprint valid at phase `fetch`), else not an instruction fetch. -/
def ifOk (b : Bool) (k : AK) : Prop :=
  match b with
  | true => True
  | false => akIfetch k = false

/-- The PROTECTED registers: the trap handler's cause registers. -/
def yfProt (r : Register) : Bool :=
  decide (r = .scause) || decide (r = .mcause)

/-- An unprotected register. -/
def yfRegOk (r : Register) : Bool := !yfProt r

/-- The register-write side condition: an `Rboot`-admitted value, to an unprotected register. -/
abbrev yfW (r : Register) (v : RegisterType r) : Prop := Rboot r v ∧ yfRegOk r = true

/-- **The footprint** (header); `b = true` allows instruction-fetch reads. -/
def yfB {X : Type} (b : Bool) (P : X → Prop) : SailM X → Prop
  | .pure x => P x
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .memRead _ _ req, k => ifOk b req.access_kind ∧ ∀ v, yfB b P (k v)
    | .barrier b', k => b' ≠ .Barrier_RISCV_i ∧ yfB b P (k ())
    | .instrAnnounce .., _ => False
    | .regRead r, k => ∀ v, Rboot r v → yfB b P (k v)
    | .regWrite r v, k => yfW r v ∧ ∀ u, yfB b P (k u)
    | .memWrite .., k => ∀ v, yfB b P (k v)
    | .branchAnnounce .., k => ∀ v, yfB b P (k v)
    | .cacheOp _, k => ∀ v, yfB b P (k v)
    | .tlbi _, k => ∀ v, yfB b P (k v)
    | .takeException _, k => ∀ v, yfB b P (k v)
    | .returnException _, k => ∀ v, yfB b P (k v)
    | .translationStart _, k => ∀ v, yfB b P (k v)
    | .translationEnd _, k => ∀ v, yfB b P (k v)
    | .cycleCount, k => ∀ v, yfB b P (k v)
    | .getCycleCount, k => ∀ v, yfB b P (k v)
    | .message _, k => ∀ v, yfB b P (k v)
    | .choose _, k => ∀ v, yfB b P (k v)
    | .readRam .., k => ∀ v, yfB b P (k v)
    | .writeRam .., k => ∀ v, yfB b P (k v)

/-- The strict footprint (no instruction fetch). -/
abbrev yf {X : Type} (P : X → Prop) (m : SailM X) : Prop := yfB false P m

/-- The strict footprint with the trivial post. -/
abbrev yfT {X : Type} (m : SailM X) : Prop := yf (fun _ => True) m

/-- The generic induction over a tree for `yfB` (every combinator below is an instance). -/
theorem yfBInd {X Y : Type} (b b' : Bool) (P : X → Prop) (P' : Y → Prop)
    (hb : b = false ∨ b' = true)
    (F : SailM X → SailM Y) (R : SailM X → Prop)
    (hpure : ∀ x, P x → R (.pure x) → yfB b' P' (F (.pure x)))
    (herr : ∀ e k, R (.impure (.error e) k) → yfB b' P' (F (.impure (.error e) k)))
    (hok : ∀ o k, (∀ r, R (k r) → yfB b P (k r) → yfB b' P' (F (k r))) →
      R (.impure (.ok o) k) → yfB b P (.impure (.ok o) k) →
      yfB b' P' (F (.impure (.ok o) k))) :
    ∀ m, R m → yfB b P m → yfB b' P' (F m) := by
  intro m
  induction m with
  | pure x => intro hr h; exact hpure x h hr
  | impure call k ih =>
    intro hr h
    cases call with
    | error e => exact herr e k hr
    | ok o => exact hok o k (fun r hr' h' => ih r hr' h') hr h

theorem ifOkMono (b b' : Bool) (hb : b = false ∨ b' = true) (k : AK) : ifOk b k → ifOk b' k := by
  rcases hb with rfl | rfl
  · cases b' <;> simp [ifOk]
  · intro _; exact trivial

theorem yfBMono {X : Type} (b b' : Bool) (hb : b = false ∨ b' = true) (P P' : X → Prop)
    (hP : ∀ x, P x → P' x) : ∀ m : SailM X, yfB b P m → yfB b' P' m := by
  intro m
  induction m with
  | pure y => exact hP y
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case memRead => exact ⟨ifOkMono b b' hb _ hm.1, fun v => ih v (hm.2 v)⟩
      case barrier => exact ⟨hm.1, ih _ hm.2⟩
      case instrAnnounce => exact hm.elim
      case regRead => exact fun v hv => ih v (hm v hv)
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u)⟩
      all_goals exact fun v => ih v (hm v)

theorem yfMono {X : Type} (P P' : X → Prop) (hP : ∀ x, P x → P' x) :
    ∀ m : SailM X, yf P m → yf P' m := yfBMono false false (Or.inl rfl) P P' hP

/-- The relaxed footprint follows from the strict one. -/
theorem yfRelax {X : Type} (P : X → Prop) (m : SailM X) (h : yf P m) : yfB true P m :=
  yfBMono false true (Or.inl rfl) P P (fun _ h => h) m h

theorem yfBBindQ {X Y : Type} (b : Bool) (Q : X → Prop) (P : Y → Prop) (m : SailM X)
    (f : X → SailM Y) : yfB b Q m → (∀ x, Q x → yfB b P (f x)) → yfB b P (m >>= f) := by
  induction m with
  | pure y => intro hm hf; exact hf y hm
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show yfB b P (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case memRead => exact ⟨hm.1, fun v => ih v (hm.2 v) hf⟩
      case barrier => exact ⟨hm.1, ih _ hm.2 hf⟩
      case instrAnnounce => exact hm.elim
      case regRead => exact fun v hv => ih v (hm v hv) hf
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u) hf⟩
      all_goals exact fun v => ih v (hm v) hf

theorem yfBindQ {X Y : Type} (Q : X → Prop) (P : Y → Prop) (m : SailM X) (f : X → SailM Y) :
    yf Q m → (∀ x, Q x → yf P (f x)) → yf P (m >>= f) := yfBBindQ false Q P m f

theorem yfBind {X Y : Type} (P : Y → Prop) (m : SailM X) (f : X → SailM Y) :
    yfT m → (∀ x, yf P (f x)) → yf P (m >>= f) :=
  fun hm hf => yfBindQ _ P m f hm (fun x _ => hf x)

/-! ## Combinators (generic in `b`) -/

@[yf_reg] theorem yfTryCatch {X : Type} (b : Bool) (P : X → Prop) (m : SailM X)
    (h : Sail.Error exception → SailM X) :
    yfB b P m → (∀ e, yfB b P (h e)) → yfB b P (PreSail.tryCatchAll m h) := by
  induction m with
  | pure y => intro hm _; exact hm
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e => exact hh e
    | ok o =>
      show yfB b P (FreeM.impure (.ok o) (fun r => PreSail.tryCatchAll (k r) h))
      cases o
      case memRead => exact ⟨hm.1, fun v => ih v (hm.2 v) hh⟩
      case barrier => exact ⟨hm.1, ih _ hm.2 hh⟩
      case instrAnnounce => exact hm.elim
      case regRead => exact fun v hv => ih v (hm v hv) hh
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u) hh⟩
      all_goals exact fun v => ih v (hm v) hh

@[yf_reg] theorem yfSailTryCatch {X : Type} (b : Bool) (P : X → Prop) (m : SailM X)
    (h : exception → SailM X) :
    yfB b P m → (∀ e, yfB b P (h e)) → yfB b P (PreSail.sailTryCatch m h) := by
  induction m with
  | pure y => intro hm _; exact hm
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e =>
      cases e
      case User u => exact hh u
      all_goals trivial
    | ok o =>
      show yfB b P (FreeM.impure (.ok o) (fun r => PreSail.sailTryCatch (k r) h))
      cases o
      case memRead => exact ⟨hm.1, fun v => ih v (hm.2 v) hh⟩
      case barrier => exact ⟨hm.1, ih _ hm.2 hh⟩
      case instrAnnounce => exact hm.elim
      case regRead => exact fun v hv => ih v (hm v hv) hh
      case regWrite => exact ⟨hm.1, fun u => ih u (hm.2 u) hh⟩
      all_goals exact fun v => ih v (hm v) hh

theorem yfBRBind {R X Y : Type} (b : Bool) (m : SailME R X) (f : X → SailME R Y) :
    yfB b (fun _ => True) (ExceptT.run m) → (∀ x, yfB b (fun _ => True) (ExceptT.run (f x))) →
      yfB b (fun _ => True) (ExceptT.run (m >>= f)) := by
  intro hm hf
  rw [ExceptT.run_bind]
  refine yfBBindQ b _ _ _ _ hm (fun e _ => ?_)
  cases e with
  | ok x => exact hf x
  | error e => trivial

@[yf_reg] theorem yfRUntilFuel {R α : Type} (b : Bool) (cond : α → SailME R Bool)
    (f : α → SailME R α)
    (hc : ∀ x, yfB b (fun _ => True) (ExceptT.run (cond x)))
    (hf : ∀ x, yfB b (fun _ => True) (ExceptT.run (f x))) :
    ∀ (n : Nat) (x : α), yfB b (fun _ => True) (ExceptT.run (untilFuelM.go cond f x n)) := by
  intro n
  induction n with
  | zero => intro x; trivial
  | succ n ih =>
    intro x
    simp only [untilFuelM.go]
    refine yfBRBind b _ _ (hf x) (fun y => ?_)
    refine yfBRBind b _ _ (hc y) (fun c => ?_)
    split
    · trivial
    · exact ih y

@[yf_reg] theorem yfForeach' {β : Type} (b : Bool) (range : IntRange) (hstep : range.step > 0)
    (f : (i : Int) → i ∈ range → β → SailM (ForInStep β))
    (hf : ∀ i h c, yfB b (fun _ => True) (f i h c)) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (c : β),
      yfB b (fun _ => True) (IntRange.forIn'.loop range f c i hs) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (c : β),
      (range.stop - i + 1).toNat = n →
      yfB b (fun _ => True) (IntRange.forIn'.loop range f c i hs) from
    fun i hs c => H _ i hs c rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hs c hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine yfBBindQ b _ _ _ _ (hf i h c) (fun r _ => ?_)
      cases r with
      | done c' => trivial
      | yield c' =>
        have hle : i ≤ range.stop := by
          simp only [Membership.mem, hstep, ite_true] at h
          exact h.1.2
        exact ih _ (by omega) _ _ c' rfl
    · simp only [dif_neg h]
      trivial

@[yf_reg] theorem yfRForInLoop {R β : Type} (b : Bool) (range : IntRange) (hstep : range.step > 0)
    (f : (i : Int) → i ∈ range → β → SailME R (ForInStep β))
    (hf : ∀ i h c, yfB b (fun _ => True) (ExceptT.run (f i h c))) :
    ∀ (i : Int) (hs : (i - range.start) % range.step = 0) (c : β),
      yfB b (fun _ => True) (ExceptT.run (IntRange.forIn'.loop range f c i hs)) := by
  suffices H : ∀ (n : Nat) (i : Int) (hs : (i - range.start) % range.step = 0) (c : β),
      (range.stop - i + 1).toNat = n →
      yfB b (fun _ => True) (ExceptT.run (IntRange.forIn'.loop range f c i hs)) from
    fun i hs c => H _ i hs c rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i hs c hn
    rw [IntRange.loop_unfold]
    by_cases h : i ∈ range
    · simp only [dif_pos h]
      refine yfBRBind b _ _ (hf i h c) (fun r => ?_)
      cases r with
      | done c' => trivial
      | yield c' =>
        have hle : i ≤ range.stop := by
          simp only [Membership.mem, hstep, ite_true] at h
          exact h.1.2
        exact ih _ (by omega) _ _ c' rfl
    · simp only [dif_neg h]
      trivial

/-! ## The walker's lemmas (on `FreeM.bind`, the normal form; generic in `b`) -/

theorem yfBindF {X Y : Type} (b : Bool) (P : Y → Prop) (m : SailM X) (f : X → SailM Y)
    (hm : yfB b (fun _ => True) m) (hf : ∀ x, yfB b P (f x)) : yfB b P (FreeM.bind m f) :=
  yfBBindQ b _ P m f hm (fun x _ => hf x)

theorem yfBindQF {X Y : Type} (b : Bool) (Q : X → Prop) (P : Y → Prop) (m : SailM X)
    (f : X → SailM Y) (hm : yfB b Q m) (hf : ∀ x, Q x → yfB b P (f x)) : yfB b P (FreeM.bind m f) :=
  yfBBindQ b Q P m f hm hf

theorem yfBindCF {X Y : Type} (b : Bool) (P : Y → Prop) (m : SailM X) (f : X → SailM Y)
    (h : yfB b (fun x => yfB b P (f x)) m) : yfB b P (FreeM.bind m f) :=
  yfBBindQ b _ P m f h (fun _ h => h)

theorem yfAssocF {X Y Z : Type} (b : Bool) (P : Z → Prop) (m : SailM X) (g : X → SailM Y)
    (f : Y → SailM Z) (h : yfB b P (FreeM.bind m (fun x => FreeM.bind (g x) f))) :
    yfB b P (FreeM.bind (FreeM.bind m g) f) := by
  rw [FreeMLemmas.bind_assoc]; exact h

theorem yfIteF {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a d : SailM X)
    (ha : c → yfB b P a) (hd : ¬ c → yfB b P d) : yfB b P (ite c a d) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hd h

theorem yfIteT {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a d : SailM X)
    (h : decide c = true) (ha : yfB b P a) : yfB b P (ite c a d) := by
  rw [if_pos (of_decide_eq_true h)]; exact ha

theorem yfIteE {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a d : SailM X)
    (h : decide c = false) (hd : yfB b P d) : yfB b P (ite c a d) := by
  rw [if_neg (of_decide_eq_false h)]; exact hd

theorem yfDiteT {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a : c → SailM X)
    (d : ¬ c → SailM X) (h : decide c = true) (ha : yfB b P (a (of_decide_eq_true h))) :
    yfB b P (dite c a d) := by
  rw [dif_pos (of_decide_eq_true h)]; exact ha

theorem yfDiteE {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a : c → SailM X)
    (d : ¬ c → SailM X) (h : decide c = false) (hd : yfB b P (d (of_decide_eq_false h))) :
    yfB b P (dite c a d) := by
  rw [dif_neg (of_decide_eq_false h)]; exact hd

theorem yfDiteF {X : Type} (b : Bool) (P : X → Prop) (c : Prop) [Decidable c] (a : c → SailM X)
    (d : ¬ c → SailM X) (ha : ∀ h, yfB b P (a h)) (hd : ∀ h, yfB b P (d h)) :
    yfB b P (dite c a d) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hd h

theorem yfMonoF {X : Type} (b : Bool) (P P' : X → Prop) (m : SailM X) (h : yfB b P m)
    (hP : ∀ x, P x → P' x) : yfB b P' m := yfBMono b b (by cases b <;> simp) P P' hP m h

/-- A strict lemma used at a relaxed goal. -/
theorem yfRelaxF {X : Type} (P P' : X → Prop) (m : SailM X) (h : yf P m)
    (hP : ∀ x, P x → P' x) : yfB true P' m := yfBMono false true (Or.inl rfl) P P' hP m h

/-- A join point (`have __do_jp := v; body`), kept ABSTRACT: its body is walked once. -/
theorem yfJpF {A Y : Type} (b : Bool) (P : Y → Prop) (v : A → SailM Y)
    (body : (A → SailM Y) → SailM Y)
    (hv : ∀ a, yfB b P (v a)) (hb : ∀ jp : A → SailM Y, (∀ a, yfB b P (jp a)) → yfB b P (body jp)) :
    yfB b P (body v) := hb v hv

/-- The decoder's clause spine `match (← clause) with | some r => pure r | none => rest`: the
clause under the option post, `rest` ONCE. -/
def optPost {X : Type} (P : X → Prop) : Option X → Prop
  | some x => P x
  | none => True

theorem yfSpineF {X : Type} (b : Bool) (P : X → Prop) (m : SailM (Option X))
    (f : Option X → SailM X) (hf : ∀ r, f (some r) = FreeM.pure r)
    (hm : yfB b (optPost P) m) (hn : yfB b P (f none)) : yfB b P (FreeM.bind m f) := by
  refine yfBBindQ b _ _ _ _ hm (fun o ho => ?_)
  cases o with
  | none => exact hn
  | some r => rw [hf]; exact ho

/-- A clause-spine join point (`have __do_jp := fun o => match o with | some r => pure r | none =>
rest; body`): `rest` once, each call `jp o` owes `optPost P o`. -/
theorem yfJpSpineF {T : Type} (b : Bool) (P : T → Prop) (v : Option T → SailM T)
    (body : (Option T → SailM T) → SailM T) (hf : ∀ r, v (some r) = FreeM.pure r)
    (hn : yfB b P (v none))
    (hb : ∀ jp : Option T → SailM T, (∀ o, optPost P o → yfB b P (jp o)) → yfB b P (body jp)) :
    yfB b P (body v) := by
  refine hb v (fun o ho => ?_)
  cases o with
  | none => exact hn
  | some r => rw [hf]; exact ho

/-- A cast along an equation with a CONSTANT motive (a literal match's alternative): the
footprint of the uncast term. -/
theorem yfEqRecF.{u} {X : Type} (b : Bool) (P : X → Prop) {α : Sort u} {a a' : α} {T : Type}
    (t : T) (h : a = a') (F : T → SailM X)
    (ht : yfB b P (F t)) : yfB b P (F (@Eq.rec α a (fun _ _ => T) t a' h)) := by
  cases h; exact ht

/-- A model internal error never returns: post `False`. -/
@[yf_reg] theorem yfInternalError {X : Type} (f : String) (l : Int) (m : String) :
    yf (fun _ => False) (internal_error f l m : SailM X) := by
  unfold internal_error; exact trivial

/-! ## The walker (a MetaM loop building the proof term; `MachCSL.UDecodeWalk`'s design) -/

namespace Walk
open Lean Meta Elab Tactic

/-- Definitions unfolded while normalizing a tree's head (the monad plumbing). -/
def plumbing : List Name :=
  [``ExceptT.run, ``ExceptT.mk, ``ExceptT.bind, ``ExceptT.bindCont, ``ExceptT.pure, ``ExceptT.lift,
   ``ExceptT.map, ``ExceptT.tryCatch, ``liftM, ``PreSail.PreSailME.run, ``PreSail.PreSailME.throw,
   ``SailME.run, ``SailME.throw, ``PreSail.readReg, ``PreSail.writeReg, ``PreSail.emit, ``PreSail.fail,
   ``PreSail.sailThrow, ``Function.comp, ``letFun, ``ExceptT.map_error, ``PreSail.sailTryCatchE]

/-- Class projections reduced at instance transparency. -/
def classProj : List Name :=
  [``Bind.bind, ``Pure.pure, ``Functor.map, ``Functor.mapConst, ``SeqRight.seqRight,
   ``SeqLeft.seqLeft, ``Seq.seq, ``MonadLift.monadLift, ``MonadLiftT.monadLift, ``monadLift,
   ``MonadExceptOf.throw, ``MonadExcept.throw, ``throwThe, ``MonadExceptOf.tryCatch,
   ``MonadExcept.tryCatch, ``tryCatchThe, ``ForIn.forIn, ``ForIn'.forIn', ``Monad.toBind,
   ``Monad.toApplicative, ``Applicative.toPure, ``Applicative.toFunctor]

/-- Is `c` a recursive definition (structural or well-founded)? -/
def isRecDef (c : Name) : MetaM Bool := do
  let env ← getEnv
  if env.contains (c ++ `_unary) || env.contains (c ++ `_mutual) then return true
  match env.find? c with
  | some (.defnInfo d) =>
    return (d.value.find? (fun e => e.isConstOf ``WellFounded.fix ||
      (match e.constName? with | some n => n == c ++ `brecOn | none => false))).isSome
  | _ => return false

/-- Normalize the head of a tree: unfold the monad plumbing and instance projections, reduce
matchers at constructor discriminants, beta. -/
partial def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let e := e.consumeMData.headBeta
  if e.getAppFn.isMData || e.getAppFn.isLambda then
    let f := e.getAppFn.consumeMData
    return ← norm (mkAppN f e.getAppArgs)
  match e.getAppFn with
  | .const c _ =>
    if c == ``FreeM.bind || c == ``FreeM.pure || c == ``FreeM.impure || c == ``ite ||
      c == ``dite then return e
    if plumbing.contains c then
      match ← unfoldDefinition? e with
      | some e' => return ← norm e'
      | none => return e
    if classProj.contains c || (← isProjectionFn c) then
      let e' ← withTransparency .instances <| whnf e
      if e' != e then return ← norm e'
      return e
    if ← isMatcher c then
      match ← Meta.reduceMatcher? e with
      | .reduced e' => return ← norm e'
      | _ => return e
    return e
  | .proj .. =>
    let e' ← withTransparency .instances <| whnf e
    if e' != e then norm e' else return e
  | _ => return e

/-- Make `yfB b P m`. -/
def mkFp (b X P m : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``Weak.PinDataOkFp.yfB) X b P m

/-- Destructure a footprint goal type (unfolding `yf`/`yfT`): `(b, X, P, m)`. -/
def yfView? (t : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let mut t := t.consumeMData
  for _ in [0:3] do
    if t.isAppOf ``Weak.PinDataOkFp.yfT || t.isAppOf ``Weak.PinDataOkFp.yf then
      t ← whnfR t
  if t.isAppOfArity ``Weak.PinDataOkFp.yfB 4 then
    return some (t.getArg! 1, t.getArg! 0, t.getArg! 2, t.getArg! 3)
  return none

/-- A fresh goal of type `ty`. -/
def newGoal (ty : Lean.Expr) : MetaM Lean.Expr := mkFreshExprSyntheticOpaqueMVar ty

def isTrivPost (post : Lean.Expr) : Bool :=
  post.isLambda && post.bindingBody!.consumeMData.isConstOf ``True

def trueE : Lean.Expr := mkConst ``Bool.true
def falseE : Lean.Expr := mkConst ``Bool.false

/-- Turn the unassigned argument metavariables of a lemma instance into proper goals. -/
def argGoals (args : Array Lean.Expr) : MetaM (List MVarId) := do
  let mut hs := []
  for a in args do
    let a ← instantiateMVars a
    if a.isMVar then
      let g ← mkFreshExprSyntheticOpaqueMVar (← inferType a)
      a.mvarId!.assign g
      hs := hs ++ [g.mvarId!]
  return hs

/-- Introduce `n` binders. -/
def introN' (g : MVarId) (n : Nat) : MetaM MVarId := do
  let (_, g) ← g.introN n
  return g

/-- Instantiate the footprint lemma or hypothesis `yf₀ : ∀ xs, yfB b' S m'` at the tree `m`
(same head, reducible unification): the proof, its `b'`, its post, its leftover hypotheses. -/
def instAt (yf₀ ty₀ m : Lean.Expr) (b : Lean.Expr := mkConst ``Bool.false) :
    MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr × List MVarId)) := do
  let (args, _, ty) ← forallMetaTelescope ty₀
  let some (b', _, S, m') ← yfView? ty |
    return none
  let m' := if m'.isAppOf ``ExceptT.run then m'.appArg! else m'
  unless m'.getAppFn == m.getAppFn || m'.getAppFn.constName? == m.getAppFn.constName? do
    return none
  unless ← withTransparency .instances (isDefEq m' m) do return none
  -- a `b`-generic lemma: instantiate it at the goal's `b`
  if (← instantiateMVars b').isMVar then discard <| isDefEq b' b
  let hs ← argGoals args
  -- a CLOSED proposition among the hypotheses is decided now: a false one rejects the lemma
  let mut keep := []
  for h in hs do
    let t ← instantiateMVars (← h.getType)
    if (← isProp t) && !t.isForall && !t.hasFVar && !t.hasMVar then
      -- `some true`: decided true; `some false`: decided false; `none`: undecidable here
      let r? : Option Bool ← try
          let yf ← mkDecideProof t
          let r ← withTransparency .all <| whnf (← mkAppOptM ``Decidable.decide #[t, none])
          if r.isConstOf ``Bool.true then h.assign yf; pure (some true)
          else if r.isConstOf ``Bool.false then pure (some false) else pure none
        catch _ => pure none
      -- `a ≠ a`: false
      let tw ← whnfR t
      let neSame ← match tw.not? with
        | some e => match e.eq? with
          | some (_, a, b) => isDefEq a b
          | none => pure false
        | none => match tw.ne? with
          | some (_, a, b) => isDefEq a b
          | none => pure false
      if neSame then return none
      match r? with
      | some true => pure ()
      | some false => return none
      | none => keep := keep ++ [h]
    else keep := keep ++ [h]
  return some (← instantiateMVars (mkAppN yf₀ args), ← instantiateMVars b', ← instantiateMVars S, keep)

/-- Close `yfB b P m` from an instance `yf : yfB b' S m`: directly, through `yfMonoF` (posts), or
through `yfRelaxF` (a strict fact at a relaxed goal). -/
def closeBy (g : MVarId) (b X P m yf b' S : Lean.Expr) (hs : List MVarId) :
    MetaM (Option (List MVarId)) := do
  let sameB ← isDefEq b b'
  if sameB && ((isTrivPost S && isTrivPost P) || (← withReducible (isDefEq S P))) then
    g.assign yf; return some hs
  -- a post `False` (a call that never returns): the post obligation is vacuous
  if S.isLambda && S.bindingBody!.consumeMData.isConstOf ``False then
    let hPv ← withLocalDeclD `a X fun a => do
      withLocalDeclD `ha (mkConst ``False) fun ha => do
        mkLambdaFVars #[a, ha] (← mkFalseElim (P.beta #[a]) ha)
    if sameB then
      g.assign (mkAppN (mkConst ``Weak.PinDataOkFp.yfMonoF) #[X, b, S, P, m, yf, hPv])
      return some hs
    else if b'.isConstOf ``Bool.false && b.isConstOf ``Bool.true then
      g.assign (mkAppN (mkConst ``Weak.PinDataOkFp.yfRelaxF) #[X, S, P, m, yf, hPv])
      return some hs
  let hP ← withLocalDeclD `a X fun a => do
    withLocalDeclD `ha (S.beta #[a]) fun ha => do mkForallFVars #[a, ha] (P.beta #[a])
  let gP ← newGoal hP
  if sameB then
    g.assign (mkAppN (mkConst ``Weak.PinDataOkFp.yfMonoF) #[X, b, S, P, m, yf, gP])
  else if b'.isConstOf ``Bool.false && b.isConstOf ``Bool.true then
    g.assign (mkAppN (mkConst ``Weak.PinDataOkFp.yfRelaxF) #[X, S, P, m, yf, gP])
  else return none
  return some (hs ++ [← introN' gP.mvarId! 2])

/-- Close `yfB b P m` from a local hypothesis (an induction hypothesis). -/
def useHyp (g : MVarId) (b X P m : Lean.Expr) : MetaM (Option (List MVarId)) := g.withContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let s ← saveState
    match ← instAt ld.toExpr (← instantiateMVars ld.type) m b with
    | some (yf, b', S, hs) =>
      if let some gs ← closeBy g b X P m yf b' S hs then return some gs
      s.restore
    | none => s.restore
  return none

/-- A post that is a continuation (`fun a => yfB … (f a)`, or the clause-spine option post), as
opposed to a value post. -/
def isCpsPost (P : Lean.Expr) : Bool :=
  P.isLambda && (P.bindingBody!.consumeMData.isAppOf ``Weak.PinDataOkFp.yfB ||
    P.bindingBody!.consumeMData.isAppOf ``Weak.PinDataOkFp.optPost)

/-- Close `yfB b P m` by a registered lemma of the head `c`. -/
def useReg (g : MVarId) (c : Name) (b X P m : Lean.Expr) : MetaM (Option (List MVarId)) := do
  for L in ← Weak.PinDataOkReg.yfRegFind c do
    let s ← saveState
    let lc ← mkConstWithFreshMVarLevels L
    match ← instAt lc (← inferType lc) m b with
    | some (yf, b', S, hs) =>
      -- a trivial-post lemma is useless for a value post (the walk unfolds and checks leaves)
      if isTrivPost S && !isTrivPost P && !isCpsPost P then
        s.restore; continue
      if let some gs ← closeBy g b X P m yf b' S hs then return some gs
      s.restore
    | none => s.restore
  return none

/-- Is `f` a clause-spine continuation (`f (some r)` normalizes to `pure r`)? -/
def spine? (α f : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let αw ← whnfR α
  unless αw.isAppOfArity ``Option 1 do return none
  let T := αw.appArg!
  withLocalDeclD `r T fun r => do
    let fr := f.beta #[mkApp2 (mkConst ``Option.some [Level.zero]) T r]
    let body ← norm fr
    if body.isAppOf ``FreeM.pure && body.appArg! == r then
      let ty ← mkForallFVars #[r] (← mkEq fr body)
      let yf ← mkLambdaFVars #[r] (← mkEqRefl fr)
      return some (← mkExpectedTypeHint yf ty)
    return none

/-- The side-condition tactic (non-footprint goals the walker cannot close itself). -/
syntax "yf_side" : tactic
macro_rules
  | `(tactic| yf_side) => `(tactic| first
      | exact True.intro
      | rfl
      | assumption
      | contradiction
      | (intro h; cases h <;> fail)
      | (simp only [classify, akIfetch, ifOk] <;> fail)
      | decide
      | (dsimp only; decide)
      | (apply Or.inl; assumption)
      | (apply Or.inr; assumption)
      | (apply Or.inr; rfl)
      | (apply Or.inl; rfl))

/-- A side goal: try the cheap closers, else leave it (or run `yf_side`). -/
def side (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let mut t ← whnfR (← instantiateMVars (← g.getType))
  -- unfold the walker's own post / read-kind definitions
  for _ in [0:3] do
    if let some n := t.getAppFn.constName? then
      if n == ``Weak.PinDataOkFp.optPost || n == ``Weak.PinDataOkFp.ifOk then
        if let some t' ← unfoldDefinition? t then
          t ← whnfR t'.headBeta
          match ← Meta.reduceMatcher? t with
          | .reduced t'' => t := t''.headBeta
          | _ => pure ()
  if t.isConstOf ``True then g.assign (mkConst ``True.intro); return []
  if (← yfView? t).isSome then
    let g' ← g.replaceTargetDefEq t
    return [g']
  if t.isForall then
    let g' ← introN' (← g.replaceTargetDefEq t) 1
    return [g']
  if t.isAppOfArity ``And 2 then
    let h1 ← newGoal (t.getArg! 0); let h2 ← newGoal (t.getArg! 1)
    g.assign (← mkAppM ``And.intro #[h1, h2])
    return [h1.mvarId!, h2.mvarId!]
  -- `l = false` with a closed `l`
  if let some (_, l, r) := t.eq? then
    if r.isConstOf ``Bool.false && !l.hasFVar && !l.hasMVar then
      let l' ← whnfD l
      if l'.isConstOf ``Bool.false then
        g.assign (← mkEqRefl r); return []
  let s ← saveState
  try
    let r ← Tactic.run g (Term.withoutErrToSorry <| Tactic.withoutRecover <|
      evalTactic (← `(tactic| yf_side)))
    if r.isEmpty then return []
    s.restore; return [g]
  catch _ => s.restore; return [g]


/-- The walker's context. -/
structure Ctx where
  jps : IO.Ref (Std.HashMap FVarId FVarId)
  spineJps : IO.Ref (Std.HashMap FVarId FVarId)
  memo : IO.Ref (Std.HashMap (Name × Bool) (Option Name))
  stats : Bool
  tab : IO.Ref (Std.HashMap String (Nat × Nat))
  steps : IO.Ref Nat
  limit : Nat
  autoMemo : Bool := false
  /-- a value post at the root: continuation-passing for every bound `match`/`if`/unregistered
  call (the post reads the values) -/
  valueMode : Bool := false
  /-- `good_walk_v`: continuation-passing (no footprint delegation) for every bound `match`/`if`
  of a `good` goal, so the branches see the matched values -/
  gValue : Bool := false
  /-- development aid: log every `good` step -/
  gDbg : Bool := false
  /-- the `good` walker's step counter and limit -/
  gsteps : IO.Ref Nat
  glimit : Nat := 200000

mutual

/-- One step on a footprint goal; returns the new goals. -/
partial def step (cx : Ctx) (g : MVarId) (b X P m0 : Lean.Expr) :
    TacticM (List MVarId) := g.withContext do
  let jps := cx.jps
  let m ← norm m0
  let fn := m.getAppFn
  let args := m.getAppArgs
  let assign (v : Lean.Expr) : MetaM Unit := g.assign v
  let replace (m' : Lean.Expr) : MetaM (List MVarId) := do
    let g' ← newGoal (mkFp b X P m')
    assign g'
    return [g'.mvarId!]
  let C (n : Name) : Lean.Expr := mkConst n
  -- let: a join point stays abstract, any other let is substituted
  if let .letE n t v bd _ := m then
    let tw ← whnfR t
    if n.toString.startsWith "__do_jp" && tw.isForall && !tw.bindingBody!.hasLooseBVars then
      let A := tw.bindingDomain!
      -- a clause-spine join point
      if let some hf ← spine? A v then
        let T := (← whnfR A).appArg!
        let body := Lean.Expr.lam n t bd .default
        let gn ← newGoal (mkFp b X P (v.beta #[mkApp (mkConst ``Option.none [Level.zero]) T]))
        let hbTy ← withLocalDeclD n t fun jp => do
          let hj ← withLocalDeclD `o A fun o => do
            withLocalDeclD `ho (mkApp3 (mkConst ``Weak.PinDataOkFp.optPost) T P o) fun ho => do
              mkForallFVars #[o, ho] (mkFp b X P (mkApp jp o))
          withLocalDeclD `hjp hj fun hjp => do
            mkForallFVars #[jp, hjp] (mkFp b X P (bd.instantiate1 jp))
        let gb ← newGoal hbTy
        assign (mkAppN (C ``Weak.PinDataOkFp.yfJpSpineF) #[T, b, P, v, body, hf, gn, gb])
        let (fvs, gb') ← gb.mvarId!.introN 2
        cx.spineJps.modify (·.insert fvs[0]! fvs[1]!)
        return [gn.mvarId!, gb']
      let body := Lean.Expr.lam n t bd .default
      let hvTy ← withLocalDeclD `a A fun a => do mkForallFVars #[a] (mkFp b X P (v.beta #[a]))
      let hbTy ← withLocalDeclD n t fun jp => do
        let hj ← withLocalDeclD `a A fun a => do mkForallFVars #[a] (mkFp b X P (mkApp jp a))
        withLocalDeclD `hjp hj fun hjp => do
          mkForallFVars #[jp, hjp] (mkFp b X P (bd.instantiate1 jp))
      let gv ← newGoal hvTy
      let gb ← newGoal hbTy
      assign (mkAppN (C ``Weak.PinDataOkFp.yfJpF) #[A, X, b, P, v, body, gv, gb])
      let gv' ← introN' gv.mvarId! 1
      let (fvs, gb') ← gb.mvarId!.introN 2
      jps.modify (·.insert fvs[0]! fvs[1]!)
      return [gv', gb']
    return ← replace (bd.instantiate1 v)
  match fn with
  | .const c _ =>
    if c == ``FreeM.pure then
      let t := (P.beta #[args[args.size - 1]!]).headBeta
      if isTrivPost P then assign (C ``True.intro); return []
      let g' ← newGoal t
      assign g'
      return [g'.mvarId!]
    if c == ``FreeM.impure then
      let call ← whnfR args[args.size - 2]!
      let k := args[args.size - 1]!
      if call.isAppOf ``Except.error then
        assign (C ``True.intro); return []
      unless call.isAppOf ``Except.ok do throwError "yf_walk: impure call not ok/error{indentExpr call}"
      let o ← whnf call.appArg!
      let some oc := o.getAppFn.constName? | throwError "yf_walk: event{indentExpr o}"
      let ret ← whnf (← inferType k).bindingDomain!
      let allK : MetaM (List MVarId) := do
        let ty ← withLocalDeclD `v ret fun v => mkForallFVars #[v] (mkFp b X P (k.beta #[v]))
        let g' ← newGoal ty
        assign g'
        return [← introN' g'.mvarId! 1]
      if oc == ``Outcome.regRead then
        let r := o.appArg!
        let ty ← withLocalDeclD `v ret fun v => do
          withLocalDeclD `hv (mkApp2 (C ``Weak.SailCycleOrderK.Rboot) r v) fun hv => do
            mkForallFVars #[v, hv] (mkFp b X P (k.beta #[v]))
        let g' ← newGoal ty
        assign g'
        return [← introN' g'.mvarId! 2]
      if oc == ``Outcome.regWrite then
        let r := o.getArg! (o.getAppNumArgs - 2)
        let v := o.getArg! (o.getAppNumArgs - 1)
        let h1 ← newGoal (mkApp2 (C ``Weak.PinDataOkFp.yfW) r v)
        let ty2 ← withLocalDeclD `u ret fun u => mkForallFVars #[u] (mkFp b X P (k.beta #[u]))
        let h2 ← newGoal ty2
        assign (← mkAppM ``And.intro #[h1, h2])
        return [h1.mvarId!, ← introN' h2.mvarId! 1]
      if oc == ``Outcome.memRead then
        let req := o.getArg! (o.getAppNumArgs - 1)
        let h1 ← newGoal (mkApp2 (C ``Weak.PinDataOkFp.ifOk) b (← mkProjection req `access_kind))
        let ty2 ← withLocalDeclD `v ret fun v => mkForallFVars #[v] (mkFp b X P (k.beta #[v]))
        let h2 ← newGoal ty2
        assign (← mkAppM ``And.intro #[h1, h2])
        return [h1.mvarId!, ← introN' h2.mvarId! 1]
      if oc == ``Outcome.barrier then
        let bk := o.appArg!
        let h1 ← newGoal (mkNot (← mkEq bk (C ``barrier_kind.Barrier_RISCV_i)))
        let h2 ← newGoal (mkFp b X P (k.beta #[C ``Unit.unit]))
        assign (← mkAppM ``And.intro #[h1, h2])
        return [h1.mvarId!, h2.mvarId!]
      if oc == ``Outcome.instrAnnounce then throwError "yf_walk: an instruction announce"
      return ← allK
    if c == ``FreeM.bind then
      let x ← norm args[args.size - 2]!
      let f := args[args.size - 1]!
      let α := (← whnf (← inferType f)).bindingDomain!; let β := X
      let yf := x.getAppFn
      if let .letE _ _ v bd _ := x then
        return ← replace (mkAppN fn (args.set! (args.size - 2) (bd.instantiate1 v)))
      if let .const xc _ := yf then
        if xc == ``FreeM.pure then return ← replace (f.beta #[x.appArg!])
        if xc == ``FreeM.impure then
          let xa := x.getAppArgs
          let k := xa[xa.size - 1]!
          let k' ← withLocalDeclD `r (← inferType k).bindingDomain! fun r => do
            mkLambdaFVars #[r] (mkAppN fn (args.set! (args.size - 2) (k.beta #[r])))
          return ← replace (mkAppN yf (xa.set! (xa.size - 1) k'))
        if xc == ``FreeM.bind then
          let xa := x.getAppArgs
          let y := xa[xa.size - 2]!; let gg := xa[xa.size - 1]!
          let γ := (← whnf (← inferType gg)).bindingDomain!
          let h ← withLocalDeclD `a γ fun a => do
            mkLambdaFVars #[a] (← mkAppM ``FreeM.bind #[gg.beta #[a], f])
          let inner ← mkAppM ``FreeM.bind #[y, h]
          let g' ← newGoal (mkFp b X P inner)
          assign (mkAppN (C ``Weak.PinDataOkFp.yfAssocF) #[γ, α, β, b, P, y, gg, f, g'])
          return [g'.mvarId!]
      -- the clause spine: the clause under the option post, the rest once
      if let some hf ← spine? α f then
        let T := (← whnfR α).appArg!
        let gm ← newGoal (mkFp b α (mkApp2 (mkConst ``Weak.PinDataOkFp.optPost) T P) x)
        let gn ← newGoal (mkFp b X P (f.beta #[mkApp (mkConst ``Option.none [Level.zero]) T]))
        assign (mkAppN (C ``Weak.PinDataOkFp.yfSpineF) #[T, b, P, x, f, hf, gm, gn])
        return [gm.mvarId!, gn.mvarId!]
      if let .const xc _ := yf then
        -- continuation-passing only where the continuation's footprint depends on the value:
        -- a computed read kind / access kind (the read node's `ifOk`)
        let αw ← whnfR α
        let αw ← if αw.isAppOf ``Except then whnfR αw.appArg! else pure αw
        let αh := αw.getAppFn.constName?
        let cpsTy := αh == some ``read_kind || αh == some ``Access_kind ||
          αh == some ``Mem_read_request || αh == some ``Option
        if (cpsTy || cx.valueMode) && (xc == ``ite || xc == ``dite || (← isMatcher xc)) then
          let post ← withLocalDeclD `a α fun a => do mkLambdaFVars #[a] (mkFp b β P (f.beta #[a]))
          let g' ← newGoal (mkFp b α post x)
          assign (mkAppN (C ``Weak.PinDataOkFp.yfBindCF) #[α, β, b, P, x, f, g'])
          return [g'.mvarId!]
        -- a registered head: bind through its post
        for L in ← Weak.PinDataOkReg.yfRegFind xc do
          let s ← saveState
          let lc ← mkConstWithFreshMVarLevels L
          match ← instAt lc (← inferType lc) x b with
          | some (yf, b', S, hs) =>
            let yf' ← if (← isDefEq b b') then pure (some yf)
              else if b'.isConstOf ``Bool.false && b.isConstOf ``Bool.true then
                pure (some (mkAppN (C ``Weak.PinDataOkFp.yfRelax) #[α, S, x, yf]))
              else pure none
            match yf' with
            | some yf' =>
              let hk ← withLocalDeclD `a α fun a => do
                withLocalDeclD `ha (S.beta #[a]) fun ha => do
                  mkForallFVars #[a, ha] (mkFp b β P (f.beta #[a]))
              let gk ← newGoal hk
              assign (mkAppN (C ``Weak.PinDataOkFp.yfBindQF) #[α, β, b, S, P, x, f, yf', gk])
              return hs ++ [← introN' gk.mvarId! 2]
            | none => s.restore
          | none => s.restore
      -- value mode: an unregistered call is unfolded under the continuation
      if cx.valueMode && yf.isConst then
        let post ← withLocalDeclD `a α fun a => do mkLambdaFVars #[a] (mkFp b β P (f.beta #[a]))
        let g' ← newGoal (mkFp b α post x)
        assign (mkAppN (C ``Weak.PinDataOkFp.yfBindCF) #[α, β, b, P, x, f, g'])
        return [g'.mvarId!]
      -- additive
      let hm ← newGoal (mkFp b α (← withLocalDeclD `a α fun a => mkLambdaFVars #[a] (C ``True)) x)
      let hk ← withLocalDeclD `a α fun a => do mkForallFVars #[a] (mkFp b β P (f.beta #[a]))
      let gk ← newGoal hk
      assign (mkAppN (C ``Weak.PinDataOkFp.yfBindF) #[α, β, b, P, x, f, hm, gk])
      return [hm.mvarId!, ← introN' gk.mvarId! 1]
    if c == ``ite || c == ``dite then
      let cnd := args[1]!; let inst := args[2]!; let a := args[3]!; let d := args[4]!
      -- a closed condition: decide it
      if !cnd.hasFVar && !cnd.hasMVar then
        let dv ← withTransparency .all <| whnf (mkApp2 (C ``Decidable.decide) cnd inst)
        if dv.isConstOf ``Bool.true || dv.isConstOf ``Bool.false then
          let isT := dv.isConstOf ``Bool.true
          let hEq ← mkEqRefl dv
          let lem := if c == ``ite then
              (if isT then ``Weak.PinDataOkFp.yfIteT else ``Weak.PinDataOkFp.yfIteE)
            else (if isT then ``Weak.PinDataOkFp.yfDiteT else ``Weak.PinDataOkFp.yfDiteE)
          let br ← if c == ``ite then pure (if isT then a else d) else do
            let yf ← if isT then mkAppOptM ``of_decide_eq_true #[cnd, inst, hEq]
              else mkAppOptM ``of_decide_eq_false #[cnd, inst, hEq]
            pure ((if isT then a else d).beta #[yf])
          let g' ← newGoal (mkFp b X P br)
          assign (mkAppN (C lem) #[X, b, P, cnd, inst, a, d, hEq, g'])
          return [g'.mvarId!]
      if c == ``ite then
        let ga ← newGoal (← mkArrow cnd (mkFp b X P a))
        let gb ← newGoal (← mkArrow (mkNot cnd) (mkFp b X P d))
        assign (mkAppN (C ``Weak.PinDataOkFp.yfIteF) #[X, b, P, cnd, inst, a, d, ga, gb])
        return [← introN' ga.mvarId! 1, ← introN' gb.mvarId! 1]
      let ta ← withLocalDeclD `h cnd fun h => do mkForallFVars #[h] (mkFp b X P (a.beta #[h]))
      let tb ← withLocalDeclD `h (mkNot cnd) fun h => do mkForallFVars #[h] (mkFp b X P (d.beta #[h]))
      let ga ← newGoal ta
      let gb ← newGoal tb
      assign (mkAppN (C ``Weak.PinDataOkFp.yfDiteF) #[X, b, P, cnd, inst, a, d, ga, gb])
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
        let g' ← newGoal (mkFp b X P (F.beta #[t]))
        let lvl := match fn with | .const _ (u :: _) => u | _ => Level.zero
        assign (mkAppN (mkConst ``Weak.PinDataOkFp.yfEqRecF [lvl])
          #[X, b, P, args[0]!, args[1]!, args[4]!, T, t, h, F, g'])
        return [g'.mvarId!]
    if ← isMatcher c then
      let some info ← getMatcherInfo? c | throwError "yf_walk: no matcher info"
      let ds := args.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
      let g1 ← if m != m0 then do
          let g' ← newGoal (mkFp b X P m); assign g'; pure g'.mvarId!
        else pure g
      let env ← getEnv
      let isCtor (d : Lean.Expr) : Bool :=
        match d.getAppFn.constName? with
        | some n => (env.find? n).any (·.isCtor)
        | none => false
      -- a match on literals compiles to an `if` chain: unfold the matcher
      let mDelta? : Option Lean.Expr ← do
        let ci ← getConstInfo c
        if ci.hasValue then
          let lvls := match m.getAppFn with | .const _ ls => ls | _ => []
          let v ← instantiateValueLevelParams ci lvls
          pure (some (v.beta m.getAppArgs))
        else pure none
      if let some m' := mDelta? then
        let m'' ← whnfCore m'.headBeta
        let h := m''.getAppFn.constName?
        if h == some ``ite || h == some ``dite then
          let g' ← newGoal (mkFp b X P m''); g1.assign g'
          return [g'.mvarId!]
      -- case on a variable leaf of the discriminants, or generalize a compound one
      let rec leaves (d : Lean.Expr) : List Lean.Expr :=
        if isCtor d then d.getAppArgs.toList.flatMap leaves
        else if d.isLit || d.isSort then []
        else [d]
      let lfs := ds.toList.flatMap leaves
      for l in lfs do
        let ty ← whnfD (← inferType l)
        let some tn := ty.getAppFn.constName? | continue
        let some (.inductInfo ii) := env.find? tn | continue
        -- many constructors against few alternatives: the splitter (wildcards) is cheaper
        if ii.ctors.length > info.numAlts + 1 then continue
        -- literal types: never case on their representation
        if [``BitVec, ``Fin, ``Nat, ``Int, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``Char,
            ``String].contains tn then continue
        let s ← saveState
        try
          if l.isFVar then
            let gs ← g1.cases l.fvarId!
            return (gs.map (·.mvarId)).toList
          let (fvs, g2) ← g1.generalize #[{ expr := l, xName? := `dsc, hName? := `hdsc }]
          let gs ← g2.cases fvs[0]!
          return (gs.map (·.mvarId)).toList
        catch _ => s.restore
      return ← Split.splitMatch g1 m
    -- a registered lemma for the head
    if let some gs ← useReg g c b X P m then return gs
    let isRec ← isRecDef c
    -- memoize the function's generic footprint (an auxiliary lemma), then use it
    if cx.autoMemo && !isRec && isTrivPost P && !plumbing.contains c then
      if let some L ← memoize cx c b then
        let lc ← mkConstWithFreshMVarLevels L
        match ← instAt lc (← inferType lc) m b with
        | some (yf, b', S, hs) =>
          if let some gs ← closeBy g b X P m yf b' S hs then return gs
        | none => pure ()
    let delta? ← if isRec then pure none else unfoldDefinition? m
    match delta? with
    | some m' => return ← replace m'
    | none => pure ()
    -- recursive (or not delta-unfoldable): an induction hypothesis in context
    if let some gs ← useHyp g b X P m then return gs
    if c == ``pt_walk || c == ``untilFuelM.go || c == ``IntRange.forIn'.loop then
      let mut info := m!""
      for L in ← Weak.PinDataOkReg.yfRegFind c do
        let lc ← mkConstWithFreshMVarLevels L
        let r ← instAt lc (← inferType lc) m b
        match r with
        | some (yf, b', S, hs) =>
          let cb ← closeBy g b X P m yf b' S hs
          info := info ++ m!"\n{L}: inst ok, b={b} b'={b'} P={P} S={S} close={cb.isSome}"
        | none => info := info ++ m!"\n{L}: no inst"
      throwError "yf_walk: recursive {c} needs a lemma{info}"
    -- unfold by the equation lemma (terminating recursion on these arguments)
    let some eqn ← getUnfoldEqnFor? c (nonRec := true) |
      let m' ← withTransparency .instances <| whnf m
      if m' != m then return ← replace m'
      throwError "yf_walk: cannot unfold {c}{indentExpr m}"
    let eqc ← mkConstWithFreshMVarLevels eqn
    let (eargs, _, ety) ← forallMetaTelescope (← inferType eqc)
    let some (_, lhs, rhs) := ety.eq? | throwError "yf_walk: bad equation {eqn}"
    unless ← isDefEq lhs m do throwError "yf_walk: equation {eqn} does not match{indentExpr m}"
    let yf ← instantiateMVars (mkAppN eqc eargs)
    let rhs ← instantiateMVars rhs
    let g' ← newGoal (mkFp b X P rhs)
    let eq ← mkCongrArg (mkApp3 (C ``Weak.PinDataOkFp.yfB) X b P) yf
    assign (← mkEqMPR eq g')
    return [g'.mvarId!]
  | .fvar fv =>
    -- an abstract join point
    if let some hj := (← jps.get)[fv]? then
      assign (mkAppN (mkFVar hj) m.getAppArgs); return []
    -- a clause-spine join point: the call owes the option post
    if let some hj := (← cx.spineJps.get)[fv]? then
      let o := m.appArg!
      let T := (← whnfR (← inferType o)).appArg!
      let go ← newGoal (mkApp3 (mkConst ``Weak.PinDataOkFp.optPost) T P o)
      assign (mkApp2 (mkFVar hj) o go)
      return [go.mvarId!]
    -- an induction hypothesis / local fact
    if let some gs ← useHyp g b X P m then return gs
    throwError "yf_walk: stuck at a local{indentExpr m}"
  | _ => throwError "yf_walk: stuck{indentExpr m}"

/-- The generic footprint of the definition `c` (all its parameters symbolic), proved once by a
nested walk in an empty context and kept as an auxiliary lemma; `none` if the walk leaves goals. -/
partial def memoize (cx : Ctx) (c : Name) (b : Lean.Expr) : TacticM (Option Name) := do
  let bb := b.isConstOf ``Bool.true
  if let some r := (← cx.memo.get)[(c, bb)]? then
    match r with
    | some L => if (← getEnv).contains L then return r
    | none => return none
  cx.memo.modify (·.insert (c, bb) none)   -- in progress / failed
  let info ← getConstInfo c
  let lps := info.levelParams
  let fc := mkConst c (lps.map mkLevelParam)
  let r? ← withLCtx {} {} <| forallTelescope (← inferType fc) fun xs body => do
    let bw ← whnfR body
    unless bw.isAppOf ``FreeM do return none
    let X := bw.appArg!
    unless ← isDefEq body (mkApp (mkConst ``LeanRV64D.SailM) X) do return none
    let post ← withLocalDeclD `a X fun a => mkLambdaFVars #[a] (mkConst ``True)
    let goalTy := mkFp b X post (mkAppN fc xs)
    let gm ← newGoal goalTy
    let s ← saveState
    try
      let left ← loop cx [gm.mvarId!]
      unless left.isEmpty do s.restore; return none
      let yf ← instantiateMVars gm
      if yf.hasMVar then s.restore; return none
      let ty ← mkForallFVars xs goalTy
      let val ← mkLambdaFVars xs yf
      return some (← mkAuxLemma lps ty val)
    catch _ => s.restore; return none
  cx.memo.modify (·.insert (c, bb) r?)
  return r?

/-- The walker's loop: process the goal stack, returning the goals it leaves. -/
partial def loop (cx : Ctx) (start : List MVarId) : TacticM (List MVarId) := do
  let mut stack := start
  let mut left : List MVarId := []
  while true do
    match stack with
    | [] => break
    | g :: rest =>
      cx.steps.modify (· + 1)
      if (← cx.steps.get) > cx.limit then throwError "yf_walk: step limit"
      if ← g.isAssigned then stack := rest; continue
      let ty ← instantiateMVars (← g.getType)
      match ← yfView? ty with
      | some (b, X, P, m) =>
        let t0 ← IO.monoNanosNow
        let gs ← step cx g b X P m
        let t1 ← IO.monoNanosNow
        if cx.stats then
          let mn ← g.withContext (norm m)
          let key := match mn.getAppFn.constName? with
            | some n => if n == ``FreeM.bind then
                (match (mn.getArg! (mn.getAppNumArgs - 2)).getAppFn.constName? with
                 | some n2 => s!"bind:{n2}" | none => "bind:?")
              else n.toString
            | none => "?"
          cx.tab.modify fun tab =>
            let (c, ns) := tab.getD key (0, 0)
            tab.insert key (c + 1, ns + (t1 - t0))
        stack := gs ++ rest
      | none =>
        let gs ← side g
        if gs == [g] then
          left := left ++ [g]; stack := rest
        else stack := gs ++ rest
  return left

end

/-- Run the walker on the main goal to completion. -/
def run (limit : Nat) (stats : Bool := false) (vmode : Bool := false) : TacticM Unit := do
  let jps ← IO.mkRef {}
  let spineJps ← IO.mkRef {}
  let memo ← IO.mkRef {}
  let tab ← IO.mkRef {}
  let steps ← IO.mkRef 0
  let g0 ← getMainGoal
  let valueMode ← if !vmode then pure false else
    match ← yfView? (← instantiateMVars (← g0.getType)) with
    | some (_, _, P, _) => pure (!isTrivPost P && !isCpsPost P)
    | none => pure false
  let gsteps ← IO.mkRef 0
  let cx : Ctx := { jps, spineJps, memo, stats, tab, steps, limit, valueMode, gsteps }
  let left ← loop cx [g0]
  if stats then
    let arr := (← cx.tab.get).toArray.qsort (fun a b => a.2.2 > b.2.2)
    let lines := arr.toList.take 25 |>.map (fun (k, c, ns) => s!"{k}: {c} steps, {ns / 1000000} ms")
    let memo := (← cx.memo.get).toList.filterMap (fun ((c, _), r) => if r.isSome then some c else none)
    logInfo m!"yf_walk: {← cx.steps.get} steps; memoized {memo.length}\n{String.intercalate "\n" lines}"
  replaceMainGoal left

end Walk

/-- **The walker** (header): closes `yfB b P m`, leaving the side conditions it cannot close. -/
elab "yf_walk" : tactic => Walk.run 1000000

/-- The walker in VALUE MODE (for a lemma with a value post read off the tree's values): every
bound `match`/`if` and every unregistered bound call is walked under the continuation. -/
elab "yf_walk_v" : tactic => Walk.run 1000000 false true

/-- The walker with a profile of its steps (development aid). -/
elab "yf_walk_stats" : tactic => Walk.run 1000000 true

end PinDataOkFp
end Weak
