/-
MachCSL: **stuttering by discarded reads** (`SailStut`, lane AND-ELIM): the
relation between Sail's short-circuit `&`/`|` and the lean-sail backend's
eager `(← a) && (← b)`.

`SailStut m₀ m`: `m` is `m₀` with extra register reads inserted whose
answers nothing uses -- at any point, `m` may read any register (any number
of times, the continuation not depending on the answer as far as `m₀` is
concerned) before going on as `m₀` does; otherwise the two take the same
events.  The program logic cannot tell them apart in the direction the proofs
need (`MachCSL/SailAndElim.lean`: `swp_stut`, `swp cpu m₀ Φ ⊢ swp cpu m Φ`):
a register read never changes the machine state, it only costs a step.

The facts here are pure (no Iris):

* congruence: `SailStut.bind` (both sides of a bind), `SailStut.bind_right`
  (the continuation only), `SailStut.ite`, `SailStut.ctx` (any monadic
  context `MCtx`);
* insertion: `SailStut.discard` -- a read-only total `b` (`SailRO`) whose
  continuation is (up to `SailStut`) `m₀` whatever `b` answers;
  `SailStut.irrel` its equational form;
* the short-circuit shapes the backend emits (`(← a) && (← b)`, a pure left
  operand `p && (← b)`, the `||` duals, their bound forms):
  `SailStut.and`, `SailStut.or`, `SailStut.and_bind`, `SailStut.or_bind`.

A nested chain `(← a) && (P && ((← b) && (← c)))` is hoisted by Lean to
`a >>= fun x => b >>= fun y => c >>= fun z => pure (x && (P && (y && z)))`;
its short-circuit form is proved by `SailStut.bind_right` on the kept prefix
and `SailStut.irrel` (the continuation is constant once the known operands
decide the result), see `SailStut.and3` for the three-operand chain
`check_CSR` uses.
-/
import MachCSL.SailRO
import MachCSL.Wp

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- **Stuttering by discarded reads**: `m` is `m₀` with extra register reads
whose answers are not used. -/
inductive SailStut {α : Type} : SailM α → SailM α → Prop where
  | refl (m : SailM α) : SailStut m m
  | read {m₀ : SailM α} (r : Register) (k : RegisterType r → SailM α) :
      (∀ v, SailStut m₀ (k v)) → SailStut m₀ (FreeM.impure (.ok (.regRead r)) k)
  | step (o : Outcome Register RegisterType) (k₀ k : o.ret → SailM α) :
      (∀ v, SailStut (k₀ v) (k v)) → SailStut (FreeM.impure (.ok o) k₀) (FreeM.impure (.ok o) k)

namespace SailStut

/-- Two computations with the same events: the continuation related pointwise. -/
theorem bind_right {α β : Type} (m : SailM α) {f₀ f : α → SailM β}
    (hf : ∀ a, SailStut (f₀ a) (f a)) : SailStut (m >>= f₀) (m >>= f) := by
  induction m with
  | pure a => exact hf a
  | impure call k ih =>
    cases call with
    | error e =>
      show SailStut (FreeM.impure (.error e) _) (FreeM.impure (.error e) _)
      have : (fun v => FreeM.bind (k v) f₀) = (fun v => FreeM.bind (k v) f) := funext fun v => nomatch v
      rw [this]; exact .refl _
    | ok o => exact .step o _ _ fun v => ih v

/-- **Congruence under bind.** -/
theorem bind {α β : Type} {m₀ m : SailM α} {f₀ f : α → SailM β} (hm : SailStut m₀ m)
    (hf : ∀ a, SailStut (f₀ a) (f a)) : SailStut (m₀ >>= f₀) (m >>= f) := by
  induction hm with
  | refl m => exact bind_right m hf
  | read r k _ ih => exact .read r _ fun v => ih v
  | step o k₀ k _ ih => exact .step o _ _ fun v => ih v

/-- **Congruence under a monadic context** (`MCtx`: a bind, `sailTryCatch`,
the early-return wrappers). -/
theorem ctx {X : Type} {C : SailM X → SailM Unit} (hC : MCtx C) {m₀ m : SailM X}
    (h : SailStut m₀ m) : SailStut (C m₀) (C m) := by
  induction h with
  | refl m => exact .refl _
  | read r k _ ih => rw [hC]; exact .read r _ fun v => ih v
  | step o k₀ k _ ih => rw [hC, hC]; exact .step o _ _ fun v => ih v

/-- Congruence under a conditional. -/
theorem ite {α : Type} {c : Prop} [Decidable c] {a₀ a b₀ b : SailM α} (ha : c → SailStut a₀ a)
    (hb : ¬ c → SailStut b₀ b) : SailStut (if c then a₀ else b₀) (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- **Discarding a read-only total computation**: running `b` first and
continuing, whatever it answers, as `m₀` does. -/
theorem discard {α β : Type} {m₀ : SailM α} {b : SailM β} {k : β → SailM α} (hb : SailRO b)
    (hk : ∀ y, SailStut m₀ (k y)) : SailStut m₀ (b >>= k) := by
  induction hb with
  | pure a => exact hk a
  | read r k' _ ih => exact .read r _ fun v => ih v

/-- `discard`, equational form: the continuation does not depend on the answer. -/
theorem irrel {α β : Type} {m₀ : SailM α} {b : SailM β} {k : β → SailM α} (hb : SailRO b)
    (hk : ∀ y, k y = m₀) : SailStut m₀ (b >>= k) :=
  discard hb fun y => hk y ▸ .refl _

/-- Discarding a sequenced read-only computation. -/
theorem seq {α β : Type} {m : SailM α} {b : SailM β} (hb : SailRO b) :
    SailStut m (b >>= fun _ => m) :=
  irrel hb fun _ => rfl

/-! ## The short-circuit shapes -/

/-- **`p && (← b)`**: Sail runs `b` only when `p`. -/
theorem and {α : Type} (p : Bool) {b : SailM Bool} (hb : SailRO b) (k : Bool → SailM α) :
    SailStut (if p then b >>= k else k false) (b >>= fun y => k (p && y)) := by
  cases p
  · exact irrel hb fun _ => rfl
  · exact .refl _

/-- **`p || (← b)`**: Sail runs `b` only when `¬ p`. -/
theorem or {α : Type} (p : Bool) {b : SailM Bool} (hb : SailRO b) (k : Bool → SailM α) :
    SailStut (if p then k true else b >>= k) (b >>= fun y => k (p || y)) := by
  cases p
  · exact .refl _
  · exact irrel hb fun _ => rfl

/-- **`(← a) && (← b)`** (the bound form): `a` runs, then `b` only when `a`
answered `true`. -/
theorem and_bind {α : Type} (a : SailM Bool) {b : SailM Bool} (hb : SailRO b) (k : Bool → SailM α) :
    SailStut (a >>= fun x => if x then b >>= k else k false)
      (a >>= fun x => b >>= fun y => k (x && y)) :=
  bind_right a fun x => SailStut.and x hb k

/-- **`(← a) || (← b)`** (the bound form). -/
theorem or_bind {α : Type} (a : SailM Bool) {b : SailM Bool} (hb : SailRO b) (k : Bool → SailM α) :
    SailStut (a >>= fun x => if x then k true else b >>= k)
      (a >>= fun x => b >>= fun y => k (x || y)) :=
  bind_right a fun x => SailStut.or x hb k

/-- **The three-operand chain** `(← a) && (P && ((← b) && (← c)))` (the shape
of `check_CSR`): `b` runs only when `a && P`, `c` only when `b` too. -/
theorem and3 {α : Type} (a : SailM Bool) (P : Bool) {b c : SailM Bool} (hb : SailRO b) (hc : SailRO c)
    (k : Bool → SailM α) :
    SailStut (a >>= fun x => if x && P then b >>= fun y => if y then c >>= k else k false else k false)
      (a >>= fun x => b >>= fun y => c >>= fun z => k (x && (P && (y && z)))) := by
  refine bind_right a fun x => ?_
  cases x <;> cases P <;>
    simp only [Bool.and_self, Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]
  · exact discard hb fun _ => irrel hc fun _ => rfl
  · exact discard hb fun _ => irrel hc fun _ => rfl
  · exact discard hb fun _ => irrel hc fun _ => rfl
  · exact SailStut.and_bind b hc k

end SailStut

end MachCSL
