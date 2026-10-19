/-
MachCSL: the generic laws of lean-sail's free monad `Sail.ArchSem.FreeM`.

The Sail model's monad is `SailM = FreeM ((Except (Sail.Error ue) InstructionEffect) ⊕ FinChoice)`
(concurrency interface v2, lean-sail v7).  lean-sail ships the monad but not its laws; the
vendored V1 runtime this tree used before the 0.16 bump had them
(`Sail.ConcurrencyInterfaceV1.FreeMLemmas`), and this file is their home now
(`MachCSL.FreeMLemmas`): the two
computation rules of `bind`, the right-unit and associativity laws, and the `LawfulMonad`
instance that makes `pure_bind`/`bind_assoc` available to `simp`.
-/
import Sail.ArchSem

namespace MachCSL.FreeMLemmas

open Sail.ArchSem

universe u w

variable {E : Type} [Effect.{u, 0} E] {α β γ : Type w}

@[simp] theorem bind_pure (a : α) (f : α → FreeM E β) :
    (FreeM.pure a : FreeM E α).bind f = f a := rfl

@[simp] theorem bind_impure (op : E) (k : Effect.ret op → FreeM E α) (f : α → FreeM E β) :
    (FreeM.impure op k).bind f = FreeM.impure op (fun r => (k r).bind f) := rfl

theorem bind_pure_right (x : FreeM E α) : x.bind FreeM.pure = x := by
  induction x with
  | pure a => rfl
  | impure op k ih => simp only [bind_impure]; congr; funext r; exact ih r

theorem bind_assoc (x : FreeM E α) (f : α → FreeM E β) (g : β → FreeM E γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  induction x with
  | pure a => rfl
  | impure op k ih => simp only [bind_impure]; congr; funext r; exact ih r

/-- A raw `FreeM.pure` at the head of a bind (lean-sail's primitives build their results with
it, e.g. a passing `sail_assert`) feeds its value to the continuation. -/
theorem freeM_pure_bind (a : α) (f : α → FreeM E β) : (FreeM.pure a : FreeM E α) >>= f = f a := rfl

instance : LawfulMonad (FreeM E) := LawfulMonad.mk'
  (id_map := fun x => by
    show x.bind (fun a => FreeM.pure a) = x
    exact bind_pure_right x)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

end MachCSL.FreeMLemmas
