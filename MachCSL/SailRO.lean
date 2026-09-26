/-
MachCSL: **read-only, total model computations** (`SailRO`), the side
condition of the short-circuit elimination (`MachCSL/SailStut.lean`,
`MachCSL/SailAndElim.lean`).

Sail's `&`/`|` on booleans short-circuit, but the lean-sail backend emits
`(← a) && (← b)` inside `do`, which Lean hoists: `b` always runs.  When `b`
only READS registers and cannot fail, the eager form differs from Sail only by
extra, discarded register reads; `SailStut` (the next file) makes that precise
and `SailAndElim` proves the program logic cannot tell the difference.

`SailRO b`: every path of `b` is register reads (for EVERY value each read
may return) ending in a value -- no write, no memory or other event, no
failure (`assert`, `throw`, `internal_error`).  It is an inductive over the
`FreeM` tree, so it quantifies over each read's answer independently (the
wire registers `sig_meip`/`sig_seip` can change between two reads).

Closure: `SailRO.pure'`, `SailRO.readReg`, `SailRO.bind`, `SailRO.map`,
`SailRO.ite`, `SailRO.dite`; a `match` is handled by `split`.  The tactic
`sail_ro` discharges a goal `SailRO t` by those rules, unfolding definitions
on the way and applying the leaf lemmas registered through the extensible
`sail_ro_leaf` (`macro_rules`), and leaves the goals it cannot close (a
failing branch).

The model's leaf lemmas are in `MachCSL/SailROModel.lean` (`currentlyEnabled`
for every extension with a live, total clause, the stateen and privilege
helpers, the CSR dispatchers).
-/
import MachCSL.Lang

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- **Read-only and total**: `b`'s only events are register reads, and every
path (whatever each read answers) ends in a value. -/
inductive SailRO {α : Type} : SailM α → Prop where
  | pure (a : α) : SailRO (FreeM.pure a)
  | read (r : Register) (k : RegisterType r → SailM α) :
      (∀ v, SailRO (k v)) → SailRO (FreeM.impure (.ok (.regRead r)) k)

namespace SailRO

theorem pure' {α : Type} (a : α) : SailRO (Pure.pure a : SailM α) := .pure a

theorem readReg (r : Register) : SailRO (LeanRV64D.readReg r : SailM (RegisterType r)) :=
  .read r _ fun v => .pure v

theorem bind {α β : Type} {m : SailM α} {f : α → SailM β} (hm : SailRO m)
    (hf : ∀ a, SailRO (f a)) : SailRO (m >>= f) := by
  induction hm with
  | pure a => exact hf a
  | read r k _ ih => exact .read r _ fun v => ih v

theorem map {α β : Type} {m : SailM α} (f : α → β) (hm : SailRO m) : SailRO (f <$> m) :=
  bind hm fun a => .pure (f a)

theorem ite {α : Type} {c : Prop} [Decidable c] {a b : SailM α} (ha : c → SailRO a)
    (hb : ¬ c → SailRO b) : SailRO (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem dite {α : Type} {c : Prop} [Decidable c] {a : c → SailM α} {b : ¬ c → SailM α}
    (ha : ∀ h, SailRO (a h)) (hb : ∀ h, SailRO (b h)) : SailRO (if h : c then a h else b h) := by
  split
  · exact ha _
  · exact hb _

end SailRO

/-! ## The prover -/

/-- Leaf lemmas for `sail_ro`: extend with
`macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply my_lemma <;> decide))`. -/
syntax "sail_ro_leaf" : tactic

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| fail "sail_ro_leaf: no leaf lemma applies")

open Lean Elab Tactic Meta in
/-- Unfold the head constant of the computation in a goal `SailRO t`
(for the well-founded definitions the unifier does not see through). -/
elab "sail_ro_unfold" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  unless ty.isAppOfArity ``SailRO 2 do throwError "sail_ro_unfold: not a SailRO goal"
  let arg := ty.appArg!
  let .const n _ := arg.getAppFn | throwError "sail_ro_unfold: no head constant"
  if [``Bind.bind, ``Pure.pure, ``ite, ``dite, ``Functor.map, ``FreeM.pure, ``FreeM.impure,
      ``FreeM.bind].contains n then
    throwError "sail_ro_unfold: plumbing"
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))

/-- **The read-only prover**: close `SailRO t` by the closure rules, the leaf
lemmas, `split` on matches and conditionals, and unfolding.  Goals it cannot
close (a failing branch) are left. -/
macro "sail_ro" : tactic => `(tactic| repeat' (first
  | intro _
  | exact SailRO.pure _
  | exact SailRO.readReg _
  | sail_ro_leaf
  | (apply SailRO.read; intro _)
  | apply SailRO.bind
  | apply SailRO.map
  | apply SailRO.ite
  | apply SailRO.dite
  | split
  | sail_ro_unfold))

end MachCSL
