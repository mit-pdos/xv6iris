/-
MachCSL: **ORDERED KEYS** -- the lawful orders every finite-map / finite-set
key of the weak-memory port needs (gap note `notes/weak-port-iris-gaps.md`,
§G3/G4, "Keys").

Rocq keys `gmap K V` / `gset K` by stdpp's `Countable K` (plus
`EqDecision K`).  The port's finite maps and sets are
`Std.ExtTreeMap K V compare` / `Std.ExtTreeSet K compare` (as
`MachCSL.RegMapF`, `MachCSL.FlatMem`, `MachCSL.StampMap`), and iris-lean's
`PartialMap`/`LawfulFiniteMap` instance for them (`Iris.Std.HeapInstances`)
and `LawfulFiniteSet` instance (`Iris.Std.GenSetsInstances`) ask, of `K`,
for `[Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]`.  This file supplies
that triple for every key type of the Rocq weak files (`Weak*.v`, `Ax*.v`,
`Wk*.v` at `../xv6iris-spinlock/iris`), and the generic constructions the
not-yet-ported weak types will use.

**The key types of the weak files, and where their order comes from**
(counts: `gmap`/`gset` occurrences over the comment-stripped sources):

| Rocq key (uses) | Lean key | order |
|---|---|---|
| `geid = agent * nat` (`gset` 551, `gmap` 167) | `MachCSL.GEid` | `instOrdProdLex` (here) + core's lex laws |
| `register` (Sail's; `gset` 276) | `LeanRV64D.Register` | `instOrdRegister` (here): `ctorIdx`, the key `regIdx` already uses |
| `Arch.pa` (`gmap` 93, `gset` 42) | `MachCSL.PAddr = BitVec 64` | core (`Init.Data.Ord.BitVec`) |
| `Arch.pa` as Sail's `physaddr` | `LeanRV64D.physaddr` | `instOrdPhysaddr` (here): the wrapped bits |
| `Z` (`gset` 54, `gmap` 47) | `Int` | core |
| `nat`, `agent`, `wreg`, `gname` | `Nat`, `MachCSL.Agent`, `Nat`, `Iris.GName` | core |
| `CPU` (`gset` 31) | `MachCSL.CPU = Fin NCPU` | core |
| `mword 27` / `bv n` | `BitVec n` | core |
| `nat * nat` and other pairs | `α × β` | `instOrdProdLex` (here) + core |
| `option A`, `list A` | `Option α`, `List α` | core |
| `A + B` | `α ⊕ β` | `instOrdSum` (here) |
| `unit` | `Unit` | `instOrdPUnit` (here) |

The weak files' OWN types with `EqDecision` instances (`ev`, `tev`, `view`,
`wmsg`, `wresv`, `ident`, `ekey`, `dtag`, `holder`, ...; 22 declarations)
are not keys of any `gmap`/`gset` in those files; when a port does key a map
by one, it should order it by an injection into a key above:
`instance : Ord T := ordOn enc`, `instance : Std.TransOrd T := transOrd_ordOn enc`,
`instance : Std.LawfulEqOrd T := lawfulEqOrd_ordOn enc enc_inj` (the
`Xv6.OffBoxCam` `BoxNames` precedent, generalised).  Their `EqDecision`
itself is `deriving DecidableEq`.

**Porting notes** (spelling, not design):

* `instOrdProdLex` moved here from `MachCSL.CtxBox` (same name, same body,
  `lexOrd`), so that key files need not import the box.  Core declares the
  pair order `lexOrd` and its `TransOrd`/`LawfulEqOrd` instances but does not
  make `lexOrd` an instance.
* Rocq's `Countable` gives `encode : K → positive`; nothing here encodes
  into `Nat` globally (no `Countable` class): the maps only need the order.
-/
import MachCSL.TsoMem
import Iris.Std.HeapInstances
import Iris.Std.GenSetsInstances

namespace MachCSL

open Std LeanRV64D

/-! ## Pairs: the lexicographic order -/

/-- The lexicographic order on pairs (Lean's `lexOrd`), as an instance. -/
instance instOrdProdLex {α β : Type _} [Ord α] [Ord β] : Ord (α × β) := lexOrd

/-! ## Transport along an injection -/

/-- The order on `α` read through `f` (Rocq's `inj_countable'` for orders). -/
@[reducible] def ordOn {α β : Type _} [Ord β] (f : α → β) : Ord α := ⟨compareOn f⟩

theorem transOrd_ordOn {α β : Type _} [Ord β] [TransOrd β] (f : α → β) :
    @TransOrd α (ordOn f) :=
  inferInstanceAs (TransCmp (compareOn f))

theorem lawfulEqOrd_ordOn {α β : Type _} [Ord β] [TransOrd β] [LawfulEqOrd β]
    (f : α → β) (hf : Function.Injective f) : @LawfulEqOrd α (ordOn f) :=
  @LawfulEqCmp.mk α (compareOn f) (inferInstanceAs (ReflCmp (compareOn f)))
    (fun h => hf (LawfulEqOrd.eq_of_compare h))

/-! ## Sums: every `inl` below every `inr` -/

/-- The order on sums: `inl` before `inr`, each side by its own order. -/
def compareSum {α β : Type _} [Ord α] [Ord β] : α ⊕ β → α ⊕ β → Ordering
  | .inl a, .inl a' => compare a a'
  | .inl _, .inr _ => .lt
  | .inr _, .inl _ => .gt
  | .inr b, .inr b' => compare b b'

instance instOrdSum {α β : Type _} [Ord α] [Ord β] : Ord (α ⊕ β) := ⟨compareSum⟩

instance instTransOrdSum {α β : Type _} [Ord α] [Ord β] [TransOrd α] [TransOrd β] :
    TransOrd (α ⊕ β) where
  eq_swap {a b} := by
    cases a <;> cases b <;> simp only [compare, compareSum, Ordering.swap] <;>
      exact OrientedCmp.eq_swap
  isLE_trans {a b c} hab hbc := by
    cases a <;> cases b <;> cases c <;>
      simp only [compare, compareSum, Ordering.isLE] at hab hbc ⊢ <;>
      first | exact TransCmp.isLE_trans hab hbc | trivial | contradiction

instance instLawfulEqOrdSum {α β : Type _} [Ord α] [Ord β] [TransOrd α] [TransOrd β]
    [LawfulEqOrd α] [LawfulEqOrd β] : LawfulEqOrd (α ⊕ β) where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp only [compare, compareSum, reduceCtorEq] at h
    · exact congrArg Sum.inl (LawfulEqOrd.eq_of_compare h)
    · exact congrArg Sum.inr (LawfulEqOrd.eq_of_compare h)

/-! ## The unit type -/

instance instOrdPUnit : Ord PUnit := ⟨fun _ _ => .eq⟩

instance instTransOrdPUnit : TransOrd PUnit where
  eq_swap := rfl
  isLE_trans _ _ := rfl

instance instLawfulEqOrdPUnit : LawfulEqOrd PUnit where
  eq_of_compare _ := rfl

/-! ## Sail's registers and physical addresses -/

theorem Register.ctorIdx_injective : Function.Injective (Register.ctorIdx) := by
  intro a b h
  have := congrArg Register.ofNat h
  simpa [Register.ofNat_ctorIdx] using this

/-- Registers ordered by constructor index (the key `MachCSL.regIdx` of a
hart's register ghost map). -/
instance instOrdRegister : Ord Register := ordOn Register.ctorIdx

instance instTransOrdRegister : TransOrd Register := transOrd_ordOn _

instance instLawfulEqOrdRegister : LawfulEqOrd Register :=
  lawfulEqOrd_ordOn _ Register.ctorIdx_injective

/-- The bits of a Sail physical address. -/
def physaddrBits : physaddr → BitVec 64
  | .Physaddr b => b

theorem physaddrBits_injective : Function.Injective physaddrBits := by
  intro a b h
  cases a; cases b
  cases h
  rfl

instance instOrdPhysaddr : Ord physaddr := ordOn physaddrBits

instance instTransOrdPhysaddr : TransOrd physaddr := transOrd_ordOn _

instance instLawfulEqOrdPhysaddr : LawfulEqOrd physaddr :=
  lawfulEqOrd_ordOn _ physaddrBits_injective

/-! ## The weak files' event identifiers -/

/-- A global event identifier (Rocq `WeakRvwmoGraph.geid := agent * nat`):
the authoring agent and the event's index in that agent's trace. -/
abbrev GEid : Type := Agent × Nat

/-! ## Checks: each key reaches iris-lean's map and set instances -/

section Checks
open Iris.Std

example : LawfulFiniteMap (ExtTreeMap GEid · compare) GEid := inferInstance
example : LawfulFiniteSet (ExtTreeSet GEid compare) GEid := inferInstance
example : LawfulFiniteMap (ExtTreeMap (GEid × GEid) · compare) (GEid × GEid) := inferInstance
example : LawfulFiniteSet (ExtTreeSet Register compare) Register := inferInstance
example : LawfulFiniteMap (ExtTreeMap PAddr · compare) PAddr := inferInstance
example : LawfulFiniteMap (ExtTreeMap physaddr · compare) physaddr := inferInstance
example : LawfulFiniteSet (ExtTreeSet Int compare) Int := inferInstance
example : LawfulFiniteSet (ExtTreeSet CPU compare) CPU := inferInstance
example : LawfulFiniteMap (ExtTreeMap (BitVec 27) · compare) (BitVec 27) := inferInstance
example : LawfulFiniteMap (ExtTreeMap (Nat × Nat) · compare) (Nat × Nat) := inferInstance
example : LawfulFiniteMap (ExtTreeMap (Option (List Nat)) · compare) (Option (List Nat)) :=
  inferInstance
example : LawfulFiniteMap (ExtTreeMap (Nat ⊕ (Bool × Int)) · compare) (Nat ⊕ (Bool × Int)) :=
  inferInstance
example : LawfulFiniteSet (ExtTreeSet Unit compare) Unit := inferInstance
example : DecidableEq (ExtTreeSet GEid compare) := inferInstance

end Checks

end MachCSL
