/-
The Sail free/interaction monad (module-system version of `proto/SailFree.lean`).

This is the substrate the generated RISC-V model will (after the lean-sail fork)
be expressed in, and that the Iris layer interprets. A polynomial/container free
monad: effects are *data* (`Outcome`), so an interpreter can interpose on them
(RAM points-to vs MMIO device vs inter-HART shared memory). Mirrors the Rocq
`Interface.outcome` / `iMon`.

`Mon … α : Type 0`; `bind` is total + structural (definitional equations kept).
-/
module

public import Iris.BI

@[expose] public section

namespace Xv6Iris.Sail

/-! ## Supporting types (from lean-sail `Sail/Sail.lean`) -/

inductive Primitive where
  | bool | bit | int | nat | string | fin (n : Nat) | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | .bool => Bool
  | .bit => BitVec 1
  | .int => Int
  | .nat => Nat
  | .string => String
  | .fin n => Fin (n + 1)
  | .bitvector n => BitVec n

structure ChoiceSource where
  (α : Type)
  (nextState : Primitive → α → α)
  (choose : ∀ p : Primitive, α → p.reflect)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false | .bit => 0 | .int => 0 | .nat => 0
    | .string => "" | .fin _ => 0 | .bitvector _ => 0

inductive Error (ue : Type) where
  | Exit
  | Unreachable
  | OutOfMemoryRange (n : Nat)
  | Assertion (s : String)
  | User (e : ue)

/-! ## The free monad core -/

section Core
variable {Register : Type} {RegisterType : Register → Type} {ue : Type}

/-- The effect signature, as data — the interposition seam. -/
inductive Outcome (Register : Type) (RegisterType : Register → Type) (ue : Type) where
  | regRead (r : Register)
  | regWrite (r : Register) (v : RegisterType r)
  | readByte (addr : Nat)
  | writeByte (addr : Nat) (v : BitVec 8)
  | choosePrim (p : Primitive)
  | incCycle
  | getCycle
  | printOut (s : String)

abbrev Outcome.resp {Register RegisterType ue} :
    Outcome Register RegisterType ue → Type
  | .regRead r => RegisterType r
  | .regWrite _ _ => Unit
  | .readByte _ => BitVec 8
  | .writeByte _ _ => Unit
  | .choosePrim p => p.reflect
  | .incCycle => Unit
  | .getCycle => Nat
  | .printOut _ => Unit

/-- The free monad: `pure`, an exception leaf, and `vis` (perform an effect then
continue). Polynomial functor ⇒ stays in `Type 0`. -/
inductive Mon (Register : Type) (RegisterType : Register → Type) (ue : Type) (α : Type) where
  | pure (a : α)
  | throw (e : Error ue)
  | vis (o : Outcome Register RegisterType ue) (k : o.resp → Mon Register RegisterType ue α)

/-- Total, structural `bind`. -/
def Mon.bind {α β} :
    Mon Register RegisterType ue α → (α → Mon Register RegisterType ue β) →
    Mon Register RegisterType ue β
  | .pure a, f => f a
  | .throw e, _ => .throw e
  | .vis o k, f => .vis o (fun x => (k x).bind f)

instance : Monad (Mon Register RegisterType ue) where
  pure := .pure
  bind := Mon.bind

def Mon.tryCatchErr {α} :
    Mon Register RegisterType ue α → (Error ue → Mon Register RegisterType ue α) →
    Mon Register RegisterType ue α
  | .pure a, _ => .pure a
  | .throw e, h => h e
  | .vis o k, h => .vis o (fun x => (k x).tryCatchErr h)

instance : MonadExceptOf (Error ue) (Mon Register RegisterType ue) where
  throw e := .throw e
  tryCatch := Mon.tryCatchErr

instance : Inhabited (Mon Register RegisterType ue α) := ⟨.throw .Unreachable⟩

/-- Keeps the model's abbreviation shape: `SailM := PreSailM RegisterType
trivialChoiceSource exception`. -/
abbrev PreSailM (RegisterType : Register → Type) (_c : ChoiceSource) (ue : Type) :
    Type → Type := Mon Register RegisterType ue

/-! ### the named primitive surface (matching lean-sail signatures)

The free monad ignores the `ChoiceSource` (choices are `choosePrim` effects), so
the primitives return `Mon …` directly rather than carrying a phantom `c`
implicit. `Mon … = PreSailM RegisterType c ue …` definitionally for any `c`, so
generated model code (which annotates results as `SailM = PreSailM … _ …`) still
type-checks against these. -/

def choose (p : Primitive) : Mon Register RegisterType ue p.reflect := .vis (.choosePrim p) .pure

def writeReg (r : Register) (v : RegisterType r) : Mon Register RegisterType ue PUnit :=
  .vis (.regWrite r v) (fun _ => .pure ⟨⟩)

def readReg (r : Register) : Mon Register RegisterType ue (RegisterType r) :=
  .vis (.regRead r) .pure

def writeByte (addr : Nat) (value : BitVec 8) : Mon Register RegisterType ue PUnit :=
  .vis (.writeByte addr value) (fun _ => .pure ⟨⟩)

def readByte (addr : Nat) : Mon Register RegisterType ue (BitVec 8) := .vis (.readByte addr) .pure

def assert (p : Bool) (s : String) : Mon Register RegisterType ue Unit :=
  if p then pure () else throw (.Assertion s)

def sailThrow (e : ue) : Mon Register RegisterType ue α := throw (.User e)

def sailTryCatch (e : Mon Register RegisterType ue α) (h : ue → Mon Register RegisterType ue α) :
    Mon Register RegisterType ue α :=
  tryCatch e fun err => match err with | .User u => h u | _ => throw err

end Core

end Xv6Iris.Sail
