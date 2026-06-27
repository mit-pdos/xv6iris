/-
PROTOTYPE — free/interaction-monad backing for lean-sail's `PreSailM`.

Goal: prove that redefining lean-sail's monad core as a *free monad* (effects as
data, interposable — what we need for MMIO + multi-HART) keeps the SAME names and
type signatures the generated RISC-V model uses, so the generated model
type-checks against it UNCHANGED.

Design: a polynomial/container free monad (a concrete `Outcome` effect inductive +
a continuation), mirroring the Rocq `Interface.outcome` / `iMon`. This keeps
`Mon … α : Type 0` (so `SailM α : Type 0`, matching EStateM and avoiding universe
friction with the generated model), and `bind` is a *total structural* function
(so we keep equational lemmas for the eventual Iris proofs — unlike `partial`).

This file is standalone (no Iris import); compile with `lake env lean`.

The block marked "VERBATIM" contains function bodies copied *unchanged* from the
generated model (opencompl/sail-riscv-lean). Only the surrounding type
declarations (which are monad-independent) are provided locally.
-/

namespace PreSail

/-! ## Supporting types (verbatim from lean-sail `Sail/Sail.lean`) -/

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
open Error

inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
export Result (Ok Err)

/-! ## The free monad core (replaces `PreSailM := EStateM …`) -/

section Regs

variable {Register : Type} {RegisterType : Register → Type}

/-- The effect signature: every primitive side-effect the generated model can
perform, as *data* (so an interpreter can interpose — route a `memRead` to RAM
points-to, an MMIO device, or an inter-HART shared resource). Mirrors the Rocq
`Interface.outcome`. -/
inductive Outcome (Register : Type) (RegisterType : Register → Type) (ue : Type) where
  | regRead (r : Register)
  | regWrite (r : Register) (v : RegisterType r)
  | readByte (addr : Nat)
  | writeByte (addr : Nat) (v : BitVec 8)
  | choosePrim (p : Primitive)
  | incCycle
  | getCycle
  | printOut (s : String)

/-- The response type each outcome produces. -/
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

/-- The free monad: `pure`, an exception leaf, and `vis` (perform an effect, then
continue). No existential over `Type`, so this stays in `Type 0`. -/
inductive Mon (Register : Type) (RegisterType : Register → Type) (ue : Type) (α : Type) where
  | pure (a : α)
  | throw (e : Error ue)
  | vis (o : Outcome Register RegisterType ue) (k : o.resp → Mon Register RegisterType ue α)

/-- Total, structural `bind` (recurses on the tree; the continuation `k x` is
handled under the `vis` node). Keeping it total means we get `bind`'s equations
definitionally for later proofs. -/
def Mon.bind {α β} :
    Mon Register RegisterType ue α → (α → Mon Register RegisterType ue β) →
    Mon Register RegisterType ue β
  | .pure a, f => f a
  | .throw e, _ => .throw e
  | .vis o k, f => .vis o (fun x => (k x).bind f)

instance : Monad (Mon Register RegisterType ue) where
  pure := .pure
  bind := Mon.bind

/-- `tryCatch` walks the tree and replaces exception leaves via the handler. -/
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

/-- Keep the exact name + 3-parameter shape the generated model abbreviates:
`abbrev SailM := PreSailM RegisterType trivialChoiceSource exception`.
The `ChoiceSource` argument is irrelevant to the free monad (choices become
`choosePrim` effects) but is kept for signature compatibility. -/
abbrev PreSailM (RegisterType : Register → Type) (_c : ChoiceSource) (ue : Type) : Type → Type :=
  Mon Register RegisterType ue

variable {c : ChoiceSource} {ue : Type}

/-! ## The named primitive surface (same signatures as lean-sail, now free-monad) -/

def choose (p : Primitive) : PreSailM RegisterType c ue p.reflect :=
  .vis (.choosePrim p) .pure

def undefined_unit (_ : Unit) : PreSailM RegisterType c ue Unit := pure ()
def undefined_bit (_ : Unit) : PreSailM RegisterType c ue (BitVec 1) := choose .bit
def undefined_bool (_ : Unit) : PreSailM RegisterType c ue Bool := choose .bool
def undefined_int (_ : Unit) : PreSailM RegisterType c ue Int := choose .int
def undefined_nat (_ : Unit) : PreSailM RegisterType c ue Nat := choose .nat
def undefined_string (_ : Unit) : PreSailM RegisterType c ue String := choose .string
def undefined_bitvector (n : Nat) : PreSailM RegisterType c ue (BitVec n) := choose (.bitvector n)
def undefined_vector (n : Nat) (a : α) : PreSailM RegisterType c ue (Vector α n) :=
  pure <| .replicate n a
def undefined_range (low high : Int) : PreSailM RegisterType c ue Int := do
  pure (low + (← choose .int) % (high - low))

def internal_pick {α : Type} : List α → PreSailM RegisterType c ue α
  | [] => .throw .Unreachable
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType c ue PUnit :=
  .vis (.regWrite r v) (fun _ => .pure ⟨⟩)

def readReg (r : Register) : PreSailM RegisterType c ue (RegisterType r) :=
  .vis (.regRead r) .pure

/-- Register references (mirrors lean-sail `RegisterRef`). -/
inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)
export RegisterRef (Reg)

def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α := do
  match reg_ref with | .Reg r => readReg r

def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
    PreSailM RegisterType c ue Unit := do
  match reg_ref with | .Reg r => writeReg r a

def reg_deref (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  readRegRef reg_ref

def assert (p : Bool) (s : String) : PreSailM RegisterType c ue Unit :=
  if p then pure () else throw (.Assertion s)

def sailThrow (e : ue) : PreSailM RegisterType c ue α := throw (.User e)

def sailTryCatch (e : PreSailM RegisterType c ue α) (h : ue → PreSailM RegisterType c ue α) :
    PreSailM RegisterType c ue α :=
  tryCatch e fun err =>
    match err with
    | .User u => h u
    | _ => throw err

/-! ### memory effects (same signatures; route through the `readByte`/`writeByte`
outcomes — the interposition seam). Bodies are monad-generic copies from lean-sail. -/

def writeByte (addr : Nat) (value : BitVec 8) : PreSailM RegisterType c ue PUnit :=
  .vis (.writeByte addr value) (fun _ => .pure ⟨⟩)

def readByte (addr : Nat) : PreSailM RegisterType c ue (BitVec 8) :=
  .vis (.readByte addr) .pure

def writeBytes (addr : Nat) (value : BitVec (8 * n)) : PreSailM RegisterType c ue Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))
  List.forM list (λ (a, v) => writeByte a v)
  pure true

def readBytes (size : Nat) (addr : Nat) :
    PreSailM RegisterType c ue ((BitVec (8 * size)) × Option Bool) :=
  match size with
  | 0 => pure (default, none)
  | 1 => do
    let b ← readByte addr
    have h : 8 * 1 = 8 := rfl
    return (h ▸ b, none)
  | n + 1 => do
    let b ← readByte addr
    let (bytes, bool) ← readBytes n (addr + 1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return (h ▸ bytes.append b, bool)

def cycle_count (_ : Unit) : PreSailM RegisterType c ue Unit := .vis .incCycle (fun _ => .pure ⟨⟩)
def get_cycle_count (_ : Unit) : PreSailM RegisterType c ue Nat := .vis .getCycle .pure

end Regs

/-! ## The early-return submonad (verbatim-compatible with lean-sail) -/

section SailME

variable {Register : Type} {RT : Register → Type}

variable (RT) in
abbrev PreSailME c ue α := ExceptT (Error ue ⊕ α) (PreSailM RT c ue)

instance : MonadExceptOf (Error ue) (PreSailME RT c ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)

def PreSailME.run (m : PreSailME RT c ue α α) : PreSailM RT c ue α := do
  match (← ExceptT.run m) with
    | .error (.inr e) => pure e
    | .error (.inl e) => throw e
    | .ok e => pure e

def PreSailME.throw (e : α) : PreSailME RT c ue α β :=
    MonadExceptOf.throw (Sum.inr (α := Error ue) e)

end SailME

end PreSail


/-! ============================================================================
   THE TEST: real generated model bodies, type-checked against the free monad.
   ============================================================================ -/

namespace LeanRV64DTest

open PreSail
open PreSail.Error

/-- Model registers (subset). Monad-independent — analogous to the model's
`Register` enum + `RegisterType` (Defs.lean). -/
inductive Register where | PC | nextPC | minstret
  deriving DecidableEq

abbrev RegisterType : Register → Type
  | _ => BitVec 64

/-- Model exception type (subset, monad-independent — from the model's `Errors`). -/
inductive exception where
  | Error_not_implemented (s : String)
  | Error_internal_error (s : String)
  | Error_reserved_behavior (s : String)

/-- The exact abbreviation the generated model emits (Defs.lean:2014). -/
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception

open Register

/-- Model `uop` type (monad-independent — BaseInsts.lean). -/
inductive uop where | LUI | AUIPC
open uop

-- ───────────────────────── VERBATIM generated bodies ─────────────────────────
-- copied unchanged from opencompl/sail-riscv-lean; only types above are local.

/-- VERBATIM `encdec_uop_backwards` (BaseInsts.lean) — exercises `do`, `match` on
BitVec literals, `pure`, `assert`, and bare `throw Error.Exit`. -/
def encdec_uop_backwards (arg_ : (BitVec 7)) : SailM uop := do
  match arg_ with
  | 0b0110111 => (pure LUI)
  | 0b0010111 => (pure AUIPC)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

/-- VERBATIM `get_arch_pc` (PcAccess.lean) — `readReg`. -/
def get_arch_pc (_ : Unit) : SailM (BitVec 64) := do
  readReg PC

/-- VERBATIM `tick_pc` (PcAccess.lean) — `readReg` + `writeReg` in sequence. -/
def tick_pc (_ : Unit) : SailM Unit := do
  writeReg PC (← readReg nextPC)

/-- VERBATIM `not_implemented` (Errors.lean) — `sailThrow`. (`k_a` is the model's
generated name for an arbitrary result type.) -/
def not_implemented (message : String) : SailM k_a := do
  sailThrow ((exception.Error_not_implemented message))

/-- VERBATIM `internal_error` (Errors.lean) — `sailThrow` + `HAppend` + `Int.repr`. -/
def internal_error (file : String) (line : Int) (s : String) : SailM k_a := do
  sailThrow ((exception.Error_internal_error
    (HAppend.hAppend file
      (HAppend.hAppend ":" (HAppend.hAppend (Int.repr line) (HAppend.hAppend ": " s))))))

-- ──────────────────── representative synthetic callers ───────────────────────
-- (the real ones have large model-specific dep chains; these exercise the same
--  primitives the model uses through them.)

/-- Memory effect path: `readBytes`/`writeBytes` (→ `readByte`/`writeByte`
outcomes), as the model's `read_ram`/`sail_mem_read` use. -/
def load_dword (addr : Nat) : SailM (BitVec 64) := do
  let (bytes, _) ← readBytes 8 addr
  pure bytes

/-- Early-return path: `SailME.run` + `SailME.throw` + `readReg`, as the model's
`fetch` uses. -/
def fetch_pc_or_zero : SailM (BitVec 64) := PreSailME.run do
  let pc ← (show SailM (BitVec 64) from readReg PC)
  if pc == 0#64 then
    PreSailME.throw ((0#64) : BitVec 64)
  pure pc

end LeanRV64DTest

-- The whole point: every definition above elaborated against the free monad.
#check @LeanRV64DTest.encdec_uop_backwards
#check @LeanRV64DTest.load_dword
#check @LeanRV64DTest.fetch_pc_or_zero
