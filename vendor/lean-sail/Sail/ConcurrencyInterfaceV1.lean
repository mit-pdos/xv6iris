/-
The Sail concurrency interface (version 1) as a FREE / INTERACTION MONAD.

This file replaces upstream lean-sail's `EStateM`-based `PreSailM` with a
free monad over an explicit `Outcome` effect type, in the style of the Sail
Rocq backend's `Interface.outcome` / `iMon`.  A Sail computation is then a
tree whose nodes are the register / memory / trace events the model emits,
and an external semantics (an Iris language, an emulator, ...) interprets
those events one at a time.  This is what MachCSL's per-event operational
semantics needs: the hart's expression *is* the remaining monad tree.

The surface (names, signatures, `simp_sail` tags) is kept identical to
upstream so that Sail's Lean backend output type-checks unchanged.  The
`ChoiceSource` argument of `PreSailM` is vestigial (nondeterminism is now a
`choose` event) but kept for signature compatibility.

A reference interpreter into the upstream `SequentialState` is provided at the
end (`PreSailM.interp`), so the generated model still runs as an executable.
-/
import Sail.Attr
import Sail.Common
import Sail.ArchSem

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

namespace Sail.ConcurrencyInterfaceV1

open Sail.ArchSem (FreeM Effect)

structure ChoiceSource where
  (α : Type)
  (nextState : Sail.Primitive → α → α)
  (choose : ∀ p : Sail.Primitive, α → p.reflect)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

class Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

inductive Access_variety where
  | AV_plain
  | AV_exclusive
  | AV_atomic_rmw
  deriving Inhabited, DecidableEq, Repr

export Access_variety (AV_plain AV_exclusive AV_atomic_rmw)

inductive Access_strength where
  | AS_normal
  | AS_rel_or_acq
  | AS_acq_rcpc
  deriving Inhabited, DecidableEq, Repr

export Access_strength(AS_normal AS_rel_or_acq AS_acq_rcpc)

structure Explicit_access_kind where
  variety : Access_variety
  strength : Access_strength
deriving Repr

inductive Access_kind (arch : Type) where
  | AK_explicit (_ : Explicit_access_kind)
  | AK_ifetch (_ : Unit)
  | AK_ttw (_ : Unit)
  | AK_arch (_ : arch)
  deriving Inhabited, Repr

export Access_kind(AK_explicit AK_ifetch AK_ttw AK_arch)


structure Mem_read_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  tag : Bool
  deriving Inhabited, Repr

structure Mem_write_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  value : (Option (BitVec (8 * n)))
  tag : (Option Bool)
  deriving Inhabited, Repr

end Sail.ConcurrencyInterfaceV1

namespace Sail.ConcurrencyInterfaceV1

open Sail (Result)
open Sail.ArchSem (FreeM Effect)

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

/-! ## The event type

One constructor per kind of event the Sail model can emit through the
concurrency interface (compare `Interface.outcome` in the Rocq backend).
The `ret` function gives the type of the value the environment answers with.
-/

/-- The observable events of a Sail computation. -/
inductive Outcome (Register : Type) (RegisterType : Register → Type) [Arch] : Type where
  | regRead (r : Register)
  | regWrite (r : Register) (v : RegisterType r)
  | memRead (n vasize : Nat)
      (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak)
  | memWrite (n vasize : Nat)
      (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak)
  /-- legacy direct RAM access (`read_ram` builtin); never emitted by models
  that go through `sail_mem_read` -/
  | readRam (addr_size data_size : Nat) (addr : BitVec addr_size)
  | writeRam (addr_size data_size : Nat) (addr : BitVec addr_size) (value : BitVec (8 * data_size))
  | barrier (b : Arch.barrier)
  | cacheOp (op : Arch.cache_op)
  | tlbi (op : Arch.tlb_op)
  | translationStart (ts : Arch.trans_start)
  | translationEnd (te : Arch.trans_end)
  | takeException (f : Arch.fault)
  | returnException (pa : Arch.pa)
  | cycleCount
  | getCycleCount
  | message (msg : String)
  | choose (p : Sail.Primitive)

section
variable [Arch]

/-- The type of the environment's answer to each event. -/
abbrev Outcome.ret : Outcome Register RegisterType → Type
  | .regRead r => RegisterType r
  | .regWrite _ _ => PUnit
  | .memRead n _ _ => Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort
  | .memWrite _ _ _ => Result (Option Bool) Arch.abort
  | .readRam _ data_size _ => BitVec (8 * data_size)
  | .writeRam _ _ _ _ => Unit
  | .barrier _ => Unit
  | .cacheOp _ => Unit
  | .tlbi _ => Unit
  | .translationStart _ => Unit
  | .translationEnd _ => Unit
  | .takeException _ => Unit
  | .returnException _ => Unit
  | .cycleCount => Unit
  | .getCycleCount => Nat
  | .message _ => Unit
  | .choose p => p.reflect

instance : Effect (Outcome Register RegisterType) where
  ret := Outcome.ret

/-- The effect type of `PreSailM`: an event, or an uncatchable-by-the-model
failure (`Sail.Error`) with no continuation. -/
abbrev Eff (RegisterType : Register → Type) (ue : Type) :=
  Except (Sail.Error ue) (Outcome Register RegisterType)

/-- The Sail monad: a free monad over `Eff`.  The `ChoiceSource` argument is
unused (nondeterminism is the `choose` event) and kept for compatibility. -/
abbrev PreSailM (RegisterType : Register → Type) (_c : ChoiceSource) (ue : Type) : Type → Type :=
  FreeM.{0, 0, 0} (Eff RegisterType ue)

variable (RegisterType) in
abbrev PreSailME c ue α := ExceptT (Sail.Error ue ⊕ α) (PreSailM RegisterType c ue)

end

/-- The executable state of the reference interpreter (as upstream). -/
structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.ExtDHashMap Register RegisterType
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)
export RegisterRef (Reg)

/-! ## Generic free-monad facts -/

namespace FreeMLemmas
open Sail.ArchSem

variable {E : Type} [Effect E]

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

instance : LawfulMonad (FreeM E) := LawfulMonad.mk'
  (id_map := fun x => by
    show x.bind (fun a => FreeM.pure a) = x
    exact bind_pure_right x)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := bind_assoc)

end FreeMLemmas

namespace PreSail

open Sail.ArchSem (FreeM Effect)

variable [Arch]

/-- Emit one event and return the environment's answer. -/
@[simp_sail]
def emit (o : Outcome Register RegisterType) : PreSailM RegisterType c ue o.ret :=
  FreeM.impure (Eff := Eff RegisterType ue) (.ok o) (fun r => FreeM.pure r)

/-- Fail: a node with no continuation (the model is stuck). -/
@[simp_sail]
def fail (e : Sail.Error ue) : PreSailM RegisterType c ue α :=
  FreeM.impure (Eff := Eff RegisterType ue) (.error e) (fun r => nomatch r)

/-- Catch every failure (used for `MonadExcept`). -/
def tryCatchAll (e : PreSailM RegisterType c ue α) (h : Sail.Error ue → PreSailM RegisterType c ue α) :
    PreSailM RegisterType c ue α :=
  match e with
  | .pure a => .pure a
  | .impure (.error err) _ => h err
  | .impure (.ok o) k => .impure (.ok o) (fun r => tryCatchAll (k r) h)

instance : MonadExceptOf (Sail.Error ue) (PreSailM RegisterType c ue) where
  throw := fail
  tryCatch := tryCatchAll

/-- Catch only user exceptions, as Sail's `try ... catch` does. -/
@[simp_sail]
def sailTryCatch (e : PreSailM RegisterType c ue α) (h : ue → PreSailM RegisterType c ue α) :
    PreSailM RegisterType c ue α :=
  match e with
  | .pure a => .pure a
  | .impure (.error (.User u)) _ => h u
  | .impure (.error err) _ => fail err
  | .impure (.ok o) k => .impure (.ok o) (fun r => sailTryCatch (k r) h)

@[simp_sail]
def sailThrow (e : ue) : PreSailM RegisterType c ue α := fail (.User e)

def choose (p : Sail.Primitive) : PreSailM RegisterType c ue p.reflect :=
  emit (.choose p)

def undefined_unit (_ : Unit) : PreSailM RegisterType c ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM RegisterType c ue (BitVec 1) :=
  choose .bit

def undefined_bool (_ : Unit) : PreSailM RegisterType c ue Bool :=
  choose .bool

def undefined_int (_ : Unit) : PreSailM RegisterType c ue Int :=
  choose .int

def undefined_range (low high : Int) : PreSailM RegisterType c ue Int := do
  pure (low + (← choose .int) % (high - low))

def undefined_nat (_ : Unit) : PreSailM RegisterType c ue Nat :=
  choose .nat

def undefined_string (_ : Unit) : PreSailM RegisterType c ue String :=
  choose .string

def undefined_bitvector (n : Nat) : PreSailM RegisterType c ue (BitVec n) :=
  choose <| .bitvector n

def undefined_vector (n : Nat) (a : α) : PreSailM RegisterType c ue (Vector α n) :=
  pure <| .replicate n a

def internal_pick {α : Type} : List α → PreSailM RegisterType c ue α
  | [] => fail .Unreachable
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

@[simp_sail]
def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType c ue PUnit :=
  emit (.regWrite r v)

@[simp_sail]
def readReg (r : Register) : PreSailM RegisterType c ue (RegisterType r) :=
  emit (.regRead r)

@[simp_sail]
def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  match reg_ref with | .Reg r => readReg r

@[simp_sail]
def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
  PreSailM RegisterType c ue Unit :=
  match reg_ref with | .Reg r => writeReg r a

@[simp_sail]
def reg_deref (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  readRegRef reg_ref

@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM RegisterType c ue Unit :=
  if p then pure () else fail (.Assertion s)

@[simp_sail]
def write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    PreSailM RegisterType c ue Unit :=
  emit (.writeRam addr_size data_size addr value)

@[simp_sail]
def read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) :
    PreSailM RegisterType c ue (BitVec (8 * data_size)) :=
  emit (.readRam addr_size data_size addr)

@[simp_sail]
def sail_mem_write (req : Mem_write_request n vasize Arch.pa Arch.translation Arch.arch_ak) :
    PreSailM RegisterType c ue (Result (Option Bool) Arch.abort) :=
  emit (.memWrite n vasize req)

@[simp_sail]
def sail_mem_read (req : Mem_read_request n vasize Arch.pa Arch.translation Arch.arch_ak) :
    PreSailM RegisterType c ue (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) :=
  emit (.memRead n vasize req)

@[simp_sail]
def sail_barrier (b : Arch.barrier) : PreSailM RegisterType c ue Unit := emit (.barrier b)
@[simp_sail]
def sail_cache_op (op : Arch.cache_op) : PreSailM RegisterType c ue Unit := emit (.cacheOp op)
@[simp_sail]
def sail_tlbi (op : Arch.tlb_op) : PreSailM RegisterType c ue Unit := emit (.tlbi op)
@[simp_sail]
def sail_translation_start (ts : Arch.trans_start) : PreSailM RegisterType c ue Unit :=
  emit (.translationStart ts)
@[simp_sail]
def sail_translation_end (te : Arch.trans_end) : PreSailM RegisterType c ue Unit :=
  emit (.translationEnd te)
@[simp_sail]
def sail_take_exception (f : Arch.fault) : PreSailM RegisterType c ue Unit :=
  emit (.takeException f)
@[simp_sail]
def sail_return_exception (pa : Arch.pa) : PreSailM RegisterType c ue Unit :=
  emit (.returnException pa)

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM RegisterType c ue Unit := emit .cycleCount

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM RegisterType c ue Nat := emit .getCycleCount

def print_effect (str : String) : PreSailM RegisterType c ue Unit := emit (.message str)

def print_int_effect (str : String) (n : Int) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{Sail.BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}\n"

@[simp_sail]
def sailTryCatchE (e : ExceptT β (PreSailM RegisterType c ue) α)
    (h : ue → ExceptT β (PreSailM RegisterType c ue) α) : ExceptT β (PreSailM RegisterType c ue) α :=
  ExceptT.mk (sailTryCatch (ExceptT.run e) (fun u => ExceptT.run (h u)))

section SailME

variable {Register : Type} {RT : Register → Type} [DecidableEq Register] [Hashable Register]

instance : MonadExceptOf (Sail.Error ue) (PreSailME RT c ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)

def PreSailME.run (m : PreSailME RT c ue α α) : PreSailM RT c ue α := do
  match (← ExceptT.run m) with
    | .error (.inr e) => pure e
    | .error (.inl e) => throw e
    | .ok e => pure e

def _root_.ExceptT.map_error [Monad m] (e : ExceptT ε m α) (f : ε → ε') : ExceptT ε' m α :=
  ExceptT.mk <| do
    match ← e.run with
    | .ok x => pure $ .ok x
    | .error e => pure $ .error (f e)

instance [∀ x, CoeT α x α'] :
    CoeT (PreSailME RT c ue α β) e (PreSailME RT c ue α' β) where
  coe := e.map_error (fun x => match x with | .inl e => .inl e | .inr e => .inr e)

def PreSailME.throw (e : α) : PreSailME RT c ue α β :=
    MonadExceptOf.throw (Sum.inr (α := Sail.Error ue) e)

instance : Inhabited (SequentialState RT trivialChoiceSource) where
  default := ⟨default, (), default, default, default, default⟩

end SailME

/-! ## The reference interpreter

Answers every event against a `SequentialState`, exactly as upstream's
`EStateM` primitives did.  Used to run the generated model as a program. -/

section Interp

variable {c : ChoiceSource}

abbrev SeqM (RegisterType : Register → Type) (c : ChoiceSource) (ue : Type) :=
  EStateM (Sail.Error ue) (SequentialState RegisterType c)

def SeqM.writeByte (addr : Nat) (value : BitVec 8) : SeqM RegisterType c ue PUnit :=
  modify fun s => { s with mem := s.mem.insert addr value }

def SeqM.writeBytes (addr : Nat) (value : BitVec (8 * n)) : SeqM RegisterType c ue Unit := do
  let list := List.ofFn (fun i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))
  List.forM list (fun (a, v) => SeqM.writeByte a v)

def SeqM.readByte (addr : Nat) : SeqM RegisterType c ue (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

def SeqM.readBytes (size : Nat) (addr : Nat) : SeqM RegisterType c ue (BitVec (8 * size)) :=
  match size with
  | 0 => pure default
  | 1 => do
    let b ← SeqM.readByte addr
    have h : 8 * 1 = 8 := rfl
    return h ▸ b
  | n + 1 => do
    let b ← SeqM.readByte addr
    let bytes ← SeqM.readBytes n (addr+1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return h ▸ bytes.append b

/-- Interpret one event against the sequential state.  Memory requests are
served only when `Arch.pa` is a bitvector of physical addresses, which the
caller supplies via `paToNat`. -/
def interpOutcome (paToNat : Arch.pa → Nat) (o : Outcome Register RegisterType) :
    SeqM RegisterType c ue o.ret :=
  match o with
  | .regRead r => do
    let .some v := (← get).regs.get? r
      | throw .Unreachable
    pure v
  | .regWrite r v => modify fun s => { s with regs := s.regs.insert r v }
  | .memRead n _ req => do
    let v ← SeqM.readBytes n (paToNat req.pa)
    pure (.Ok (v, none))
  | .memWrite _ _ req => do
    match req.value with
    | some v => SeqM.writeBytes (paToNat req.pa) v
    | none => pure ()
    pure (.Ok (some true))
  | .readRam _ data_size addr => SeqM.readBytes data_size addr.toNat
  | .writeRam _ _ addr value => SeqM.writeBytes addr.toNat value
  | .barrier _ | .cacheOp _ | .tlbi _ | .translationStart _ | .translationEnd _
  | .takeException _ | .returnException _ => pure ()
  | .cycleCount => modify fun s => { s with cycleCount := s.cycleCount + 1 }
  | .getCycleCount => do pure (← get).cycleCount
  | .message msg => modify fun s => { s with sailOutput := s.sailOutput.push msg }
  | .choose p => modifyGet
      (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState p σ.choiceState }))

def _root_.Sail.ConcurrencyInterfaceV1.PreSailM.interp (paToNat : Arch.pa → Nat) :
    PreSailM RegisterType c ue α → SeqM RegisterType c ue α :=
  FreeM.liftM (fun
    | .error err => throw err
    | .ok o => interpOutcome paToNat o)

end Interp

end Sail.ConcurrencyInterfaceV1.PreSail
