import Sail.ArchSem

import Std.Data.ExtHashMap

namespace Sail.ArchSem

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

structure SequentialState (RegisterType : Register → Type) /- (c : ChoiceSource) -/ where
  regs : Std.ExtDHashMap Register RegisterType
  -- choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run
  deriving Inhabited

open Sail.ArchSem
variable [Arch]

abbrev M ue ty := EStateM (Sail.Error ue) (SequentialState Arch.register_type) ty

variable {ue : Type}

def writeByte (addr : Nat) (value : BitVec 8) : M ue PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }

def writeBytes (addr : Nat) (value : BitVec (8 * n)) : M ue PUnit := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))
  List.forM list (λ (a, v) => writeByte a v)

def readByte (addr : Nat) : M ue (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

def readBytes (size : Nat) (addr : Nat) : M ue (BitVec (8 * size)) :=
  match size with
  | 0 => pure default
  | 1 => do
    let b ← readByte addr
    have h : 8 * 1 = 8 := rfl
    return h ▸ b
  | n + 1 => do
    let b ← readByte addr
    let bytes ← readBytes n (addr+1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return h ▸ bytes.append b

def interpretInstructionEffect : (eff : InstructionEffect) → M ue eff.ret
  | .regRead reg _accessType => do
    let .some s := (← get).regs.get? reg
      | throw .Unreachable
    pure s
  | .regWrite reg _racc value =>
    modify fun s => {s with regs := s.regs.insert reg value}
  | .memRead req => do
    if req.numTag != 0 then throw (.Assertion "Tagged memory not supported")
    let addr := req.address.toNat
    let value ← readBytes req.size addr
    pure (.ok (value, BitVec.zero req.numTag))
  | .memWriteAnnounce _memReq => pure ()
  | .memWrite req value _tags => do
    if req.numTag != 0 then throw (.Assertion "Tagged memory not supported")
    let addr := req.address.toNat
    writeBytes addr value
    pure (.ok ())
  | .barrier _barrier => pure ()
  | .clockCycle => modify (fun s => { s with cycleCount := s.cycleCount + 1 })
  | .getCycleCount => do pure (← get).cycleCount
  | .printMessage msg => modify fun s ↦ { s with sailOutput := s.sailOutput.push msg }
  | .archException _exception
  | .cacheOp _op
  | .tlbOp _op
  | .translationStart _translationStart
  | .translationEnd _translationEnd
  | .returnException => pure ()

def interpretSailEffects : PreSailM ue ty → M ue ty :=
  FreeM.liftM (fun
    | .inl (.error err) => throw err
    | .inl (.ok eff) => interpretInstructionEffect eff
    | .inr choice => if h : (0 : Nat) < choice then pure (⟨0, h⟩ : Fin choice) else throw .Unreachable)

def main_of_sail_main (initialState : SequentialState Arch.register_type)
    (main : Unit → PreSailM ue Unit) : IO UInt32 := do
  let res := main () |> interpretSailEffects |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

end Sail.ArchSem
