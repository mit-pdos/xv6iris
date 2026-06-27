/-
The interpreter over the Sail free monad — the analog of Rocq's
`RiscvLang.run` (relational) and `RiscvExec.exec` (functional).

Machine state `MState` holds the register and byte-memory maps (kept as total
functions into `Option` here — the Iris `gen_heap` layer authoritatively owns
them). `exec` runs a `Mon` computation against a state, resolving effects:
register/memory reads/writes hit the maps; `choosePrim` is resolved
deterministically by `trivialChoiceSource` (matching the model's `SailM`).

Because choices are resolved deterministically, `exec` is a partial *function*
(no separate relational/functional split is needed, unlike Rocq whose free monad
had genuine `Choose` nondeterminism). `run` is the graph of `exec`, kept for the
Iris `primStep`.
-/
module

public import Xv6Iris.SailMonad

@[expose] public section

namespace Xv6Iris.Sail

/-- Machine state: dependent register map + byte memory. (The cycle counter and
output are dropped for now; added back when needed.) -/
structure MState (Register : Type) (RegisterType : Register → Type) where
  regs : (r : Register) → Option (RegisterType r)
  mem : Nat → Option (BitVec 8)

namespace MState
variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register]

/-- Update one register. -/
def setReg (s : MState Register RegisterType) (r : Register) (v : RegisterType r) :
    MState Register RegisterType :=
  { s with regs := fun r' => if h : r' = r then some (h ▸ v) else s.regs r' }

/-- Update one memory byte. -/
def setMem (s : MState Register RegisterType) (a : Nat) (b : BitVec 8) :
    MState Register RegisterType :=
  { s with mem := fun a' => if a' = a then some b else s.mem a' }

end MState

section Exec
variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register]
variable {ue : Type} {c : ChoiceSource}

/-- Functional interpreter: run `m` from state `s`, returning the result and the
final state, or `none` if it gets stuck (missing register/byte, or `throw`). -/
def exec {α} : Mon Register RegisterType ue α → MState Register RegisterType →
    Option (α × MState Register RegisterType)
  | .pure a, s => some (a, s)
  | .throw _, _ => none
  | .vis o k, s =>
    match o with
    | .regRead r => match s.regs r with
        | some v => exec (k v) s
        | none => none
    | .regWrite r v => exec (k ()) (s.setReg r v)
    | .readByte a => match s.mem a with
        | some b => exec (k b) s
        | none => none
    | .writeByte a b => exec (k ()) (s.setMem a b)
    | .choosePrim p => exec (k (trivialChoiceSource.choose p ())) s
    | .incCycle => exec (k ()) s
    | .getCycle => exec (k 0) s
    | .printOut _ => exec (k ()) s

/-- The relational twin (graph of `exec`), used for the Iris `primStep`. -/
def run {α} (m : Mon Register RegisterType ue α) (s : MState Register RegisterType)
    (a : α) (s' : MState Register RegisterType) : Prop :=
  exec m s = some (a, s')

/-- `exec` determines `run` (determinism is immediate here). -/
theorem run_iff_exec {α} {m : Mon Register RegisterType ue α} {s a s'} :
    run m s a s' ↔ exec m s = some (a, s') := Iff.rfl

theorem run_deterministic {α} {m : Mon Register RegisterType ue α} {s a₁ s₁ a₂ s₂}
    (h₁ : run m s a₁ s₁) (h₂ : run m s a₂ s₂) :
    a₁ = a₂ ∧ s₁ = s₂ := by
  unfold run at h₁ h₂
  rw [h₁] at h₂
  have h := Option.some.inj h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Exec

end Xv6Iris.Sail
