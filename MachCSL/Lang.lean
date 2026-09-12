/-
MachCSL: the operational semantics of a RISC-V machine as an Iris language.

A machine is a fixed set of harts (`CPU`) sharing one byte-addressed memory.
Each hart runs the Sail RISC-V model, one *event* at a time: a hart's
expression `Expr.hart cpu m` carries the in-flight Sail computation `m` (a
free monad over the concurrency-interface events), and a primitive step
consumes exactly one event of `m` -- a register read/write, a memory
read/write, a trace event, a nondeterministic choice -- or, at the cycle
boundary (`m = pure ()`), restarts the model's fetch/decode/execute cycle.

This mirrors the Rocq MachCSL prototype's `HartE gen cpu m` / `mnode_step`
design (claude-notes/design/main-cycle-port.md there): control state inside an
instruction is model-defined and lives in the expression; inter-instruction
control (PC, registers, memory) is memory-defined and lives in the state.

Eras (the Rocq prototype's generations, claude-notes/design/crash.md there):
the machine can lose power and be powered on again.  The global state carries
the current *generation* `gen` and the power bit `pow`; a hart expression
`Expr.hart gen cpu m` names the generation it belongs to and is *live* only
while the power is on and its generation is current.  A live hart takes real
steps; a hart of a dead generation only self-loops (the "corpse" arm), so it
needs no resources and can be dropped from any proof.  The power thread
`Expr.power` is the one expression with observable arms: `PowerOff` bumps the
generation and clears the power bit; `PowerOn` resets the machine to the boot
image and forks the new generation's harts.  Both are observed
(`Obs.powerOff` / `Obs.powerOn`), so a trace property can segment the run by
power cycle.

Shared memory is the TSO machine of `MachCSL.TsoMem` (the Rocq prototype's
`mnode_step`): per-byte write histories, per-hart data and instruction views,
per-hart read side, reservations for exclusive accesses.  What is deliberately
NOT here yet: devices (UART/PLIC/disk) and MMIO, and the disk as a bus master.
-/
import Sail
import LeanRV64D
import MachCSL.Platform
import MachCSL.TsoMem
import Iris.ProgramLogic.Language

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-! ## Machine state -/

/-- A hart's register file: every Sail register, at its own type. -/
abbrev RegFile := (r : Register) → RegisterType r

/-- Update one register of a register file. -/
def RegFile.set (f : RegFile) (r : Register) (v : RegisterType r) : RegFile :=
  fun r' => if h : r' = r then h ▸ v else f r'

@[simp] theorem RegFile.set_same (f : RegFile) (r : Register) (v : RegisterType r) :
    f.set r v r = v := by
  simp [RegFile.set]

theorem RegFile.set_other (f : RegFile) (r r' : Register) (v : RegisterType r) (h : r' ≠ r) :
    f.set r v r' = f r' := by
  simp [RegFile.set, h]

/-- The global machine state: one register file per hart, and the shared
memory of `MachCSL.TsoMem`: the byte histories, the author log (its length is
the top of the store order), each hart's data view (floor), instruction view,
read side and reservation. -/
structure MState where
  regs : CPU → RegFile
  mem : FlatMem
  log : List Agent
  tv : CPU → Nat
  itv : CPU → Nat
  hr : CPU → HRead
  resv : CPU → Option Resv

/-- The top of the store order: the timestamp of the latest store. -/
abbrev MState.top (σ : MState) : Nat := σ.log.length

/-- Update one register of one hart. -/
abbrev MState.setReg (σ : MState) (cpu : CPU) (r : Register) (v : RegisterType r) : MState :=
  { σ with regs := fun c => if c = cpu then (σ.regs cpu).set r v else σ.regs c }

/-- Update one hart's entry of a per-hart map. -/
abbrev updCpu {α : Type} (f : CPU → α) (cpu : CPU) (x : α) : CPU → α :=
  fun c => if c = cpu then x else f c

/-- After a plain load of `n` bytes at `pa` at view `tvn`: the read side moves,
nothing else. -/
noncomputable abbrev MState.afterLoad (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat)
    (tvn : Nat) : MState :=
  { σ with hr := updCpu σ.hr cpu ((σ.hr cpu).afterLoad pa n tvn) }

/-- After an exclusive read of `w` at `pa`: the watermark to the top, the
floor to the top iff an acquire, the acquire bit recorded, the snapshot
reserved. -/
abbrev MState.afterExcl (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (acq : Bool) : MState :=
  { σ with tv := updCpu σ.tv cpu (if acq then σ.top else σ.tv cpu),
           hr := updCpu σ.hr cpu ((σ.hr cpu).afterExcl σ.top acq),
           resv := updCpu σ.resv cpu (some (snapOf pa n w)) }

/-- A blocked exclusive read abandons the hart's own reservation. -/
abbrev MState.dropResv (σ : MState) (cpu : CPU) : MState :=
  { σ with resv := updCpu σ.resv cpu none }

/-- After a store of `w` at `pa` by `cpu`: the bytes' histories grow, the
author log grows, the floor passes the store iff it is the write half of an
acquire pair, the acquire bit and the reservation clear. -/
abbrev MState.store (σ : MState) (cpu : CPU) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (excl : Bool) : MState :=
  { σ with mem := σ.mem.writeBytes pa n w (σ.top + 1) (hartAgent cpu),
           log := σ.log ++ [hartAgent cpu],
           tv := updCpu σ.tv cpu (if excl && (σ.hr cpu).acq then σ.top + 1 else σ.tv cpu),
           hr := updCpu σ.hr cpu (σ.hr cpu).clearAcq,
           resv := updCpu σ.resv cpu none }

/-- After a fence: the floor per `fencePost`; `fence.i` raises the
instruction view past the floor and the hart's own last store. -/
abbrev MState.fence (σ : MState) (cpu : CPU) (b : barrier_kind) : MState :=
  let pub := ownPub (hartAgent cpu) σ.log
  let tv' := fencePost (fenceDrains b) (fenceAcq b) (σ.tv cpu) (σ.hr cpu).rv pub
  { σ with tv := updCpu σ.tv cpu tv',
           itv := updCpu σ.itv cpu
             (if fenceIfetch b then max (σ.itv cpu) (fencePost true false (σ.tv cpu) (σ.hr cpu).rv pub)
              else σ.itv cpu) }

/-! ## One cycle of the model -/

/-- One fetch/decode/execute cycle of the Sail model, optionally followed by
a clock tick.  The model's own `loop` ticks the clock every
`plat_insns_per_tick` instructions; the language has no instruction counter,
so the tick is chosen nondeterministically at each cycle boundary (a sound
weakening, exactly as in the Rocq prototype). -/
noncomputable def riscvStep (tick : Bool) : SailM Unit := do
  let _ ← Functions.try_step 0 false
  if tick then Functions.tick_clock () else pure ()

/-! ## Expressions -/

/-- A hart of generation `gen`, with the rest of its current cycle left to
run; or the power thread. -/
inductive Expr where
  | hart (gen : Nat) (cpu : CPU) (m : SailM Unit)
  | power

/-- The cycle boundary: hart `cpu` of generation `gen` with nothing left of
its current cycle. -/
def Loop (gen : Nat) (cpu : CPU) : Expr := .hart gen cpu (pure ())

/-- No expression is a value: the machine runs forever. -/
abbrev Val := Empty

/-- Observations: the power events.  (Devices will add console I/O.) -/
inductive Obs where
  | powerOn
  | powerOff
  deriving DecidableEq, Repr

/-! ## The global state -/

/-- The global state: the machine (registers and memory) of the current era,
the era bookkeeping, and the boot image.

* `gen` is the current generation and `pow` the power bit.  A generation's
  threads are live iff the power is on and `gen` is theirs; `PowerOff` bumps
  `gen`, so "`gen` has passed" is a stable death certificate.
* `image` is what memory is reset to at power-on (the ROM the machine boots
  from).  It is a constant of the run: no arm changes it.  Keeping it in the
  state (rather than baking a kernel into the language) keeps `MachCSL`
  independent of any particular kernel; adequacy picks it. -/
structure GState where
  m : MState
  gen : Nat
  pow : Bool
  image : Mem

/-- A generation-`gen` thread is live iff the power is on and `gen` is the
current generation. -/
def threadLive (g : GState) (gen : Nat) : Prop := g.pow = true ∧ g.gen = gen

instance (g : GState) (gen : Nat) : Decidable (threadLive g gen) := by
  unfold threadLive; infer_instance

/-! ## What a booted machine looks like -/

/-- The reset value of register `r` on hart `cpu`, for the registers reset
pins: machine mode, the platform's `misa`, every configuration register at
its reset value, the PC at the platform's reset vector, and `mhartid` the
hart's own number -- exactly the cells `MConf.confCells` at `bootConf`,
`pcIs` and the hart-id cell are stated over.  `none` for every other
register (the bookkeeping registers of `clockCells` are unconstrained).
(The Rocq prototype anchors this on a run of the platform's boot program from
arbitrary garbage; the explicit list here is the same fact set.) -/
def resetVal (cpu : CPU) : (r : Register) → Option (RegisterType r)
  | .cur_privilege => some Privilege.Machine
  | .hart_state => some (HartState.HART_ACTIVE ())
  | .misa => some 0x800000000014112D#64
  | .mstatus => some 0xA00000000#64
  | .mie => some 0#64
  | .mideleg => some 0#64
  | .medeleg => some 0#64
  | .mepc => some 0#64
  | .satp => some 0#64
  | .menvcfg => some 0#64
  | .mcounteren => some 0#32
  | .scounteren => some 0#32
  | .mtimecmp => some 0xFFFFFFFFFFFFFFFF#64
  | .stimecmp => some 0xFFFFFFFFFFFFFFFF#64
  | .pmpcfg_n => some bootPmpcfg
  | .pmpaddr_n => some bootPmpaddr
  | .sig_meip => some 0#1
  | .sig_seip => some 0#1
  | .mseccfg => some 0#64
  | .elp => some 0#1
  | .senvcfg => some 0#64
  | .mcountinhibit => some 0#32
  | .minstretcfg => some 0#64
  | .mcyclecfg => some 0#64
  | .pma_regions => some bootPMA
  | .htif_tohost_base => some none
  | .PC => some 0x80000000#64
  | .nextPC => some 0x80000000#64
  | .mhartid => some (BitVec.ofNat 64 cpu.val)
  | _ => none

/-- The register file of hart `cpu` is reset: every pinned register holds its
reset value. -/
def resetRegs (cpu : CPU) (f : RegFile) : Prop :=
  ∀ (r : Register) (v : RegisterType r), resetVal cpu r = some v → f r = v

/-- Reset the pinned registers of a file, keeping the others (a witness that
a reset file exists, built from any file at all). -/
def resetWith (cpu : CPU) (f₀ : RegFile) : RegFile :=
  fun r => (resetVal cpu r).getD (f₀ r)

theorem resetRegs_resetWith (cpu : CPU) (f₀ : RegFile) : resetRegs cpu (resetWith cpu f₀) := by
  intro r v h
  simp [resetWith, h]

/-- A booted machine, with no reference to the one it replaces: memory is the
boot image and every hart is reset.  This is the fact set the power thread
hands the boot client (`wp_power`'s `Hboot`). -/
def bootFacts (σ : MState) (image : Mem) : Prop :=
  σ.mem = imgFlat image ∧ σ.log = [] ∧
  (∀ cpu, σ.tv cpu = 0 ∧ σ.itv cpu = 0 ∧ σ.hr cpu = HRead.zero ∧ σ.resv cpu = none) ∧
  ∀ cpu, resetRegs cpu (σ.regs cpu)

/-- The state a `PowerOn` hands over: same generation (`PowerOff` already
bumped it), power on, the same image, and a booted machine. -/
def bootShape (g g' : GState) : Prop :=
  g'.gen = g.gen ∧ g'.pow = true ∧ g'.image = g.image ∧ bootFacts g'.m g.image

/-- A booted state exists (so the power-on arm is always enabled): reset every
hart's file and reload the image. -/
def bootWitness (g : GState) : GState :=
  { m := ⟨fun cpu => resetWith cpu (g.m.regs cpu), imgFlat g.image, [], fun _ => 0, fun _ => 0,
          fun _ => HRead.zero, fun _ => none⟩,
    gen := g.gen, pow := true, image := g.image }

theorem bootShape_bootWitness (g : GState) : bootShape g (bootWitness g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun cpu => resetRegs_resetWith cpu _⟩

/-- All harts. -/
def cpus : List CPU := List.finRange NCPU

/-- What a `PowerOn` forks: the new generation's whole complement of harts,
each at its cycle boundary. -/
def powerFork (gen : Nat) : List Expr := cpus.map (Loop gen)

/-! ## The per-event step relation -/

/-- The events, as they appear at the head of a Sail computation. -/
abbrev Ev := Eff RegisterType exception

/-- `evStep cpu o σ v σ'`: in state `σ`, hart `cpu`'s event `o` can be
answered with `v`, moving the state to `σ'`.  Failure events and the legacy
direct-RAM events have no answer (the hart is stuck).  Memory events follow
`MachCSL.TsoMem` (the Rocq prototype's `mnode_step`):

* a **fetch** (`AK_ifetch`) reads every byte of the footprint as the hart's
  instruction-cache agent at one view between the hart's instruction view
  and the top, and moves nothing;
* a **plain read** (explicit non-exclusive, or a page-table walk) reads as
  the hart at one view between its floor (and the footprint's coherence
  floors) and the top; the floor stays, the watermark and the footprint's
  coherence floors move;
* an **exclusive read** (LR, the read half of an AMO) reads at the top,
  takes the reservation, and moves the floor to the top iff it is an
  acquire -- unless another hart reserves a byte of the footprint, in which
  case it is blocked (`blockedStep`);
* a **write** appends at the top (`MState.store`) unless another hart
  reserves a byte of the footprint (blocked);
* a **fence** moves the hart's views (`MState.fence`). -/
abbrev evStep (cpu : CPU) (o : Outcome Register RegisterType) (σ : MState) :
    o.ret → MState → Prop :=
  match o with
  | .regRead r => fun v σ' => v = σ.regs cpu r ∧ σ' = σ
  | .regWrite r v => fun _ σ' => σ' = σ.setReg cpu r v
  | .memRead n _ req => fun v σ' =>
      (akIfetch req.access_kind = true ∧
        ∃ (tvn : Nat) (w : BitVec (8 * n)), σ.itv cpu ≤ tvn ∧ tvn ≤ σ.top ∧
          σ.mem.readBytes (ifetchAgent cpu) tvn req.pa n w ∧ v = .Ok (w, none) ∧ σ' = σ) ∨
      (akPlain req.access_kind = true ∧
        ∃ (tvn : Nat) (w : BitVec (8 * n)), σ.tv cpu ≤ tvn ∧ tvn ≤ σ.top ∧
          (σ.hr cpu).cohOk req.pa n tvn ∧
          σ.mem.readBytes (hartAgent cpu) tvn req.pa n w ∧ v = .Ok (w, none) ∧
          σ' = σ.afterLoad cpu req.pa n tvn) ∨
      (akExcl req.access_kind = true ∧ ¬ othersReserve σ.resv cpu req.pa n ∧
        ∃ w : BitVec (8 * n), σ.mem.topBytes req.pa n w ∧ v = .Ok (w, none) ∧
          σ' = σ.afterExcl cpu req.pa n w (akAcq req.access_kind))
  | .memWrite n _ req => fun v σ' =>
      ∃ w : BitVec (8 * n), req.value = some w ∧ ¬ othersReserve σ.resv cpu req.pa n ∧
        v = .Ok (some true) ∧ σ' = σ.store cpu req.pa n w (akExcl req.access_kind)
  | .readRam .. => fun _ _ => False
  | .writeRam .. => fun _ _ => False
  | .barrier b => fun _ σ' => σ' = σ.fence cpu b
  | .cacheOp _ => fun _ σ' => σ' = σ
  | .tlbi _ => fun _ σ' => σ' = σ
  | .translationStart _ => fun _ σ' => σ' = σ
  | .translationEnd _ => fun _ σ' => σ' = σ
  | .takeException _ => fun _ σ' => σ' = σ
  | .returnException _ => fun _ σ' => σ' = σ
  | .cycleCount => fun _ σ' => σ' = σ
  | .getCycleCount => fun v σ' => v = (0 : Nat) ∧ σ' = σ
  | .message _ => fun _ σ' => σ' = σ
  | .choose _ => fun _ σ' => σ' = σ

/-- `blockedStep cpu o σ σ'`: event `o` is blocked by another hart's
reservation; the hart self-loops (the event is retried), a blocked exclusive
read dropping the hart's own reservation. -/
abbrev blockedStep (cpu : CPU) (o : Outcome Register RegisterType) (σ σ' : MState) : Prop :=
  match o with
  | .memRead n _ req =>
      akExcl req.access_kind = true ∧ othersReserve σ.resv cpu req.pa n ∧ σ' = σ.dropResv cpu
  | .memWrite n _ req => othersReserve σ.resv cpu req.pa n ∧ σ' = σ
  | _ => False

/-- `hartStep cpu m σ m' σ'`: hart `cpu`, with `m` left to run in state `σ`,
consumes one event (or restarts the cycle at the boundary, or is blocked and
retries the event) and continues with `m'` in state `σ'`. -/
def hartStep (cpu : CPU) (m : SailM Unit) (σ : MState) (m' : SailM Unit) (σ' : MState) : Prop :=
  match m with
  | .pure _ => ∃ tick : Bool, m' = riscvStep tick ∧ σ' = σ
  | .impure (.error _) _ => False
  | .impure (.ok o) k =>
      (∃ v : o.ret, m' = k v ∧ evStep cpu o σ v σ') ∨ (blockedStep cpu o σ σ' ∧ m' = m)

/-- The primitive step relation of the language.

* A hart of generation `gen`: if live, one event step of the machine (silent,
  no forks); otherwise the corpse arm, a pure self-loop.  The two arms
  partition, so the relation is total without a stutter arm, and a dead
  generation's hart can only self-loop.
* The power thread: with the power on, `PowerOff` (observed) bumps the
  generation and clears the power bit, freezing the machine; with the power
  off, `PowerOn` (observed) resets the machine to the image and forks the new
  generation's harts. -/
def primStep : Expr × GState → List Obs → Expr × GState × List Expr → Prop
  | (.hart gen cpu m, g), obs, (e', g', efs) =>
    obs = [] ∧ efs = [] ∧
    ((threadLive g gen ∧ ∃ m' σ', e' = .hart gen cpu m' ∧ hartStep cpu m g.m m' σ' ∧
        g' = { g with m := σ' }) ∨
     (¬ threadLive g gen ∧ e' = .hart gen cpu m ∧ g' = g))
  | (.power, g), obs, (e', g', efs) =>
    e' = .power ∧
    ((g.pow = true ∧ obs = [.powerOff] ∧ efs = [] ∧
        g' = { g with gen := g.gen + 1, pow := false }) ∨
     (g.pow = false ∧ obs = [.powerOn] ∧ efs = powerFork g.gen ∧ bootShape g g'))

open Iris.ProgramLogic in
instance : PrimStep Expr GState (List Obs) := ⟨primStep⟩

open Iris.ProgramLogic in
instance : ToVal Expr Val where
  toVal _ := none
  ofVal v := nomatch v
  coe_of_toVal_eq_some h := nomatch h
  toVal_coe v := nomatch v

open Iris.ProgramLogic in
instance : Language Expr GState Obs Val where
  val_stuck _ := rfl

/-! ## Inversion and introduction for the step relation -/

open Iris.ProgramLogic

theorem primStep_hart_inv {gen : Nat} {cpu : CPU} {m : SailM Unit} {g : GState}
    {obs : List Obs} {e' : Expr} {g' : GState} {efs : List Expr}
    (h : PrimStep.primStep (Expr.hart gen cpu m, g) obs (e', g', efs)) :
    obs = [] ∧ efs = [] ∧
    ((threadLive g gen ∧ ∃ m' σ', e' = .hart gen cpu m' ∧ hartStep cpu m g.m m' σ' ∧
        g' = { g with m := σ' }) ∨
     (¬ threadLive g gen ∧ e' = .hart gen cpu m ∧ g' = g)) := h

theorem primStep_hart_live {gen : Nat} {cpu : CPU} {m m' : SailM Unit} {g : GState}
    {σ' : MState} (hl : threadLive g gen) (h : hartStep cpu m g.m m' σ') :
    PrimStep.primStep (Expr.hart gen cpu m, g) ([] : List Obs)
      (.hart gen cpu m', { g with m := σ' }, []) :=
  ⟨rfl, rfl, Or.inl ⟨hl, m', σ', rfl, h, rfl⟩⟩

theorem primStep_hart_dead {gen : Nat} {cpu : CPU} {m : SailM Unit} {g : GState}
    (hd : ¬ threadLive g gen) :
    PrimStep.primStep (Expr.hart gen cpu m, g) ([] : List Obs) (.hart gen cpu m, g, []) :=
  ⟨rfl, rfl, Or.inr ⟨hd, rfl, rfl⟩⟩

theorem primStep_power_inv {g : GState} {obs : List Obs} {e' : Expr} {g' : GState}
    {efs : List Expr} (h : PrimStep.primStep (Expr.power, g) obs (e', g', efs)) :
    e' = .power ∧
    ((g.pow = true ∧ obs = [.powerOff] ∧ efs = [] ∧
        g' = { g with gen := g.gen + 1, pow := false }) ∨
     (g.pow = false ∧ obs = [.powerOn] ∧ efs = powerFork g.gen ∧ bootShape g g')) := h

theorem primStep_power_off {g : GState} (h : g.pow = true) :
    PrimStep.primStep (Expr.power, g) [Obs.powerOff]
      (.power, { g with gen := g.gen + 1, pow := false }, []) :=
  ⟨rfl, Or.inl ⟨h, rfl, rfl, rfl⟩⟩

theorem primStep_power_on {g g' : GState} (h : g.pow = false) (hb : bootShape g g') :
    PrimStep.primStep (Expr.power, g) [Obs.powerOn] (.power, g', powerFork g.gen) :=
  ⟨rfl, Or.inr ⟨h, rfl, rfl, hb⟩⟩

end MachCSL
