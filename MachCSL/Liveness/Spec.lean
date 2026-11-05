import MachCSL.Liveness.Gates
import MachCSL.Liveness.Cycle

/-! # The statement of xv6's liveness theorem over MachCSL's runs

This file states the hypotheses of xv6's liveness theorem and the shapes of its conclusions, over
the runs of `Fairness.lean`.  It proves only what the statements need to be usable: the small
temporal lemmas, the facts the bundle gives along a run, and the forms the logic consumes.  It is
milestone C2 of lane `xv6-liveness-spec` (`local-plan/xv6-liveness-spec/PLAN.md`, outside the
repository); the prose it formalises is `local-plan/liveness/fairness-formulas.md` §3, §4 and
§7.1.  Nothing in the trusted base imports it, and it follows the naming policy of
`Fairness.lean`'s header.

A run is a sequence `σ : Nat → Cfg` of configurations in which every position is a step of some
thread of the pool (`PoolRun`, the convention of the previous lane).  The prose states the theorem
over stutter-closed behaviours instead.  A stutter is not a step of MachCSL's pool, so the Lantana
integration removes the stutters of a behaviour before it applies this bundle.

**Map of the file.**

1. The temporal vocabulary: `Always`, `Eventually`, `LeadsTo`, `powerOn`, `off`, `EraLive` (a
   component in the cut-tolerant form), `EvAlwaysOn`, `InputQuiet`, and the bridge to
   `MissHit.InfOften` (`infOften_iff`).
2. The initial configuration (`boot`), the hypotheses of the closed adequacy theorem; what the
   first step of a run from it is (`step_of_boot`).
3. Fair scheduling of every thread but the power thread (`FairSched`), and what it gives a thread
   that is live infinitely often (`stepsInfOften_of_fairSched`).  A thread is live from some
   point on or dead from some point on (`live_or_dead`).
4. The declared arms of the devices' `choose` nodes (`ArmDecl`, `declaredArms`, `ArmFair`), each
   node checked against its program, and the theorem that each declared node is a choice whose
   continuation depends only on the class of the answer (`declaredArms_classes`).
5. The kernel's MMIO discipline along the run (`KernelStores`) and the three hypotheses of the
   disk's gate theorems it gives.
6. The bundle `Hyps img σ` and what it gives along the run: the disk's programs at every
   position, the three MMIO hypotheses, a history at every RAM byte from the first power-on.
7. Era-locality: every assumption holds vacuously of a thread that is dead from some point on
   (`sf_of_dead_from`), the attempt–grant forms the logic consumes (`ag_of_hyps`), and, under fair
   scheduling, the equivalence of the two forms at every position (`sf_iff_ag`).
8. The theorem shapes: `Component`, `xv6EraLive`, `xv6Live`, and `xv6Live_of_xv6EraLive`.
9. The targets.  The first target is milestone C4's and is added here later.

**Where the tree differs from the prose.**  The disk image is a parameter `img` of the bundle,
because the closed adequacy theorem assumes the disk holds `fs.img` (`Xv6.fsImgDisk`), which this
library cannot name; xv6's theorem instantiates `img` with it.  The MMIO discipline is required
only while a request is in flight: the kernel's disk initialisation stores to other registers at
every boot, so the discipline at every position would be false on every run that initialises the
disk (section 5).  That the disk's tasks run its programs at the start, `Disk.progs (σ 0)`,
follows from `boot` (`progs_of_boot`), so the bundle does not list it.

**A conjecture, not proved in this lane.**  The bundle excludes no finite run of xv6 that
`KernelStores` admits, and it constrains only eras that never end.  Formally: every finite prefix
of a run from boot extends to a run satisfying the bundle in which the power is never cut again
(`fairness-formulas.md` §7.1, `UncutExtension`; plan decision D4 makes it optional).  The
argument is a scheduler that never runs the power thread again and serves the longest-waiting
enabled action of the other threads.  `KernelStores` is a safety property of the kernel, which
the kernel's proof establishes for every run from boot; the conjecture is about the fairness
fields.  As a statement:

```
UncutExtension : ∀ (img : Nat → BitVec 8) (σ : Nat → Cfg), PoolRun σ → boot img (σ 0) →
  (∀ σ', PoolRun σ' → σ' 0 = σ 0 → KernelStores σ') →
  ∀ n, ∃ σ', (∀ m ≤ n, σ' m = σ m) ∧ Hyps img σ' ∧ EvAlwaysOn σ' ∧
    ∀ m ≥ n, powerOn (σ' m) → powerOn (σ' (m + 1))
```

Its third premise says the kernel keeps the discipline on every run from the same start, which
the kernel proof supplies for xv6's image.  The extension powers the machine on if it is off at
`n` and never cuts it afterwards.

The antecedents that belong to particular targets are not in the bundle: `InputQuiet` (section 1)
and the finitely many competitors of a disk request (milestone C3).  A target takes them as
hypotheses of its component. -/

namespace Fairness.Spec

open MachCSL Sail Sail.ArchSem LeanRV64D
open Era (liveAt)

variable {i : Nat} {c c' : Cfg} {σ : Nat → Cfg}

/-! ## 1. The temporal vocabulary

The formulas are over a run `σ` and configuration predicates `P`, `T`, `B`. -/

section Temporal

variable {P T B C : Cfg → Prop}

/-- `P` holds at every position of the run. -/
def Always (P : Cfg → Prop) (σ : Nat → Cfg) : Prop := ∀ n, P (σ n)

/-- `P` holds at some position at or after `n`. -/
def Eventually (P : Cfg → Prop) (σ : Nat → Cfg) (n : Nat) : Prop := ∃ m ≥ n, P (σ m)

/-- Whenever `T` holds, `B` holds then or later. -/
def LeadsTo (T B : Cfg → Prop) (σ : Nat → Cfg) : Prop := ∀ n, T (σ n) → ∃ m ≥ n, B (σ m)

/-- The power is on. -/
def powerOn (c : Cfg) : Prop := c.2.pow = true

/-- The power is off. -/
def off (c : Cfg) : Prop := c.2.pow = false

/-- A component in the cut-tolerant form: whenever `T` holds, `B` holds then or later, or the
power is off then or later.  An era that ends before `B` discharges the component by its cut. -/
def EraLive (T B : Cfg → Prop) (σ : Nat → Cfg) : Prop := LeadsTo T (fun c => B c ∨ off c) σ

/-- From some position on, the power stays on: the run has a last era, which never ends. -/
def EvAlwaysOn (σ : Nat → Cfg) : Prop := ∃ n, ∀ m ≥ n, powerOn (σ m)

/-- From some position on, UART 0 accepts no byte from outside.  The UART keeps the bytes it ever
accepted as a list (`UartState.recvd`, read through `DevStates.recvd`), and the list never grows
from that position on.  An antecedent of the input-handling targets. -/
def InputQuiet (σ : Nat → Cfg) : Prop :=
  ∃ n, ∀ m ≥ n,
    ((σ (m + 1)).2.m.devs.recvd .uart0).length ≤ ((σ m).2.m.devs.recvd .uart0).length

theorem off_iff_not_powerOn : off c ↔ ¬ powerOn c := by
  unfold off powerOn
  cases c.2.pow <;> simp

/-- The bridge to `Fairness.lean`: holding infinitely often is holding eventually after every
position. -/
theorem infOften_iff : MissHit.InfOften (fun n => P (σ n)) ↔ ∀ n, Eventually P σ n := Iff.rfl

theorem LeadsTo.trans (h₁ : LeadsTo T B σ) (h₂ : LeadsTo B C σ) : LeadsTo T C σ := by
  intro n hT
  obtain ⟨m, hm, hB⟩ := h₁ n hT
  obtain ⟨k, hk, hC⟩ := h₂ m hB
  exact ⟨k, Nat.le_trans hm hk, hC⟩

theorem LeadsTo.mono (hBC : ∀ c, B c → C c) (h : LeadsTo T B σ) : LeadsTo T C σ := by
  intro n hT
  obtain ⟨m, hm, hB⟩ := h n hT
  exact ⟨m, hm, hBC _ hB⟩

/-- A component that holds outright holds in the cut-tolerant form. -/
theorem LeadsTo.eraLive (h : LeadsTo T B σ) : EraLive T B σ :=
  h.mono fun _ hB => Or.inl hB

theorem EraLive.mono (hBC : ∀ c, B c → C c) (h : EraLive T B σ) : EraLive T C σ :=
  LeadsTo.mono (fun _ hB => hB.imp_left (hBC _)) h

/-- Two cut-tolerant components chain: a cut on the way discharges the chain. -/
theorem EraLive.trans (h₁ : EraLive T B σ) (h₂ : EraLive B C σ) : EraLive T C σ := by
  intro n hT
  obtain ⟨m, hm, hB | hoff⟩ := h₁ n hT
  · obtain ⟨k, hk, hC⟩ := h₂ m hB
    exact ⟨k, Nat.le_trans hm hk, hC⟩
  · exact ⟨m, hm, Or.inr hoff⟩

/-- In a run whose last era never ends, a cut-tolerant component holds outright from the start of
that era on. -/
theorem live_of_eraLive (hon : EvAlwaysOn σ) (h : EraLive T B σ) :
    ∃ n, ∀ m ≥ n, T (σ m) → ∃ k ≥ m, B (σ k) := by
  obtain ⟨n, hn⟩ := hon
  refine ⟨n, fun m hm hT => ?_⟩
  obtain ⟨k, hk, hB | hoff⟩ := h m hT
  · exact ⟨k, hk, hB⟩
  · exact absurd (hn k (Nat.le_trans hm hk)) (off_iff_not_powerOn.1 hoff)

end Temporal

/-! ## 2. The initial configuration

The adequacy theorems start from the pool `[Expr.power]` and a global state `g` with
`g.gen = 0` and `g.pow = false` (`MachCSL.riscvPowerAdequacy`, `MachCSL/Adequacy.lean`), and the
closed theorem `Xv6.xv6FsAdequacy_closed` adds `diskOf g.m.devs = fsImgDisk`.  Nothing else is
assumed of `g`: in particular its memory before the first power-on is arbitrary. -/

/-- The initial configuration of xv6's runs, with the disk holding `img`.  It copies the
hypotheses of `Xv6.xv6FsAdequacy_closed` (`Xv6/LinkSystemAdequacyClosed.lean`): the pool is the
power thread alone, the generation is zero, the power is off, and the disk holds the image. -/
def boot (img : Nat → BitVec 8) (c : Cfg) : Prop :=
  c.1 = [Expr.power] ∧ c.2.gen = 0 ∧ c.2.pow = false ∧ diskOf c.2.m.devs = img

/-- From the initial configuration the only step is the power-on: the power thread forks the
first era's harts and device roots and boots the machine. -/
theorem step_of_boot {img : Nat → BitVec 8} {j : Nat} (hb : boot img c) (hs : Step j c c') :
    j = 0 ∧ c'.1 = Expr.power :: powerFork 0 ∧ c'.2.gen = 0 ∧ powerOn c' ∧ bootFacts c'.2.m := by
  obtain ⟨hp, hgen, hpow, -⟩ := hb
  obtain ⟨e, obs, e', efs, he, hst, hc'⟩ := hs
  rw [hp] at he hc'
  obtain rfl : j = 0 := by
    cases j with
    | zero => rfl
    | succ j => simp at he
  simp only [List.getElem?_cons_zero, Option.some.injEq] at he
  subst he
  rcases c with ⟨p, g⟩
  rcases c' with ⟨p', g'⟩
  rcases hst with ⟨rfl, ⟨hon, -⟩ | ⟨-, -, rfl, hbs⟩⟩
  · simp only at hon hpow
    rw [hpow] at hon
    cases hon
  · refine ⟨rfl, ?_, hbs.1.trans hgen, hbs.2.1, hbs.2.2.1⟩
    simp only at hgen hc' ⊢
    rw [hc', hgen]
    rfl

/-- The initial configuration runs no disk task, so the disk's tasks run its programs. -/
theorem progs_of_boot {img : Nat → BitVec 8} (hb : boot img c) : Disk.progs c := by
  intro j e tid m h
  rw [hb.1] at h
  cases j with
  | zero => simp at h
  | succ j => simp at h

/-! ## 3. Fair scheduling of every thread but the power thread -/

/-- A live thread is eventually scheduled.  The power thread is exempt without saying so: it sits
at position 0 and is never live (`Era.liveAt` holds of harts and device tasks only).  A thread
that was live and has died since is still scheduled once more, as a corpse; its step changes
nothing. -/
def FairSched (σ : Nat → Cfg) : Prop := ∀ i n, liveAt i (σ n) → ∃ m ≥ n, Steps i σ m

/-- From some position on, the thread at `i` is live. -/
def EventuallyLive (i : Nat) (σ : Nat → Cfg) : Prop := ∃ N, ∀ m ≥ N, liveAt i (σ m)

/-- From some position on, the thread at `i` is not live: its era has ended, or it never began. -/
def EventuallyDead (i : Nat) (σ : Nat → Cfg) : Prop := ∃ N, ∀ m ≥ N, ¬ liveAt i (σ m)

/-- Fair scheduling gives a thread that is live infinitely often infinitely many steps, the
hypothesis of the instances' `sf_iff`. -/
theorem stepsInfOften_of_fairSched (h : FairSched σ) (hl : ∀ n, ∃ m ≥ n, liveAt i (σ m)) :
    StepsInfOften i σ := by
  intro n
  obtain ⟨m, hm, hlm⟩ := hl n
  obtain ⟨k, hk, hs⟩ := h i m hlm
  exact ⟨k, Nat.le_trans hm hk, hs⟩

/-- A thread live infinitely often is live at every position from its first live position on:
liveness is convex along a run (`Era.liveAt_between`). -/
theorem liveAt_from_of_infOften (hrun : PoolRun σ) (hl : ∀ n, ∃ m ≥ n, liveAt i (σ m))
    {n : Nat} (hn : liveAt i (σ n)) : ∀ m ≥ n, liveAt i (σ m) := by
  intro m hm
  obtain ⟨k, hk, hlk⟩ := hl m
  exact Era.liveAt_between hrun hn hlk hm hk

/-- A thread live infinitely often is eventually live. -/
theorem eventuallyLive_of_infOften (hrun : PoolRun σ) (hl : ∀ n, ∃ m ≥ n, liveAt i (σ m)) :
    EventuallyLive i σ :=
  let ⟨N, _, hN⟩ := hl 0
  ⟨N, liveAt_from_of_infOften hrun hl hN⟩

/-- A thread that dies stays dead (`Era.dead_forever`). -/
theorem eventuallyDead_of_dead (hrun : PoolRun σ) {n m : Nat} (hn : liveAt i (σ n)) (hnm : n ≤ m)
    (hm : ¬ liveAt i (σ m)) : EventuallyDead i σ :=
  ⟨m, fun _ hk => Era.dead_forever hrun hn hnm hm hk⟩

/-- Every thread is eventually live or eventually dead. -/
theorem live_or_dead (hrun : PoolRun σ) : EventuallyLive i σ ∨ EventuallyDead i σ := by
  by_cases h : MissHit.InfOften (fun n => liveAt i (σ n))
  · exact Or.inl (eventuallyLive_of_infOften hrun h)
  · exact Or.inr (MissHit.eventually_not_of_not_infOften h)

/-- An eventually live thread is scheduled infinitely often. -/
theorem stepsInfOften_of_eventuallyLive (h : FairSched σ) (hl : EventuallyLive i σ) :
    StepsInfOften i σ := by
  obtain ⟨N, hN⟩ := hl
  exact stepsInfOften_of_fairSched h fun n =>
    ⟨n + N, Nat.le_add_right n N, hN _ (Nat.le_add_left N n)⟩

/-! ## 4. The declared arms

Each device's root program begins with a `choose` node, and so do the PLIC's two inner choices
and its pin choice.  `chooseLt n` answers `k % n` and `chooseBool` answers `k % 2 = 1`, so the
class of an answer `k` modulo `n` decides the continuation.  An arm is a node with a modulus and
a class; the arm assumption says a root that stands at the node infinitely often takes the class
infinitely often (`Arm.SF`, `Fairness.lean` 6.2).  The list below is `fairness-formulas.md` §3.4.
The classes left free are the UART's receive and idle arms, the PLIC's unwired sources and its
machine-mode pin, the disk's idle arm, and which cached sector the disk's drain arm writes. -/

/-- An arm: a `choose` node of device `d`'s program, a modulus `m` and a class `b < m`. -/
structure ArmDecl where
  d : DevId
  node : DevProg d
  m : Nat
  b : Nat

/-! ### The PLIC's inner nodes

They are the continuations of the PLIC's root program at its first choice, read off the program
with `Arm.at?`.  The `Option` is `some` by evaluation. -/

namespace Plic

/-- The gateway arm (class 0 of the root's first choice): choose which source to sample. -/
def srcNode : DevProg .plic := (Arm.at? MachCSL.Plic.body 0).get rfl

/-- The wire arm (class 1 of the root's first choice): choose which hart's pin to drive. -/
def cpuNode : DevProg .plic := (Arm.at? MachCSL.Plic.body 1).get rfl

/-- Hart `x` chosen at the wire arm: choose the machine-mode pin (odd) or the supervisor pin
(even). -/
def mmNode (x : CPU) : DevProg .plic := (Arm.at? cpuNode x.val).get rfl

end Plic

/-- The declared arms: the UARTs' transmit arm; the PLIC's gateway and wire arms, its sampling of
each wired source (the disk on 1, the UARTs on 10 and 12), its choice of each hart and that hart's
supervisor pin; the disk's poll and drain arms. -/
def declaredArms : List ArmDecl :=
  UartId.all.map (fun u => ⟨.uart u, Uart.body u, 3, 0⟩) ++
  [⟨.plic, MachCSL.Plic.body, 2, 0⟩, ⟨.plic, MachCSL.Plic.body, 2, 1⟩] ++
  [1, 10, 12].map (fun s => ⟨.plic, Plic.srcNode, MachCSL.Plic.nsrc, s⟩) ++
  cpus.flatMap (fun x => [⟨.plic, Plic.cpuNode, NCPU, x.val⟩, ⟨.plic, Plic.mmNode x, 2, 0⟩]) ++
  [⟨.virtio, Virtio.body, 3, 0⟩, ⟨.virtio, Virtio.body, 3, 1⟩]

/-- The arm assumption at position `i`: strong fairness of every declared arm.  At a position
where no root of the arm's device stands, the arm is never enabled and its conjunct holds
vacuously. -/
def ArmFair (i : Nat) (σ : Nat → Cfg) : Prop :=
  ∀ a ∈ declaredArms, Arm.SF i a.d a.node a.m a.b σ

/-- The arm assumption, unfolded into the conjunction of `fairness-formulas.md` §3.4. -/
theorem armFair_iff : ArmFair i σ ↔
    (∀ u : UartId, Arm.SF i (.uart u) (Uart.body u) 3 0 σ) ∧
    Arm.SF i .plic MachCSL.Plic.body 2 0 σ ∧ Arm.SF i .plic MachCSL.Plic.body 2 1 σ ∧
    (∀ s ∈ [1, 10, 12], Arm.SF i .plic Plic.srcNode MachCSL.Plic.nsrc s σ) ∧
    (∀ x : CPU, Arm.SF i .plic Plic.cpuNode NCPU x.val σ ∧ Arm.SF i .plic (Plic.mmNode x) 2 0 σ) ∧
    Arm.SF i .virtio Virtio.body 3 0 σ ∧ Arm.SF i .virtio Virtio.body 3 1 σ := by
  have hu : ∀ u : UartId, u ∈ UartId.all := fun u => by cases u <;> simp [UartId.all]
  simp only [ArmFair, declaredArms, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_cons, List.forall_mem_flatMap, List.not_mem_nil, false_imp_iff,
    implies_true, and_true, cpus, List.mem_finRange, forall_const, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨fun u => h1 u (hu u), h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨fun u _ => h1 u, h2, h3, h4, h5, h6, h7⟩

/-! ### The nodes against the programs

The answer at a `chooseLt n` node, and at a `chooseBool` node, is a function of its class.  Each
declared node is one of the two forms, by evaluation of the program. -/

section Nodes

variable {S T β : Type}

theorem at?_chooseLt (n : Nat) (f : Nat → DevM S T β) (v : Nat) :
    Arm.at? (DevM.chooseLt n >>= f) v = some (f (v % n)) := rfl

theorem at?_chooseBool (f : Bool → DevM S T β) (v : Nat) :
    Arm.at? (DevM.chooseBool >>= f) v = some (f (decide (v % 2 = 1))) := rfl

/-- The node is a `choose` node whose continuation depends only on the class of the answer
modulo `m`, and `b` is a class. -/
def ArmDecl.Classes (a : ArmDecl) : Prop :=
  (∃ k, a.node = .op .choose k) ∧ (∀ v w, v % a.m = w % a.m → Arm.at? a.node v = Arm.at? a.node w) ∧
    a.b < a.m

theorem classes_chooseLt {d : DevId} {n b : Nat} {f : Nat → DevProg d} (hb : b < n) :
    ArmDecl.Classes ⟨d, DevM.chooseLt n >>= f, n, b⟩ :=
  ⟨⟨_, rfl⟩, fun v w h => by simp only [at?_chooseLt, h], hb⟩

theorem classes_chooseBool {d : DevId} {b : Nat} {f : Bool → DevProg d} (hb : b < 2) :
    ArmDecl.Classes ⟨d, DevM.chooseBool >>= f, 2, b⟩ :=
  ⟨⟨_, rfl⟩, fun v w h => by simp only [at?_chooseBool, h], hb⟩

/-- Every declared arm is a choice whose continuation depends only on the class of the answer,
and its class can be chosen.  The first is what makes an arm's class meaningful; the second is
the arm's machine closure (`Arm.exists_grant`). -/
theorem declaredArms_classes : ∀ a ∈ declaredArms, a.Classes := by
  simp only [declaredArms, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.forall_mem_flatMap, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  repeat' first
    | exact classes_chooseLt (by decide)
    | exact classes_chooseLt (Fin.isLt _)
    | exact classes_chooseBool (by decide)
    | intro _ _
    | apply And.intro

end Nodes

/-! What each declared class does, checked against the programs by evaluation at the class's
least answer; `declaredArms_classes` extends each check to every answer of the class. -/

/-- UART `u`, class 0 of 3: the transmit arm. -/
example (u : UartId) : Arm.at? (Uart.body u) 0 = some (DevM.step (Uart.txArm u)) := rfl

/-- The PLIC, class 0 of 2: the gateway arm, the node `Plic.srcNode`; class 1: the wire arm. -/
example : Arm.at? MachCSL.Plic.body 0 = some Plic.srcNode := rfl
example : Arm.at? MachCSL.Plic.body 1 = some Plic.cpuNode := rfl

/-- The gateway arm, class `s` of `nsrc` for each wired source: sample source `s`. -/
example : ∃ k, Arm.at? Plic.srcNode 1 = some (.op (.sample 1) k) := ⟨_, rfl⟩
example : ∃ k, Arm.at? Plic.srcNode 10 = some (.op (.sample 10) k) := ⟨_, rfl⟩
example : ∃ k, Arm.at? Plic.srcNode 12 = some (.op (.sample 12) k) := ⟨_, rfl⟩
example : MachCSL.uartIrq .uart0 = 10 ∧ MachCSL.uartIrq .uart1 = 12 ∧ MachCSL.virtioIrq = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The wire arm, class `x` of `NCPU`: hart `x`'s pin node. -/
example (x : CPU) : Arm.at? Plic.cpuNode x.val = some (Plic.mmNode x) := rfl

/-- Hart `x`'s pin node, class 0 of 2: read the PLIC's state, then drive hart `x`'s supervisor
pin. -/
example (x : CPU) (p : PlicState) : ∃ k c b, Arm.at? (Plic.mmNode x) 0 = some (.op .get k) ∧
    k p = .op (.setPin c false b) .pure ∧ c = x :=
  ⟨_, _, _, rfl, rfl, Fin.ext (by simp [Nat.mod_eq_of_lt x.isLt])⟩

/-- The disk, class 0 of 3: the poll arm, which reads the available ring's index when the queue
is live. -/
example (v : VirtioState) (hv : Virtio.live v.cfg = true) : ∃ k k',
    Arm.at? Virtio.body 0 = some (.op .get k) ∧
    k v = .op (.dmaRead (Virtio.availIdxAddr v.cfg) 2) k' := by
  refine ⟨_, ?k', rfl, ?_⟩
  show (if Virtio.live v.cfg = true then _ else _) = _
  rw [hv]
  rfl

/-- The disk, class 1 of 3: the drain arm, which chooses a cached sector when the cache is not
empty. -/
example (v : VirtioState) (hv : v.cache.isEmpty = false) : ∃ k k',
    Arm.at? Virtio.body 1 = some (.op .get k) ∧ k v = .op .choose k' := by
  refine ⟨_, ?k', rfl, ?_⟩
  show (if v.cache.isEmpty = true then _ else _) = _
  rw [hv]
  rfl

/-! ## 5. The kernel's MMIO discipline along the run

The disk's gate theorems (`Gates.lean`) exclude three kinds of hart store while a request is in
flight: a reset (`NoBusyReset`), a store turning the write-back mode off (`NoWceOff`) and a
store changing the configuration (`NoConfigWrite`).  All three follow from `Disk.kernelStores`
at the configurations where a request is in flight.  `Disk.kernelStores` says every live hart
storing to the disk's window stores to the queue-notify or the interrupt-acknowledge register.
That is xv6's discipline after the disk's initialisation, and the initialisation stores to the
status, feature and queue registers at every boot.  A power-on resets the disk and empties its
in-flight list, and xv6 submits no request before the initialisation ends, so the discipline is
required only while a request is in flight. -/

/-- While a request is in flight, the harts store to the disk's window only at the queue-notify
and the interrupt-acknowledge registers. -/
def KernelStores (σ : Nat → Cfg) : Prop :=
  ∀ n, (Disk.disk (σ n)).inflight ≠ [] → Disk.kernelStores (σ n)

/-- The discipline at every position gives the discipline while a request is in flight. -/
theorem kernelStores_of_always (h : ∀ n, Disk.kernelStores (σ n)) : KernelStores σ :=
  fun n _ => h n

/-- No step of the run resets the disk while a request is in flight. -/
theorem noBusyReset_of_kernelStores (h : KernelStores σ) : Disk.NoBusyReset σ := by
  intro n j hs hb
  exact Disk.noBusyReset_of_kernelStores (h n (let ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := hb; hin))
    j hs hb

/-- No step of the run turns the disk's write-back mode off while a request is in flight. -/
theorem noWceOff_of_kernelStores (h : KernelStores σ) : Disk.NoWceOff σ := by
  intro n j hs hst
  exact Disk.noWceOff_of_kernelStores (h n (let ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := hst; hin))
    j hs hst

/-- No step of the run changes the disk's configuration while a request is in flight. -/
theorem noConfigWrite_of_kernelStores (h : KernelStores σ) : Disk.NoConfigWrite σ := by
  intro n j hs hst
  exact Disk.noConfigWrite_of_kernelStores (h n (let ⟨_, _, _, _, _, _, _, _, _, _, _, hin⟩ := hst; hin))
    j hs hst

/-! ## 6. The bundle -/

/-- The hypotheses of xv6's liveness theorem on a run `σ` from the disk image `img`: the run
starts at boot; every thread but the power thread is fairly scheduled; the five strong
assumptions hold at every position (the tick, the arms, the visibility of stores, harts progress
and the disk's DMA writes); the kernel keeps its MMIO discipline while a disk request is in
flight. -/
structure Hyps (img : Nat → BitVec 8) (σ : Nat → Cfg) : Prop where
  run : PoolRun σ
  boot : boot img (σ 0)
  sched : FairSched σ
  tick : ∀ i, Tick.SF i σ
  arm : ∀ i, ArmFair i σ
  fresh : ∀ i t a, Fresh.SF i t a σ
  hart : ∀ i, Hart.SF i σ
  dma : ∀ i tid, Dma.SF i .virtio tid σ
  stores : KernelStores σ

namespace Hyps

variable {img : Nat → BitVec 8} (h : Hyps img σ)
include h

/-- Every disk task in every configuration of the run runs the disk's programs. -/
theorem progs_all : ∀ n, Disk.progs (σ n) := Disk.progs_run h.run (progs_of_boot h.boot)

theorem noBusyReset : Disk.NoBusyReset σ := noBusyReset_of_kernelStores h.stores
theorem noWceOff : Disk.NoWceOff σ := noWceOff_of_kernelStores h.stores
theorem noConfigWrite : Disk.NoConfigWrite σ := noConfigWrite_of_kernelStores h.stores

/-- The first step of the run is the power-on. -/
theorem first_step : (σ 1).1 = Expr.power :: powerFork 0 ∧ (σ 1).2.gen = 0 ∧ powerOn (σ 1) ∧
    bootFacts (σ 1).2.m :=
  let ⟨_, hs⟩ := h.run 0
  (step_of_boot h.boot hs).2

/-- From the first power-on, the run's first step, every RAM byte has a history.  At position 0
the memory is the initial state's, of which nothing is assumed. -/
theorem ramHist {n : Nat} (hn : 1 ≤ n) : Fairness.ramHist (σ n).2.m.mem := by
  have h1 : Fairness.ramHist (σ 1).2.m.mem := by
    rw [h.first_step.2.2.2.1]
    exact ramHist_boot
  exact ramHist_run h.run h1 hn

/-- A live thread's configuration has a history at every RAM byte. -/
theorem ramHist_of_liveAt {n : Nat} (hl : liveAt i (σ n)) : Fairness.ramHist (σ n).2.m.mem := by
  apply h.ramHist
  rcases n with _ | n
  · obtain ⟨_, -, hpow, -⟩ := Era.liveAt_gen hl
    rw [h.boot.2.2.1] at hpow
    cases hpow
  · exact Nat.succ_pos n

/-- A thread live infinitely often is scheduled infinitely often. -/
theorem stepsInfOften (hl : ∀ n, ∃ m ≥ n, liveAt i (σ m)) : StepsInfOften i σ :=
  stepsInfOften_of_fairSched h.sched hl

end Hyps

/-! ## 7. Era-locality

An assumption about the thread at position `i` constrains only runs in which `i`'s era never
ends.  Every attempt condition is a live thread's, so on a run where the thread is dead from some
point on there are finitely many attempts and the strong fairness holds vacuously
(`sf_of_dead_from`; a thread that dies stays dead, `eventuallyDead_of_dead`).  The forms the
logic consumes are the attempt–grant forms; strong fairness gives them on every run
(`Action.attemptGrant_of_sf`), so `ag_of_hyps` needs no case split.  The case split is what the
converse needs: under fair scheduling the two forms coincide at every position (`sf_iff_ag`),
by the instance's `sf_iff` where the thread is eventually live and vacuously where it is
eventually dead. -/

namespace Action

/-- Strong fairness of an action whose attempt condition is a live thread's holds vacuously on a
run where the thread is eventually dead. -/
theorem sf_of_dead_from {A : Cfg → Prop} {G : Cfg → Cfg → Prop} (hlive : ∀ c, A c → liveAt i c)
    (hd : EventuallyDead i σ) : Action.SF i A G σ := by
  intro hA
  obtain ⟨N, hN⟩ := hd
  obtain ⟨m, hm, hAm⟩ := hA N
  exact absurd (hlive _ hAm) (hN m hm)

/-- Under fair scheduling, strong fairness of an action whose attempt condition is a live
thread's, and persists while the thread is eventually live, is its attempt–grant form. -/
theorem sf_iff_ag {A : Cfg → Prop} {G : Cfg → Cfg → Prop} (hrun : PoolRun σ)
    (hsched : FairSched σ) (hlive : ∀ c, A c → liveAt i c)
    (hper : EventuallyLive i σ → Fairness.Action.Persists i A σ) :
    Action.SF i A G σ ↔ Fairness.Action.AttemptGrant i A G σ := by
  rcases live_or_dead hrun with hl | hd
  · exact Action.sf_iff_attemptGrant (stepsInfOften_of_eventuallyLive hsched hl) (hper hl)
  · exact ⟨Action.attemptGrant_of_sf, fun _ => sf_of_dead_from hlive hd⟩

end Action

namespace Tick

theorem sf_of_dead_from (hd : EventuallyDead i σ) : Tick.SF i σ :=
  Action.sf_of_dead_from (fun _ => Fairness.Tick.live) hd

theorem ag_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) : Tick.AG i σ :=
  Fairness.Action.attemptGrant_of_sf (h.tick i)

theorem sf_iff_ag (hrun : PoolRun σ) (hsched : FairSched σ) : Tick.SF i σ ↔ Tick.AG i σ :=
  Action.sf_iff_ag hrun hsched (fun _ => Fairness.Tick.live) fun _ => Fairness.Tick.persists hrun

end Tick

namespace Arm

theorem sf_of_dead_from {d : DevId} {node : DevProg d} {m b : Nat} (hd : EventuallyDead i σ) :
    Arm.SF i d node m b σ :=
  Action.sf_of_dead_from (fun _ => Fairness.Arm.live) hd

theorem ag_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) {a : ArmDecl} (ha : a ∈ declaredArms) :
    Arm.AG i a.d a.node a.m a.b σ :=
  Fairness.Action.attemptGrant_of_sf (h.arm i a ha)

theorem sf_iff_ag {d : DevId} {node : DevProg d} {m b : Nat} (hrun : PoolRun σ)
    (hsched : FairSched σ) : Arm.SF i d node m b σ ↔ Arm.AG i d node m b σ :=
  Action.sf_iff_ag hrun hsched (fun _ => Fairness.Arm.live) fun _ => Fairness.Arm.persists hrun

end Arm

namespace Fresh

theorem sf_of_dead_from {t : Nat} {a : PAddr} (hd : EventuallyDead i σ) : Fresh.SF i t a σ :=
  Action.sf_of_dead_from (fun _ => Fairness.Fresh.live) hd

theorem ag_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) {t : Nat} {a : PAddr} :
    Fresh.AG i t a σ :=
  Fairness.Action.attemptGrant_of_sf (h.fresh i t a)

theorem sf_iff_ag {t : Nat} {a : PAddr} (hrun : PoolRun σ) (hsched : FairSched σ) :
    Fresh.SF i t a σ ↔ Fresh.AG i t a σ :=
  Action.sf_iff_ag hrun hsched (fun _ => Fairness.Fresh.live) fun _ => Fairness.Fresh.persists hrun

end Fresh

namespace Hart

theorem sf_of_dead_from (hd : EventuallyDead i σ) : Hart.SF i σ :=
  Action.sf_of_dead_from (fun _ => Fairness.Hart.live) hd

theorem ag_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) : Hart.AG i σ :=
  Fairness.Action.attemptGrant_of_sf (h.hart i)

theorem sf_iff_ag (hrun : PoolRun σ) (hsched : FairSched σ) : Hart.SF i σ ↔ Hart.AG i σ :=
  Action.sf_iff_ag hrun hsched (fun _ => Fairness.Hart.live) fun _ => Fairness.Hart.persists hrun

/-- The bundle gives the Progress Axiom relativised to the era: every pending access is served,
or the hart dies (`Fairness.Hart.sf_iff_progressOrCut`). -/
theorem progressOrCut_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) :
    Fairness.Hart.ProgressOrCut i σ :=
  Fairness.Hart.progressOrCut_of_sf h.run (h.hart i)

end Hart

namespace Dma

theorem sf_of_dead_from {d : DevId} {tid : TaskId} (hd : EventuallyDead i σ) : Dma.SF i d tid σ :=
  Action.sf_of_dead_from (fun _ => Fairness.Dma.live) hd

theorem ag_of_hyps {img : Nat → BitVec 8} (h : Hyps img σ) {tid : TaskId} :
    Dma.AG i .virtio tid σ :=
  Fairness.Action.attemptGrant_of_sf (h.dma i tid)

/-- The DMA write's attempt condition reads the disk's shared state, so its persistence is a
protocol property and stays a hypothesis (`Fairness.Dma.sf_iff`). -/
theorem sf_iff_ag {d : DevId} {tid : TaskId} (hrun : PoolRun σ) (hsched : FairSched σ)
    (hper : EventuallyLive i σ → Fairness.Action.Persists i (Fairness.Dma.enabled i d tid) σ) :
    Dma.SF i d tid σ ↔ Dma.AG i d tid σ :=
  Action.sf_iff_ag hrun hsched (fun _ => Fairness.Dma.live) hper

end Dma

/-! ## 8. The theorem shapes

A component of the specification is a pair of configuration predicates: whenever `T` holds, `B`
holds then or later.  xv6's liveness theorem is a list of components.  It is stated per era
(`xv6EraLive`: every component in the cut-tolerant form, on every run satisfying the bundle) and
in full (`xv6Live`: every component outright from some position on, on every such run whose last
era never ends).  The second follows from the first.  The names are those of the prose. -/

/-- A component of the specification: whenever `T` holds, `B` holds then or later. -/
structure Component where
  T : Cfg → Prop
  B : Cfg → Prop

/-- The era form of xv6's liveness theorem for the components `comps`, on the run `σ`. -/
def xv6EraLive (img : Nat → BitVec 8) (comps : List Component) (σ : Nat → Cfg) : Prop :=
  Hyps img σ → ∀ c ∈ comps, EraLive c.T c.B σ

/-- The full form: on a run whose last era never ends, every component holds outright from some
position on. -/
def xv6Live (img : Nat → BitVec 8) (comps : List Component) (σ : Nat → Cfg) : Prop :=
  Hyps img σ → EvAlwaysOn σ → ∀ c ∈ comps, ∃ n, ∀ m ≥ n, c.T (σ m) → ∃ k ≥ m, c.B (σ k)

theorem xv6Live_of_xv6EraLive {img : Nat → BitVec 8} (comps : List Component)
    (h : xv6EraLive img comps σ) : xv6Live img comps σ :=
  fun hh hon c hc => live_of_eraLive hon (h hh c hc)

/-- The shapes typecheck: a component whose trigger never holds is live. -/
example (img : Nat → BitVec 8) (σ : Nat → Cfg) :
    xv6EraLive img [⟨fun _ => False, fun _ => True⟩] σ := by
  intro _ c hc
  rw [List.mem_singleton] at hc
  subst hc
  intro _ hT
  exact hT.elim

/-! ## 9. The targets

The first target, T1 (every secondary hart leaves its boot spin on `started`), is milestone C4's;
its component and the statement `xv6EraLive img [T1]` are added here. -/

end Fairness.Spec
