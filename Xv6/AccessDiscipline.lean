/-
**THE ACCESS DISCIPLINE, PROVISIONAL (β′)** (weak-allocproc plan rev 30
§C top [R25.2] (ii)/(iii), §C W8's skeleton): W8's export `xv6AccessDisc`
at the conjunction W8-β′ delivers, `lockWordDiscAt ∧ cpuStaticAt`; W8
(f2-ctx) only STRENGTHENS it (adds `chainOkAt`, `pteDiscAt`,
`cpuProcDiscAt`, `utextDiscAt`, the pipe locks, the rest of the custody
map).

* `Cust` (the custody classes, W8-design §1 with [R25.1]'s `pte`) and the
  PROVISIONAL custody map `custAt`: `cpus[h]`'s three cells (`c->proc`,
  `c->noff`, `c->intena`) are `hart h`; a static spinlock's two words are
  `lockw b`; every other byte is `free` (no claim yet).
* `xv6LockWord σ b t`: `b` is the lock word of one of xv6's 157 STATIC image
  spinlocks (`xv6StaticLocks`: the thirteen singletons, every `proc[i].lock`,
  the static sleeplocks' inner locks; among them every lock W13 (K) reads on
  the `allocproc` trace: `proc[j].lock`, `pid_lock`, `wait_lock`); in β′
  independent of `σ` and `t` (pipe locks, born in kalloc pages, join at
  (f2-ctx)).
* `lockWordDiscAt σ`: every such lock's two word histories obey the spinlock
  kit's discipline (`MachCSL.lockRegionOk`: whole-word histories over the
  image, every post-power-on entry a hart's, the lock word 0/1, the holder
  fold legal -- a 0 only by the holder or from free -- and `lockWordAt`/
  `lkCpuAt` at the folded state; `lk->cpu` entries 0 or the writer's own
  `&cpus[c]`).
* `cpuStaticAt σ`: every post-power-on entry on a `hart h` byte is `h`'s.

**The registration lemma** [R26.1] (`xv6LockWord_registered`): every lock
word `xv6LockWord` names is a region of the static list `KernelRsv.static`
(the decidable list-membership fact) -- NOT the converse.

**`powerInterp_accessDiscβ`** (on `MachCSL.powerInterp_mmOk`'s pattern,
through `MachCSL.powerInterp_rsvOk`): the state interpretation gives
`g.pow = true → lockWordDiscAt g.m ∧ cpuStaticAt g.m`, at a record whose
static list is xv6's (`MachFixedGS.rsvStatic = KernelRsv.static`, `rfl` at
`bootFixedGS`'s literal).

Deviation from the plan's skeleton: the definitions are at xv6's
`KernelGeom` instance (`Xv6.Geom`), not under a `[KernelGeom]` binder (the
static list they read is xv6's).
-/
import Xv6.KernelRsv
import MachCSL.Adequacy

namespace Xv6

namespace AccessDiscipline

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-! ## The custody map (provisional) -/

/-- The custody classes (W8-design §1; [R25.1]'s `pte`). -/
inductive Cust where
  /-- hart `h`'s own: `cpus[h]` (β′: its three cells) -/
  | hart (h : CPU)
  /-- process-owned memory, migrating with the process (W8 (f2-ctx)) -/
  | proc (j : Nat)
  /-- protected by the lock word at `b` (W8 (f2-ctx)) -/
  | prot (b : PAddr)
  /-- the lock layer's own words (`lk->locked`, `lk->cpu`) of the lock at `b` -/
  | lockw (b : PAddr)
  /-- a kernel page-table entry byte (W8 (f2-ctx)) -/
  | pte
  /-- read-only after boot publication -/
  | ro
  /-- no claim -/
  | free
  deriving DecidableEq

/-- `cpus[h]`'s registered cells' bytes (`c->proc` 8 at +0, `c->noff` 4 at
+120, `c->intena` 4 at +124). -/
def cpuCellBytes (h : CPU) : List PAddr := (⟨cpuAddr h, .cpu h⟩ : RsvRegion).bytes

/-- A spinlock's two words' bytes (`lk->locked` 4 at +0, `lk->cpu` 8 at +16). -/
def lockWordBytes (b : PAddr) : List PAddr := (⟨b, .lock KernelGeom.cpusBase⟩ : RsvRegion).bytes

/-- xv6's STATIC spinlocks: both ports' `uarts[i].lock`, `cons.lock`, `pr.lock`,
`kmem.lock`, `pid_lock`, `wait_lock`, `tickslock`, `bcache.lock`,
`itable.lock`, `log.lock`, `ftable.lock`, `disk.vdisk_lock`, every
`proc[i].lock`, and the inner spinlocks of the 30 buffers' and the 50 inodes'
sleeplocks. -/
def xv6StaticLocks : List PAddr :=
  [rsvUartLk 0, rsvUartLk 1, KA.«cons», KA.«pr», KA.«kmem», KA.«pid_lock», KA.«wait_lock»,
    KA.«tickslock», KA.«bcache», KA.«itable», KA.«log», KA.«ftable», rsvDiskLk] ++
  ((List.range 64).map rsvProcLk ++ ((List.range 30).map rsvBufLk ++ (List.range 50).map rsvInodeLk))

/-- **The custody map, provisional** (β′): `cpus[h]`'s cells are `hart h`, a
static lock's words `lockw b`, every other byte `free`. -/
def custAt (_σ : MState) (a : PAddr) (_t : Nat) : Cust :=
  match cpus.find? (fun h => decide (a ∈ cpuCellBytes h)) with
  | some h => .hart h
  | none =>
    match xv6StaticLocks.find? (fun b => decide (a ∈ lockWordBytes b)) with
    | some b => .lockw b
    | none => .free

/-- The lock words at `σ` as of `t` (β′: the static locks). -/
def xv6LockWord (_σ : MState) (b : PAddr) (_t : Nat) : Prop := b ∈ xv6StaticLocks

/-! ## The disciplines -/

/-- **The lock layer's discipline**: every lock word's two histories obey the
spinlock kit's discipline (`MachCSL.lockRegionOk` at `&cpus[c]`). -/
def lockWordDiscAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWord σ b t → lockRegionOk (cpuPtrAt KernelGeom.cpusBase) σ.mem b

/-- **`PPerCpu` (β′)**: `cpus[h]`'s bytes are written only by `h` after
power-on. -/
def cpuStaticAt (σ : MState) : Prop :=
  ∀ (h : CPU) (a : PAddr) (H : Hist) (e : HEnt), custAt σ a e.t = .hart h → σ.mem[a]? = some H →
    e ∈ H → e.t ≠ 0 → e.tid = hartAgent h

/-- **W8's export, provisional** (β′: `lockWordDiscAt ∧ cpuStaticAt`
[R25.2]; W8 (f2-ctx) strengthens it). -/
def xv6AccessDisc (σ : MState) : Prop := lockWordDiscAt σ ∧ cpuStaticAt σ

/-! ## The registration lemma -/

/-- The owner pointer a static lock's discipline names is `&cpus[c]`. -/
theorem cpuPtrAt_cpus (c : CPU) : cpuPtrAt KernelGeom.cpusBase c = cpuAddr c := rfl

/-- Every static lock is a region of xv6's list. -/
theorem xv6StaticLocks_registered (b : PAddr) (hb : b ∈ xv6StaticLocks) :
    (⟨b, .lock KernelGeom.cpusBase⟩ : RsvRegion) ∈ xv6RsvStatic := by
  unfold xv6StaticLocks at hb
  rcases List.mem_append.1 hb with hb | hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact xv6RsvStatic_uart 0 (by decide)
    · exact xv6RsvStatic_uart 1 (by decide)
    · exact xv6RsvStatic_cons
    · exact xv6RsvStatic_pr
    · exact xv6RsvStatic_kmem
    · exact xv6RsvStatic_pid
    · exact xv6RsvStatic_wait
    · exact xv6RsvStatic_ticks
    · exact xv6RsvStatic_bcache
    · exact xv6RsvStatic_itable
    · exact xv6RsvStatic_log
    · exact xv6RsvStatic_ftable
    · exact xv6RsvStatic_disk
  · rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      exact xv6RsvStatic_proc i (List.mem_range.1 hi)
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      exact xv6RsvStatic_buf i (List.mem_range.1 hi)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
      exact xv6RsvStatic_inode k (List.mem_range.1 hk)

/-- **The registration lemma** [R26.1]: every lock word at `σ` is registered
in the static list (`xv6LockWord σ b t → b ∈ reg`). -/
theorem xv6LockWord_registered (σ : MState) (b : PAddr) (t : Nat) (hb : xv6LockWord σ b t) :
    (⟨b, .lock KernelGeom.cpusBase⟩ : RsvRegion) ∈ KernelRsv.static :=
  xv6StaticLocks_registered b hb

/-- A `hart h` byte is a byte of `cpus[h]`'s registered region. -/
theorem custAt_hart {σ : MState} {a : PAddr} {t : Nat} {h : CPU} (hc : custAt σ a t = .hart h) :
    a ∈ cpuCellBytes h := by
  unfold custAt at hc
  cases hf : cpus.find? (fun h => decide (a ∈ cpuCellBytes h)) with
  | some h' =>
    rw [hf] at hc
    cases hc
    simpa using List.find?_some hf
  | none =>
    rw [hf] at hc
    cases hl : xv6StaticLocks.find? (fun b => decide (a ∈ lockWordBytes b)) <;> rw [hl] at hc <;> cases hc

/-! ## The extraction -/

/-- The discipline, from the static list's. -/
theorem accessDisc_of_rsvAllOk (σ : MState) (h : rsvAllOk KernelRsv.static σ.mem) :
    lockWordDiscAt σ ∧ cpuStaticAt σ := by
  refine ⟨fun b t hb => ?_, fun c a H e hc hH he het => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (xv6LockWord_registered σ b t hb)
    exact h i _ hi
  · have hR := h (rsvCpuIdx c) _ (xv6RsvStatic_cpu c)
    exact hR a (custAt_hart hc) H hH e he het

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- **THE ACCESS DISCIPLINE (β′), EXTRACTED** (plan [R25.2] (ii), on
`powerInterp_mmOk`'s pattern [R26.s1]): while the power is on, the state
interpretation gives `lockWordDiscAt ∧ cpuStaticAt`. -/
theorem powerInterp_accessDiscβ (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (g : GState) :
    powerInterp g ⊢@{IProp GF} ⌜g.pow = true → lockWordDiscAt g.m ∧ cpuStaticAt g.m⌝ := by
  iintro H
  ihave %h := powerInterp_rsvOk g $$ H
  ipureintro
  intro hp
  exact accessDisc_of_rsvAllOk g.m (heq ▸ h hp)

end AccessDiscipline

end Xv6
