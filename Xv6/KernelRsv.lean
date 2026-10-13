/-
xv6's STATIC RESERVED REGIONS (W8-β′, plan rev 30 §C top [R26.2-alt]): the
`MachCSL.KernelRsv` instance -- the regions the `PowerOn` mint reserves for
every era (the `KernelMap.static` pattern, `Xv6.KernelMap`).

* `cpus[h]`'s three cells (`c->proc`, `c->noff`, `c->intena`), one region per
  hart (`xv6CpuRegions`): written only by hart `h` after power-on;
* (W8 (f2-ctx), [R35.2]) `started`, a one-shot PUBLICATION word written only
  by hart 0 (`xv6StartedR`, `MachCSL.RsvKind.pub`): the boot gate;
* the static spinlocks' two words (`lk->locked`, `lk->cpu`, `xv6LockR`):
  the singletons before `cpus` (`xv6PreLockRegions`: both ports'
  `uarts[i].lock`, `cons.lock`, `pr.lock`, `kmem.lock`, `pid_lock`,
  `wait_lock`), every `proc[i].lock` (`xv6ProcLockRegions`) and the
  locks after `proc` (`xv6PostLockRegions`: `tickslock`, `bcache.lock`,
  the 30 buffers' sleeplocks' inner locks, `itable.lock`, the 50 inodes'
  sleeplocks' inner locks, `log.lock`, `ftable.lock`, `disk.vdisk_lock`).

The list is in address order (`uarts < started < cons < pr < kmem < pid_lock <
wait_lock < cpus < proc < tickslock < bcache < buf[] < itable < inode[] <
log < ftable < disk`).

The list's well-formedness (`rsvWf`: byte-distinct, in RAM) is checked by
`decide`.
-/
import MachCSL.Reserved
import Xv6.Geom

namespace Xv6

open MachCSL

/-- `cpus[h]`'s cells, one region per hart. -/
def xv6CpuRegions : List RsvRegion := cpus.map (fun h => ⟨cpuAddr h, .cpu h⟩)

/-- A static spinlock's two words. -/
def xv6LockR (lk : BitVec 64) : RsvRegion := ⟨lk, .lock KernelGeom.cpusBase⟩

/-- `&proc[i].lock` (`sizeof(struct proc) = 376`, the lock first). -/
def rsvProcLk (i : Nat) : BitVec 64 := KA.«proc» + BitVec.ofNat 64 (376 * i)

/-- `proc[i].lock`, one region per slot. -/
def xv6ProcLockRegions : List RsvRegion := (List.range 64).map (fun i => xv6LockR (rsvProcLk i))

/-- `&uarts[i].lock` (`sizeof(struct uart) = 40`, the lock at +16). -/
def rsvUartLk (i : Nat) : BitVec 64 := KA.«uarts» + BitVec.ofNat 64 (40 * i + 16)

/-- `&disk.vdisk_lock` (+296). -/
def rsvDiskLk : BitVec 64 := KA.«disk» + 296#64

/-- The address of the string `"pipe"` (`.rodata`, `KStr.«pipe»`), the name
`pipealloc` passes to `initlock` (`auipc a1,0x3 ; addi a1,a1,-146` at
`pipealloc+0x48`; the tie to the image is the `pipealloc` proof's own
computation, `Xv6.pipealloc_br_2fb6 : KA.«pipealloc» + 0x2fb6 = KStr.«pipe»`,
`0x2fb6 = 0x48 + 0x3000 - 146`): the name of xv6's only dynamic spinlocks,
the pipe locks (W8 (f2-ctx) [R35.1]/[R36.2]: their lock bytes are hops while
the name word holds it, `MachCSL.nameLockAt`). -/
def pipeLockNameStr : BitVec 64 := KStr.«pipe»

/-- The pipe locks' registered name (W8 (f2-ctx) [R35.1]/[R36.2]): a
footprint-free `.name` registry entry of the static list, so the boot's
pinning of the list (`MachFixedGS.rsvStatic = KernelRsv.static`) pins it. -/
def xv6PipeNameR : RsvRegion := ⟨pipeLockNameStr, .name⟩

/-- `started` (`main.c`), the boot handover's ONE-SHOT PUBLICATION word (W8
(f2-ctx), Q-F2-BOOTGATE (a) as amended by [R35.2]): written once, by hart 0. -/
def xv6StartedR : RsvRegion := ⟨KA.«started», .pub ⟨0, by decide⟩⟩

/-- The singleton regions before `cpus`, in address order: both ports' transmit
locks, `started`, the console/printf/allocator/pid/wait locks. -/
def xv6PreLockRegions : List RsvRegion :=
  [xv6LockR (rsvUartLk 0), xv6LockR (rsvUartLk 1), xv6StartedR, xv6LockR KA.«cons», xv6LockR KA.«pr»,
    xv6LockR KA.«kmem», xv6LockR KA.«pid_lock», xv6LockR KA.«wait_lock»]

/-- `&bcache.buf[i].lock.lk`, the inner spinlock of buffer `i`'s sleeplock
(`buf[i]` at `bcache + 24 + 1112 i`, its sleeplock at +16, the spinlock at +8). -/
def rsvBufLk (i : Nat) : BitVec 64 := KA.«bcache» + BitVec.ofNat 64 (48 + 1112 * i)

/-- `&itable.inode[k].lock.lk`, the inner spinlock of inode `k`'s sleeplock
(`inode[k]` at `itable + 24 + 136 k`, its sleeplock at +16, the spinlock at +8). -/
def rsvInodeLk (k : Nat) : BitVec 64 := KA.«itable» + BitVec.ofNat 64 (48 + 136 * k)

/-- The buffers' sleeplocks' inner spinlocks. -/
def xv6BufLockRegions : List RsvRegion := (List.range 30).map (fun i => xv6LockR (rsvBufLk i))

/-- The inodes' sleeplocks' inner spinlocks. -/
def xv6InodeLockRegions : List RsvRegion := (List.range 50).map (fun k => xv6LockR (rsvInodeLk k))

/-- The locks after `proc`, in address order: `tickslock`, `bcache.lock`, the
buffers' inner locks, `itable.lock`, the inodes' inner locks, `log.lock`,
`ftable.lock`, `disk.vdisk_lock`; and (W8 (f2-ctx)) the pipe locks' registered
name, a footprint-free registry entry (`xv6PipeNameR`). -/
def xv6PostLockRegions : List RsvRegion :=
  [xv6LockR KA.«tickslock», xv6LockR KA.«bcache»] ++ (xv6BufLockRegions ++ ([xv6LockR KA.«itable»] ++
    (xv6InodeLockRegions ++ [xv6LockR KA.«log», xv6LockR KA.«ftable», xv6LockR rsvDiskLk, xv6PipeNameR])))

/-- xv6's static reserved regions, in address order. -/
def xv6RsvStatic : List RsvRegion :=
  xv6PreLockRegions ++ (xv6CpuRegions ++ (xv6ProcLockRegions ++ xv6PostLockRegions))

theorem xv6RsvStatic_eq :
    xv6RsvStatic = xv6PreLockRegions ++ (xv6CpuRegions ++ (xv6ProcLockRegions ++ xv6PostLockRegions)) := rfl

/-- Hart `h`'s region's index. -/
def rsvCpuIdx (h : CPU) : Nat := h.val + 8

theorem xv6RsvStatic_sorted : strictSorted (rsvBytes xv6RsvStatic) = true := by decide +kernel

theorem xv6RsvStatic_ramB : (rsvBytes xv6RsvStatic).all (fun a => decide (inRam a 1)) = true := by
  decide +kernel

theorem xv6RsvStatic_bases : (xv6RsvStatic.map (fun R => R.base.toNat)).Nodup := by decide +kernel

theorem xv6RsvStatic_wf : rsvWf xv6RsvStatic :=
  rsvWf_of_check _ xv6RsvStatic_sorted xv6RsvStatic_ramB xv6RsvStatic_bases



/-- xv6's static reserved regions, as the machine's class (with its dynamic
spinlocks' registered name). -/
instance : KernelRsv where
  static := xv6RsvStatic
  wf := xv6RsvStatic_wf

/-- xv6's ONLY registered dynamic-lock name is `"pipe"`'s (W8 (f2-ctx)). -/
theorem xv6RsvNames : rsvNameList xv6RsvStatic = [pipeLockNameStr] := by decide +kernel

/-- Hart `h`'s cells are registered, at index `h + 8`. -/
theorem xv6RsvStatic_cpu (h : CPU) : xv6RsvStatic[rsvCpuIdx h]? = some ⟨cpuAddr h, .cpu h⟩ := by
  have hh := h.isLt
  have hl : xv6CpuRegions.length = NCPU := by simp [xv6CpuRegions, cpus]
  unfold xv6RsvStatic rsvCpuIdx
  rw [List.getElem?_append_right (by simp [xv6PreLockRegions])]
  simp only [xv6PreLockRegions, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_sub_cancel]
  rw [List.getElem?_append_left (by rw [hl]; exact hh)]
  unfold xv6CpuRegions
  rw [List.getElem?_map, cpus_get?]
  rfl

theorem xv6RsvStatic_mem_pre {R : RsvRegion} (h : R ∈ xv6PreLockRegions) : R ∈ xv6RsvStatic :=
  List.mem_append_left _ h

theorem xv6RsvStatic_mem_post {R : RsvRegion} (h : R ∈ xv6PostLockRegions) : R ∈ xv6RsvStatic :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))

theorem xv6RsvStatic_pid : xv6LockR KA.«pid_lock» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; simp)

theorem xv6RsvStatic_wait : xv6LockR KA.«wait_lock» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; simp)

theorem xv6RsvStatic_uart (i : Nat) (hi : i < 2) : xv6LockR (rsvUartLk i) ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; rcases i with _ | _ | i <;> simp <;> omega)

theorem xv6RsvStatic_cons : xv6LockR KA.«cons» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; simp)

theorem xv6RsvStatic_pr : xv6LockR KA.«pr» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; simp)

theorem xv6RsvStatic_kmem : xv6LockR KA.«kmem» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_pre (by unfold xv6PreLockRegions; simp)

theorem xv6RsvStatic_ticks : xv6LockR KA.«tickslock» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_left _ (by simp))

theorem xv6RsvStatic_bcache : xv6LockR KA.«bcache» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_left _ (by simp))

theorem xv6RsvStatic_itable : xv6LockR KA.«itable» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (by simp))))

theorem xv6RsvStatic_log : xv6LockR KA.«log» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (by simp)))))

theorem xv6RsvStatic_ftable : xv6LockR KA.«ftable» ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (by simp)))))

theorem xv6RsvStatic_disk : xv6LockR rsvDiskLk ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (by simp)))))

theorem xv6RsvStatic_buf (i : Nat) (hi : i < 30) : xv6LockR (rsvBufLk i) ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_left _
    (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

theorem xv6RsvStatic_inode (k : Nat) (hk : k < 50) : xv6LockR (rsvInodeLk k) ∈ xv6RsvStatic :=
  xv6RsvStatic_mem_post (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)))))

theorem xv6RsvStatic_proc (i : Nat) (hi : i < 64) : xv6LockR (rsvProcLk i) ∈ xv6RsvStatic := by
  unfold xv6RsvStatic xv6ProcLockRegions
  exact List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))

/-- The lock at `lk` is one of xv6's REGISTERED (static) locks.  Every other
lock (a pipe lock, in a kalloc page) is dynamic. -/
def rsvLockAt (lk : BitVec 64) : Prop := xv6LockR lk ∈ xv6RsvStatic

instance (lk : BitVec 64) : Decidable (rsvLockAt lk) := by unfold rsvLockAt; infer_instance

/-- Every registered LOCK region lies below the linker's `end` (in the image's
`.data`/`.bss`), so no kalloc page carries a reserved lock. -/
def rsvLocksLow (rs : List RsvRegion) : Bool :=
  rs.all (fun R => match R.kind with
    | .lock _ => R.base.ult KA.«end»
    | .cpu _ => true
    | .pub _ => true
    | .name => true)

theorem xv6RsvStatic_locksLow : rsvLocksLow xv6RsvStatic = true := by decide +kernel

theorem rsvLocksLow_mem {rs : List RsvRegion} (h : rsvLocksLow rs = true) {b cb : BitVec 64}
    (hm : (⟨b, .lock cb⟩ : RsvRegion) ∈ rs) : b.ult KA.«end» = true := by
  unfold rsvLocksLow at h
  have := List.all_eq_true.mp h _ hm
  simpa using this

theorem xv6RsvStatic_lockLow {b cb : BitVec 64} (hm : (⟨b, .lock cb⟩ : RsvRegion) ∈ xv6RsvStatic) :
    b.ult KA.«end» = true :=
  rsvLocksLow_mem xv6RsvStatic_locksLow hm

-- The list is read through its lemmas only (the proof mode must not unfold it).
attribute [irreducible] xv6RsvStatic

end Xv6
