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

/-- **The pipe locks' registration slots** (W8 (f2-ctx) [OWN.49] (a′-r), the
RULED (a′) window [OWN.46]): xv6's only dynamic spinlocks are the pipe
locks, and a pipe's lock word `b` is live from the position at which a
`struct file` slot's `f->pipe` word (`aFpipe k`, `k < NFILE = 100`, stride
`sizeof (struct file) = 40`) took `b` (`pipealloc`'s `f0->pipe = pi`,
`MachCSL.wp_s_sd_ent`; `MachCSL.slotWit`) -- a footprint-free registry entry
of the static list.  The base is `&ftable.file[0].pipe` as a literal
(`ftable` + 24 + 16; `Xv6.aFpipe_slot` in `ProofPipealloc` ties it to the file
geometry), so the file geometry stays out of the statements' trusted base. -/
def xv6PipeSlotBase : BitVec 64 := KA.«ftable» + 40#64

def xv6PipeSlotsR : RsvRegion := ⟨xv6PipeSlotBase, .slots 100 40⟩

/-- **The page-table root words** (W8 (f2-ctx) S3, the `.pte` exemption of
BOTH tables, design (A′) [R25.1 (a)][OWN.39]): `kernel_pagetable` (one word)
and every `proc[i].pagetable` (`NPROC = 64` words at `&proc[0] + 80`, stride
`sizeof (struct proc) = 376`, `Xv6.ProcGeom`'s `pagetable@80`) -- footprint-free
registry entries of the static list: the page-table bytes as of a position
are the pages a walk reaches from these words as of that position.  W8
(pte-ghost) [OWN.57] [R42.1] splits them: `kernel_pagetable` is a PERMANENT
root (`MachCSL.RsvKind.roots`; never freed -- frozen after the seal,
`MachCSL.KptInv`), walked unrestricted (`MachCSL.ptByteAt`); the
`proc[i].pagetable` words are FREEABLE roots (`MachCSL.RsvKind.uroots`; freed
by `proc_freepagetable`/`freewalk`), walked hop-restricted: no page pushed
onto `kmem.freelist` (`xv6FreeHeadR`) after its naming word's last write is
walked (`MachCSL.ptByteLiveAt`). -/
def xv6KptRootR : RsvRegion := ⟨KA.«kernel_pagetable», .roots 1 8⟩

def xv6ProcRootsR : RsvRegion := ⟨KA.«proc» + 80#64, .uroots 64 376⟩

/-- **The free-list head word** (W8 (pte-ghost) [OWN.57] [R42.1]):
`kmem.freelist` (`&kmem + 24`, `Xv6.kmemFreelistAddr`), whose stores push
(`kfree`'s `kmem.freelist = r`, `kalloc.c:61`) and pop (`kalloc`'s
`kmem.freelist = r->next`) pages -- a footprint-free registry entry
(`MachCSL.RsvKind.freeHead`): a page the word held after a position was
freed since that position (`MachCSL.ptFreedSince`). -/
def xv6FreeHeadR : RsvRegion := ⟨KA.«kmem» + 0x18#64, .freeHead 1 8⟩

/-- **The audited racy words** (W8 (f2-ctx) S3; value set by W8 (f3-racy)
[OWN.63]): `itable.inode[k].ref` (`inode[k]` at `itable + 24 + 136 k`, `ref`
at +8; `NINODE = 50`), read lock-free by `ilock`'s/`iunlock`'s guard
`ip->ref < 1` -- a race the program has (benign: the caller holds its own
reference), so a load of them is claimed chained OR to return an entry whose
word, as of its position, is in `[1, 2^31)` -- as a signed `int`, `≥ 1`
(`MachCSL.RsvKind.racy`, a footprint-free registry entry; the tie to
`Xv6.iRef`/`Xv6.ientry` and the value fact are `IcachePinwObl.iref_certs`). -/
def xv6IrefRacyR : RsvRegion := ⟨KA.«itable» + 32#64, .racy 50 136 4 1 0x80000000⟩

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
`ftable.lock`, `disk.vdisk_lock`; and (W8 (f2-ctx)) the pipe locks'
registration slots, the page-table root words, the audited racy words and
(W8 (pte-ghost)) the free-list head word, footprint-free registry entries
(`xv6PipeSlotsR`, `xv6KptRootR`, `xv6ProcRootsR`, `xv6IrefRacyR`,
`xv6FreeHeadR`; W8 (f3-gate) [OWN.62] retired the device-ring pointer
word). -/
def xv6PostLockRegions : List RsvRegion :=
  [xv6LockR KA.«tickslock», xv6LockR KA.«bcache»] ++ (xv6BufLockRegions ++ ([xv6LockR KA.«itable»] ++
    (xv6InodeLockRegions ++ [xv6LockR KA.«log», xv6LockR KA.«ftable», xv6LockR rsvDiskLk, xv6PipeSlotsR,
      xv6KptRootR, xv6ProcRootsR, xv6IrefRacyR, xv6FreeHeadR])))

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
spinlocks' registration slots, `xv6PipeSlotsR`). -/
instance : KernelRsv where
  static := xv6RsvStatic
  wf := xv6RsvStatic_wf

/-- The pipe slots are registered. -/
theorem xv6RsvStatic_pipeSlots : xv6PipeSlotsR ∈ xv6RsvStatic := by decide +kernel

/-- The page-table root words are registered. -/
theorem xv6RsvStatic_kptRoot : xv6KptRootR ∈ xv6RsvStatic := by decide +kernel

theorem xv6RsvStatic_procRoots : xv6ProcRootsR ∈ xv6RsvStatic := by decide +kernel

theorem xv6RsvStatic_irefRacy : xv6IrefRacyR ∈ xv6RsvStatic := by decide +kernel

/-- The free-list head word is registered. -/
theorem xv6RsvStatic_freeHead : xv6FreeHeadR ∈ xv6RsvStatic := by decide +kernel

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
    | .slots _ _ => true
    | .roots _ _ => true
    | .uroots _ _ => true
    | .freeHead _ _ => true
    | .racy _ _ _ _ _ => true)

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
