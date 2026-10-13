/-
**THE ACCESS DISCIPLINE** (weak-allocproc plan §C W8's skeleton, [R25.1],
[R34.1]; W8 (f2-ctx) S4; W8 (f3-hold) [OWN.64]): W8's export `xv6AccessDisc`,
`chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt ∧ lkCpuReadAt` -- FOUR conjuncts:
THREE of the skeleton's six (W8 (f2-ctx)) and the ruled `holding()` clause
`lkCpuReadAt` (W8 (f3-hold)).  NOT exported here: `pteDiscAt` (the A/D
write-back clause [R25.1]: no σ-pure fact of the state interpretation carries
it -- `KptInv` is an Iris invariant; `PROGRESS-W8f2.md` S4, an open point),
and W8 (f3-rest)'s `cpuProcDiscAt`/`utextDiscAt` [R34.1].  Later items only
STRENGTHEN the conjunction.

* `Cust` (the custody classes, W8-design §1 with [R25.1]'s `pte`, and the
  S3 exemption classes `pub`, `racy`) and the custody map `custAt σ a
  t`, σ-READABLE (a predicate of the memory and xv6's static registry
  `KernelRsv.static`, no ghost state), its arms read off the load-side
  invariant's exemption `MachCSL.chainExAt`, in this order:
  - `lockw b`: a byte of the two words (`lk->locked`, `lk->cpu`) of a STATIC
    spinlock at `b` of the registry; or of a DYNAMIC (pipe) lock at `b` live
    as of `t` (`MachCSL.dynLkAt`: an `f->pipe` slot named `b` and every later
    entry on `b`'s word is word-sized -- the ruled (a′) window [OWN.46],
    [OWN.49] (a′-r)).  The dynamic lock words are EXEMPT from `chainOkAt`
    but NOT covered by `lockWordDiscAt` (static locks only): the windowed
    `lockRegionOk` of the plan's S4 text [R36.3] is not a fact of the state
    interpretation (a pipe lock's discipline is its Iris lock invariant,
    `Lock.lkDynRegW`) -- a named gap, `PROGRESS-W8f2.md` S4;
  - `pub w`: a byte of a one-shot publication word written only by hart `w`
    (xv6: `started`, the boot gate; its discipline is the registry's
    `RsvKind.pub`);
  - **`pte`**: a LIVE page-table byte as of `t` (`MachCSL.ptByteLiveAt`,
    design (A′) + W8 (pte-ghost) [OWN.57], scoped to the freeable tables
    [R42.1]): the bytes of the pages a Sv39 walk reaches, as of the access,
    from a registered root word -- BOTH tables [R25.1 (a)], [OWN.39]:
    - from the PERMANENT root `kernel_pagetable` (`RsvKind.roots`) the walk
      is unrestricted (`MachCSL.ptByteAt`): the kernel table is NEVER freed
      (its pointer entries and root word are frozen after the seal,
      `MachCSL.KptInv`'s `kptPtrs`/`kptRootW`; xv6 has no `kfree` of a
      kernel page-table page), so its walk needs no freed-check;
    - from a FREEABLE root `proc[i].pagetable` (`RsvKind.uroots`) every hop
      (root word → root page, pointer slot → child page) is taken only if
      the named page was NOT pushed onto `kmem.freelist` (`kfree`'s
      `kmem.freelist = r`, `kalloc.c:61`; the registered head word
      `RsvKind.freeHead`, read off its byte history -- `MachCSL.ptFreedSince`)
      after the naming word's last write (`MachCSL.wordPosAsOf`, entry-based).
    **No window** [OWN.57]: from its push on, no page is covered through a
    still-stored pointer (`freewalk` `kfree`s each interior page before
    `pagetable[i] = 0`, `vm.c:273-274`; `freeproc` frees the root before
    `p->pagetable = 0`, `proc.c:162-163`) -- `MachCSL.ptByteLiveAt_freed`;
    a freed page is not walked through, so pointer-shaped words a later
    owner writes lead nowhere; a reallocated page is covered again only
    through a fresh slot write after its pop (`walk`'s
    `*pte = PA2PTE(pagetable) | PTE_V`, `vm.c:112`).  On every xv6 run the
    class is the intended "bytes of pages in use as page-table pages" up to
    **the residual** [R42.2]: exemption is decided AS OF the ENTRY's
    position (`loadsChained`'s `¬ ex a e.t`) and never revoked, so the
    entries the freeing hart writes inside `kfree` BEFORE its push -- the
    `0x01` junk fill and the link `r->next` (`kalloc.c:55,60`), written while
    the page is still a live page-table page -- STAY exempt.  Their one later
    foreign read in xv6 is `kalloc`'s `r->next` (`kalloc.c:76`), under
    `kmem.lock` (lock-chained, but not claimed so here).  The fill's partial
    words lead nowhere in RAM: a page-table page is all-zero at `kfree`
    (`freewalk` zeroes each pointer slot and panics on a leaf,
    `vm.c:270-277`), and no byte-subset of `0x01` over zero is a pointer into
    `[0x80000000, 0x88000000)` (`MachCSL.ptPtrTo_fill01_notRam`, 256 cases).
    This entry residual is ACCEPTED [OWN.67] (Q-PTE-RESIDUAL = (a)): a
    named, documented residual beside [OWN.57]'s "no window".  Spec: RVWMO/riscv.cat/Sail/Zifencei/PMAs are SILENT (custody is
    not an ISA notion; no hart's `satp` names a dying user table at
    `freeproc`), FAITHFUL;
  - `racy`: a byte of an AUDITED RACY word (`MachCSL.racyByteIn`; xv6:
    `itable.inode[k].ref`, read lock-free by `ilock`'s/`iunlock`'s guard
    `ip->ref < 1`) -- finding **F-RACY**: a NAMED WEAKENING (no chain is
    claimed for these bytes; the race is real).  Ruled [OWN.63]: W8
    (f3-racy) replaces it by the value fact "every value the guard can read
    is ≥ 1" -- the SAME defect class as `lkCpuReadAt` below;
  - (no device-ring class: W8 (f3-gate) [OWN.62] retired finding
    **F-DISKTAIL**'s exemption.  The used ring's hart-authored entries --
    hart 0's `kalloc` fill and `memset(disk.used, 0, PGSIZE)`
    (`virtio_disk.c`), both before `started = 1` (`main.c`) -- are now
    CHAIN-certified: the one read that can return them, `used->idx` at a
    watermark of zero, pays `MachCSL.srcCertAt`'s chain arm from full keys
    for the two heads' positions that `disk.vdisk_lock`'s payload carries
    (`Xv6.diskHeadKeys`, `Xv6.DiskAcc.usedIdx_certs`), whose chain half
    the lock's handoffs carry to every later holder (`MachCSL.ctx_dom_key`);
    the device's own entries are DMA authors, exempt as every DMA author
    is; so `chainOkAt` now covers the ring's bytes);
  - `hart h`: a byte of `cpus[h]`'s three cells (`c->proc`, `c->noff`,
    `c->intena`), not in an exempt class;
  - every other byte `free`.
* `syncPath σ A t B τ`: the entries of hart `A` at or below `t` reach hart
  `B` -- a chain of release → acquire hops through hop bytes (a static
  spinlock's lock byte, or a dynamic lock's live as of the acquire), each
  hop a WORD-sized held/release/acquire triple (`MachCSL.syncHop`,
  [R36.3]), the last acquire below `τ`; or the BOOT HOP (`MachCSL.pubCover`,
  F-B adopted [R36.1]): `B` read a store of the publication word's writer
  `w ≠ B` that `A`'s entries precede (`A`'s own, or chained to `w`).
* **`chainOkAt σ`** (§C W8 (iii+)): every hart `j`'s coherence floor at a
  byte `a` names, when it is a FOREIGN hart's post-power-on entry (DMA
  authors exempt) on a byte whose custody as of the entry is not exempt
  (`lockw`, `pub`, `pte`, `racy`), an entry SYNC-CHAINED to `j`
  before `σ.top + 1`.
* `xv6LockWord σ b t`: `b` is the lock word of one of xv6's 157 STATIC image
  spinlocks (`xv6StaticLocks`).
* `lockWordDiscAt σ`: every such lock's two word histories obey the spinlock
  kit's discipline (`MachCSL.lockRegionOk`: whole-word histories over the
  image, every post-power-on entry a hart's, the lock word 0/1, the holder
  fold legal, `lk->cpu` entries 0 or the writer's own `&cpus[c]`).
* `cpuStaticAt σ`: every post-power-on entry on a byte of `cpus[h]`'s cells
  is `h`'s (custody-free: every byte of the cells, so at least the β′
  clause).
* **`lkCpuReadAt σ`** (W8 (f3-hold) [OWN.64]): for every exported lock word
  `b` the two word histories decompose as in `lockWordDiscAt` at a state
  `st`, and a hart `c` that is not `st`'s holder never reads its own
  pointer `&cpus[c]` out of `lk->cpu` -- at ANY view, and for any image
  value of the word other than `&cpus[c]` (xv6's static locks' is 0).  This
  is `holding()`'s harmlessness: `acquire` calls `holding(lk)` WITHOUT the
  lock (`spinlock.c`), an unlocked read of `lk->cpu`, a lock-protected word
  -- a C11 data race, benign on hardware by a VALUE argument (whatever the
  non-holder reads, it is not its own pointer, so `holding` answers 0 and
  `acquire` does not panic).  The SAME defect class as `ip->ref` (F-RACY,
  [OWN.63], W8 (f3-racy)): unlocked reads of lock-protected words, benign by
  a value argument.  A
  corollary of `lockWordDiscAt` (`MachCSL.lkCpu_read_not_mine`).  Static
  locks only, as `xv6LockWord` (every lock after W8 (f3-pipelk)).  Spec:
  RVWMO/riscv.cat/Sail are SILENT on lock disciplines (a proof notion);
  the reads quantified are every value RVWMO lets the load return under the
  discipline -- FAITHFUL.

**The registration lemma** [R26.1] (`xv6LockWord_registered`).

**`powerInterp_accessDisc`** (on `MachCSL.powerInterp_rsvOk`'s pattern): the
state interpretation gives `g.pow = true → xv6AccessDisc g.m`, at a record
whose static list is xv6's -- `chainOkAt` from the chain conjunct's
load-side invariant (`MachCSL.loadsChained`, S3) and `mmOk` (the deadline),
`lockWordDiscAt ∧ cpuStaticAt ∧ lkCpuReadAt` from the reserved regions'
discipline.

Deviations from the plan's skeleton: the definitions are at xv6's
`KernelGeom` instance (`Xv6.Geom`), not under a `[KernelGeom]` binder; the
boot hop is `pubCover` (the implemented [R36.1] form), not "`t ≤ bootEnd`";
the exemption has the S3 classes `pub`, `racy` beyond `lockw`/`pte` (S3's
third, `dev`, retired by W8 (f3-gate)).
-/
import Xv6.KernelRsv
import MachCSL.Adequacy
import MachCSL.Lock

namespace Xv6

namespace AccessDiscipline

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-! ## The custody map -/

/-- The custody classes (W8-design §1; [R25.1]'s `pte`; S3's `pub`, `racy`). -/
inductive Cust where
  /-- hart `h`'s own: `cpus[h]`'s three cells -/
  | hart (h : CPU)
  /-- process-owned memory, migrating with the process (W8 (f3-rest)) -/
  | proc (j : Nat)
  /-- protected by the lock word at `b` (W8 (f3-rest)) -/
  | prot (b : PAddr)
  /-- the lock layer's own words (`lk->locked`, `lk->cpu`) of the lock at `b` -/
  | lockw (b : PAddr)
  /-- a one-shot publication word written only by hart `w` (`started`) -/
  | pub (w : CPU)
  /-- a page-table byte of either table, as of the position -/
  | pte
  /-- an audited racy word's byte (F-RACY: `ip->ref`) -/
  | racy
  /-- read-only after boot publication -/
  | ro
  /-- no claim -/
  | free
  deriving DecidableEq

/-- xv6's static registry (the record's `MachFixedGS.rsvStatic`). -/
abbrev xv6Rsv : List RsvRegion := KernelRsv.static

/-- `cpus[h]`'s registered cells' bytes (`c->proc` 8 at +0, `c->noff` 4 at
+120, `c->intena` 4 at +124). -/
def cpuCellBytes (h : CPU) : List PAddr := (⟨cpuAddr h, .cpu h⟩ : RsvRegion).bytes

/-- A spinlock's two words' bytes (`lk->locked` 4 at +0, `lk->cpu` 8 at +16). -/
def lockWordBytes (b : PAddr) : List PAddr := (⟨b, .lock KernelGeom.cpusBase⟩ : RsvRegion).bytes

/-- `a` is a byte of the two words of a static spinlock of the registry at `b`. -/
def staticLockByteOf (b a : PAddr) : Prop :=
  ∃ cb, (⟨b, .lock cb⟩ : RsvRegion) ∈ xv6Rsv ∧ a ∈ (⟨b, .lock cb⟩ : RsvRegion).bytes

/-- `a` is a byte of a publication word of the registry written by `w`. -/
def pubByteOf (w : CPU) (a : PAddr) : Prop :=
  ∃ f, (⟨f, .pub w⟩ : RsvRegion) ∈ xv6Rsv ∧ a ∈ (⟨f, .pub w⟩ : RsvRegion).bytes

/-- `a` is a byte of the two words of a dynamic lock at `b` live as of `t`
(`MachCSL.dynLkAt` over the registry's `f->pipe` slots). -/
def dynLockByteAt (σ : MState) (b a : PAddr) (t : Nat) : Prop :=
  dynLkAt (slotWit xv6Rsv) σ.mem σ.top b t ∧ lockWordsByte b a

open Classical in
/-- **The custody map** (σ-readable): the exempt classes first, in the order
of `MachCSL.chainExAt`'s arms (static lock words, publication words, live
dynamic lock words, LIVE page-table bytes as of `t` -- no freed page of a
freeable table, W8 (pte-ghost) [OWN.57], up to the as-of-entry residual of
the header --, audited racy words (F-RACY)), then `cpus[h]`'s cells, then
`free`. -/
noncomputable def custAt (σ : MState) (a : PAddr) (t : Nat) : Cust :=
  if h1 : ∃ b, staticLockByteOf b a then .lockw (Classical.choose h1) else
  if h2 : ∃ w, pubByteOf w a then .pub (Classical.choose h2) else
  if h3 : ∃ b, dynLockByteAt σ b a t then .lockw (Classical.choose h3) else
  if ptByteLiveAt xv6Rsv σ.mem t a then .pte else
  if racyByteIn xv6Rsv a then .racy else
  if h7 : ∃ c, a ∈ cpuCellBytes c then .hart (Classical.choose h7) else .free

/-! ## Sync paths and the chain conjunct -/

/-- The certificate environment of `σ` at xv6's registry. -/
def xv6Env (σ : MState) : ChainEnv := chainEnvAt xv6Rsv (slotWit xv6Rsv) σ

/-- `b` is a hop byte for an acquire at `a`: a static spinlock's lock byte,
or a dynamic lock's live as of `a`. -/
def hopByteAt (σ : MState) (b : PAddr) (a : Nat) : Prop :=
  lockByteIn xv6Rsv b ∨ dynLkAt (slotWit xv6Rsv) σ.mem σ.top b a

/-- **A sync path** from the entries of hart `A` at or below `t` to hart `B`
before `τ`: release → acquire hops through hop bytes, the last acquire below
`τ`; or the boot hop (`B` read the publication store `A`'s entries precede). -/
def syncPath (σ : MState) (A : CPU) (t : Nat) (B : CPU) (τ : Nat) : Prop :=
  (∃ a, a < τ ∧ hopChain σ.mem (hopByteAt σ) A t B a) ∨ pubCover (xv6Env σ) A t B

/-- **(iii+) Every observed foreign hart entry off the exempt classes is
sync-chained**: hart `j`'s coherence floor at `a` names a post-power-on entry
of a hart other than `j`; unless the byte is, as of the entry, a lock-layer
word, a publication word, a LIVE page-table byte (no page of a freeable table
from its push onto the free list on; the as-of-entry residual of the header)
or an audited racy word (F-RACY), that entry reaches `j` along a sync path
(the virtio used ring included: W8 (f3-gate) [OWN.62]). -/
def chainOkAt (σ : MState) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
    e.t = (σ.hr j).coh a → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j →
    (∀ b, custAt σ a e.t ≠ .lockw b) → (∀ w, custAt σ a e.t ≠ .pub w) → custAt σ a e.t ≠ .pte →
    custAt σ a e.t ≠ .racy →
    syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1)

/-! ## The lock layer and the per-hart cells -/

/-- xv6's STATIC spinlocks: both ports' `uarts[i].lock`, `cons.lock`, `pr.lock`,
`kmem.lock`, `pid_lock`, `wait_lock`, `tickslock`, `bcache.lock`,
`itable.lock`, `log.lock`, `ftable.lock`, `disk.vdisk_lock`, every
`proc[i].lock`, and the inner spinlocks of the 30 buffers' and the 50 inodes'
sleeplocks. -/
def xv6StaticLocks : List PAddr :=
  [rsvUartLk 0, rsvUartLk 1, KA.«cons», KA.«pr», KA.«kmem», KA.«pid_lock», KA.«wait_lock»,
    KA.«tickslock», KA.«bcache», KA.«itable», KA.«log», KA.«ftable», rsvDiskLk] ++
  ((List.range 64).map rsvProcLk ++ ((List.range 30).map rsvBufLk ++ (List.range 50).map rsvInodeLk))

/-- The lock words at `σ` as of `t` whose discipline is exported: the static
locks (the dynamic pipe locks are a named gap, see the header). -/
def xv6LockWord (_σ : MState) (b : PAddr) (_t : Nat) : Prop := b ∈ xv6StaticLocks

/-- **The lock layer's discipline**: every lock word's two histories obey the
spinlock kit's discipline (`MachCSL.lockRegionOk` at `&cpus[c]`). -/
def lockWordDiscAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWord σ b t → lockRegionOk (cpuPtrAt KernelGeom.cpusBase) σ.mem b

/-- **`PPerCpu`**: `cpus[h]`'s bytes are written only by `h` after power-on. -/
def cpuStaticAt (σ : MState) : Prop :=
  ∀ (h : CPU) (a : PAddr) (H : Hist) (e : HEnt), a ∈ cpuCellBytes h → σ.mem[a]? = some H →
    e ∈ H → e.t ≠ 0 → e.tid = hartAgent h

/-- **`holding()`'s harmlessness** (W8 (f3-hold) [OWN.64]): for every exported
lock word `b`, its two word histories (`lk->locked` at `b`, `lk->cpu` at
`b + 16`) decompose over the memory as in `lockRegionOk` at a state `st`
obeying the kit's discipline, and every hart `c` that is not `st`'s holder,
reading `lk->cpu` at any view `tvn` with an image value `v0 ≠ &cpus[c]`,
never obtains `&cpus[c]`.  The unlocked `lk->cpu == mycpu()` read of
`holding(lk)` in `acquire` -- a benign race of the same class as `ip->ref`'s
guard (F-RACY, [OWN.63]): an unlocked read of a lock-protected word, benign
by a value argument. -/
def lkCpuReadAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWord σ b t →
    ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool)) (B : Nat),
      wordHistAt σ.mem b 4 W Hold ∧ wordHistAt σ.mem (b + 16#64) 8 W' Hold' ∧
      lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
      ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
        ReadCases W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c

/-- **W8's export** (W8 (f2-ctx): `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt`,
three of the skeleton's six; W8 (f3-hold) [OWN.64]: `lkCpuReadAt`;
`pteDiscAt` open, `cpuProcDiscAt`/`utextDiscAt` W8 (f3-rest)'s). -/
def xv6AccessDisc (σ : MState) : Prop :=
  chainOkAt σ ∧ lockWordDiscAt σ ∧ cpuStaticAt σ ∧ lkCpuReadAt σ

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

/-! ## The extraction -/

/-- Off the exempt classes, a byte is not in the load-side exemption. -/
theorem custAt_notEx {σ : MState} {a : PAddr} {t : Nat} (h1 : ∀ b, custAt σ a t ≠ .lockw b)
    (h2 : ∀ w, custAt σ a t ≠ .pub w) (h3 : custAt σ a t ≠ .pte) (h4 : custAt σ a t ≠ .racy) :
    ¬ chainExAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top a t := by
  unfold custAt at h1 h2 h3 h4
  by_cases c1 : ∃ b, staticLockByteOf b a
  · rw [dif_pos c1] at h1; exact absurd rfl (h1 _)
  rw [dif_neg c1] at h1 h2 h3 h4
  by_cases c2 : ∃ w, pubByteOf w a
  · rw [dif_pos c2] at h2; exact absurd rfl (h2 _)
  rw [dif_neg c2] at h1 h2 h3 h4
  by_cases c3 : ∃ b, dynLockByteAt σ b a t
  · rw [dif_pos c3] at h1; exact absurd rfl (h1 _)
  rw [dif_neg c3] at h1 h2 h3 h4
  by_cases c4 : ptByteLiveAt xv6Rsv σ.mem t a
  · rw [if_pos c4] at h3; exact absurd rfl h3
  rw [if_neg c4] at h1 h2 h3 h4
  by_cases c5 : racyByteIn xv6Rsv a
  · rw [if_pos c5] at h4; exact absurd rfl h4
  rintro (⟨⟨base, kind⟩, hR, hk, ha⟩ | ⟨b, hd, hw⟩ | hp | hr)
  · rcases hk with ⟨cb, hcb⟩ | ⟨w, hw⟩
    · simp only at hcb
      subst hcb
      exact c1 ⟨base, cb, hR, ha⟩
    · simp only at hw
      subst hw
      exact c2 ⟨w, base, hR, ha⟩
  · exact c3 ⟨b, hd, hw⟩
  · exact c4 hp
  · exact c5 hr

/-- **`chainOkAt` from the load-side invariant** (and `mmOk`: every hop's
last acquire is an entry at or below the top). -/
theorem chainOkAt_of (σ : MState) (hmm : mmOk σ)
    (h : loadsChained (xv6Env σ) (chainExAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top)) : chainOkAt σ := by
  intro j a H e hH he het hc hA hne h1 h2 h3 h4
  obtain ⟨τ, hv⟩ := h j a H e hH he het hc hA hne (custAt_notEx h1 h2 h3 h4)
  unfold ChainCert.valid at hv
  rcases hv with ⟨hj, _⟩ | ⟨b', _, hch⟩ | hp
  · exact absurd (congrArg Fin.val hj) hne
  · obtain ⟨b, H', e', hH', he', het'⟩ := hopChain_acq_ent hch
    have hle := ((hmm.1 b H' hH').2 e' he').1
    exact .inl ⟨b', by simp only [MState.top]; omega, hch⟩
  · exact .inr hp

/-- `lockWordDiscAt ∧ cpuStaticAt` from the static list's discipline. -/
theorem lockCpuDisc_of_rsvAllOk (σ : MState) (h : rsvAllOk KernelRsv.static σ.mem) :
    lockWordDiscAt σ ∧ cpuStaticAt σ := by
  refine ⟨fun b t hb => ?_, fun c a H e ha hH he het => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (xv6LockWord_registered σ b t hb)
    exact h i _ hi
  · have hR := h (rsvCpuIdx c) _ (xv6RsvStatic_cpu c)
    exact hR a ha H hH e he het

/-- `lkCpu_read_not_mine` at any image value other than the reader's own
pointer, at the reserved discipline's pointer function `cpuPtrAt cpusBase`
(`= cpuAddr` by `rfl`). -/
theorem lkCpuP_read_not_mine {W : WordHist 8} {st : Option (CPU × Bool)}
    (h : lkCpuAtP (cpuPtrAt KernelGeom.cpusBase) st W) (c : CPU) (hst : ∀ k, st ≠ some (c, k))
    (tvn : Nat) (v0 w : BitVec 64) (hv0 : v0 ≠ cpuAddr c) (hres : ReadCases W (hartAgent c) tvn v0 w) :
    w ≠ cpuAddr c := by
  rcases hres with hr | ⟨_, rfl⟩
  · exact lkCpu_read_not_mine (st := st) h c hst tvn w (Or.inl hr)
  · exact hv0

/-- **(f3-hold) from the lock layer's discipline** [OWN.64]. -/
theorem lkCpuReadAt_of (σ : MState) (h : lockWordDiscAt σ) : lkCpuReadAt σ := by
  intro b t hb
  obtain ⟨W, W', Hold, Hold', st, B, hw, hw', hd⟩ := h b t hb
  exact ⟨W, W', Hold, Hold', st, B, hw, hw', hd,
    fun c hst tvn v0 w hv0 hres => lkCpuP_read_not_mine hd.2.2.2.2 c hst tvn v0 w hv0 hres⟩

/-- **The export from the three pure facts** of the state interpretation. -/
theorem accessDisc_of (σ : MState) (hmm : mmOk σ) (hr : rsvAllOk KernelRsv.static σ.mem)
    (h : loadsChained (xv6Env σ) (chainExAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top)) : xv6AccessDisc σ :=
  have hl := lockCpuDisc_of_rsvAllOk σ hr
  ⟨chainOkAt_of σ hmm h, hl.1, hl.2, lkCpuReadAt_of σ hl.1⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- **THE ACCESS DISCIPLINE, EXTRACTED** (plan [R25.2] (ii), on
`powerInterp_rsvOk`'s pattern): while the power is on, the state
interpretation gives `xv6AccessDisc` -- `mmOk`, the reserved regions'
discipline and the chain conjunct's load-side invariant, at a record whose
static list is xv6's. -/
theorem powerInterp_accessDisc (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (g : GState) :
    powerInterp g ⊢@{IProp GF} ⌜g.pow = true → xv6AccessDisc g.m⌝ := by
  unfold powerInterp eraCur
  cases hpw : g.pow
  · iintro _
    ipureintro
    intro h; cases h
  · iintro ⟨_, _, ⟨%R, _, _, %E, _, Hera⟩, _⟩
    unfold eraInterp memModelAt rsvModelAt chainModelAt
    icases Hera with ⟨_, _, ⟨_, _, _, _, %hmm, ⟨%reg, _, %⟨hin, _, hok⟩⟩, _, %hch, _⟩, _⟩
    ipureintro
    intro _
    have hch' : loadsChained
        (chainEnvAt (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m)
        (chainExAt (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m.mem g.m.top) := hch
    rw [heq] at hch'
    exact accessDisc_of g.m hmm (heq ▸ all_of_reservedOk hin hok) hch'

end AccessDiscipline

end Xv6
