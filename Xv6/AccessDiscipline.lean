/-
**THE ACCESS DISCIPLINE** (weak-allocproc plan §C W8's skeleton, [R25.1],
[R34.1]; W8 (f2-ctx) S4; W8 (f3-hold) [OWN.64]; W8 (f3-racy) [OWN.63]; W8
(f3-pipelk) [OWN.65]; W8 (f3-ptek) [OWN.66]; W8 (f3-utext) [OWN.89]): W8's
export `xv6AccessDisc`, `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt ∧ lkCpuReadAt
∧ pteDiscAt ∧ utextDiscAt ∧ uptDiscAt ∧ kptMapsExp ∧ relProvAt` -- NINE conjuncts:
THREE of the skeleton's six (W8 (f2-ctx)), the ruled `holding()` clause
`lkCpuReadAt` (W8 (f3-hold)), the KERNEL half of the skeleton's A/D
write-back clause `pteDiscAt` (W8 (f3-ptek)), the user code clause
`utextDiscAt` (W8 (f3-utext), O1: every byte a user text leaf maps is at or
below the hart's instruction view), the USER tables' half of the A/D clause
`uptDiscAt` (W8 (f3-utext) T4) and the sealed kernel table's mappings in
plain addresses `kptMapsExp` (mcslrec (1) [OWN.99]) and the release sites'
provenance `relProvAt` (mcslrec (2) [OWN.82] (a1)); `chainOkAt` carries the
ruled `ip->ref` clause `racyValOk` (W8 (f3-racy)); `lockWordDiscAt` and
`lkCpuReadAt` cover EVERY lock -- the static spinlocks and the live pipe
locks (W8 (f3-pipelk)).

**ONE benign-race class, two instances** ([OWN.63], [OWN.64]; plan §A(4′)):
UNLOCKED reads of LOCK-PROTECTED words, harmless by a VALUE argument -- both
C11 data races (real defects of the C program), benign on hardware (aligned
word accesses, coherence):
  - `holding()`'s read of `lk->cpu` by a non-holder inside `acquire`
    (`spinlock.c`): `lkCpuReadAt` -- whatever it reads is not its own
    pointer;
  - `ilock`'s/`iunlock`'s guard `ip->ref < 1` (`fs.c`), read without
    `itable.lock`: `chainOkAt`'s `racyValOk` arm -- every unchained value a
    hart observed on `ip->ref` is `≥ 1` (the caller holds its own
    reference).
Each is stated as a VALUE clause of the export, NOT an exemption.  NOT exported here: the USER
tables' half of the A/D write-back clause as of the tables' creation
[R25.1], [OWN.66] (W8 (f3-pteu) T1; T4, from userret's stamp on, IS exported:
`uptDiscAt`); `cpuProcDiscAt` is permanently
OUT of the export ([OWN.80]: W11-D needs no `kOwnerAt` uniqueness).  Later
items only STRENGTHEN the conjunction.

* `Cust` (the custody classes, W8-design §1 with [R25.1]'s `pte`, and the
  S3 classes `pub` (exempt), `racy` (value-qualified)) and the custody map `custAt σ a
  t`, σ-READABLE (a predicate of the memory and xv6's static registry
  `KernelRsv.static`, no ghost state), its arms read off the load-side
  invariant's exemption `MachCSL.chainExAt`, in this order:
  - `lockw b`: a byte of the two words (`lk->locked`, `lk->cpu`) of a STATIC
    spinlock at `b` of the registry; or of a DYNAMIC (pipe) lock at `b` live
    as of `t` (`xv6DynLock`, `MachCSL.dynLkDiscAt`: an `f->pipe` slot named
    `b` at `te`, every later entry on `b`'s word up to `t` is word-sized --
    the ruled (a′) window [OWN.46], [OWN.49] (a′-r) -- AND the lock words'
    history over a window `(p, t]` opening at or before `te` is a lock
    history from free: the WINDOWED `lockRegionOk` [R36.3], W8 (f3-pipelk)
    [OWN.65]).  So every lock word this class exempts from `chainOkAt` is
    covered by `lockWordDiscAt` and `lkCpuReadAt`: a byte whose `f->pipe`
    window is NOT so disciplined is not exempt (`chainOkAt` claims its
    chains).  The window's discipline is proved at every racy read of a
    pipe lock's word, from the lock's invariant (`Lock.lkDynRegW`: the
    registration at or past both words' `initlock` floors, every time-cut
    of the post-birth histories a lock history from free, `Lock.lkCutsOk`;
    `Lock.dynLkDiscAt_of`); it ends σ-readably at the reclaim (`kfree`'s
    junk fill is byte stores: no later `t` is live);
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
    `ip->ref < 1`).  NOT an exemption class since W8 (f3-racy) [OWN.63]
    (finding F-RACY's weakening is gone): `chainOkAt` claims for such a byte
    a sync path OR the value clause `racyValOk` -- the word, as of the
    observed entry's position, is in the registry's value set `[1, 2^31)`,
    i.e. the guard reads `≥ 1` (proved: `IcachePinwObl.iref_certs`, from
    `irefSet`'s window invariant).  The race is real and benign -- the SAME
    defect class as `lkCpuReadAt` below (see "ONE benign-race class");
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
  (`lockw`, `pub`, `pte`), an entry SYNC-CHAINED to `j` before
  `σ.top + 1` -- or, on a `racy` byte (`ip->ref`), one AS OF which the word
  is in the value set (`racyValOk`, W8 (f3-racy) [OWN.63]: "every unchained
  value a hart observed on `ip->ref` is `≥ 1`").  Spec: RVWMO lets the
  guard's load return any store not coherence-before what the hart has
  observed; riscv.cat/Sail/Zifencei/PMAs say nothing about custody --
  FAITHFUL (a value theorem about the program, no ISA assumption added).
* `xv6LockWord σ b t` (W8 (f3-pipelk) [OWN.65]: EVERY lock): `b` is the
  lock word of one of xv6's 157 STATIC image spinlocks (`xv6StaticLocks`),
  or of a pipe lock live as of `t` (`xv6DynLock`, the `lockw` class's
  dynamic arm).
* `lockWordDiscAt σ`: every such lock's two word histories obey the spinlock
  kit's discipline -- a static lock's whole histories (`MachCSL.lockRegionOk`:
  whole-word histories over the image, every post-power-on entry a hart's,
  the lock word 0/1, the holder fold legal, `lk->cpu` entries 0 or the
  writer's own `&cpus[c]`), a pipe lock's over its window `(p, t]`, `p` at or
  before the `f->pipe` store that named it (`dynLockWinAt`,
  `MachCSL.lockWinAt`: the same discipline from free, the owner word's
  pointers into xv6's `cpus`).
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
  `acquire` does not panic).  The SAME defect class as `ip->ref`'s guard
  (`chainOkAt`'s `racyValOk`, [OWN.63], W8 (f3-racy)): unlocked reads of
  lock-protected words, benign by a value argument.  A
  corollary of `lockWordDiscAt` (`MachCSL.lkCpu_read_not_mine`).  EVERY
  lock, as `xv6LockWord` (W8 (f3-pipelk) [OWN.65]): a pipe lock's over its
  window, the initial value its window's opening's (`initlock`'s 0).  Spec:
  RVWMO/riscv.cat/Sail are SILENT on lock disciplines (a proof notion);
  the reads quantified are every value RVWMO lets the load return under the
  discipline -- FAITHFUL.

**The registration lemma** [R26.1] (`xv6LockWord_registered`): every lock
word is registered -- a static region, or named by a registered `f->pipe`
slot.

**`powerInterp_accessDisc`** (on `MachCSL.powerInterp_rsvOk`'s pattern): the
state interpretation gives `g.pow = true → xv6AccessDisc g.m`, at a record
whose static list is xv6's -- `chainOkAt` from the chain conjunct's
load-side invariant (`MachCSL.loadsChained`, S3) and `mmOk` (the deadline),
`lockWordDiscAt ∧ cpuStaticAt ∧ lkCpuReadAt` from the reserved regions'
discipline (static locks, `cpus`) and the live window's definition (pipe
locks: the registry's `cpus` cells fix the owner word's pointers,
`xv6Rsv_cpuBase`), `pteDiscAt` from the sealed kernel table's record
(`MachCSL.kptStateOk`: its fragments agree with the heap).

Deviations from the plan's skeleton: the definitions are at xv6's
`KernelGeom` instance (`Xv6.Geom`), not under a `[KernelGeom]` binder; the
boot hop is `pubCover` (the implemented [R36.1] form), not "`t ≤ bootEnd`";
the exemption has the S3 class `pub` beyond `lockw`/`pte` (S3's `dev` retired
by W8 (f3-gate); S3's `racy` value-qualified by W8 (f3-racy)); W8 (f3-pipelk)
[OWN.65]: the pipe locks' windowed discipline is carried by each lock's
invariant and stated in the σ-readable live window (`MachCSL.dynLkDiscAt`, the
exemption's dynamic arm) -- not by a dynamic registry in `reservedOk` (see
`PROGRESS-W8pipelk.md`).
-/
import Xv6.KernelRsv
import MachCSL.Adequacy
import MachCSL.Lock
import MachCSL.UEpochDisc

namespace Xv6

namespace AccessDiscipline

open Iris Iris.BI Iris.ProofMode Std MachCSL

/-! ## The custody map -/

/-- The custody classes (W8-design §1; [R25.1]'s `pte`; S3's `pub`, `racy` --
`racy` value-qualified, not exempt, since W8 (f3-racy)). -/
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
  /-- an audited racy word's byte (`ip->ref`: chained or value-safe, `racyValOk`) -/
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

/-- **A live dynamic (pipe) lock at `b` as of `t`** (W8 (f3-pipelk) [OWN.65]):
`MachCSL.dynLkDiscAt` over the registry's `f->pipe` slots -- a slot store
named `b` at `te ≤ t`, every later entry on `b`'s lock word up to `t` is
word-sized, and the lock words' history over a window `(p, t]` with `p ≤ te`
is a lock history from free, the owner-word pointers those of the registry's
`cpus` array. -/
def xv6DynLock (σ : MState) (b : PAddr) (t : Nat) : Prop :=
  dynLkDiscAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top b t

/-- `a` is a byte of the two words of a live dynamic lock at `b` as of `t`, and (mcslrec (3) X1-c
[OWN.90] [OWN.104] (b)) no kernel-stack byte as of `t` (`MachCSL.ksByteAt`: `stack0`, or -- the
boot gate open -- a page the kernel table maps at a `KSTACK(i)`): a pipe lock never lives on a
kernel stack, so its exemption never reaches a stack frame. -/
def dynLockByteAt (σ : MState) (b a : PAddr) (t : Nat) : Prop :=
  xv6DynLock σ b t ∧ lockWordsByte b a ∧ ¬ ksByteAt xv6Rsv σ.mem t a

open Classical in
/-- **The custody map** (σ-readable): the exempt classes first, in the order
of `MachCSL.chainExAt`'s arms (static lock words, publication words, live
dynamic lock words, LIVE page-table bytes as of `t` -- no freed page of a
freeable table, W8 (pte-ghost) [OWN.57], up to the as-of-entry residual of
the header --, audited racy words (`ip->ref`; value-qualified in
`chainOkAt`, W8 (f3-racy))), then `cpus[h]`'s cells, then `free`. -/
noncomputable def custAt (σ : MState) (a : PAddr) (t : Nat) : Cust :=
  if h1 : ∃ b, staticLockByteOf b a then .lockw (Classical.choose h1) else
  if h2 : ∃ w, pubByteOf w a then .pub (Classical.choose h2) else
  if h3 : ∃ b, dynLockByteAt σ b a t then .lockw (Classical.choose h3) else
  if ptByteExAt xv6Rsv σ.mem t a then .pte else
  if racyByteIn xv6Rsv a then .racy else
  if h7 : ∃ c, a ∈ cpuCellBytes c then .hart (Classical.choose h7) else .free

/-! ## Sync paths and the chain conjunct -/

/-- The certificate environment of `σ` at xv6's registry. -/
def xv6Env (σ : MState) : ChainEnv := chainEnvAt xv6Rsv KernelRsv.relPcs (slotWit xv6Rsv) σ

/-- `b` is a hop byte for an acquire at `a`: a static spinlock's lock byte,
or a dynamic lock's live as of `a` whose release under the acquire was issued
at a release site (mcslrec (2) [OWN.82] (a1), Q-MCSL2-DYN ruled (i): the
pc clause the winning AMO's hop carries, `MachCSL.relBelowOk`). -/
def hopByteAt (σ : MState) (b : PAddr) (a : Nat) : Prop :=
  lockByteIn xv6Rsv b ∨ (dynLkAt (slotWit xv6Rsv) σ.mem σ.top b a ∧ relBelowOk KernelRsv.relPcs σ b a)

/-- **A sync path** from the entries of hart `A` at or below `t` to hart `B`
before `τ`: release → acquire hops through hop bytes, the last acquire below
`τ`; or the boot hop (`B` read the publication store `A`'s entries precede). -/
def syncPath (σ : MState) (A : CPU) (t : Nat) (B : CPU) (τ : Nat) : Prop :=
  (∃ a, a < τ ∧ hopChain σ.mem (hopByteAt σ) A t B a) ∨ pubCover (xv6Env σ) A t B

/-- **The racy word's value clause** (W8 (f3-racy) [OWN.63]): `a` is a byte
of an audited racy word whose value AS OF position `t` lies in the registry's
value set -- for xv6's one racy region (`ip->ref`, `KernelRsv.xv6IrefRacyR`)
the 4-byte word read as an unsigned number is in `[1, 2^31)`, i.e. as the
signed `int` the guard `ip->ref < 1` compares, `≥ 1`. -/
def racyValOk (σ : MState) (a : PAddr) (t : Nat) : Prop := racyValAt xv6Rsv σ.mem t a

/-- **(iii+) Every observed foreign hart entry off the exempt classes is
sync-chained, and on an audited racy word it is chained OR value-safe**: hart
`j`'s coherence floor at `a` names a post-power-on entry of a hart other than
`j`; unless the byte is, as of the entry, a lock-layer word, a publication
word or a LIVE page-table byte (no page of a freeable table from its push onto
the free list on; the as-of-entry residual of the header), that entry reaches
`j` along a sync path (the virtio used ring included: W8 (f3-gate) [OWN.62]),
or the byte is an audited racy word's (`ip->ref`) and the word, as of the
entry, is in the value set (`racyValOk`: every unchained value a hart
observed on `ip->ref` is `≥ 1` -- W8 (f3-racy) [OWN.63], replacing F-RACY's
exemption). -/
def chainOkAt (σ : MState) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
    e.t = (σ.hr j).coh a → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j →
    (∀ b, custAt σ a e.t ≠ .lockw b) → (∀ w, custAt σ a e.t ≠ .pub w) → custAt σ a e.t ≠ .pte →
    syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1) ∨ (custAt σ a e.t = .racy ∧ racyValOk σ a e.t)

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

/-- **The lock words at `σ` as of `t`** (W8 (f3-pipelk) [OWN.65]: EVERY lock):
the static locks, and the dynamic (pipe) locks live as of `t`. -/
def xv6LockWord (σ : MState) (b : PAddr) (t : Nat) : Prop := b ∈ xv6StaticLocks ∨ xv6DynLock σ b t

/-- A dynamic lock's WINDOWED discipline as of `t` [R36.3]: a registered
`f->pipe` slot named `b` at `te ≤ t`, and the lock words' history over a
window `(p, t]` opening at or before `te` is a lock history from free, the
owner word's entries 0 or the writer's own `&cpus[c]`
(`MachCSL.lockWinAt`). -/
def dynLockWinAt (σ : MState) (b : PAddr) (t : Nat) : Prop :=
  ∃ (L : List (PAddr × HEnt)) (te p : Nat), slotWit xv6Rsv L b te ∧ p ≤ te ∧ te ≤ t ∧
    lockWinAt (cpuPtrAt KernelGeom.cpusBase) σ.mem b p t

/-- **The lock layer's discipline** (W8 (f3-pipelk) [OWN.65]: every lock):
a static lock's two histories obey the spinlock kit's discipline over the
whole history (`MachCSL.lockRegionOk` at `&cpus[c]`); a live dynamic lock's,
over its window (`dynLockWinAt`). -/
def lockWordDiscAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWord σ b t →
    (b ∈ xv6StaticLocks → lockRegionOk (cpuPtrAt KernelGeom.cpusBase) σ.mem b) ∧
    (xv6DynLock σ b t → dynLockWinAt σ b t)

/-- **`PPerCpu`**: `cpus[h]`'s bytes are written only by `h` after power-on. -/
def cpuStaticAt (σ : MState) : Prop :=
  ∀ (h : CPU) (a : PAddr) (H : Hist) (e : HEnt), a ∈ cpuCellBytes h → σ.mem[a]? = some H →
    e ∈ H → e.t ≠ 0 → e.tid = hartAgent h

/-- **`holding()`'s harmlessness** (W8 (f3-hold) [OWN.64]; W8 (f3-pipelk)
[OWN.65]: every lock): for every lock word `b` as of `t`, its two word
histories -- a STATIC lock's whole histories (`lk->locked` at `b`, `lk->cpu`
at `b + 16`, over the image), a live DYNAMIC lock's over its window `(p, t]`
(`p` at or before the `f->pipe` store that named it) -- decompose as word
histories `W`/`W'` at a state `st` obeying the kit's discipline, and every
hart `c` that is not `st`'s holder, reading `lk->cpu` at any view `tvn` with
an initial value `v0 ≠ &cpus[c]` (the image's, resp. the value as of the
window's opening -- `initlock`'s 0), never obtains `&cpus[c]`.  The unlocked
`lk->cpu == mycpu()` read of `holding(lk)` in `acquire` -- a benign race of
the same class as `ip->ref`'s guard (`chainOkAt`'s `racyValOk`, [OWN.63]):
an unlocked read of a lock-protected word, benign by a value argument. -/
def lkCpuReadAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWord σ b t →
    (b ∈ xv6StaticLocks →
      ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool)) (B : Nat),
        wordHistAt σ.mem b 4 W Hold ∧ wordHistAt σ.mem (b + 16#64) 8 W' Hold' ∧
        lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
        ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
          ReadCases W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c) ∧
    (xv6DynLock σ b t →
      ∃ (L : List (PAddr × HEnt)) (te p : Nat) (W : WordHist 4) (W' : WordHist 8) (st : Option (CPU × Bool))
        (B : Nat), slotWit xv6Rsv L b te ∧ p ≤ te ∧ te ≤ t ∧
        (∀ j, j < 4 → ∃ H, σ.mem[b + BitVec.ofNat 64 j]? = some H ∧ H.filter (lkWinIn p t) = W.map (WEnt.proj j)) ∧
        (∀ j, j < 8 → ∃ H, σ.mem[b + 16#64 + BitVec.ofNat 64 j]? = some H ∧
          H.filter (lkWinIn p t) = W'.map (WEnt.proj j)) ∧
        lockDiscWin (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
        ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
          ReadCases W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c)

/-! ## The kernel page table's discipline (W8 (f3-ptek))

[OWN.66] (Q-PTEDISC = (P-a)), kernel half: "after the seal every entry is the
sealed value up to A/D".  Stated σ-readably here and carried by a pure fact
of the state interpretation: the sealed table's record (`MachCSL.kptModelAt`,
registered at `MachCSL.kptOn_seal`: the interpretation holds a discarded
fragment of every frozen slot and half of every leaf, `MachCSL.kpt_exclWriteAU`
the leaves' only writer) -- the final hook gets the interpretation under `◇`
only, so no invariant is opened there (`pteDiscAt_of`).

The seal is not a memory event, so the clause names a position `S` and pins
it from both sides by memory events: every post-power-on entry of the root
word `kernel_pagetable` is at or before `S` (once `kvminit` has stored the
root, `S` is past that store, and the root is frozen after `S`), and every
post-power-on entry of the boot gate `started` is after `S` (the seal
precedes `started = 1`, so every hart but the boot hart runs after `S`).
Spec: the privileged spec's Svadu A/D update is atomic per PTE; Sail
performs it as `read_pte_exclusive`/`write_pte_conditional`
(`Vmem.lean:237`/`:228`) -- one whole doubleword store of the same entry
with A/D possibly set; RVWMO orders implicit page-table accesses only via
`SFENCE.VMA`; Zifencei/PMAs silent.  FAITHFUL: a value fact of xv6's runs,
no ISA assumption. -/

/-- The kernel root word's bytes (`kernel_pagetable`, 8 bytes). -/
def kptRootBytes : List PAddr := wordBytes (KA.«kernel_pagetable», 8)

/-- **A seal position** `S` of the kernel table at `σ`: at or below the top,
past every post-power-on entry of the root word, before every post-power-on
entry of `started`. -/
def kptSealAt (σ : MState) (S : Nat) : Prop :=
  S ≤ σ.top ∧
  (∀ a ∈ kptRootBytes, ∀ H, σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ 0 → e.t ≤ S) ∧
  (∀ a ∈ xv6StartedR.bytes, ∀ H, σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ 0 → S < e.t)

/-- **One slot's discipline after `S`**: every entry after `S` on a byte of
the 8-byte slot at `addr` is a HART's (no DMA author), and part of one
WHOLE-doubleword store, at the same position by the same hart, of an A/D
variant of `c` (`MachCSL.pteVariant`: a leaf at any A/D, any other entry
exactly). -/
def kptSlotDisc (σ : MState) (S : Nat) (addr : PAddr) (c : BitVec 64) : Prop :=
  ∀ (j : Nat) (H : Hist) (e : HEnt), j < 8 → σ.mem[addr + BitVec.ofNat 64 j]? = some H → e ∈ H → S < e.t →
    e.tid < NCPU ∧ ∃ v : BitVec 64, pteVariant c v ∧ e.v = nthByte (n := 8) v j ∧
      ∀ j', j' < 8 → ∃ H', σ.mem[addr + BitVec.ofNat 64 j']? = some H' ∧
        (⟨e.t, e.tid, nthByte (n := 8) v j'⟩ : HEnt) ∈ H'

/-- **`pteDiscAt`, the kernel table** ([OWN.66] (P-a), W8 (f3-ptek)):
there is a seal position `S` (`kptSealAt`) such that every slot of the
kernel table as of `S` -- an aligned doubleword in a page a Sv39 walk reaches,
as of `S`, from the permanent root `kernel_pagetable` (`MachCSL.ptByteAt`) --
holding `c` as of `S`, is after `S` written only by harts, whole, with A/D
variants of `c`: a leaf's A/D bits may change, nothing else of any entry. -/
def pteDiscAt (σ : MState) : Prop :=
  ∃ S : Nat, kptSealAt σ S ∧ ∀ (addr : PAddr) (c : BitVec 64), addr.toNat % 8 = 0 →
    ptByteAt xv6Rsv σ.mem S addr → wordAsOf σ.mem addr S c → kptSlotDisc σ S addr c

/-- Before the boot gate opens the clause is trivial (`S` = the top: no entry
is above it) -- its content is the run after `started = 1`, where `S` is pinned
below the gate's store. -/
theorem pteDiscAt_preGate (σ : MState) (hmm : mmOk σ)
    (hg : ∀ a ∈ xv6StartedR.bytes, ∀ H, σ.mem[a]? = some H → ∀ e ∈ H, e.t = 0) :
    pteDiscAt σ := by
  have hle : ∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≤ σ.top :=
    fun a H e hH he => by simp only [MState.top]; exact ((hmm.1 a H hH).2 e he).1
  refine ⟨σ.top, ⟨Nat.le_refl _, fun a _ H hH e he _ => hle a H e hH he,
    fun a ha H hH e he h0 => absurd (hg a ha H hH e he) h0⟩, ?_⟩
  intro addr c _ _ _ j H e _ hH he hS
  exact absurd (hle _ H e hH he) (Nat.not_le.2 hS)

/-! ### `pteDiscAt` from the interpretation's record of the sealed table

The record (`MachCSL.kptStateOk`, read off `MachCSL.kptModelAt`): before
the seal `started` is unwritten (`pteDiscAt_preGate`); from the seal on, the
seal's facts (`MachCSL.kptSealOk`: the root word a frozen slot naming a
sealed page, the pointer closure, the leaves' shape, `started` after the
seal) and every sealed slot's histories disciplined (`MachCSL.kslotHistOk`).
A walk from the root as of the seal visits only sealed pages (the converse
of `MachCSL.KptInv.leaf_ptByteAt`): a leaf is no pointer, a frozen slot's
value as of the seal is its canonical one. -/

/-- `started` is a publication word of xv6's list. -/
theorem xv6StartedR_mem : xv6StartedR ∈ xv6RsvStatic := by decide +kernel

/-- A variant of a variant of `c` is a variant of the first. -/
theorem pteVariant_trans {c v w : BitVec 64} (hv : pteVariant c v) (hw : pteVariant c w) : pteVariant v w := by
  rcases hv with rfl | ⟨ppn, perm, a, d, a', d', rfl, rfl⟩
  · exact hw
  · obtain ⟨a'', d'', rfl⟩ := pteVariant_of_kLeaf ppn perm a d hw
    exact pteVariant_kLeaf ppn perm a' d' a'' d''

/-- A page a pointer names is page-aligned. -/
theorem ptPtrTo_aligned {v : BitVec 64} {p : PAddr} (h : ptPtrTo v p) : p.toNat % 4096 = 0 := by
  obtain ⟨_, _, rfl⟩ := h
  rw [BitVec.toNat_and, show (4096 : Nat) = 2 ^ 12 from rfl, Nat.and_mod_two_pow]
  have hm : (0x00FFFFFFFFFFF000#64).toNat % 2 ^ 12 = 0 := by decide
  rw [hm, Nat.and_zero]

/-- The doubleword at `a` as of `S`, read off its histories. -/
theorem kptHist_word {m : FlatMem} {a : PAddr} {S : Nat} {Hs : Nat → Hist} {v w : BitVec 64}
    (hm : ∀ j, j < 8 → m[a + BitVec.ofNat 64 j]? = some (Hs j)) (hh : histWordAsOf Hs S v)
    (hw : wordAsOf m a S w) : w = v := by
  apply bv_eq_of_bytes (n := 8)
  intro j hj
  have h1 := hw j hj
  unfold FlatMem.entAsOf at h1
  rw [hm j hj, Option.bind_some, hh j hj] at h1
  exact (Option.some.inj h1).symm

/-- A sealed slot's value as of the seal: its canonical value (frozen) or
a variant of it (a leaf). -/
theorem kptSlot_asOf {m : FlatMem} {S : Nat} {dyn : List KSlot} (hh : kptHistsAt m S dyn) {d : KSlot}
    (hd : d ∈ dyn) {v : BitVec 64} (hv : wordAsOf m d.addr S v) :
    if d.frozen then v = d.c else pteVariant d.c v := by
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, _⟩ := hh d hd
  rw [kptHist_word hm hv0 hv]
  exact hc0

/-- A child, as of the seal, of a sealed page is a sealed page. -/
theorem kptChild_in {rs : List RsvRegion} {m : FlatMem} {top S : Nat} {dyn : List KSlot}
    (hok : kptSealOk rs m top S dyn) (hh : kptHistsAt m S dyn) {q p : PAddr} (hq : pageIn dyn q)
    (hc : ptChildAt m S q p) : pageIn dyn p := by
  obtain ⟨i, v, hi, hv, hp⟩ := hc
  obtain ⟨d, hd, haddr⟩ := hq i hi
  have hs := kptSlot_asOf hh hd (v := v) (by rw [haddr]; exact hv)
  cases hfz : d.frozen
  · simp only [hfz, Bool.false_eq_true, ↓reduceIte] at hs
    obtain ⟨ppn, perm, a, dd, hcd⟩ := (hok.2.2.1 d hd).1 hfz
    rw [hcd] at hs
    obtain ⟨a', d', rfl⟩ := pteVariant_of_kLeaf ppn perm a dd hs
    exact absurd hp (KptInv.not_ptPtrTo_kLeaf ppn perm a' d' p)
  · simp only [hfz, ↓reduceIte] at hs
    subst hs
    exact hok.2.2.2.2 d hd hfz p hp

/-- A root page, as of the seal, of a permanent root word is a sealed,
page-aligned page. -/
theorem kptRoot_in {rs : List RsvRegion} {m : FlatMem} {top S : Nat} {dyn : List KSlot}
    (hok : kptSealOk rs m top S dyn) (hh : kptHistsAt m S dyn) {r : PAddr} (hr : ptRootAt rs m S r) :
    pageIn dyn r ∧ r.toNat % 4096 = 0 := by
  obtain ⟨hr0, base, cnt, stride, k, hR, hk, hw⟩ := hr
  obtain ⟨d, hd, haddr, hfz, halign, hpage⟩ := hok.2.2.2.1 base cnt stride k hR hk
  have hs := kptSlot_asOf hh hd (v := r) (by rw [haddr]; exact hw)
  simp only [hfz, ↓reduceIte] at hs
  subst hs
  exact ⟨hpage hr0, halign⟩

/-- Every page a walk from a sealed root page visits as of the seal is a
sealed, page-aligned page. -/
theorem kptPage_in {rs : List RsvRegion} {m : FlatMem} {top S : Nat} {dyn : List KSlot}
    (hok : kptSealOk rs m top S dyn) (hh : kptHistsAt m S dyn) {r p : PAddr} (hr : pageIn dyn r)
    (hra : r.toNat % 4096 = 0) (hp : ptPageAt m S r p) : pageIn dyn p ∧ p.toNat % 4096 = 0 := by
  rcases hp with rfl | hc | ⟨q, h1, h2⟩
  · exact ⟨hr, hra⟩
  · obtain ⟨_, _, _, _, hpp⟩ := id hc
    exact ⟨kptChild_in hok hh hr hc, ptPtrTo_aligned hpp⟩
  · obtain ⟨_, _, _, _, hpp⟩ := id h2
    exact ⟨kptChild_in hok hh (kptChild_in hok hh hr h1) h2, ptPtrTo_aligned hpp⟩

/-- **`pteDiscAt` from the sealed table's record.** -/
theorem pteDiscAt_of (σ : MState) (hmm : mmOk σ) (hk : kptStateOk xv6Rsv σ) : pteDiscAt σ := by
  obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh⟩⟩ := hk
  · exact pteDiscAt_preGate σ hmm (fun a ha H hH e he => hclean _ _ xv6StartedR_mem a ha H hH e he)
  refine ⟨S, ⟨hok.1, ?_, fun a ha H hH e he he0 => hok.2.1 _ _ xv6StartedR_mem a ha H hH e he he0⟩, ?_⟩
  · intro a ha H hH e he _
    obtain ⟨d, hd, haddr, hfz, -, -⟩ := hok.2.2.2.1 KA.«kernel_pagetable» 1 8 0 xv6RsvStatic_kptRoot (by decide)
    obtain ⟨Hs, hm, -, hent⟩ := hh d hd
    simp only [kptRootBytes, wordBytes, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hda : d.addr = KA.«kernel_pagetable» := by rw [haddr]; simp
    rw [← hda, hm j hj] at hH
    obtain rfl := Option.some.inj hH
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have := (hent j hj e he hlt).1
    rw [hfz] at this
    cases this
  · intro addr c halign hpt hw
    obtain ⟨r, p, hroot, hpage, hlo, hhi⟩ := hpt
    obtain ⟨hpr, hra⟩ := kptRoot_in hok hh hroot
    obtain ⟨hpp, hpa⟩ := kptPage_in hok hh hpr hra hpage
    obtain ⟨d, hd, hdaddr⟩ := hpp ((addr.toNat - p.toNat) / 8) (by omega)
    have haddr : d.addr = addr := by
      rw [hdaddr]
      apply BitVec.eq_of_toNat_eq
      have := addr.isLt
      have := p.isLt
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ := hh d hd
    rw [haddr] at hm
    have hc := kptHist_word hm hv0 hw
    subst hc
    intro j H e hj hH he hSe
    rw [hm j hj] at hH
    obtain rfl := Option.some.inj hH
    obtain ⟨hfz, htid, v, hv, hev, hall⟩ := hent j hj e he hSe
    simp only [hfz, Bool.false_eq_true, ↓reduceIte] at hc0
    exact ⟨htid, v, pteVariant_trans hc0 hv, hev, fun j' hj' => ⟨Hs j', hm j' hj', hall j' hj'⟩⟩

/-! ### The sealed kernel table's mappings, in plain addresses (mcslrec (1), [OWN.99] (B)) -/

/-- **One kernel mapping's walk at the seal `S` from the root page `b`, in plain addresses**:
the root page's slot `kSlotP b (kIdxP vpn 2)` holds, as of `S`, a pointer to the page `b1`,
`b1`'s slot `kIdxP vpn 1` a pointer to `b0`, `b0`'s slot `kIdxP vpn 0` an A/D variant of the
leaf `kLeaf ppn perm a d`; each slot disciplined after `S` (`kptSlotDisc`). -/
def kptWalkP (σ : MState) (S : Nat) (b : BitVec 44) (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm) :
    Prop :=
  ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
    wordAsOf σ.mem (kSlotP b (kIdxP vpn 2)) S (kPtr b1) ∧ kptSlotDisc σ S (kSlotP b (kIdxP vpn 2)) (kPtr b1) ∧
    wordAsOf σ.mem (kSlotP b1 (kIdxP vpn 1)) S (kPtr b0) ∧ kptSlotDisc σ S (kSlotP b1 (kIdxP vpn 1)) (kPtr b0) ∧
    (∃ v, wordAsOf σ.mem (kSlotP b0 (kIdxP vpn 0)) S v ∧ pteVariant (kLeaf ppn perm a d) v) ∧
    kptSlotDisc σ S (kSlotP b0 (kIdxP vpn 0)) (kLeaf ppn perm a d)

/-- **`kptMapsExp`, THE SEALED KERNEL TABLE'S MAPPINGS** (mcslrec (1), [OWN.99] (B): a
self-contained statement in plain addresses and bit fields): before the boot gate (`started`
unwritten) nothing; from then on there is a seal position `S` (`kptSealAt`) at which the root word
`kernel_pagetable` holds the root page `b · 4096`, and for each of the kernel's mappings
(`kMapP pas`: the text `0x80000000 ..< 0x80007000` identity `R|X`, the rest of RAM `..<
0x88000000` identity `R|W`, the 64 kernel stacks `R|W` at some pages `pas i`) the Sv39 walk from
`b` reads two pointers and an A/D variant of the leaf (`kptWalkP`), each slot written after `S`
only by harts, whole, with A/D variants (`kptSlotDisc`).  From the interpretation's sealed-table
record, which keeps xv6's shape of the sealed slots (`KernelRsv.kptOk` = `xv6KptOk`, registered at
`Xv6.KptBoot` from `kvmmake`'s table).  Spec: the privileged spec's Sv39 (three levels, `pt_base
@ vpn_i @ 0b000`, a leaf `V ∧ (R ∨ X)`); Svadu A/D updates whole-PTE.  FAITHFUL: facts of xv6's
table, no ISA assumption.  Consumers: `Xv6.kptMapsAt_ofExp`, `Xv6.kptTextAt_ofExp`. -/
def kptMapsExp (σ : MState) : Prop :=
  (∀ a ∈ xv6StartedR.bytes, ∀ H : Hist, σ.mem[a]? = some H → ∀ e ∈ H, e.t = 0) ∨
  ∃ (pas : Nat → BitVec 44) (S : Nat) (b : BitVec 44), kptSealAt σ S ∧
    wordAsOf σ.mem KA.«kernel_pagetable» S (kSlotP b 0) ∧
    ∀ (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm), kMapP pas vpn ppn perm → kptWalkP σ S b vpn ppn perm

/-- A sealed slot of the record: its value as of the seal (exact if frozen, a variant if a leaf)
and its discipline after the seal. -/
theorem kptDynSlot {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAt σ.mem S dyn) {d : KSlot}
    (hd : d ∈ dyn) :
    ∃ v, wordAsOf σ.mem d.addr S v ∧ (if d.frozen then v = d.c else pteVariant d.c v) ∧
      kptSlotDisc σ S d.addr d.c := by
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ := hh d hd
  refine ⟨v0, fun j hj => ?_, hc0, ?_⟩
  · unfold FlatMem.entAsOf
    rw [hm j hj, Option.bind_some]
    exact hv0 j hj
  · intro j H e hj hH he' hSe
    rw [hm j hj] at hH
    obtain rfl := Option.some.inj hH
    obtain ⟨_, htid, v, hv, hev, hall⟩ := hent j hj e he' hSe
    exact ⟨htid, v, hv, hev, fun j' hj' => ⟨Hs j', hm j' hj', hall j' hj'⟩⟩

theorem kptDynFrozen {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAt σ.mem S dyn)
    {a : PAddr} {c : BitVec 64} (hd : (⟨a, c, true⟩ : KSlot) ∈ dyn) :
    wordAsOf σ.mem a S c ∧ kptSlotDisc σ S a c := by
  obtain ⟨v, hw, hif, hdisc⟩ := kptDynSlot hh hd
  simp only [if_true] at hif
  subst hif
  exact ⟨hw, hdisc⟩

theorem kptDynLeaf {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAt σ.mem S dyn)
    {a : PAddr} {c : BitVec 64} (hd : (⟨a, c, false⟩ : KSlot) ∈ dyn) :
    (∃ v, wordAsOf σ.mem a S v ∧ pteVariant c v) ∧ kptSlotDisc σ S a c := by
  obtain ⟨v, hw, hif, hdisc⟩ := kptDynSlot hh hd
  simp only [Bool.false_eq_true, if_false] at hif
  exact ⟨⟨v, hw, hif⟩, hdisc⟩

/-- **`kptMapsExp` from the record** with xv6's shape of the sealed slots. -/
theorem kptMapsExp_of (σ : MState) (hk : kptStateOkK xv6Rsv xv6KptOk σ) : kptMapsExp σ := by
  obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh, ⟨pas, b, hroot, hmaps, -⟩⟩⟩ := hk
  · exact Or.inl (fun a ha H hH e he => hclean _ _ xv6StartedR_mem a ha H hH e he)
  right
  obtain ⟨hrw, -⟩ := kptDynFrozen hh hroot
  refine ⟨pas, S, b, ⟨hok.1, ?_, fun a ha H hH e he he0 => hok.2.1 _ _ xv6StartedR_mem a ha H hH e he he0⟩,
    hrw, fun vpn ppn perm hm => ?_⟩
  · intro a ha H hH e he _
    obtain ⟨Hs, hm, -, hent⟩ := hh _ hroot
    simp only [kptRootBytes, wordBytes, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hm' := hm j hj
    simp only at hm'
    rw [hm'] at hH
    obtain rfl := Option.some.inj hH
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have := (hent j hj e he hlt).1
    cases this
  · obtain ⟨b1, b0, a, d, h2, h1, h0⟩ := hmaps vpn ppn perm hm
    obtain ⟨w2, d2⟩ := kptDynFrozen hh h2
    obtain ⟨w1, d1⟩ := kptDynFrozen hh h1
    obtain ⟨w0, d0⟩ := kptDynLeaf hh h0
    exact ⟨b1, b0, a, d, w2, d2, w1, d1, w0, d0⟩

/-! ### The kernel-stack pages past the seal (mcslrec (3) X1-b, [OWN.90] [OWN.104] (b))

As of every position past the seal, the permanent root's walk at a `KSTACK(i)` page reads the
same frozen pointers and an `A`/`D` variant of the same leaf (`MachCSL.KptSeal.slot_asOfGe`), so
the kernel-stack pages (`MachCSL.kstkPageAt`) are exactly xv6's 64 `pas i` (`kstkPage_walk`,
`kstkPage_build`), and a kernel-stack byte stays one (`ksByteAt_mono`). -/

/-- A pointer entry names the page `kSlotP b 0`. -/
theorem kPtr_target (b : BitVec 44) : ((kPtr b >>> 10) <<< 12) &&& 0x00FFFFFFFFFFF000#64 = kSlotP b 0 := by
  simp only [kPtr, mkPte, ptrFlags, kSlotP, Nat.mul_zero]
  bv_decide

/-- A kernel leaf names the page `kSlotP ppn 0`. -/
theorem kLeaf_target (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) :
    ((kLeaf ppn perm a d >>> 10) <<< 12) &&& 0x00FFFFFFFFFFF000#64 = kSlotP ppn 0 := by
  cases perm <;>
    simp only [kLeaf, pteSetAD, mkPte, KPerm.flags, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
      Sail.BitVec.updateSubrange', BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D, kSlotP,
      Nat.mul_zero] <;>
    bv_decide

theorem ptLeafTo_kLeaf (ppn : BitVec 44) (perm : KPerm) (a d : BitVec 1) : ptLeafTo (kLeaf ppn perm a d) (kSlotP ppn 0) := by
  refine ⟨?_, ?_, (kLeaf_target ppn perm a d).symm⟩ <;> cases perm <;>
    simp only [kLeaf, pteSetAD, mkPte, KPerm.flags, Sail.BitVec.extractLsb, Sail.BitVec.updateSubrange,
      Sail.BitVec.updateSubrange', BitVec.extractLsb, LeanRV64D.Functions._update_PTE_Flags_A, LeanRV64D.Functions._update_PTE_Flags_D] <;>
    bv_decide

theorem ptPtrTo_kPtr_slot (b : BitVec 44) : ptPtrTo (kPtr b) (kSlotP b 0) := by
  refine ⟨?_, ?_, (kPtr_target b).symm⟩ <;> simp only [kPtr, mkPte, ptrFlags] <;> bv_decide

theorem kSlotP_add (b : BitVec 44) (k : Nat) : kSlotP b 0 + BitVec.ofNat 64 (8 * k) = kSlotP b k := by
  simp [kSlotP]

theorem kstk_idx (i l : Nat) (hi : i < 64) :
    kIdxP (BitVec.ofNat 27 (0x3FFFFFF - 2 * (i + 1))) l = kvpnIdx (0x3FFFFFF - 2 * (i + 1)) l := by
  simp only [kIdxP, kvpnIdx, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 0x3FFFFFF - 2 * (i + 1)) (by omega)]

/-- xv6's root word, read off a permanent root as of `t`. -/
theorem kstk_root {m : FlatMem} {top S : Nat} {dyn : List KSlot} (hok : kptSealOk xv6Rsv m top S dyn)
    (hh : kptHistsAt m S dyn) {b : BitVec 44} (hroot : (⟨KA.«kernel_pagetable», kSlotP b 0, true⟩ : KSlot) ∈ dyn)
    {t : Nat} (hSt : S ≤ t) {r : PAddr} (hr : ptRootAt xv6Rsv m t r) : r = kSlotP b 0 := by
  obtain ⟨_, base, cnt, stride, k, hR, hk, hw⟩ := hr
  obtain ⟨rfl, rfl⟩ := xv6Roots_only base cnt stride hR
  have hk0 : k = 0 := by omega
  subst hk0
  have hs := KptSeal.slot_asOfGe hok hh hroot hSt (v := r) (by simpa using hw)
  simpa using hs

/-- **A kernel-stack page past the seal is one of the 64 `pas i`.** -/
theorem kstkPage_walk {m : FlatMem} {top S : Nat} {dyn : List KSlot} (hok : kptSealOk xv6Rsv m top S dyn)
    (hh : kptHistsAt m S dyn) {pas : Nat → BitVec 44} {b : BitVec 44}
    (hroot : (⟨KA.«kernel_pagetable», kSlotP b 0, true⟩ : KSlot) ∈ dyn)
    (hmaps : ∀ (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm), kMapP pas vpn ppn perm →
      ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
        (⟨kSlotP b (kIdxP vpn 2), kPtr b1, true⟩ : KSlot) ∈ dyn ∧
        (⟨kSlotP b1 (kIdxP vpn 1), kPtr b0, true⟩ : KSlot) ∈ dyn ∧
        (⟨kSlotP b0 (kIdxP vpn 0), kLeaf ppn perm a d, false⟩ : KSlot) ∈ dyn)
    {t : Nat} (hSt : S ≤ t) {p : PAddr} (hp : kstkPageAt xv6Rsv m t p) :
    ∃ i, i < 64 ∧ p = kSlotP (pas i) 0 ∧ kSlotP b 0 ≠ 0 := by
  obtain ⟨base, cnt, vhi, i, r, hR, hi, hr, v2, v1, v0, p1, p0, w2, pp2, w1, pp1, w0, pl⟩ := hp
  obtain ⟨rfl, rfl⟩ := xv6Kstacks_only base cnt vhi hR
  have hr0 := hr.1
  have hrb := kstk_root hok hh hroot hSt hr
  subst hrb
  obtain ⟨b1, b0, a, d, h2, h1, h0⟩ := hmaps _ (pas i) .rw (Or.inr (Or.inr ⟨i, hi, rfl, rfl, rfl⟩))
  rw [kSlotP_add, ← kstk_idx i 2 hi] at w2
  have e2 := KptSeal.slot_asOfGe hok hh h2 hSt w2
  simp only [↓reduceIte] at e2
  subst e2
  have hp1 : p1 = kSlotP b1 0 := by rw [pp2.2.2, kPtr_target]
  subst hp1
  rw [kSlotP_add, ← kstk_idx i 1 hi] at w1
  have e1 := KptSeal.slot_asOfGe hok hh h1 hSt w1
  simp only [↓reduceIte] at e1
  subst e1
  have hp0 : p0 = kSlotP b0 0 := by rw [pp1.2.2, kPtr_target]
  subst hp0
  rw [kSlotP_add, ← kstk_idx i 0 hi] at w0
  have e0 := KptSeal.slot_asOfGe hok hh h0 hSt w0
  simp only [Bool.false_eq_true, ↓reduceIte] at e0
  obtain ⟨a', d', rfl⟩ := pteVariant_of_kLeaf _ _ _ _ e0
  exact ⟨i, hi, by rw [pl.2.2, kLeaf_target], hr0⟩

/-- **Every `pas i` is a kernel-stack page past the seal** (the root page nonzero). -/
theorem kstkPage_build {m : FlatMem} {top S : Nat} {dyn : List KSlot} (hok : kptSealOk xv6Rsv m top S dyn)
    (hh : kptHistsAt m S dyn) {pas : Nat → BitVec 44} {b : BitVec 44}
    (hroot : (⟨KA.«kernel_pagetable», kSlotP b 0, true⟩ : KSlot) ∈ dyn)
    (hmaps : ∀ (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm), kMapP pas vpn ppn perm →
      ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
        (⟨kSlotP b (kIdxP vpn 2), kPtr b1, true⟩ : KSlot) ∈ dyn ∧
        (⟨kSlotP b1 (kIdxP vpn 1), kPtr b0, true⟩ : KSlot) ∈ dyn ∧
        (⟨kSlotP b0 (kIdxP vpn 0), kLeaf ppn perm a d, false⟩ : KSlot) ∈ dyn)
    (hb0 : kSlotP b 0 ≠ 0) {t : Nat} (hSt : S ≤ t) {i : Nat} (hi : i < 64) :
    kstkPageAt xv6Rsv m t (kSlotP (pas i) 0) := by
  obtain ⟨b1, b0, a, d, h2, h1, h0⟩ := hmaps _ (pas i) .rw (Or.inr (Or.inr ⟨i, hi, rfl, rfl, rfl⟩))
  obtain ⟨vr, wr⟩ := KptSeal.slot_existsGe hh hroot hSt
  have er := KptSeal.slot_asOfGe hok hh hroot hSt wr
  simp only [↓reduceIte] at er
  subst er
  obtain ⟨v2, w2⟩ := KptSeal.slot_existsGe hh h2 hSt
  have e2 := KptSeal.slot_asOfGe hok hh h2 hSt w2
  simp only [↓reduceIte] at e2
  subst e2
  obtain ⟨v1, w1⟩ := KptSeal.slot_existsGe hh h1 hSt
  have e1 := KptSeal.slot_asOfGe hok hh h1 hSt w1
  simp only [↓reduceIte] at e1
  subst e1
  obtain ⟨v0, w0⟩ := KptSeal.slot_existsGe hh h0 hSt
  have e0 := KptSeal.slot_asOfGe hok hh h0 hSt w0
  simp only [Bool.false_eq_true, ↓reduceIte] at e0
  obtain ⟨a', d', rfl⟩ := pteVariant_of_kLeaf _ _ _ _ e0
  refine ⟨0#64, 64, 0x3FFFFFF, i, kSlotP b 0, xv6RsvStatic_kstacks, hi,
    ⟨hb0, KA.«kernel_pagetable», 1, 8, 0, xv6RsvStatic_kptRoot, by omega, by simpa using wr⟩,
    kPtr b1, kPtr b0, kLeaf (pas i) .rw a' d', kSlotP b1 0, kSlotP b0 0, ?_, ptPtrTo_kPtr_slot b1, ?_,
    ptPtrTo_kPtr_slot b0, ?_, ptLeafTo_kLeaf _ _ _ _⟩
  · rw [kSlotP_add, ← kstk_idx i 2 hi]; exact w2
  · rw [kSlotP_add, ← kstk_idx i 1 hi]; exact w1
  · rw [kSlotP_add, ← kstk_idx i 0 hi]; exact w0

/-- **A kernel-stack byte stays one** at every later position (the record's facts). -/
theorem ksByteAt_mono {σ : MState} (hk : kptStateOkK xv6Rsv xv6KptOk σ) {s t : Nat} (hst : s ≤ t) {a : PAddr}
    (h : ksByteAt xv6Rsv σ.mem s a) : ksByteAt xv6Rsv σ.mem t a := by
  rcases h with h | ⟨hpw, p, hp, hlo, hhi⟩
  · exact .inl h
  obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh, ⟨pas, b, hroot, hmaps, -⟩⟩⟩ := hk
  · exfalso
    obtain ⟨f, w, e, hR, he, he0⟩ := hpw
    unfold FlatMem.entAsOf at he
    cases hH : σ.mem[f]? with
    | none => rw [hH] at he; cases he
    | some H =>
      rw [hH, Option.bind_some] at he
      exact he0 (hclean f w hR f (RsvRegion.base_mem _ rfl) H hH e (List.mem_of_find?_eq_some he))
  have hSs := KptSeal.pubWritten_gt hok hpw
  obtain ⟨i, hi, rfl, hb0⟩ := kstkPage_walk hok hh hroot hmaps (by omega) hp
  exact .inr ⟨KptSeal.pubWritten_mono hst hpw, _, kstkPage_build hok hh hroot hmaps hb0 (by omega) hi, hlo, hhi⟩

/-- **`utextDiscAt`, the user code** (W8 (f3-utext) [OWN.89] (W-R), [R34.1],
O1; `MachCSL.uTextDiscAt`): while hart `h` is in user mode, every history
entry on a byte of a page that a user TEXT leaf (`U`, `X` set, `W` clear) of
the table `h`'s `satp` names maps -- a slot a Sv39 walk reaches as of now from
the root (`MachCSL.uSlotNow`) -- is at or below `σ.itv h`, the hart's
instruction view (raised only at `fence.i`, `MachCSL.Lang`).  So every
instruction byte user code can fetch is one its last `fence.i` covered.
From the interpretation's user-epoch record (`MachCSL.uepModel_textDisc`):
userret's `fence.i` stamps the text and the table and its `csrw satp` deposits
a quarter of every byte (`Xv6.UEpochDeposit`), held until uservec's `csrw
satp`.  Spec: Zifencei -- a hart's instruction fetches see the stores before
its `fence.i` (Sail `Fetch.lean`, the model's `itv`); RVWMO orders nothing
else for fetches.  FAITHFUL.  Deviations: the table is the one `satp` names
(xv6: the running process's); a text leaf has `U` set (a `U = 0` page cannot be
fetched from in user mode; the trampoline's is such a page). -/
def utextDiscAt (σ : MState) : Prop := uTextDiscAt σ

/-- **`uptDiscAt`, the user page tables** (W8 (f3-utext) [OWN.87], [OWN.89]
(W-R), T4; `MachCSL.uPtDiscAt` at xv6's registry): while hart `h`'s `satp`
names a USER table -- outside machine mode, a root other than the one
`kernel_pagetable` (xv6's one registered root word) holds as of now -- every
slot of it a Sv39 walk reaches as of now is written after `σ.itv h` only by
HARTS (no DMA author), WHOLE (each entry one byte of a doubleword store at one
position by one hart), with `A`/`D` variants (`MachCSL.pteAD`'s body) of its
value as of `σ.itv h`: the walkers' write-backs, nothing else.  From the
interpretation's user-epoch record (`MachCSL.uepModel_ptDisc`): the record's
quarter of every slot carries `MachCSL.uslotHistOk` at the stamp `K ≤ itv h`,
and `A`/`D` variance is an equivalence.  Spec: Sail's walker writes A/D as a
whole-doubleword store (`MachCSL.PteClass`, the model's `update_PTE_Bits`
write-back); RVWMO orders implicit page-table accesses only via
`SFENCE.VMA`; Zifencei/PMAs silent.  FAITHFUL: a value fact of xv6's runs.
Deviation: the stamp is userret's `fence.i` view; slots are those reached as
of now (on xv6 runs the table's pointer slots do not change while the epoch is
open). -/
def uptDiscAt (σ : MState) : Prop := uPtDiscAt xv6Rsv σ

/-- **A sync path's first move at position `r`** (mcslrec (2) [OWN.82] (a1);
the self-contained copy of Weak's `RvwmoXv6Adequacy.relEntAt`, the same
definition): a release on a hop byte, directly under an acquire on it, or an
entry of a publication word by its writer. -/
def relEntAtX (σ : MState) (r : Nat) : Prop :=
  (∃ (b : PAddr) (A C : CPU) (a' : Nat), syncHop σ.mem b A r C a' ∧ hopByteAt σ b a') ∨
  (∃ (f : PAddr) (w : CPU) (v : BitVec 8) (H : Hist),
      (xv6Env σ).isPub f w ∧ σ.mem[f]? = some H ∧ (⟨r, hartAgent w, v⟩ : HEnt) ∈ H)

/-- **The release sites' provenance** (mcslrec (2) [OWN.82] (a1), Q-MCSL2-DYN
ruled (i)): every post-power-on first move of a sync path -- a release on a
static spinlock's or a (pc-checked) pipe lock's lock byte, a store of
`started` -- was issued (`MState.pcAt`, the per-store pc record) at one of
xv6's release sites `KernelRsv.relPcs` (`release+0x1a`, `main+0xb0`; the
self-contained copy of Weak's `releasePcs`).  Spec: the issuing pc of a
store is the `PC` of the Sail instruction whose `memWrite` made it (the
model's `sail_mem_write` inside `execute`); RVWMO/Zifencei/PMAs are silent on
provenance (a proof notion).  FAITHFUL. -/
def relProvAt (σ : MState) : Prop :=
  ∀ r : Nat, r ≠ 0 → relEntAtX σ r → r ≤ σ.top ∧ σ.pcAt r ∈ KernelRsv.relPcs

/-- The provenance, from the reserved regions' pc record (static locks,
`started`) and the hop bytes' pc clause (pipe locks); the position is an
issued one (`mmOk`'s histories). -/
theorem relProvAt_of (σ : MState) (hle : ∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≤ σ.top)
    (h : relPcOk xv6Rsv KernelRsv.relPcs σ) : relProvAt σ := by
  intro r hr hrel
  rcases hrel with ⟨b, A, C, a', hh, hb⟩ | ⟨f, w, v, H, hp, hf, he⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨H1, H2, e0, va, hm, -⟩ := hh
      exact hle b _ ⟨r, hartAgent A, 0⟩ hm (by simp)
    · rcases hb with hb | ⟨_, hpc⟩
      · exact h.1 b r A hb (relPat_of_syncHop hh)
      · exact relBelowOk_syncHop hh hpc
  · exact ⟨hle f H _ hf he, h.2 f w H _ hp hf he hr⟩

/-- **W8's export** (W8 (f2-ctx): `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt`,
three of the skeleton's six; W8 (f3-hold) [OWN.64]: `lkCpuReadAt`; W8
(f3-racy) [OWN.63]: `chainOkAt`'s `racyValOk` arm -- the two instances of ONE
benign-race class (unlocked reads of lock-protected words, harmless by a
value argument); W8 (f3-pipelk) [OWN.65]: `lockWordDiscAt` and `lkCpuReadAt`
over EVERY lock, the live pipe locks included; W8 (f3-ptek) [OWN.66]:
`pteDiscAt`, the kernel page table's A/D discipline after the seal (the user
tables' half is W8 (f3-pteu)'s; `cpuProcDiscAt` permanently dropped, [OWN.80]);
W8 (f3-utext) [OWN.89]: `utextDiscAt`, the user code (O1), and `uptDiscAt`,
the user page tables after the stamp (T4); mcslrec (1) [OWN.99]: `kptMapsExp`,
the sealed kernel table's mappings (text, data, kernel stacks) in plain
addresses; mcslrec (2) [OWN.82] (a1): `relProvAt`, the release sites'
provenance (the per-store pc record). -/
def xv6AccessDisc (σ : MState) : Prop :=
  chainOkAt σ ∧ lockWordDiscAt σ ∧ cpuStaticAt σ ∧ lkCpuReadAt σ ∧ pteDiscAt σ ∧ utextDiscAt σ ∧ uptDiscAt σ ∧
    kptMapsExp σ ∧ relProvAt σ


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

/-- **The registration lemma** [R26.1] (W8 (f3-pipelk) [OWN.65]): every lock
word at `σ` is registered -- a static lock region of the list, or named by a
store into a registered `f->pipe` slot (`.slots`). -/
theorem xv6LockWord_registered (σ : MState) (b : PAddr) (t : Nat) (hb : xv6LockWord σ b t) :
    (⟨b, .lock KernelGeom.cpusBase⟩ : RsvRegion) ∈ KernelRsv.static ∨
      ∃ (L : List (PAddr × HEnt)) (te : Nat), slotWit xv6Rsv L b te := by
  rcases hb with hb | ⟨_, L, te, _, _, _, hw, _⟩
  · exact .inl (xv6StaticLocks_registered b hb)
  · exact .inr ⟨L, te, hw⟩

/-! ## The static locks' boot value (plan row 5′ E3, [R43.3], [OWN.107])

Every static spinlock's two words (`lk->locked`, `lk->cpu`) are 0 in the boot
image: 155 of the 157 sit in `.bss` (past `KernelElf.elfEnd`, zero by the
loader), the two `uarts[i].lock` in `.data`, whose file bytes there are 0.
Decided over `MachCSL.bootByte`.  Spec: RVWMO/riscv.cat/Sail/Zifencei/PMAs are
silent (an image fact: the initial value of a memory location); FAITHFUL. -/

/-- The loaded byte at `n` is a RAM byte holding 0. -/
def bootZeroB (n : Nat) : Bool := decide (ramBase ≤ n ∧ n < ramEnd) && bootByte n == 0#8

/-- Both words of the spinlock at `b` are 0 in the boot image, byte by byte. -/
def staticLockZeroB (b : Nat) : Bool :=
  (List.range 4).all (fun j => bootZeroB (b + j)) && (List.range 8).all (fun j => bootZeroB (b + 16 + j))

/-- **E3, decided**: every static lock's words are 0 in the boot image. -/
theorem xv6StaticLocks_zeroB : xv6StaticLocks.all (fun b => staticLockZeroB b.toNat) = true := by
  decide +kernel

theorem bootImage_zeroB {a : PAddr} (h : bootZeroB a.toNat = true) : bootImage[a]? = some 0#8 := by
  simp only [bootZeroB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [bootImage_get?, if_pos (by unfold inRam; omega), h.2]

theorem bootZero_addr {b : PAddr} {j : Nat} (h : b.toNat + j < ramEnd) :
    (b + BitVec.ofNat 64 j).toNat = b.toNat + j := by
  have hr : ramEnd < 2 ^ 64 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The static lock words are 0 in the boot image** (E3): the lock word's
four bytes and the owner word's eight. -/
theorem xv6StaticLocks_bootZero (b : PAddr) (hb : b ∈ xv6StaticLocks) :
    (∀ j, j < 4 → bootImage[b + BitVec.ofNat 64 j]? = some 0#8) ∧
      (∀ j, j < 8 → bootImage[b + 16#64 + BitVec.ofNat 64 j]? = some 0#8) := by
  have hz := List.all_eq_true.1 xv6StaticLocks_zeroB b hb
  simp only [staticLockZeroB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hz
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h := hz.1 j hj
    have hlt : b.toNat + j < ramEnd := by
      simp only [bootZeroB, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    apply bootImage_zeroB
    rw [bootZero_addr hlt]
    exact h
  · have h := hz.2 j hj
    have hlt : b.toNat + 16 + j < ramEnd := by
      simp only [bootZeroB, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    have h16 : (b + 16#64).toNat = b.toNat + 16 := bootZero_addr (j := 16) (by omega)
    apply bootImage_zeroB
    rw [bootZero_addr (b := b + 16#64) (by rw [h16]; exact hlt), h16]
    exact h

/-- Every per-hart region of xv6's list sits at its hart's `&cpus[h]` (by
evaluation). -/
def cpuRegsAt (rs : List RsvRegion) : Bool :=
  rs.all (fun R => match R.kind with
    | .cpu c => decide (R.base = cpuAddr c)
    | _ => true)

theorem xv6RsvStatic_cpuRegs : cpuRegsAt xv6RsvStatic = true := by decide +kernel

/-- A per-hart region of xv6's list at `cpuPtrAt cb c` names xv6's `cpus`. -/
theorem xv6Rsv_cpuBase {cb : BitVec 64} {c : CPU}
    (h : (⟨cpuPtrAt cb c, .cpu c⟩ : RsvRegion) ∈ xv6Rsv) : cb = KernelGeom.cpusBase := by
  have hall := List.all_eq_true.mp xv6RsvStatic_cpuRegs _ h
  have h2 : cpuPtrAt cb c = cpuAddr c := by simpa using hall
  have h3 : cb + BitVec.ofNat 64 (128 * c.val) = KernelGeom.cpusBase + BitVec.ofNat 64 (128 * c.val) := h2
  exact (BitVec.add_left_inj _).1 h3

/-! ## The extraction -/

/-- Off the exempt classes and the value-safe racy bytes, a byte is not in
the load-side exemption. -/
theorem custAt_notEx {σ : MState} {a : PAddr} {t : Nat} (h1 : ∀ b, custAt σ a t ≠ .lockw b)
    (h2 : ∀ w, custAt σ a t ≠ .pub w) (h3 : custAt σ a t ≠ .pte)
    (h4 : ¬ (custAt σ a t = .racy ∧ racyValOk σ a t)) :
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
  by_cases c4 : ptByteExAt xv6Rsv σ.mem t a
  · rw [if_pos c4] at h3; exact absurd rfl h3
  rw [if_neg c4] at h1 h2 h3 h4
  by_cases c5 : racyByteIn xv6Rsv a
  · rw [if_pos c5] at h4
    intro hx
    rcases hx with (⟨⟨base, kind⟩, hR, hk, ha⟩ | ⟨b, hd, hw, hks⟩ | hp | hr)
    · rcases hk with ⟨cb, hcb⟩ | ⟨w, hw⟩
      · simp only at hcb
        subst hcb
        exact c1 ⟨base, cb, hR, ha⟩
      · simp only at hw
        subst hw
        exact c2 ⟨w, base, hR, ha⟩
    · exact c3 ⟨b, hd, hw, hks⟩
    · exact c4 hp
    · exact h4 ⟨rfl, hr⟩
  rintro (⟨⟨base, kind⟩, hR, hk, ha⟩ | ⟨b, hd, hw, hks⟩ | hp | hr)
  · rcases hk with ⟨cb, hcb⟩ | ⟨w, hw⟩
    · simp only at hcb
      subst hcb
      exact c1 ⟨base, cb, hR, ha⟩
    · simp only at hw
      subst hw
      exact c2 ⟨w, base, hR, ha⟩
  · exact c3 ⟨b, hd, hw, hks⟩
  · exact c4 hp
  · exact c5 (racyByteIn_of_racyValAt hr)

/-- **`chainOkAt` from the load-side invariant** (and `mmOk`: every hop's
last acquire is an entry at or below the top). -/
theorem chainOkAt_of (σ : MState) (hmm : mmOk σ)
    (h : loadsChained (xv6Env σ) (chainExAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top)) : chainOkAt σ := by
  intro j a H e hH he het hc hA hne h1 h2 h3
  by_cases h4 : custAt σ a e.t = .racy ∧ racyValOk σ a e.t
  · exact .inr h4
  left
  obtain ⟨τ, hv⟩ := h j a H e hH he het hc hA hne (custAt_notEx h1 h2 h3 h4)
  unfold ChainCert.valid at hv
  rcases hv with ⟨hj, _⟩ | ⟨b', _, hch⟩ | hp
  · exact absurd (congrArg Fin.val hj) hne
  · obtain ⟨b, H', e', hH', he', het'⟩ := hopChain_acq_ent hch
    have hle := ((hmm.1 b H' hH').2 e' he').1
    exact .inl ⟨b', by simp only [MState.top]; omega, hch⟩
  · exact .inr hp

/-- A live dynamic lock's windowed discipline, at xv6's `cpus` (W8
(f3-pipelk) [OWN.65]). -/
theorem dynLockWinAt_of (σ : MState) (b : PAddr) (t : Nat) (h : xv6DynLock σ b t) : dynLockWinAt σ b t := by
  obtain ⟨_, L, te, p, cb, c, hw, _, hte, _, hp, hR, hwin⟩ := h
  have hcb := xv6Rsv_cpuBase hR
  subst hcb
  exact ⟨L, te, p, hw, hp, hte, hwin⟩

/-- `lockWordDiscAt ∧ cpuStaticAt` from the static list's discipline (and,
for the dynamic locks, the definition of a live one). -/
theorem lockCpuDisc_of_rsvAllOk (σ : MState) (h : rsvAllOk KernelRsv.static σ.mem) :
    lockWordDiscAt σ ∧ cpuStaticAt σ := by
  refine ⟨fun b t _ => ⟨fun hb => ?_, dynLockWinAt_of σ b t⟩, fun c a H e ha hH he het => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (xv6StaticLocks_registered b hb)
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

/-- **(f3-hold) from the lock layer's discipline** [OWN.64] (W8 (f3-pipelk)
[OWN.65]: static and dynamic locks). -/
theorem lkCpuReadAt_of (σ : MState) (h : lockWordDiscAt σ) : lkCpuReadAt σ := by
  intro b t hb
  obtain ⟨hs, hd⟩ := h b t hb
  refine ⟨fun hst => ?_, fun hdyn => ?_⟩
  · obtain ⟨W, W', Hold, Hold', st, B, hw, hw', hdisc⟩ := hs hst
    exact ⟨W, W', Hold, Hold', st, B, hw, hw', hdisc,
      fun c hst' tvn v0 w hv0 hres => lkCpuP_read_not_mine hdisc.2.2.2.2 c hst' tvn v0 w hv0 hres⟩
  · obtain ⟨L, te, p, hwit, hp, hte, W, W', st, B, h1, h2, hdisc⟩ := hd hdyn
    exact ⟨L, te, p, W, W', st, B, hwit, hp, hte, h1, h2, hdisc,
      fun c hst' tvn v0 w hv0 hres => lkCpuP_read_not_mine hdisc.2.2.2.2 c hst' tvn v0 w hv0 hres⟩

/-- **The export from the four pure facts** of the state interpretation. -/
theorem accessDisc_of (σ : MState) (hmm : mmOk σ) (hr : rsvAllOk KernelRsv.static σ.mem)
    (h : loadsChained (xv6Env σ) (chainExAt xv6Rsv (slotWit xv6Rsv) σ.mem σ.top))
    (hk : kptStateOk xv6Rsv σ) (hu : uTextDiscAt σ) (hp : uPtDiscAt xv6Rsv σ)
    (hkk : kptStateOkK xv6Rsv xv6KptOk σ) (hrp : relPcOk xv6Rsv KernelRsv.relPcs σ) : xv6AccessDisc σ :=
  have hl := lockCpuDisc_of_rsvAllOk σ hr
  ⟨chainOkAt_of σ hmm h, hl.1, hl.2, lkCpuReadAt_of σ hl.1, pteDiscAt_of σ hmm hk, hu, hp, kptMapsExp_of σ hkk,
    relProvAt_of σ (relPc_le_top hmm.1) hrp⟩

variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- **THE ACCESS DISCIPLINE, EXTRACTED** (plan [R25.2] (ii), on
`powerInterp_rsvOk`'s pattern): while the power is on, the state
interpretation gives `xv6AccessDisc` -- `mmOk`, the reserved regions'
discipline and the chain conjunct's load-side invariant, at a record whose
static list is xv6's. -/
theorem powerInterp_accessDisc (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (heqK : MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk)
    (heqP : MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs) (g : GState) :
    powerInterp g ⊢@{IProp GF} ⌜g.pow = true → xv6AccessDisc g.m⌝ := by
  unfold powerInterp eraCur
  cases hpw : g.pow
  · iintro _
    ipureintro
    intro h; cases h
  · iintro ⟨_, _, ⟨%R, _, _, %E, _, Hera⟩, _⟩
    unfold eraInterp memModelAt rsvModelAt chainModelAt
    icases Hera with ⟨_, Hm, Hmm, _, Huep⟩
    ihave %hu := uepModel_textDisc E g.m $$ [Hm Hmm Huep]
    · iframe Hm Huep
      unfold memModelAt rsvModelAt chainModelAt
      iexact Hmm
    ihave %hpt := uepModel_ptDisc E g.m $$ [Hm Hmm Huep]
    · iframe Hm Huep
      unfold memModelAt rsvModelAt chainModelAt
      iexact Hmm
    icases Hmm with ⟨_, _, _, _, %hmm, ⟨%reg, _, %⟨hin, _, hok⟩, Hk⟩, _, %hch, _⟩
    ihave %hk : ⌜kptStateOk (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) g.m⌝ $$ [Hm Hk]
    · iapply kptModel_stateOk _ g.m reg $$ [Hm Hk]
      iframe
    ihave %hkk : ⌜kptStateOkK (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))
        (MachFixedGS.kptOk (hlc := hlc) (GF := GF)) g.m⌝ $$ [Hm Hk]
    · iapply kptModel_stateOkK _ g.m reg $$ [Hm Hk]
      iframe
    ipureintro
    intro _
    have hch' : loadsChained
        (chainEnvAt (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) (MachFixedGS.relPcs (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m)
        (chainExAt (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m.mem g.m.top) := hch
    have hrp := hok.2
    rw [heq, heqP] at hch'
    rw [heq] at hk
    rw [heq] at hpt
    rw [heq, heqK] at hkk
    rw [heq, heqP] at hrp
    exact accessDisc_of g.m hmm (heq ▸ all_of_reservedOk hin hok.1) hch' hk hu hpt hkk hrp

end AccessDiscipline

end Xv6
