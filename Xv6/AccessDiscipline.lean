/-
**THE ACCESS DISCIPLINE** (weak-allocproc plan §C W8's skeleton, [R25.1],
[R34.1]; W8 (f2-ctx) S4; W8 (f3-hold) [OWN.64]; W8 (f3-racy) [OWN.63]; W8
(f3-pipelk) [OWN.65]; W8 (f3-ptek) [OWN.66]; W8 (f3-utext) [OWN.89]): W8's
export `xv6AccessDisc`, `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt ∧ lkCpuReadAt
∧ pteDiscAt ∧ utextDiscAt ∧ uptDiscAt ∧ kptMapsExp ∧ relProvAt ∧ dynLockWinZAt ∧ ksFrameAt ∧
chainOkCertAtP ∧ startedFloorPcAt` -- THIRTEEN conjuncts:
THREE of the skeleton's six (W8 (f2-ctx)), the ruled `holding()` clause
`lkCpuReadAt` (W8 (f3-hold)), the KERNEL half of the skeleton's A/D
write-back clause `pteDiscAt` (W8 (f3-ptek)), the user code clause
`utextDiscAt` (W8 (f3-utext), O1: every byte a user text leaf maps is at or
below the hart's instruction view), the USER tables' half of the A/D clause
`uptDiscAt` (W8 (f3-utext) T4) and the sealed kernel table's mappings in
plain addresses `kptMapsExp` (mcslrec (1) [OWN.99]) and the release sites'
provenance `relProvAt` (mcslrec (2) [OWN.82] (a1)), the TENTH `dynLockWinZAt` (row 5′ E4 [OWN.107]:
a pipe lock's word is 0 at its window's opening -- option (c): the zero is part of the exemption's
dynamic arm `MachCSL.dynLkDiscAt`, so the exemption NARROWED and `chainOkAt` got STRONGER; the
dynamic arms of `lockWordDiscAt`/`lkCpuReadAt` got a narrower premise but are definitional
consequences of it -- not strictly append-only), the ELEVENTH `ksFrameAt` (mcslrec (3) X1
[OWN.90] [OWN.104] (b): a kernel-stack byte is, from then on, in no exempt class and written by
harts only -- the X1 carve also narrowed `custAt`'s dynamic and user-table arms by `¬ ksByteAt`,
STRONGER), the TWELFTH `chainOkCertAtP` (Q2 [OWN.153] (D4), the certified-hop form:
`chainOkAt` whose sync paths' hops are CERTIFIED -- each acquire an issued position whose pc record
is `-1`, an exclusive write's; the first conjunct follows from it, `chainOkAtP_of_cert`; the
certificate environment's hop registry `MachCSL.chainEnvAt` carries the same pc clause, so the
boot hop's `pubCover` arm of `syncPath` got STRONGER), and the THIRTEENTH `startedFloorPcAt` (Q4
[OWN.154] (L1): a hart's positive floor at `started` was raised by the boot spin's load at `main+0x16`,
the ghost load-pc record); `chainOkAt` carries the
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
    `Lock.dyn_certs4`); it ends σ-readably at the reclaim (`kfree`'s
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
  (∃ a, a < τ ∧ hopChain (σ.mem.landedOnly σ.lp) (hopByteAt σ) A t B a) ∨ pubCover (xv6Env σ) A t B

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
    fun a H e hH he => by simp only [MState.top]; exact ((mmOk_hist hmm a H hH).2 e he).1
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

/-- A `.bss` byte past `stack0` and below `end` is below `end` and off `stack0`. -/
theorem staticByte_ok (a : PAddr) (h1 : KernelSyms.«stack0» + 0x8000 ≤ a.toNat) (h2 : a.toNat < KernelSyms.«end») :
    a.toNat < KA.«end».toNat ∧ ¬ stackByteIn xv6RsvStatic a := by
  refine ⟨h2, ?_⟩
  rintro ⟨base, size, hR, hlo, hhi⟩
  obtain ⟨rfl, rfl⟩ := xv6Stack_only base size hR
  have hs : KA.«stack0».toNat = KernelSyms.«stack0» := rfl
  omega

/-- **A static DMA target is certified** (mcslrec (3) X1-d): every byte below `end` and off
`stack0` is off every kernel-stack page of a sealed table of xv6's shape (those pages lie at or above
`end`, `xv6KptOk`). -/
theorem dmaCert_static {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF] (E : EraGS)
    (hR : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (hK : MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk) (pa : PAddr) (n : Nat)
    (h : ∀ j, j < n → (pa + BitVec.ofNat 64 j).toNat < KA.«end».toNat ∧
      ¬ stackByteIn xv6RsvStatic (pa + BitVec.ofNat 64 j)) :
    ⊢@{IProp GF} ksDmaCertAt E pa n := by
  unfold ksDmaCertAt
  ileft
  ipureintro
  intro j hj
  rw [hR, hK]
  refine ⟨(h j hj).2, fun m top S dyn hs hh hk p hp hin => ?_⟩
  obtain ⟨pas, b, hroot, hmaps, hks⟩ := hk
  obtain ⟨i, hi, rfl, -⟩ := kstkPage_walk hs hh hroot hmaps (Nat.le_refl _) hp
  have h1 := (hks i hi).1
  have h2 := (h j hj).1
  unfold inPage at hin
  omega

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
  (∃ (b : PAddr) (A C : CPU) (a' : Nat), syncHop (σ.mem.landedOnly σ.lp) b A r C a' ∧ hopByteAt σ b a') ∨
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

/-- An entry of the landed-only memory is an entry of the memory. -/
theorem landedOnly_memX {σ : MState} {b : PAddr} {H' : Hist} {e : HEnt}
    (hH : (σ.mem.landedOnly σ.lp)[b]? = some H') (he : e ∈ H') : ∃ H, σ.mem[b]? = some H ∧ e ∈ H := by
  rw [FlatMem.landedOnly_get?] at hH
  cases hm : σ.mem[b]? with
  | none => rw [hm] at hH; cases hH
  | some H =>
    rw [hm] at hH
    obtain rfl := Option.some.inj hH
    exact ⟨H, rfl, (List.mem_filter.1 he).1⟩

/-- A co-ordered history's landed entries are its suffix below the pending prefix. -/
theorem filter_landed_eq (lp : LandPos) (log : List Agent) (H : Hist) (hH : histOkP lp log H) :
    H.filter (fun e => (lp e.t).isSome) = H.dropWhile (fun x => (lp x.t).isNone) := by
  conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun x => (lp x.t).isNone) (l := H)]
  rw [List.filter_append]
  have h1 : (H.takeWhile (fun x => (lp x.t).isNone)).filter (fun e => (lp e.t).isSome) = [] := by
    apply List.filter_eq_nil_iff.2
    intro e he
    have := (List.mem_takeWhile_pred _ _ _ he).1
    cases hl : lp e.t with
    | none => simp
    | some _ => rw [hl] at this; simp at this
  have h2 : (H.dropWhile (fun x => (lp x.t).isNone)).filter (fun e => (lp e.t).isSome) =
      H.dropWhile (fun x => (lp x.t).isNone) :=
    List.filter_eq_self.2 (fun e he => histOkP_dropWhile_landed lp log H hH e he)
  rw [h1, h2, List.nil_append]

/-- A release pattern of the landed-only memory is one of the memory (the landed entries are a
suffix: route P, design D6). -/
theorem relPat_merged {σ : MState} (hord : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → histOkP σ.lp σ.log H)
    {b : PAddr} {r : Nat} {A : CPU} (h : relPat (σ.mem.landedOnly σ.lp) b r A) : relPat σ.mem b r A := by
  obtain ⟨H1, H2, e0, hm, he0, hwr, hwe⟩ := h
  have hwm : ∀ {t : Nat} {g : Agent}, wordEntAt (σ.mem.landedOnly σ.lp) b t g → wordEntAt σ.mem b t g := by
    intro t g hw i hi
    obtain ⟨H, e, hH, he, het, heg⟩ := hw i hi
    obtain ⟨H0, hH0, he0'⟩ := landedOnly_memX hH he
    exact ⟨H0, e, hH0, he0', het, heg⟩
  rw [FlatMem.landedOnly_get?] at hm
  cases hb : σ.mem[b]? with
  | none => rw [hb] at hm; cases hm
  | some H =>
    rw [hb] at hm
    have hf : H.filter (fun e => (σ.lp e.t).isSome) = H1 ++ ⟨r, hartAgent A, 0⟩ :: e0 :: H2 :=
      Option.some.inj hm
    rw [filter_landed_eq σ.lp σ.log H (hord b H hb)] at hf
    refine ⟨H.takeWhile (fun x => (σ.lp x.t).isNone) ++ H1, H2, e0, ?_, he0, hwm hwr, hwm hwe⟩
    rw [List.append_assoc, ← hf, List.takeWhile_append_dropWhile]
    exact hb

/-- The provenance, from the reserved regions' pc record (static locks,
`started`) and the hop bytes' pc clause (pipe locks); the position is an
issued one (`mmOk`'s histories). -/
theorem relProvAt_of (σ : MState) (hle : ∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≤ σ.top)
    (hord : ∀ (a : PAddr) (H : Hist), σ.mem[a]? = some H → histOkP σ.lp σ.log H)
    (h : relPcOk xv6Rsv KernelRsv.relPcs σ) : relProvAt σ := by
  intro r hr hrel
  rcases hrel with ⟨b, A, C, a', hh, hb⟩ | ⟨f, w, v, H, hp, hf, he⟩
  · refine ⟨?_, ?_⟩
    · obtain ⟨H1, H2, e0, va, hm, -⟩ := hh
      obtain ⟨H0, hH0, he0⟩ := landedOnly_memX hm (show (⟨r, hartAgent A, 0⟩ : HEnt) ∈ _ by simp)
      exact hle b H0 _ hH0 he0
    · rcases hb with hb | ⟨_, hpc⟩
      · exact h.1 b r A hb (relPat_merged hord (relPat_of_syncHop hh))
      · exact relBelowOk_syncHop hh hpc
  · exact ⟨hle f H _ hf he, h.2 f w H _ hp hf he hr⟩

/-- **A pipe lock's word is 0 at its window's opening** (row 5′ E4 [R43.3] [OWN.107]): a live
dynamic lock at `b` as of `t` has a window `(p, t]` -- `p` at or before the `f->pipe` store that
named it -- over which its two words form a lock history from free (`dynLockWinAt`), and the lock
word's four bytes are 0 as of `p` (`initlock`'s `sw zero`, which precedes the publication).  Spec:
a word's value at a point of an xv6 run; RVWMO/riscv.cat/Sail/Zifencei/PMAs silent; FAITHFUL. -/
def dynLockWinZAt (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6DynLock σ b t →
    ∃ (L : List (PAddr × HEnt)) (te p : Nat), slotWit xv6Rsv L b te ∧ p ≤ te ∧ te ≤ t ∧
      lockWinAt (cpuPtrAt KernelGeom.cpusBase) σ.mem b p t ∧
      ∀ j, j < 4 → (σ.mem.entAsOf (b + BitVec.ofNat 64 j) p).map HEnt.v = some 0

/-! ### The kernel stacks' frames (mcslrec (3) X1-d, [OWN.90] [OWN.104] (b)) -/

/-- A static exempt address's bounds: off `stack0`'s boot stacks and below `end`. -/
def staticAddrOk (a : PAddr) : Bool :=
  decide ((a.toNat < KernelSyms.«stack0» ∨ KernelSyms.«stack0» + 0x8000 ≤ a.toNat) ∧ a.toNat < KernelSyms.«end»)

/-- xv6's static lock, publication and racy words all lie off `stack0`'s boot stacks and below
`end` (decided over the registry). -/
def rsvStaticInBss (R : RsvRegion) : Bool :=
  match R.kind with
  | .lock _ | .pub _ => R.bytes.all staticAddrOk
  | .racy cnt stride n _ _ => (List.range cnt).all fun k => (List.range n).all fun j =>
      staticAddrOk (R.base + BitVec.ofNat 64 (stride * k) + BitVec.ofNat 64 j)
  | _ => true

theorem xv6RsvStatic_inBss : xv6RsvStatic.all rsvStaticInBss = true := by decide +kernel

/-- A byte of an exempt static class (a static lock word, a publication word, a racy word) lies
off `stack0`'s boot stacks and below `end`. -/
theorem staticClass_bounds {a : PAddr}
    (h : (∃ b, staticLockByteOf b a) ∨ (∃ w, pubByteOf w a) ∨ racyByteIn xv6Rsv a) :
    (a.toNat < KernelSyms.«stack0» ∨ KernelSyms.«stack0» + 0x8000 ≤ a.toNat) ∧ a.toNat < KernelSyms.«end» := by
  have hall := List.all_eq_true.1 xv6RsvStatic_inBss
  rcases h with ⟨b, cb, hR, ha⟩ | ⟨w, f, hR, ha⟩ | ⟨base, cnt, stride, n, vlo, vhi, k, j, hR, hk, hj, rfl⟩
  · have := hall _ hR
    simp only [rsvStaticInBss, List.all_eq_true] at this
    simpa [staticAddrOk] using this a ha
  · have := hall _ hR
    simp only [rsvStaticInBss, List.all_eq_true] at this
    simpa [staticAddrOk] using this a ha
  · have := hall _ hR
    simp only [rsvStaticInBss, List.all_eq_true, List.mem_range] at this
    simpa [staticAddrOk] using this k hk j hj

/-- The record's facts give the record's facts without the carve. -/
theorem kptStateOkK_of_D {σ : MState} (h : kptStateOkD xv6Rsv xv6KptOk σ) : kptStateOkK xv6Rsv xv6KptOk σ := by
  obtain ⟨S, dyn, stk, -, hpre | ⟨hok, hh, hk, -⟩⟩ := h
  · exact ⟨S, dyn, .inl hpre⟩
  · exact ⟨S, dyn, .inr ⟨hok, hh, hk⟩⟩

/-- **A kernel-stack byte is no static exempt byte**: static bytes lie below `end` and off
`stack0`; kernel-stack pages lie at or above `end`. -/
theorem ksByte_not_static {σ : MState} (hk : kptStateOkK xv6Rsv xv6KptOk σ) {t : Nat} {a : PAddr}
    (hks : ksByteAt xv6Rsv σ.mem t a) (h1 : a.toNat < KernelSyms.«stack0» ∨ KernelSyms.«stack0» + 0x8000 ≤ a.toNat)
    (h2 : a.toNat < KernelSyms.«end») : False := by
  rcases hks with ⟨base, size, hR, hlo, hhi⟩ | ⟨hpw, p, hp, hlo, hhi⟩
  · obtain ⟨rfl, rfl⟩ := xv6Stack_only base size hR
    have hs : KA.«stack0».toNat = KernelSyms.«stack0» := rfl
    omega
  obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh, ⟨pas, b, hroot, hmaps, hks⟩⟩⟩ := hk
  · obtain ⟨f, w, e, hR, he, he0⟩ := hpw
    unfold FlatMem.entAsOf at he
    cases hH : σ.mem[f]? with
    | none => rw [hH] at he; cases he
    | some H =>
      rw [hH, Option.bind_some] at he
      exact he0 (hclean f w hR f (RsvRegion.base_mem _ rfl) H hH e (List.mem_of_find?_eq_some he))
  have hS := KptSeal.pubWritten_gt hok hpw
  obtain ⟨i, hi, rfl, -⟩ := kstkPage_walk hok hh hroot hmaps (by omega) hp
  have := (hks i hi).1
  have he : KA.«end».toNat = KernelSyms.«end» := rfl
  omega

/-- A page a permanent-root walk reaches past the seal is sealed and page-aligned. -/
theorem kptPage_inGeA {m : FlatMem} {top S : Nat} {dyn : List KSlot} (hok : kptSealOk xv6Rsv m top S dyn)
    (hh : kptHistsAt m S dyn) {t : Nat} (hSt : S ≤ t) {r p : PAddr} (hr : ptRootAt xv6Rsv m t r)
    (hp : ptPageAt m t r p) : pageIn dyn p ∧ p.toNat % 4096 = 0 := by
  have hpr := KptSeal.root_inGe hok hh hSt hr
  refine ⟨KptSeal.page_inGe hok hh hSt hpr hp, ?_⟩
  rcases hp with rfl | ⟨_, _, _, _, hpp⟩ | ⟨q, _, ⟨_, _, _, _, hpp⟩⟩
  · obtain ⟨_, base, cnt, stride, k, hR, hk, hw⟩ := hr
    obtain ⟨d, hd, haddr, hfz, halign, _⟩ := hok.2.2.2.1 base cnt stride k hR hk
    have hs := KptSeal.slot_asOfGe hok hh hd hSt (v := p) (by rw [haddr]; exact hw)
    simp only [hfz, ↓reduceIte] at hs
    rw [hs]; exact halign
  · exact ptPtrTo_aligned hpp
  · exact ptPtrTo_aligned hpp

/-- **`ksFrameAt`, THE KERNEL STACKS' FRAMES** (mcslrec (3) X1, [OWN.90] [OWN.104] (b)): a byte that
is a kernel-stack byte as of `s` (`MachCSL.ksByteAt`: of `stack0`, or -- the boot gate open -- of
a page the sealed kernel table maps at a `KSTACK(i)`) is, as of every later position, in no
exempt custody class (no lock-layer word, no publication word, no live page-table byte, no audited
racy word: `chainOkAt` covers it), and every later entry on it is a hart's (no DMA).  From the
interpretation's sealed-table record, its kernel-stack carve and its DMA facts.  Spec: RVWMO /
riscv.cat / Sail say nothing about which agent writes which address; PMAs make all RAM
DMA-capable -- a fact of xv6's allocator and driver, FAITHFUL.  Deviation: "no user PTE points at
a kernel-stack page" stays NAMED in the header ([OWN.104] (b)). -/
def ksFrameAt (σ : MState) : Prop :=
  ∀ (a : PAddr) (s : Nat), ksByteAt xv6Rsv σ.mem s a →
    (∀ t, s < t → (∀ b, custAt σ a t ≠ .lockw b) ∧ (∀ w, custAt σ a t ≠ .pub w) ∧ custAt σ a t ≠ .pte ∧
      custAt σ a t ≠ .racy) ∧
    (∀ (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → s < e.t → e.tid < NCPU)

/-- `ksFrameAt` from the record's facts. -/
theorem ksFrameAt_of (σ : MState) (hd : kptStateOkD xv6Rsv xv6KptOk σ) : ksFrameAt σ := by
  have hk := kptStateOkK_of_D hd
  intro a s hks
  refine ⟨fun t hst => ?_, fun H e hH he hse => ?_⟩
  · have hkt := ksByteAt_mono hk (Nat.le_of_lt hst) hks
    -- every exempt condition fails at `a` as of `t`
    have hsta : ¬ ((∃ b, staticLockByteOf b a) ∨ (∃ w, pubByteOf w a) ∨ racyByteIn xv6Rsv a) := fun h =>
      let hb := staticClass_bounds h
      ksByte_not_static hk hkt hb.1 hb.2
    have hdyn : ¬ ∃ b, dynLockByteAt σ b a t := fun ⟨_, _, _, h⟩ => h hkt
    have hpte : ¬ ptByteExAt xv6Rsv σ.mem t a := by
      rintro (⟨⟨r, p', hr, hp', hlo', hhi'⟩, hns⟩ | ⟨_, hnk⟩)
      · rcases hkt with hs | ⟨hpw, p, hp, hlo, hhi⟩
        · exact hns hs
        obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh, ⟨pas, b, hroot, hmaps, hksl⟩⟩⟩ := hk
        · obtain ⟨f, w, e, hR, he, he0⟩ := hpw
          unfold FlatMem.entAsOf at he
          cases hH : σ.mem[f]? with
          | none => rw [hH] at he; cases he
          | some H =>
            rw [hH, Option.bind_some] at he
            exact he0 (hclean f w hR f (RsvRegion.base_mem _ rfl) H hH e (List.mem_of_find?_eq_some he))
        have hS := KptSeal.pubWritten_gt hok hpw
        obtain ⟨i, hi, rfl, -⟩ := kstkPage_walk hok hh hroot hmaps (by omega) hp
        obtain ⟨hin, hal'⟩ := kptPage_inGeA hok hh (by omega) hr hp'
        have hal : (kSlotP (pas i) 0).toNat % 4096 = 0 := by
          have := KptSeal.leafTo_aligned (p := kSlotP (pas i) 0) (ptLeafTo_kLeaf (pas i) .rw 0#1 0#1)
          exact this
        have heq : p' = kSlotP (pas i) 0 := inPage_eq hal' hal ⟨hlo', hhi'⟩ ⟨hlo, hhi⟩
        obtain ⟨d, hd, haddr⟩ := hin 0 (by decide)
        exact (hksl i hi).2 d hd (by rw [haddr, heq]; simp)
      · exact hnk hkt
    unfold custAt
    rw [dif_neg (fun h => hsta (.inl h)), dif_neg (fun h => hsta (.inr (.inl h))), dif_neg hdyn,
      if_neg hpte, if_neg (fun h => hsta (.inr (.inr h)))]
    split <;> exact ⟨fun _ h => Cust.noConfusion h, fun _ h => Cust.noConfusion h,
      fun h => Cust.noConfusion h, fun h => Cust.noConfusion h⟩
  · refine Nat.lt_of_not_le (fun hnc => ?_)
    obtain ⟨S, dyn, stk, hdma, hpre | ⟨hok, hh, hkok, hstk⟩⟩ := hd
    · rcases hks with hs | ⟨hpw, -⟩
      · exact hdma.1 a H e hH he hnc hs
      · obtain ⟨f, w, e', hR, he', he0⟩ := hpw
        unfold FlatMem.entAsOf at he'
        cases hH' : σ.mem[f]? with
        | none => rw [hH'] at he'; cases he'
        | some H' =>
          rw [hH', Option.bind_some] at he'
          exact he0 (hpre.2 f w hR f (RsvRegion.base_mem _ rfl) H' hH' e' (List.mem_of_find?_eq_some he'))
    rcases hks with hs | ⟨hpw, p, hp, hlo, hhi⟩
    · exact hdma.1 a H e hH he hnc hs
    have hS := KptSeal.pubWritten_gt hok hpw
    have hpS := KptSeal.kstk_toS hok hh (Nat.le_of_lt hS) hp
    have hne : dyn ≠ [] := by
      obtain ⟨pas, b, hroot, -⟩ := hkok
      rintro rfl; cases hroot
    exact hdma.2 hne a H e hH he hnc (by omega) p ((hstk p).2 hpS) ⟨hlo, hhi⟩

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
provenance (the per-store pc record); row 5′ E4 [R43.3] [OWN.107]: `dynLockWinZAt`, a pipe lock's
word is 0 at its window's opening; mcslrec (3) X1 [OWN.90] [OWN.104] (b): `ksFrameAt`, the kernel
stacks' frames are unexempt and DMA-free. -/
def xv6AccessDiscS (σ : MState) : Prop :=
  chainOkAt σ ∧ lockWordDiscAt σ ∧ cpuStaticAt σ ∧ lkCpuReadAt σ ∧ pteDiscAt σ ∧ utextDiscAt σ ∧ uptDiscAt σ ∧
    kptMapsExp σ ∧ relProvAt σ ∧ dynLockWinZAt σ ∧ ksFrameAt σ


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

/-! ## Route P, increment P-M4c: the export's sub-definitions over landing positions (DUAL)

(`PROGRESS-W11F.md` §10.)  The export `xv6AccessDisc` and its eleven conjuncts are UNCHANGED.
Beside them, their route-P twins: readings AS OF a position over the LANDED VIEW
(`MachCSL.FlatMem.lview`: the co-latest store landed at or before the position -- riscv.cat's
global memory order), entry-wise "after `S`" as "not landed at or before `S`" (pending or landed
later, `MachCSL.HEnt.landedLe`), reads over `WEnt.visibleP` (landed at or below the view, or
own), the load floor `coh` as the read entry's LANDING position.  Verbatim (identity, keyed by
ISSUE stamp): the sync paths (`syncPath`, `relProvAt`: P-M5's hops), the pc record, the power-on
clauses (`e.t ≠ 0`), the static locks' list shape (`lockRegionOk`), `cpuStaticAt`.  Under eager
landing each twin IS today's (`xv6AccessDiscP_eager`); the flip after P-M7 swaps them.
Spec: RVWMO/riscv.cat (a store is in the global memory order from its landing); FAITHFUL. -/

/-- A live dynamic (pipe) lock at `b` as of LANDING position `t` (route P). -/
def xv6DynLockP (σ : MState) (b : PAddr) (t : Nat) : Prop :=
  dynLkDiscAtP xv6Rsv (slotWit xv6Rsv) σ.mem σ.lp σ.ltop b t

/-- A byte of a live dynamic lock's words as of `t`, off every kernel-stack byte (route P). -/
def dynLockByteAtP (σ : MState) (b a : PAddr) (t : Nat) : Prop :=
  xv6DynLockP σ b t ∧ lockWordsByte b a ∧ ¬ ksByteAtP xv6Rsv σ.mem σ.lp t a

open Classical in
/-- **The custody map as of landing position `t`** (route P; `custAt`'s twin). -/
noncomputable def custAtP (σ : MState) (a : PAddr) (t : Nat) : Cust :=
  if h1 : ∃ b, staticLockByteOf b a then .lockw (Classical.choose h1) else
  if h2 : ∃ w, pubByteOf w a then .pub (Classical.choose h2) else
  if h3 : ∃ b, dynLockByteAtP σ b a t then .lockw (Classical.choose h3) else
  if ptByteExAtP xv6Rsv σ.mem σ.lp σ.ltop t a then .pte else
  if racyByteIn xv6Rsv a then .racy else
  if h7 : ∃ c, a ∈ cpuCellBytes c then .hart (Classical.choose h7) else .free

/-- The racy word's value clause as of landing position `t` (route P). -/
def racyValOkP (σ : MState) (a : PAddr) (t : Nat) : Prop := racyValAtP xv6Rsv σ.mem σ.lp t a

/-- **(iii+), route P**: hart `j`'s coherence floor at `a` is the LANDING position of a
post-power-on foreign hart entry; custody and the racy value are read as of that position. -/
def chainOkAtP (σ : MState) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
    σ.lp e.t = some ((σ.hr j).coh a) → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j →
    (∀ b, custAtP σ a ((σ.hr j).coh a) ≠ .lockw b) → (∀ w, custAtP σ a ((σ.hr j).coh a) ≠ .pub w) →
    custAtP σ a ((σ.hr j).coh a) ≠ .pte →
    syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1) ∨
      (custAtP σ a ((σ.hr j).coh a) = .racy ∧ racyValOkP σ a ((σ.hr j).coh a))

/-- **A CERTIFIED hop byte** for an acquire at `a` (Q2 [OWN.153] (D4)): a hop byte (`hopByteAt`)
whose acquire is an issued position stamped exclusive (`σ.pcAt a = -1`: `MState.storeL`, an AMO's
write half) -- the certificate environment's hop registry (`(xv6Env σ).isLk`, definitionally). -/
def certHopAt (σ : MState) (b : PAddr) (a : Nat) : Prop := hopByteAt σ b a ∧ a ≤ σ.top ∧ σ.pcAt a = -1

/-- A certified hop byte is a hop byte. -/
theorem hopByteAt_of_cert {σ : MState} {b : PAddr} {a : Nat} (h : certHopAt σ b a) : hopByteAt σ b a := h.1

/-- **A CERTIFIED sync path** (Q2 [OWN.153] (D4)): `syncPath` whose hops are certified. -/
def syncPathC (σ : MState) (A : CPU) (t : Nat) (B : CPU) (τ : Nat) : Prop :=
  (∃ a, a < τ ∧ hopChain (σ.mem.landedOnly σ.lp) (certHopAt σ) A t B a) ∨ pubCover (xv6Env σ) A t B

/-- A certified sync path is a sync path. -/
theorem syncPath_of_cert {σ : MState} {A : CPU} {t : Nat} {B : CPU} {τ : Nat} (h : syncPathC σ A t B τ) :
    syncPath σ A t B τ := by
  rcases h with ⟨a, ha, hc⟩ | hp
  · exact .inl ⟨a, ha, hopChain_mono (memExt_refl _) (fun _ _ h => hopByteAt_of_cert h) hc⟩
  · exact .inr hp

/-- **(iii+), route P, CERTIFIED** (Q2 [OWN.153] (D4), the export's TWELFTH conjunct): `chainOkAtP`
whose sync paths' hops are certified -- every acquire on the path was an exclusive write. -/
def chainOkCertAtP (σ : MState) : Prop :=
  ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
    σ.lp e.t = some ((σ.hr j).coh a) → ∀ hA : e.tid < NCPU, e.tid ≠ hartAgent j →
    (∀ b, custAtP σ a ((σ.hr j).coh a) ≠ .lockw b) → (∀ w, custAtP σ a ((σ.hr j).coh a) ≠ .pub w) →
    custAtP σ a ((σ.hr j).coh a) ≠ .pte →
    syncPathC σ ⟨e.tid, hA⟩ e.t j (σ.top + 1) ∨
      (custAtP σ a ((σ.hr j).coh a) = .racy ∧ racyValOkP σ a ((σ.hr j).coh a))

/-- The first conjunct follows from the twelfth. -/
theorem chainOkAtP_of_cert {σ : MState} (h : chainOkCertAtP σ) : chainOkAtP σ := by
  intro j a H e hH he het hc hA hne h1 h2 h3
  rcases h j a H e hH he het hc hA hne h1 h2 h3 with hs | hr
  · exact .inl (syncPath_of_cert hs)
  · exact .inr hr

/-- **The publication reads' provenance** (Q4 [OWN.154] (L1), the export's THIRTEENTH conjunct; the
body of Weak's `CapSync.startedFloorPcP σ σ.ldPcAt`): a hart's POSITIVE coherence floor at the base
byte of another hart's publication word (`started`) was last raised by a plain load issued at the
boot spin's `main+0x16` (`MState.ldPcAt`, the ghost load-pc record [OWN.119]). -/
def startedFloorPcAt (σ : MState) : Prop :=
  ∀ (f : PAddr) (w j : CPU), pubByteIn xv6Rsv f w → j ≠ w → 0 < (σ.hr j).coh f →
    σ.ldPcAt j f = (KernelSyms.«main» : Int) + 0x16

/-- The thirteenth conjunct from the machine's record (`MachCSL.ldPcOk` at xv6's read sites). -/
theorem startedFloorPcAt_of {σ : MState} (h : ldPcOk xv6Rsv KernelRsv.pubLdPcs σ) : startedFloorPcAt σ := by
  intro f w j hf hj hpos
  have := h f w j hf hj hpos
  simpa [KernelRsv.pubLdPcs, xv6PubLdPcs] using this

/-- The lock words as of landing position `t` (route P). -/
def xv6LockWordP (σ : MState) (b : PAddr) (t : Nat) : Prop := b ∈ xv6StaticLocks ∨ xv6DynLockP σ b t

/-- A dynamic lock's windowed discipline, route P ([OWN.128] (A), F-11.1d): its two words' entries
issued after the registration `te` (a landed slot store) and landed by `t`, relabeled to their
landing positions, are a lock history from free (`lockWinA`). -/
def dynLockWinAtP (σ : MState) (b : PAddr) (t : Nat) : Prop :=
  ∃ (L : List (PAddr × HEnt)) (te : Nat), slotWit xv6Rsv L b te ∧ (∃ q, σ.lp te = some q) ∧
    lockWinA (cpuPtrAt KernelGeom.cpusBase) σ.mem σ.lp b te t

/-- **The lock layer's discipline, route P.** -/
def lockWordDiscAtP (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWordP σ b t →
    (b ∈ xv6StaticLocks → lockRegionOk (cpuPtrAt KernelGeom.cpusBase) σ.mem b) ∧
    (xv6DynLockP σ b t → dynLockWinAtP σ b t)

/-- **`holding()`'s harmlessness, route P**: a static lock's merged word histories read over
`WEnt.visibleP` (any landing view); a dynamic lock's window over the landed view. -/
def lkCpuReadAtP (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6LockWordP σ b t →
    (b ∈ xv6StaticLocks →
      ∃ (W : WordHist 4) (W' : WordHist 8) (Hold Hold' : Nat → Hist) (st : Option (CPU × Bool)) (B : Nat),
        wordHistAt σ.mem b 4 W Hold ∧ wordHistAt σ.mem (b + 16#64) 8 W' Hold' ∧
        lockDiscW (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
        ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
          ReadCasesP σ.lp W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c) ∧
    (xv6DynLockP σ b t →
      ∃ (L : List (PAddr × HEnt)) (te : Nat) (W : WordHist 4) (W' : WordHist 8) (st : Option (CPU × Bool))
        (B : Nat), slotWit xv6Rsv L b te ∧ (∃ q, σ.lp te = some q) ∧
        (∀ j, j < 4 → ∃ H, σ.mem[b + BitVec.ofNat 64 j]? = some H ∧
          Hist.winA σ.lp te t H = W.map (WEnt.proj j)) ∧
        (∀ j, j < 8 → ∃ H, σ.mem[b + 16#64 + BitVec.ofNat 64 j]? = some H ∧
          Hist.winA σ.lp te t H = W'.map (WEnt.proj j)) ∧
        lockDiscWin (cpuPtrAt KernelGeom.cpusBase) st B W W' ∧
        ∀ (c : CPU), (∀ k, st ≠ some (c, k)) → ∀ (tvn : Nat) (v0 w : BitVec 64), v0 ≠ cpuAddr c →
          ReadCases W' (hartAgent c) tvn v0 w → w ≠ cpuAddr c)

/-- **`started` has not landed** (route P, [OWN.135]): every post-power-on entry of the boot gate is
still pending.  The kernel page table's three conjuncts (`pteDiscAtP`, `kptMapsExpP`, `ksFrameAtP`)
are claimed only once `started` has LANDED: before that, hart 0's `kvmmake` stores may still be
pending behind the landed root store (RVWMO W→W, no fence), and no other hart walks the table
(`started` is read by every secondary before its first walk; main's `fence rw,rw` at `+0xac` drains
hart 0's earlier stores before `started = 1` lands). -/
def startedUnlandedP (σ : MState) : Prop :=
  ∀ a ∈ xv6StartedR.bytes, ∀ H : Hist, σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ 0 → σ.lp e.t = none

/-- **A seal position, route P**: at or below the LANDING top; every post-power-on entry of the
root word landed at or before it, or not landed at all ([OWN.132] (i): a PENDING root store is no
part of the landed view's table -- the table as of `S` is then the image's); no post-power-on
entry of `started` landed at or before it. -/
def kptSealAtP (σ : MState) (S : Nat) : Prop :=
  S ≤ σ.ltop ∧
  (∀ a ∈ kptRootBytes, ∀ H, σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ 0 →
    e.landedLe σ.lp S = true ∨ σ.lp e.t = none) ∧
  (∀ a ∈ xv6StartedR.bytes, ∀ H, σ.mem[a]? = some H → ∀ e ∈ H, e.t ≠ 0 → e.landedLe σ.lp S = false)

/-- **One slot's discipline after `S`, route P**: every entry not landed at or before `S`. -/
def kptSlotDiscP (σ : MState) (S : Nat) (addr : PAddr) (c : BitVec 64) : Prop :=
  ∀ (j : Nat) (H : Hist) (e : HEnt), j < 8 → σ.mem[addr + BitVec.ofNat 64 j]? = some H → e ∈ H →
    e.landedLe σ.lp S = false →
    e.tid < NCPU ∧ ∃ v : BitVec 64, pteVariant c v ∧ e.v = nthByte (n := 8) v j ∧
      ∀ j', j' < 8 → ∃ H', σ.mem[addr + BitVec.ofNat 64 j']? = some H' ∧
        (⟨e.t, e.tid, nthByte (n := 8) v j'⟩ : HEnt) ∈ H'

/-- **`pteDiscAt`, route P**, claimed once `started` has landed ([OWN.135]). -/
def pteDiscAtP (σ : MState) : Prop :=
  startedUnlandedP σ ∨ ∃ S : Nat, kptSealAtP σ S ∧ ∀ (addr : PAddr) (c : BitVec 64), addr.toNat % 8 = 0 →
    ptByteAtP xv6Rsv σ.mem σ.lp S addr → wordAsOfP σ.mem σ.lp addr S c → kptSlotDiscP σ S addr c

/-- One kernel mapping's walk at the seal, route P (`kptWalkP`'s twin: as of `S` over the landed
view, each slot disciplined after `S` over landing positions). -/
def kptWalkPL (σ : MState) (S : Nat) (b : BitVec 44) (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm) :
    Prop :=
  ∃ (b1 b0 : BitVec 44) (a d : BitVec 1),
    wordAsOfP σ.mem σ.lp (kSlotP b (kIdxP vpn 2)) S (kPtr b1) ∧ kptSlotDiscP σ S (kSlotP b (kIdxP vpn 2)) (kPtr b1) ∧
    wordAsOfP σ.mem σ.lp (kSlotP b1 (kIdxP vpn 1)) S (kPtr b0) ∧ kptSlotDiscP σ S (kSlotP b1 (kIdxP vpn 1)) (kPtr b0) ∧
    (∃ v, wordAsOfP σ.mem σ.lp (kSlotP b0 (kIdxP vpn 0)) S v ∧ pteVariant (kLeaf ppn perm a d) v) ∧
    kptSlotDiscP σ S (kSlotP b0 (kIdxP vpn 0)) (kLeaf ppn perm a d)

/-- **`kptMapsExp`, route P** (the seal position and the as-of-`S` readings over landing positions;
`kptMapsExp` reads positions too -- design §2.5 lists it as untouched, it is not).  Its first
disjunct reads "no post-power-on `started` entry LANDED" ([OWN.132] (ii)) -- the [OWN.135] guard. -/
def kptMapsExpP (σ : MState) : Prop :=
  startedUnlandedP σ ∨
  ∃ (pas : Nat → BitVec 44) (S : Nat) (b : BitVec 44), kptSealAtP σ S ∧
    wordAsOfP σ.mem σ.lp KA.«kernel_pagetable» S (kSlotP b 0) ∧
    ∀ (vpn : BitVec 27) (ppn : BitVec 44) (perm : KPerm), kMapP pas vpn ppn perm → kptWalkPL σ S b vpn ppn perm

/-- **O1, route P.** -/
def utextDiscAtP (σ : MState) : Prop := uTextDiscAtP σ

/-- **T4, route P.** -/
def uptDiscAtP (σ : MState) : Prop := uPtDiscAtP xv6Rsv σ

/-- **A pipe lock's word is 0 at its window's opening, route P** ([OWN.128] (A), F-11.1d): the window
opens at the registration `te` (a landed slot store), and at each lock-word byte the co-latest entry
issued at or before it reads 0 (`zeroAtReg`). -/
def dynLockWinZAtP (σ : MState) : Prop :=
  ∀ (b : PAddr) (t : Nat), xv6DynLockP σ b t →
    ∃ (L : List (PAddr × HEnt)) (te : Nat), slotWit xv6Rsv L b te ∧ (∃ q, σ.lp te = some q) ∧
      lockWinA (cpuPtrAt KernelGeom.cpusBase) σ.mem σ.lp b te t ∧ zeroAtReg σ.mem b te

/-- **The kernel stacks' frames, route P**: a kernel-stack byte as of `s` is unexempt as of every
later position, and every entry on it not landed at or before `s` is a hart's. -/
def ksFrameAtP (σ : MState) : Prop :=
  ∀ (a : PAddr) (s : Nat), ksByteAtP xv6Rsv σ.mem σ.lp s a →
    (∀ t, s < t → (∀ b, custAtP σ a t ≠ .lockw b) ∧ (∀ w, custAtP σ a t ≠ .pub w) ∧ custAtP σ a t ≠ .pte ∧
      custAtP σ a t ≠ .racy) ∧
    (∀ (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.landedLe σ.lp s = false → e.tid < NCPU)

/-- **THE EXPORT, route P** (DUAL; the SAME eleven conjuncts in the same order, each its twin;
`cpuStaticAt` and `relProvAt` verbatim; Q2 [OWN.153] (D4) appends the twelfth, `chainOkCertAtP`, and Q4
[OWN.154] (L1) the thirteenth, `startedFloorPcAt`). -/
def xv6AccessDiscP (σ : MState) : Prop :=
  chainOkAtP σ ∧ lockWordDiscAtP σ ∧ cpuStaticAt σ ∧ lkCpuReadAtP σ ∧ pteDiscAtP σ ∧ utextDiscAtP σ ∧
    uptDiscAtP σ ∧ kptMapsExpP σ ∧ relProvAt σ ∧ dynLockWinZAtP σ ∧ ksFrameAtP σ ∧ chainOkCertAtP σ ∧
    startedFloorPcAt σ

/-! ## THE EXPORT (route P, the flip)

The export `xv6AccessDisc` IS the route-P twins' conjunction: the same eleven conjuncts in the same
order, each read over the landing positions (`cpuStaticAt` and `relProvAt` verbatim), then the
appended conjuncts (12: `chainOkCertAtP`, Q2 [OWN.153] (D4); 13: `startedFloorPcAt`, Q4 [OWN.154] (L1)).  The
pre-route-P stamp form is kept above as `xv6AccessDiscS` (documentation; no statement uses it). -/

/-- **THE ACCESS DISCIPLINE** (route P): the eleven conjuncts, as their landing-position twins, and
(Q2 [OWN.153] (D4), APPEND-ONLY) the twelfth `chainOkCertAtP`: the first conjunct's sync paths
with every hop CERTIFIED (each acquire an exclusive write, `pcAt = -1`); and (Q4 [OWN.154] (L1)) the
thirteenth `startedFloorPcAt`: the load that raised a foreign floor at `started` was `main+0x16`'s. -/
def xv6AccessDisc (σ : MState) : Prop :=
  chainOkAtP σ ∧ lockWordDiscAtP σ ∧ cpuStaticAt σ ∧ lkCpuReadAtP σ ∧ pteDiscAtP σ ∧ utextDiscAtP σ ∧
    uptDiscAtP σ ∧ kptMapsExpP σ ∧ relProvAt σ ∧ dynLockWinZAtP σ ∧ ksFrameAtP σ ∧ chainOkCertAtP σ ∧
    startedFloorPcAt σ

theorem xv6AccessDisc_eq_P (σ : MState) : xv6AccessDisc σ = xv6AccessDiscP σ := rfl

/-- The export's TWELFTH conjunct (Q2 [OWN.153] (D4)). -/
theorem chainOkCertAtP_ofExport {σ : MState} (h : xv6AccessDisc σ) : chainOkCertAtP σ :=
  h.2.2.2.2.2.2.2.2.2.2.2.1

/-- The export's THIRTEENTH conjunct (Q4 [OWN.154] (L1)). -/
theorem startedFloorPcAt_ofExport {σ : MState} (h : xv6AccessDisc σ) : startedFloorPcAt σ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## The extraction (route P) -/

/-- Off the exempt classes and the value-safe racy bytes, a byte is not in
the load-side exemption (route P: the custody and the exemption read the landed view). -/
theorem custAtP_notEx {σ : MState} {a : PAddr} {t : Nat} (h1 : ∀ b, custAtP σ a t ≠ .lockw b)
    (h2 : ∀ w, custAtP σ a t ≠ .pub w) (h3 : custAtP σ a t ≠ .pte)
    (h4 : ¬ (custAtP σ a t = .racy ∧ racyValOkP σ a t)) :
    ¬ chainExAtP xv6Rsv (slotWit xv6Rsv) σ.mem σ.lp σ.ltop a t := by
  unfold custAtP at h1 h2 h3 h4
  by_cases c1 : ∃ b, staticLockByteOf b a
  · rw [dif_pos c1] at h1; exact absurd rfl (h1 _)
  rw [dif_neg c1] at h1 h2 h3 h4
  by_cases c2 : ∃ w, pubByteOf w a
  · rw [dif_pos c2] at h2; exact absurd rfl (h2 _)
  rw [dif_neg c2] at h1 h2 h3 h4
  by_cases c3 : ∃ b, dynLockByteAtP σ b a t
  · rw [dif_pos c3] at h1; exact absurd rfl (h1 _)
  rw [dif_neg c3] at h1 h2 h3 h4
  by_cases c4 : ptByteExAtP xv6Rsv σ.mem σ.lp σ.ltop t a
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

/-- An entry of the landed-only memory is an entry of the memory. -/
theorem landedOnly_mem {σ : MState} {b : PAddr} {H' : Hist} {e : HEnt}
    (hH : (σ.mem.landedOnly σ.lp)[b]? = some H') (he : e ∈ H') : ∃ H, σ.mem[b]? = some H ∧ e ∈ H := by
  rw [FlatMem.landedOnly_get?] at hH
  cases hm : σ.mem[b]? with
  | none => rw [hm] at hH; cases hH
  | some H =>
    rw [hm] at hH
    obtain rfl := Option.some.inj hH
    exact ⟨H, rfl, (List.mem_filter.1 he).1⟩

/-- **`chainOkCertAtP` from the load-side invariant** (and `mmOk`: every hop's last acquire is an
entry at or below the issue top): the certificates' chains run through the environment's hop
registry, which IS `certHopAt` (Q2 [OWN.153] (D4)). -/
theorem chainOkCertAtP_of (σ : MState) (hmm : mmOk σ)
    (h : loadsChained (xv6Env σ) (chainExAtP xv6Rsv (slotWit xv6Rsv) σ.mem σ.lp σ.ltop)) :
    chainOkCertAtP σ := by
  intro j a H e hH he het hc hA hne h1 h2 h3
  by_cases h4 : custAtP σ a ((σ.hr j).coh a) = .racy ∧ racyValOkP σ a ((σ.hr j).coh a)
  · exact .inr h4
  left
  obtain ⟨τ, hv⟩ := h j a H e hH he het hc hA hne (custAtP_notEx h1 h2 h3 h4)
  unfold ChainCert.valid at hv
  rcases hv with ⟨hj, _⟩ | ⟨b', _, hch⟩ | hp
  · exact absurd (congrArg Fin.val hj) hne
  · obtain ⟨b, H', e', hH', he', het'⟩ := hopChain_acq_ent hch
    obtain ⟨H0, hH0, he0⟩ := landedOnly_mem hH' he'
    have hle := ((mmOk_hist hmm b H0 hH0).2 e' he0).1
    exact .inl ⟨b', by simp only [MState.top]; omega, hch⟩
  · exact .inr hp

/-- **`chainOkAtP` from the load-side invariant** (through the certified form). -/
theorem chainOkAtP_of (σ : MState) (hmm : mmOk σ)
    (h : loadsChained (xv6Env σ) (chainExAtP xv6Rsv (slotWit xv6Rsv) σ.mem σ.lp σ.ltop)) : chainOkAtP σ :=
  chainOkAtP_of_cert (chainOkCertAtP_of σ hmm h)

/-- A live dynamic lock's windowed discipline over the landed view, at xv6's `cpus`. -/
theorem dynLockWinAtP_of (σ : MState) (b : PAddr) (t : Nat) (h : xv6DynLockP σ b t) : dynLockWinAtP σ b t := by
  obtain ⟨_, L, te, cb, c, hw, _, hq, hR, hwin, -⟩ := h
  have hcb := xv6Rsv_cpuBase hR
  subst hcb
  exact ⟨L, te, hw, hq, hwin⟩

/-- `dynLockWinZAtP` from the definition of a live dynamic lock. -/
theorem dynLockWinZAtP_of (σ : MState) : dynLockWinZAtP σ := by
  intro b t h
  obtain ⟨_, L, te, cb, c, hw, _, hq, hR, hwin, hz⟩ := h
  have hcb := xv6Rsv_cpuBase hR
  subst hcb
  exact ⟨L, te, hw, hq, hwin, hz⟩

/-- `lockWordDiscAtP ∧ cpuStaticAt` from the static list's discipline (and, for the dynamic locks,
the definition of a live one). -/
theorem lockCpuDiscP_of_rsvAllOk (σ : MState) (h : rsvAllOk KernelRsv.static σ.mem) :
    lockWordDiscAtP σ ∧ cpuStaticAt σ := by
  refine ⟨fun b t _ => ⟨fun hb => ?_, dynLockWinAtP_of σ b t⟩, fun c a H e ha hH he het => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (xv6StaticLocks_registered b hb)
    exact h i _ hi
  · have hR := h (rsvCpuIdx c) _ (xv6RsvStatic_cpu c)
    exact hR a ha H hH e he het

/-- `lkCpu_read_not_mine` at any image value other than the reader's own pointer, over landing
positions. -/
theorem lkCpuP_read_not_mineP {lp : LandPos} {W : WordHist 8} {st : Option (CPU × Bool)}
    (h : lkCpuAtP (cpuPtrAt KernelGeom.cpusBase) st W) (c : CPU) (hst : ∀ k, st ≠ some (c, k))
    (tvn : Nat) (v0 w : BitVec 64) (hv0 : v0 ≠ cpuAddr c) (hres : ReadCasesP lp W (hartAgent c) tvn v0 w) :
    w ≠ cpuAddr c := by
  rcases hres with hr | ⟨_, rfl⟩
  · exact lkCpu_read_not_mineP (lp := lp) (st := st) h c hst tvn w (Or.inl hr)
  · exact hv0

/-- The same over a window's word history (the stamp-indexed read cases). -/
theorem lkCpuP_read_not_mine {W : WordHist 8} {st : Option (CPU × Bool)}
    (h : lkCpuAtP (cpuPtrAt KernelGeom.cpusBase) st W) (c : CPU) (hst : ∀ k, st ≠ some (c, k))
    (tvn : Nat) (v0 w : BitVec 64) (hv0 : v0 ≠ cpuAddr c) (hres : ReadCases W (hartAgent c) tvn v0 w) :
    w ≠ cpuAddr c := by
  rcases hres with hr | ⟨_, rfl⟩
  · exact lkCpu_read_not_mine (st := st) h c hst tvn w (Or.inl hr)
  · exact hv0

/-- **(f3-hold) from the lock layer's discipline, route P.** -/
theorem lkCpuReadAtP_of (σ : MState) (h : lockWordDiscAtP σ) : lkCpuReadAtP σ := by
  intro b t hb
  obtain ⟨hs, hd⟩ := h b t hb
  refine ⟨fun hst => ?_, fun hdyn => ?_⟩
  · obtain ⟨W, W', Hold, Hold', st, B, hw, hw', hdisc⟩ := hs hst
    exact ⟨W, W', Hold, Hold', st, B, hw, hw', hdisc,
      fun c hst' tvn v0 w hv0 hres => lkCpuP_read_not_mineP hdisc.2.2.2.2 c hst' tvn v0 w hv0 hres⟩
  · obtain ⟨L, te, hwit, hq, W, W', st, B, h1, h2, hdisc⟩ := hd hdyn
    exact ⟨L, te, W, W', st, B, hwit, hq, h1, h2, hdisc,
      fun c hst' tvn v0 w hv0 hres => lkCpuP_read_not_mine hdisc.2.2.2.2 c hst' tvn v0 w hv0 hres⟩

/-! ### The three page-table conjuncts over the landed view (route P, DESIGN D17′, [OWN.135])

Once `started` has landed, the interpretation's record holds over landing positions
(`MachCSL.KptSeal.recordP_of`); its landed view, read with positions as stamps, is a stamp-form
sealed record (`MachCSL.KptSeal.sealOk_lview`/`histsOk_lview`), so today's walk lemmas apply to it;
the slots' disciplines are over the merged histories (`kptSlotDiscP`). -/

/-- The landed view as a machine (bookkeeping for the σ-reading stamp-form lemmas). -/
def lvState (σ : MState) : MState := { σ with mem := σ.mem.lview σ.lp }

/-- **The route-P sealed record, in xv6's shape** at seal position `S`. -/
def kptLandedRec (σ : MState) (S : Nat) (dyn : List KSlot) (stk : List PAddr) : Prop :=
  kptSealOkP xv6Rsv σ.mem σ.lp σ.ltop S dyn ∧ kptHistsAtP σ.mem σ.lp S dyn ∧
    dmaOkAtP xv6Rsv σ.mem σ.lp S stk dyn ∧ (∀ p, p ∈ stk ↔ kstkPageAtP xv6Rsv σ.mem σ.lp S p) ∧ xv6KptOk dyn

/-- The landed view's stamp-form record (top weakened to the issue top). -/
theorem kptStateOkK_lv (σ : MState) (hmm : mmOk σ) {S : Nat} {dyn : List KSlot} {stk : List PAddr}
    (h : kptLandedRec σ S dyn stk) : kptStateOkK xv6Rsv xv6KptOk (lvState σ) := by
  obtain ⟨hsealP, hhP, -, -, hokx⟩ := h
  obtain ⟨hS, hpub, hrest⟩ := KptSeal.sealOk_lview hsealP
  exact ⟨S, dyn, .inr ⟨⟨Nat.le_trans hS (mmOk_ltop_le hmm), hpub, hrest⟩, KptSeal.histsOk_lview hhP, hokx⟩⟩

/-- No publication entry landed: the landed view's publication words are unwritten. -/
theorem pubClean_lv (σ : MState) (hno : ∀ p, ¬ pubLandedAt xv6Rsv σ.mem σ.lp p) :
    pubClean xv6Rsv (lvState σ).mem := by
  intro f w hf a ha H' hH' e' he'
  obtain ⟨H, hH, rfl⟩ := FlatMem.lview_get?_eq_some hH'
  obtain ⟨e, he, hlt, _, _⟩ := (Hist.mem_lview σ.lp H e').1 he'
  rcases Nat.eq_zero_or_pos e'.t with h0 | h0
  · exact h0
  · exfalso
    have he0 : e.t ≠ 0 := fun h => by rw [h] at hlt; simp [MState.lp, lpOf] at hlt; omega
    exact hno e'.t ⟨f, w, hf, a, ha, H, hH, e, he, he0, hlt⟩

/-- A slot of the route-P record: its landed-view value as of `S` and its discipline. -/
theorem kptDynSlotP {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAtP σ.mem σ.lp S dyn) {d : KSlot}
    (hd : d ∈ dyn) :
    ∃ v, wordAsOfP σ.mem σ.lp d.addr S v ∧ (if d.frozen then v = d.c else pteVariant d.c v) ∧
      kptSlotDiscP σ S d.addr d.c := by
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ := hh d hd
  refine ⟨v0, fun j hj => ?_, hc0, ?_⟩
  · unfold FlatMem.entAsOf
    rw [FlatMem.lview_get?_some (hm j hj), Option.bind_some]
    exact hv0 j hj
  · intro j H e hj hH he' hl
    rw [hm j hj] at hH
    obtain rfl := Option.some.inj hH
    obtain ⟨_, htid, v, hv, hev, hall⟩ := hent j hj e he' hl
    exact ⟨htid, v, hv, hev, fun j' hj' => ⟨Hs j', hm j' hj', hall j' hj'⟩⟩

theorem kptDynFrozenP {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAtP σ.mem σ.lp S dyn)
    {a : PAddr} {c : BitVec 64} (hd : (⟨a, c, true⟩ : KSlot) ∈ dyn) :
    wordAsOfP σ.mem σ.lp a S c ∧ kptSlotDiscP σ S a c := by
  obtain ⟨v, hw, hif, hdisc⟩ := kptDynSlotP hh hd
  simp only [if_true] at hif
  subst hif
  exact ⟨hw, hdisc⟩

theorem kptDynLeafP {σ : MState} {S : Nat} {dyn : List KSlot} (hh : kptHistsAtP σ.mem σ.lp S dyn)
    {a : PAddr} {c : BitVec 64} (hd : (⟨a, c, false⟩ : KSlot) ∈ dyn) :
    (∃ v, wordAsOfP σ.mem σ.lp a S v ∧ pteVariant c v) ∧ kptSlotDiscP σ S a c := by
  obtain ⟨v, hw, hif, hdisc⟩ := kptDynSlotP hh hd
  simp only [Bool.false_eq_true, if_false] at hif
  exact ⟨⟨v, hw, hif⟩, hdisc⟩

/-- The seal position of the route-P record is a `kptSealAtP` one. -/
theorem kptSealAtP_of (σ : MState) {S : Nat} {dyn : List KSlot} {stk : List PAddr}
    (h : kptLandedRec σ S dyn stk) : kptSealAtP σ S := by
  obtain ⟨hsealP, hhP, -, -, -⟩ := h
  refine ⟨hsealP.1, fun a ha H hH e he _ => ?_, fun a ha H hH e he he0 =>
    hsealP.2.1 _ _ xv6StartedR_mem a ha H hH e he he0⟩
  obtain ⟨d, hd, haddr, hfz, -, -⟩ := hsealP.2.2.2.1 KA.«kernel_pagetable» 1 8 0 xv6RsvStatic_kptRoot (by decide)
  obtain ⟨Hs, hm, -, hent⟩ := hhP d hd
  simp only [kptRootBytes, wordBytes, List.mem_map, List.mem_range] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hda : d.addr = KA.«kernel_pagetable» := by rw [haddr]; simp
  rw [← hda, hm j hj] at hH
  obtain rfl := Option.some.inj hH
  left
  cases hl : e.landedLe σ.lp S
  · have := (hent j hj e he hl).1
    rw [hfz] at this
    cases this
  · rfl

/-- **`pteDiscAtP` from the route-P record** (DESIGN D17′). -/
theorem pteDiscAtP_ofRec (σ : MState) {S : Nat} {dyn : List KSlot} {stk : List PAddr}
    (h : kptLandedRec σ S dyn stk) : pteDiscAtP σ := by
  refine .inr ⟨S, kptSealAtP_of σ h, ?_⟩
  obtain ⟨hsealP, hhP, -, -, -⟩ := h
  have hok' := KptSeal.sealOk_lview hsealP
  have hh' := KptSeal.histsOk_lview hhP
  intro addr c halign hpt hw
  obtain ⟨r, p, hroot, hpage, hlo, hhi⟩ := hpt
  obtain ⟨hpr, hra⟩ := kptRoot_in hok' hh' hroot
  obtain ⟨hpp, hpa⟩ := kptPage_in hok' hh' hpr hra hpage
  obtain ⟨d, hd, hdaddr⟩ := hpp ((addr.toNat - p.toNat) / 8) (by omega)
  have haddr : d.addr = addr := by
    rw [hdaddr]
    apply BitVec.eq_of_toNat_eq
    have := addr.isLt
    have := p.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨Hs, hm, ⟨v0, hv0, hc0⟩, hent⟩ := hhP d hd
  rw [haddr] at hm
  have hc := kptHist_word (m := σ.mem.lview σ.lp) (Hs := fun j => Hist.lview σ.lp (Hs j))
    (fun j hj => FlatMem.lview_get?_some (hm j hj)) hv0 hw
  subst hc
  intro j H e hj hH he hl
  rw [hm j hj] at hH
  obtain rfl := Option.some.inj hH
  obtain ⟨hfz, htid, v, hv, hev, hall⟩ := hent j hj e he hl
  simp only [hfz, Bool.false_eq_true, ↓reduceIte] at hc0
  exact ⟨htid, v, pteVariant_trans hc0 hv, hev, fun j' hj' => ⟨Hs j', hm j' hj', hall j' hj'⟩⟩

/-- **`kptMapsExpP` from the route-P record** (DESIGN D17′). -/
theorem kptMapsExpP_ofRec (σ : MState) {S : Nat} {dyn : List KSlot} {stk : List PAddr}
    (h : kptLandedRec σ S dyn stk) : kptMapsExpP σ := by
  have hsa := kptSealAtP_of σ h
  obtain ⟨-, hhP, -, -, ⟨pas, b, hroot, hmaps, -⟩⟩ := h
  refine .inr ⟨pas, S, b, hsa, (kptDynFrozenP hhP hroot).1, fun vpn ppn perm hm => ?_⟩
  obtain ⟨b1, b0, a, d, h2, h1, h0⟩ := hmaps vpn ppn perm hm
  obtain ⟨w2, d2⟩ := kptDynFrozenP hhP h2
  obtain ⟨w1, d1⟩ := kptDynFrozenP hhP h1
  obtain ⟨w0, d0⟩ := kptDynLeafP hhP h0
  exact ⟨b1, b0, a, d, w2, d2, w1, d1, w0, d0⟩

/-- No publication entry landed: `started` is unlanded. -/
theorem startedUnlandedP_of (σ : MState) (hno : ∀ p, ¬ pubLandedAt xv6Rsv σ.mem σ.lp p) : startedUnlandedP σ := by
  intro a ha H hH e he he0
  cases hl : σ.lp e.t with
  | none => rfl
  | some p => exact absurd ⟨_, _, xv6StartedR_mem, a, ha, H, hH, e, he, he0, hl⟩ (hno p)

/-- **`ksFrameAtP`, generically** (DESIGN D17′): from the landed view's stamp-form record and a DMA
fact for the landed view's kernel-stack bytes. -/
theorem ksFrameAtP_gen (σ : MState) (hk : kptStateOkK xv6Rsv xv6KptOk (lvState σ))
    (hdmaK : ∀ (a : PAddr) (s : Nat), ksByteAt xv6Rsv (lvState σ).mem s a → ∀ (H : Hist) (e : HEnt),
      σ.mem[a]? = some H → e ∈ H → e.landedLe σ.lp s = false → NCPU ≤ e.tid → False) : ksFrameAtP σ := by
  intro a s hks
  refine ⟨fun t hst => ?_, fun H e hH he hse => Nat.lt_of_not_le (fun hnc => hdmaK a s hks H e hH he hse hnc)⟩
  have hkt := ksByteAt_mono hk (Nat.le_of_lt hst) hks
  have hsta : ¬ ((∃ b, staticLockByteOf b a) ∨ (∃ w, pubByteOf w a) ∨ racyByteIn xv6Rsv a) := fun h =>
    let hb := staticClass_bounds h
    ksByte_not_static hk hkt hb.1 hb.2
  have hdyn : ¬ ∃ b, dynLockByteAtP σ b a t := fun ⟨_, _, _, h⟩ => h hkt
  have hpte : ¬ ptByteExAtP xv6Rsv σ.mem σ.lp σ.ltop t a := by
    rintro (⟨⟨q, htq, _, r, p', hr, hp', hlo', hhi'⟩, hns⟩ | ⟨_, hnk⟩)
    · have hkq := ksByteAt_mono hk htq hkt
      rcases hkq with hs | ⟨hpw, p, hp, hlo, hhi⟩
      · exact hns hs
      obtain ⟨S, dyn, ⟨_, hclean⟩ | ⟨hok, hh, ⟨pas, b, hroot, hmaps, hksl⟩⟩⟩ := hk
      · obtain ⟨f, w, e, hR, he, he0⟩ := hpw
        unfold FlatMem.entAsOf at he
        cases hH : (lvState σ).mem[f]? with
        | none => rw [hH] at he; cases he
        | some H =>
          rw [hH, Option.bind_some] at he
          exact he0 (hclean f w hR f (RsvRegion.base_mem _ rfl) H hH e (List.mem_of_find?_eq_some he))
      have hS := KptSeal.pubWritten_gt hok hpw
      obtain ⟨i, hi, rfl, -⟩ := kstkPage_walk hok hh hroot hmaps (by omega) hp
      obtain ⟨hin, hal'⟩ := kptPage_inGeA hok hh (by omega) hr hp'
      have hal : (kSlotP (pas i) 0).toNat % 4096 = 0 :=
        KptSeal.leafTo_aligned (p := kSlotP (pas i) 0) (ptLeafTo_kLeaf (pas i) .rw 0#1 0#1)
      have heq : p' = kSlotP (pas i) 0 := inPage_eq hal' hal ⟨hlo', hhi'⟩ ⟨hlo, hhi⟩
      obtain ⟨d, hd, haddr⟩ := hin 0 (by decide)
      exact (hksl i hi).2 d hd (by rw [haddr, heq]; simp)
    · exact hnk hkt
  unfold custAtP
  rw [dif_neg (fun h => hsta (.inl h)), dif_neg (fun h => hsta (.inr (.inl h))), dif_neg hdyn,
    if_neg hpte, if_neg (fun h => hsta (.inr (.inr h)))]
  split <;> exact ⟨fun _ h => Cust.noConfusion h, fun _ h => Cust.noConfusion h,
    fun h => Cust.noConfusion h, fun h => Cust.noConfusion h⟩

/-- **`ksFrameAtP` from the route-P record** (DESIGN D17′). -/
theorem ksFrameAtP_ofRec (σ : MState) (hmm : mmOk σ) {S : Nat} {dyn : List KSlot} {stk : List PAddr}
    (h : kptLandedRec σ S dyn stk) (hpS : ∀ p, pubLandedAt xv6Rsv σ.mem σ.lp p → S < p) : ksFrameAtP σ := by
  refine ksFrameAtP_gen σ (kptStateOkK_lv σ hmm h) (fun a s hks H e hH he hse hnc => ?_)
  obtain ⟨hsealP, hhP, hdmaP, hstkP, ⟨pas, b, hroot, -⟩⟩ := h
  rcases hks with hs | ⟨hpw, p, hp, hlo, hhi⟩
  · exact hdmaP.1 a H e hH he hnc hs
  obtain ⟨pe, hpe, hpes⟩ := KptSeal.pubWrittenP_landed hpw
  have hSs : S ≤ s := by have := hpS pe hpe; omega
  have hpS' := KptSeal.kstk_toS (KptSeal.sealOk_lview hsealP) (KptSeal.histsOk_lview hhP) hSs hp
  have hne : dyn ≠ [] := by rintro rfl; cases hroot
  have hlS : e.landedLe σ.lp S = false := by
    cases hl : e.landedLe σ.lp S
    · rfl
    · exfalso
      simp only [HEnt.landedLe] at hl hse
      cases hx : σ.lp e.t with
      | none => rw [hx] at hl; cases hl
      | some x =>
        rw [hx] at hl hse
        simp only [Option.any_some, decide_eq_true_eq, decide_eq_false_iff_not] at hl hse
        omega
  exact hdmaP.2 hne a H e hH he hnc hlS p ((hstkP p).2 hpS') ⟨hlo, hhi⟩

/-- **`ksFrameAtP` while no publication entry has landed** (DESIGN D17′): a landed-view kernel-stack
byte is `stack0`'s, which no disk entry touches. -/
theorem ksFrameAtP_unlanded (σ : MState) (hno : ∀ p, ¬ pubLandedAt xv6Rsv σ.mem σ.lp p)
    (hdma1 : ∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → NCPU ≤ e.tid →
      ¬ stackByteIn xv6Rsv a) : ksFrameAtP σ := by
  refine ksFrameAtP_gen σ ⟨0, [], .inl ⟨rfl, pubClean_lv σ hno⟩⟩ (fun a s hks H e hH he _ hnc => ?_)
  rcases hks with hs | ⟨hpw, -⟩
  · exact hdma1 a H e hH he hnc hs
  · obtain ⟨pe, hpe, -⟩ := KptSeal.pubWrittenP_landed hpw
    exact hno pe hpe

/-- **The export from the interpretation's pure facts** (route P).  The three page-table conjuncts
(`pteDiscAtP`, `kptMapsExpP`, `ksFrameAtP`) are taken as premises here; `powerInterp_accessDisc`
derives them from the sealed table's record (`ptConjuncts_of`, DESIGN D17′, [OWN.135]: claimed once
`started` has landed). -/
theorem accessDisc_of (σ : MState) (hmm : mmOk σ) (hr : rsvAllOk KernelRsv.static σ.mem)
    (h : loadsChained (xv6Env σ) (chainExAtP xv6Rsv (slotWit xv6Rsv) σ.mem σ.lp σ.ltop))
    (hpte : pteDiscAtP σ) (hu : uTextDiscAtP σ) (hp : uPtDiscAtP xv6Rsv σ) (hkm : kptMapsExpP σ)
    (hrp : relPcOk xv6Rsv KernelRsv.relPcs σ) (hks : ksFrameAtP σ)
    (hld : ldPcOk xv6Rsv KernelRsv.pubLdPcs σ) : xv6AccessDisc σ :=
  have hl := lockCpuDiscP_of_rsvAllOk σ hr
  ⟨chainOkAtP_of σ hmm h, hl.1, hl.2, lkCpuReadAtP_of σ hl.1, hpte, hu, hp, hkm,
    relProvAt_of σ (fun a H e hH he => ((mmOk_hist hmm a H hH).2 e he).1) (mmOk_hist hmm) hrp,
    dynLockWinZAtP_of σ, hks, chainOkCertAtP_of σ hmm h, startedFloorPcAt_of hld⟩

section power
variable {hlc : HasLC} {GF : BundledGFunctors} [MachFixedGS hlc GF]

/-- The seal's receipts, read off era `E`'s landing authority (pure; DESIGN D17′). -/
theorem lpAuth_factsE (E : EraGS) (σ : MState) (hmm : mmOk σ) (ll : List Nat) (R : List PubDep) :
    lpAuthAt E σ.log σ.llog σ.sb σ.sbEp ∗ ([∗list] i ↦ u ∈ ll, landedAtE E u (i + 1)) ∗
      ([∗list] r ∈ R, pubDepAt E r) ⊢@{IProp GF}
      ⌜(∀ i u, ll[i]? = some u → σ.lp u = some (i + 1)) ∧
        (∀ r ∈ R, ∀ p, σ.lp r.t = some p → r.L < p) ∧
        (∀ r ∈ R, ∀ t t' p', 1 ≤ t → t ≤ r.s → r.s < t' → σ.log[t - 1]? = some (hartAgent r.c) →
          σ.log[t' - 1]? = some (hartAgent r.c) → σ.lp t' = some p' → ∃ p, p < p' ∧ σ.lp t = some p)⌝ := by
  iintro ⟨Hlp, #Hll, #HR⟩
  ihave %h1 : ⌜∀ i u, ll[i]? = some u → σ.lp u = some (i + 1)⌝ $$ [Hlp]
  · iapply BI.pure_forall.2
    iintro %i
    iapply BI.pure_forall.2
    iintro %u
    iapply BI.pure_wand.1
    iintro %hi
    ihave #Hl := BigSepL.bigSepL_lookup (Φ := fun i u => landedAtE (GF := GF) E u (i + 1)) hi $$ Hll
    ihave %h := lpAuthAt_landed E _ _ _ _ u (i + 1) $$ [Hlp Hl]
    · iframe Hlp Hl
    ipureintro
    have hu : u ≠ 0 := by
      have := ((mmOk_okP hmm).2.2.2.2.1 u (List.mem_of_getElem? h.2)).1; omega
    exact lpOf_of_get σ.llog u (i + 1) (mmOk_okP hmm).2.2.2.1 h.1 h.2 hu
  ihave %h2 : ⌜∀ r ∈ R, ∀ p, σ.lp r.t = some p → r.L < p⌝ $$ [Hlp]
  · iapply BI.pure_forall.2
    iintro %r
    iapply BI.pure_wand.1
    iintro %hr
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
    ihave #Hd := BigSepL.bigSepL_lookup (Φ := fun _ r => pubDepAt (GF := GF) E r) hi $$ HR
    unfold pubDepAt
    icases Hd with ⟨_, #Hla⟩
    iapply lpAuthAt_landsAbove E _ _ _ _ r.t r.L $$ [Hlp Hla]
    iframe Hlp Hla
  ihave %h3 : ⌜∀ r ∈ R, ∀ t t' p', 1 ≤ t → t ≤ r.s → r.s < t' → σ.log[t - 1]? = some (hartAgent r.c) →
      σ.log[t' - 1]? = some (hartAgent r.c) → σ.lp t' = some p' → ∃ p, p < p' ∧ σ.lp t = some p⌝ $$ [Hlp]
  · iapply BI.pure_forall.2
    iintro %r
    iapply BI.pure_wand.1
    iintro %hr
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
    ihave #Hd := BigSepL.bigSepL_lookup (Φ := fun _ r => pubDepAt (GF := GF) E r) hi $$ HR
    unfold pubDepAt
    icases Hd with ⟨#Hep, _⟩
    iapply lpAuthAt_landedBefore E _ _ _ _ r.c r.k r.s $$ [Hlp Hep]
    iframe Hlp Hep
  ipureintro
  exact ⟨h1, h2, h3⟩

/-- **Era `E`'s sealed-table record, pure** (DESIGN D17′): every disk entry is off the static
stacks, and the record is unsealed (no publication word written) or the seal's facts. -/
theorem memModel_kptRecE (E : EraGS) (σ : MState) :
    genHeapInterp (G := E.mem) σ.mem ∗ memModelAt E σ ⊢@{IProp GF}
      ⌜(∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → NCPU ≤ e.tid →
          ¬ stackByteIn (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) a) ∧
        (pubClean (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) σ.mem ∨
          ∃ (S0 : Nat) (dyn : List KSlot) (stk : List PAddr),
            KptSeal.sealFacts (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) (MachFixedGS.kptOk (hlc := hlc) (GF := GF))
              σ S0 dyn stk)⌝ := by
  unfold memModelAt rsvModelAt kptModelAt
  iintro ⟨Hm, ⟨_, ⟨_, Hlp⟩, _, _, %hmm, ⟨%reg, _, %⟨hin, _, hok, _⟩, %S, %dyn, %stk, %⟨_, hdma, hseal⟩, Hcells, _, _,
    #Hsnap⟩, _, _⟩⟩
  rcases hseal with h0 | h0
  · ipureintro; exact ⟨hdma.1, .inl h0.2.1⟩
  unfold kptSnapAt
  icases Hsnap with (%hs | ⟨%c0, %L0, %ll, %R, %⟨_, _, hsn, hdep⟩, #Hll, #HR⟩)
  · ipureintro; exact ⟨hdma.1, .inl hs.2⟩
  ihave %hh : ⌜kptHistsAt σ.mem S dyn⌝ $$ [Hm Hcells]
  · iapply kptCells_hists E σ.mem S dyn $$ [Hm Hcells]
    iframe
  ihave %hf := lpAuth_factsE E σ hmm ll R $$ [Hlp]
  · iframe Hlp Hll HR
  ipureintro
  have hrsv := all_of_reservedOk hin hok
  refine ⟨hdma.1, .inr ⟨S, dyn, stk, c0, L0, ll, R, h0.1, hh, h0.2.1, h0.2.2.1, hdma, hsn, hdep, hf.1, hf.2.1, hf.2.2,
    fun f w hf' => ?_⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf'
  exact (hrsv i _ hi).1

/-- **The three page-table conjuncts from the record** (DESIGN D17′, [OWN.135]): claimed once
`started` has landed, from the route-P record at the least landing position of a publication
entry; before, trivially (`startedUnlandedP`) and from the static stacks' DMA fact. -/
theorem ptConjuncts_of (σ : MState) (hmm : mmOk σ)
    (hdma1 : ∀ (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → NCPU ≤ e.tid →
      ¬ stackByteIn xv6Rsv a)
    (hrec : pubClean xv6Rsv σ.mem ∨ ∃ (S0 : Nat) (dyn : List KSlot) (stk : List PAddr),
      KptSeal.sealFacts xv6Rsv xv6KptOk σ S0 dyn stk) :
    pteDiscAtP σ ∧ kptMapsExpP σ ∧ ksFrameAtP σ := by
  by_cases hl : ∃ p, pubLandedAt xv6Rsv σ.mem σ.lp p
  · obtain ⟨p, hp⟩ := hl
    rcases hrec with hc | ⟨S0, dyn, stk, hf⟩
    · exfalso
      obtain ⟨f, w, hf, a, ha, H, hH, e, he, he0, _⟩ := hp
      exact he0 (hc f w hf a ha H hH e he)
    obtain ⟨c0, L0, ll, R, hseal, hh, hokd, hks, hdma, hsn, hdep, hll, hla, hep, hcpu⟩ := hf
    obtain ⟨pmin, hmin, hle⟩ := KptSeal.exists_least _ p hp
    obtain ⟨hsealP, hhP, hdmaP, hstk⟩ := KptSeal.recordP_of xv6Rsv σ hmm S0 dyn stk hseal hh hks hdma c0 L0 ll R
      hsn hdep hll hla hep hcpu pmin hmin hle
    have hrecP : kptLandedRec σ (pmin - 1) dyn stk := ⟨hsealP, hhP, hdmaP, hstk, hokd⟩
    have hp1 : 1 ≤ pmin := by
      obtain ⟨f, w, hf, a, ha, H, hH, e, he, he0, hlp⟩ := hmin
      rcases Nat.eq_zero_or_pos pmin with h0 | h0
      · rw [h0] at hlp; exact absurd (lpOf_eq_zero hlp) he0
      · exact h0
    exact ⟨pteDiscAtP_ofRec σ hrecP, kptMapsExpP_ofRec σ hrecP,
      ksFrameAtP_ofRec σ hmm hrecP (fun q hq => by have := hle q hq; omega)⟩
  · have hno : ∀ p, ¬ pubLandedAt xv6Rsv σ.mem σ.lp p := fun p hp => hl ⟨p, hp⟩
    exact ⟨.inl (startedUnlandedP_of σ hno), .inl (startedUnlandedP_of σ hno), ksFrameAtP_unlanded σ hno hdma1⟩

/-- **THE ACCESS DISCIPLINE, EXTRACTED** (plan [R25.2] (ii)): while the power is on, the state
interpretation gives `xv6AccessDisc` -- `mmOk`, the reserved regions' discipline, the chain
conjunct's load-side invariant over landing positions, the user-epoch record's O1/T4 twins. -/
theorem powerInterp_accessDisc (heq : MachFixedGS.rsvStatic (hlc := hlc) (GF := GF) = KernelRsv.static)
    (heqK : MachFixedGS.kptOk (hlc := hlc) (GF := GF) = KernelRsv.kptOk)
    (heqP : MachFixedGS.relPcs (hlc := hlc) (GF := GF) = KernelRsv.relPcs)
    (heqL : MachFixedGS.pubLdPcs (hlc := hlc) (GF := GF) = KernelRsv.pubLdPcs) (g : GState) :
    powerInterp g ⊢@{IProp GF} ⌜g.pow = true → xv6AccessDisc g.m⌝ := by
  unfold powerInterp eraCur
  cases hpw : g.pow
  · iintro _
    ipureintro
    intro h; cases h
  · iintro ⟨_, _, ⟨%R, _, _, %E, _, Hera⟩, _⟩
    unfold eraInterp memModelAt rsvModelAt chainModelAt
    icases Hera with ⟨_, Hm, Hmm, _, Huep⟩
    ihave %hu := uepModel_textDiscP E g.m $$ [Hm Hmm Huep]
    · iframe Hm Huep
      unfold memModelAt rsvModelAt chainModelAt
      iexact Hmm
    ihave %hpt := uepModel_ptDiscP E g.m $$ [Hm Hmm Huep]
    · iframe Hm Huep
      unfold memModelAt rsvModelAt chainModelAt
      iexact Hmm
    ihave %hkr := memModel_kptRecE E g.m $$ [Hm Hmm]
    · iframe Hm
      unfold memModelAt rsvModelAt chainModelAt
      iexact Hmm
    icases Hmm with ⟨_, _, _, _, %hmm, ⟨%reg, _, %⟨hin, _, hok⟩, Hk⟩, _, %hch, _⟩
    ipureintro
    intro _
    have hch' : loadsChained
        (chainEnvAt (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF)) (MachFixedGS.relPcs (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m)
        (chainExAtP (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))
          (slotWit (MachFixedGS.rsvStatic (hlc := hlc) (GF := GF))) g.m.mem g.m.lp g.m.ltop) := hch
    have hrp := hok.2.1
    have hld := hok.2.2
    rw [heq, heqL] at hld
    rw [heq, heqP] at hch'
    rw [heq] at hpt
    rw [heq, heqP] at hrp
    rw [heq, heqK] at hkr
    obtain ⟨hpte, hkm, hks⟩ := ptConjuncts_of g.m hmm hkr.1 hkr.2
    exact accessDisc_of g.m hmm (heq ▸ all_of_reservedOk hin hok.1) hch' hpte hu hpt hkm hrp hks hld

end power


end AccessDiscipline

end Xv6
