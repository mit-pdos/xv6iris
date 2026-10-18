# W10-6m census — the twin's per-step datum (`SilOrd.stepSupplyS`), site by site

Plan rev 53, REMAINING WORK row **6m** (W11-F B5, the W10-4 site datum).  Slot w2, 2026-10-18.  Census only:
no Lean.  Image: `Xv6/KernelImage.lean`, xv6-riscv `b72cbac1` (branch verified), 8 814 instructions; pin table
`Weak/KernelPins.lean` (1 689 load sites); custody registry `Xv6/KernelRsv.lean`; export `Xv6/AccessDiscipline.lean`.

## 0. Spec first, and what the datum asks

**Spec.**  RVWMO / riscv.cat let a plain load return any write that is not overwritten (in gmo) before it and
not po-after it (load value axiom; rules 1–13 order only the listed pairs); an AMO reads the coherence-latest
value (atomicity); Sail executes each hart in program order, fetching at `PC`; Zifencei and the PMAs say nothing
about data loads.  Nothing below changes or assumes anything about these texts: every route listed is
FAITHFUL proof organisation unless marked.

**The datum.**  `SilOrd.hartStepRIS` (`Weak/SilOrd.lean:81`), supplied by `CatLin.SilOrd.stepSupplyS
(:288)`: at a walk-invariant twin state, for the next event `L[k] = (x, n)` of the walk order `L`, an appended
twin step `(lb', o)` with `SilWalk.relW` (same label up to read re-indexing; SILENT exactly at a failed acquire),
`SilWalk.stepOk` (`Weak/SilWalk.lean:61`) and the program relation `Rel` advanced.  What `stepOk` demands of a
read is the candidate machine's rule, NOT "latest":
* plain load — `mstepOk`/`rdOk`/`byteRd` (`Weak/WeakAxiomatic.lean:129`): the byte's message must be
  `readable` at the hart's pre-view (`loadVpre ws aq`) — a STALE value is fine as long as no newer write to
  the byte lies at or below the hart's view;
* successful AMO — `rmwLatest`: the coherence-latest message;
* failed acquire — `SilCand.silentOk`: the latest message as of a past position `q` is the read value, with
  the dependency bound `SilCand.depView … ≤ q` (6c's faithful bound: fence / aq / address / data / control
  predecessors, rules 4/5/9–11/13).
So a read must be **poisoned** (re-valued, the hart running tainted until its taint dies, CertZ11
`loadTail`/`realizeT`, CertZ13 `relT`) only when the graph's source is NOT available to the walk: (F) the
source is walked after the read ("future"), or (V) a newer write to the byte is at or below the hart's
view.  A poisoned value may not reach an exit write's address or data, a fault, a CSR, or a branch whose
outcome differs; otherwise the hart's event sequence leaves the graph's row and `relW` fails.

**Which reads can be poisoned at all.**  The export's chain conjunct `chainOkAt`
(`Xv6/AccessDiscipline.lean:315`) says every FOREIGN HART entry a hart observes is reached by a sync path
(release→acquire hops through lock bytes, or the boot publication hop) — EXCEPT on the four exempt custody
classes of `custAt :271` (`lockw`, `pub`, `pte`, `racy`-with-value) — and it says nothing about DISK-row
entries (`e.tid < NCPU`).  A sync path is made of po, protocol lock co and the `started` publication edge,
i.e. of walk-order edges; along an order respecting them the source is walked before the read and the
co-later writes after it, so the read agrees (the race-free-read theorem, §5).  Own entries and boot-image
entries agree trivially (own coherence floor; image never superseded by an earlier walk write).  Hence the
census set = load sites that can read (a) an exempt-class byte, or (b) a disk-written RAM byte, plus the
non-text readers (device program, page-table walker, fetch) and the one AMO.

## 1. Headline numbers

* **1** failed-acquire slot pc: `acquire+0x1c` (`0x80000c74`, `amoswap.w.aq`, the image's ONLY AMO), reached
  from **62** `acquire` call sites (29 with a link-time-constant lock address, 33 register-passed).
* **18** kernel-text load sites can read an exempt-class or disk-written byte (of 1 689):
  lock words 2 (`holding`), publication word 1 (`started`), racy word 2 (`ip->ref`), page-table bytes 9
  (software walks of user tables), disk-written RAM 4 (`virtio_disk_intr`).
* **8** device-program read nodes (`Weak/VirtioProg.lean:74-80`: avail idx (aq), ring entry, 3 descriptors,
  type, sector, OUT payload) read hart-written RAM; plus the page-table walker's implicit PTE reads and every
  instruction fetch (rows 6d / 6h / G7, §4).
* The other **1 671** load sites agree by ownership (1 034 `PStack` + 3 `PPerCpu` pins: private bytes) or by the
  race-free-read theorem (chained classes: `prot`, `proc`, `ro`, `free`, `hart`).
* Of the 18 + 8 + 1: **taint-dischargeable 3 + (7)** (value argument or bit-level dead taint); **agree by
  ownership at the call site 2 call contexts**; **ORDER-pinned 6 + 8 + the silent window** (no value argument:
  the walk order must honour the read's rf (and fr) — these belong with row 6l); **2 not dischargeable by
  taint if poisonable** (A/D bits into exit-write data; poisonable only without a pte custody chain).

## 2. The failed-acquire slot

| pc | function | instruction | datum at the slot | ruling | mechanical? |
|---|---|---|---|---|---|
| `0x80000c74` | `acquire+0x1c` | `amoswap.w.aq a5,a5,(s1)` | GF reads ≠ 0 ⇒ `relW` silent; `silentOk` at a `q` whose latest lock value is GF's 1, `depView ≤ q`; rd `a5` feeds only `sext.w` (`+0x20`) and the back-edge `bnez` (`+0x22`) — the silent read returns GF's value, so NO taint and the branch agrees | [OWN.100] (twin), 6c bound | loop shape: YES (4 instructions, `0x80000c72–0x80000c7a`; a `decide +kernel` check of the rd's uses, S); the window `q`: NO — an ORDER obligation (§6 F3) |

GF side: the graph's failed AMO is an `LRmw` writing 1 over 1; its source chain of failed AMOs ends at a
successful AMO `a` with no release in between (atomicity), so the hold window `[a, rel)` exists in GF.  The
walk needs a position `q` in the WALKED window with every dependency predecessor's source walked at or below
`q`; in GF those sources are gmo-before the AMO's write, hence before `rel`, but an order built only from
po ∪ protocol co ∪ fabric does not place them before `rel` (w3's 4c-i counterexample shape, with `wVrOld`
replaced by the control/address dependencies of the 62 call contexts: e.g. `holding()`'s branch on
`lk->locked` (`holding+0x2`), the caller's branches, the lock pointer loaded from `p`/`f->pipe`/`ip`).

## 3. Kernel-text sites that can be poisoned

Columns: **feeds** = where the loaded value flows (from the disassembly; pin = `Weak/KernelPins.lean`'s first
pin before the hart's next store); **route** = T (taint dies / value argument), O (agree by ownership at the
call site), P (ORDER-pinned: the order must honour the read's source), N (not dischargeable by taint).

### 3.1 Lock words (`custAt = .lockw`; [OWN.64], [OWN.65])

| pc | site | load | pin | feeds | route |
|---|---|---|---|---|---|
| `0x80000bf2` | `holding+0x0` | `lw a5,0(a0)` (`lk->locked`) | `PCtrl +0x2` | branch `bnez` choosing between `li a0,0; ret` and the frame / `lk->cpu` / `mycpu` path — the two outcomes emit DIFFERENT event sequences (3 stack stores, the `lk->cpu` load, `mycpu`'s frame) | from `acquire+0x12`: **P** (no value argument: a non-holder may see 0 or ≠ 0); from `release+0xc`, `sched+0x14`: **O** (the caller holds `lk`: GF's source is co-≥ its own AMO, every co-later write before its release is a failed AMO's 1 — value 1 both sides) |
| `0x80000c04` | `holding+0x12` | `ld a5,16(a0)` (`lk->cpu`) | `PResidue` | `mv s1` → `sub`/`seqz` → return `a0` → caller's branch (`acquire+0x18 bnez`, `release+0x10 beqz`, `sched+0x18 beqz`) | `acquire`: **T** by [OWN.64] (`lkCpuReadAt`: a non-holder never reads `&cpus[x]`; GF side by CoWR + the CS structure: the hart's own `&cpus[x]` write is po-followed by its `release+0x12 sd zero` before its next `holding`) — `seqz` gives 0 both sides, the taint dies at `seqz`; `release`/`sched`: **O** (value `&cpus[x]` both sides) |

### 3.2 Publication word (`.pub`, `started`, `KernelRsv.xv6StartedR`)

| pc | site | load | pin | feeds | route |
|---|---|---|---|---|---|
| `0x80000ee4` | `main+0x16` | `lw a5,0(a4)` + `fence r,rw` | `PFence +0x18` | the spin's back-edge `beqz` (`main+0x1e`) | GF value 0: agrees without any order help (the hart's view at `started` is the image's, so the image 0 stays `readable`); GF value 1: **P** — the order must walk hart 0's `started` store (`main+0xb0`) before the read (the boot publication hop of `syncPath`; acyclic trivially: readers have no events before it but `started` reads and `cpuid`) |

### 3.3 Racy word (`.racy`, `ip->ref`, `KernelRsv.xv6IrefRacyR`; [OWN.63])

| pc | site | load | pin | feeds | route |
|---|---|---|---|---|---|
| `0x80003360` | `ilock+0xe` | `lw a5,8(a0)` | `PCtrl +0x10` | `blez` → `unreachable` | **T**: walk side `racyValOk` (≥ 1 at the realized state); GF side a co-interval argument (the reader's own increment is po-before (CoWR), its decrement po-after (CoRW), every co-between write is an `itable.lock`-protected ±1 of a count that includes the reader's reference) — same outcome, taint dies at `blez` |
| `0x8000341c` | `iunlock+0x1c` | `lw a5,8(s1)` | `PCtrl +0x1e` | `blez` → `unreachable` | **T**, as `ilock+0xe` |

### 3.4 Page-table bytes (`.pte`, exempt; software walks of USER tables)

Writers of a user PTE: the owning process's kernel code and the walker's A/D write-backs on the hart that
runs the process — one hart at a time, handed off under `p->lock` — so the reads AGREE along an order
respecting lock co IF a GF-level custody chain for PTE bytes is available; the export does not give one
(`pte` is exempt in `chainOkAt`).  Without it, a poisoned PTE differs at most in A/D (bits 6, 7):

| pc | site | load | pin | feeds (A/D-sensitive?) | route |
|---|---|---|---|---|---|
| `0x80000fe0` | `walk+0x32` | `ld s1,0(s2)` | `PCtrl` | `andi 1` → `beqz`; `srli 10; slli 12` → next-level address (no) | T (bit-level) |
| `0x80001064` | `walkaddr+0x1c` | `ld a5,0(a0)` | `PCtrl` | `andi 17` → `beq`; PA → returned, a load/store address in `copyin*` (no) | T (bit-level) |
| `0x800010cc` | `mappages+0x4a` | `ld a5,0(a0)` | `PCtrl` | `andi 1` → `bnez` (remap) (no) | T (bit-level) |
| `0x800012be` | `uvmunmap+0x5e` | `ld a5,0(a0)` | `PCtrl` | `andi 1` → `beqz`; PA → `kfree` (store addresses) (no) | T (bit-level) |
| `0x80001402` | `freewalk+0x2a` | `ld a5,0(s1)` | `PCtrl` | `andi 1`, `andi 14` → branches; PA → recursion (no) | T (bit-level) |
| `0x8000153a` | `ismapped+0x10` | `ld a0,0(a0)` | `PResidue` | `andi 1` → returned (no) | T (bit-level) |
| `0x80001644` | `copyout+0x82` | `ld a5,0(a0)` | `PCtrl` | `andi 4` → `beqz` (no) | T (bit-level) |
| `0x8000149c` | `uvmcopy+0x36` | `ld s3,0(a0)` | `PCtrl` | `andi 1` → `beqz`; PA → `memmove` source; **`andi 1023` → `mappages` flags → the child PTE's DATA** (yes) | **N** unless the PTE custody chain makes it agree |
| `0x80001510` | `uvmclear+0x10` | `ld a5,0(a0)` | `PDep` | `andi -17` → **`sd` back, exit-write DATA** (yes) | **N** unless the PTE custody chain makes it agree |

(Kernel-table reads happen only in `kvmmake` on hart 0 before the `started` publication — own entries.)

### 3.5 Disk-written RAM (`virtio_disk_intr`; entries with `tid = NCPU`, outside `chainOkAt`)

| pc | site | load | pin | feeds | route |
|---|---|---|---|---|---|
| `0x80005d5e` | `virtio_disk_intr+0x36` | `lhu a5,2(a5)` (`used->idx`) | `PCtrl` | `beq` (loop entry) | **P** |
| `0x80005d76` | `+0x4e` | `lw a5,4(a5)` (`used->ring[i].id`) | `PCtrl` | index → `info[id].status` load address and `info[id].b` → **the address of `sw zero,4(a0)` (`b->disk = 0`)** | **P** |
| `0x80005d82` | `+0x5a` | `lbu a4,16(a4)` (`info[id].status`, DMA-written) | `PCtrl` | `bnez` → `unreachable` | **P** (or T with a GF value argument "status = 0", not available) |
| `0x80005daa` | `+0x82` | `lhu a4,2(a4)` (`used->idx`) | `PCtrl` | `bne` (loop back-edge) | **P** |

Not in the set: the MMIO accesses (`+0x22`, `+0x2a`; I/O, walked in fabric order), `disk.used`/`used_idx`/
`info[].b`/`b->disk` (hart-written under `disk.vdisk_lock`: chained), buffer DATA read after `virtio_disk_rw`
returns (device write <po used-ring write <po IRQ <fabric claim <po … release(`vdisk_lock`) <lock co waiter's
acquire: chained through order edges).  Why P: a later completion's `used->idx`/element written AFTER the claim
in fabric order can be the GF source; in GF it is gmo-before the read (fabric ⊆ gmo for members, R1 makes the
claim/ack a one-way fence), but nothing in po ∪ coNP ∪ fabric walks it before the read.

## 4. Readers outside the kernel text

| reader | count | route |
|---|---|---|
| disk program `DRead` nodes (`VirtioProg.lean:74-80`) | 8 | **P**: their values choose the popped head, the descriptor addresses and the DMA-write addresses/data (exit writes); the sources (driver writes under `vdisk_lock`, `fence`, then the NOTIFY MMIO) are not walk-ordered before a device read that precedes the NOTIFY in fabric order |
| page-table walker's implicit PTE reads + A/D write-backs | per access | agree: kernel table sealed with A/D preset (`kptMapsExp`, W11-C2 finding); user tables by the custody chain of §3.4 — rows 6d (`DCfg`/`TCfg`) |
| instruction fetches (`LIFetch`) | per instruction | `stepOk`'s view-0 `ifetchOk`; kernel text never written (`textPristine`), user text by G7 (`fetchProv`/`fetchReplayOk`) — rows 6h / 6i |
| CSR / MMIO reads | — | not memory reads of the walk (registers; I/O events in fabric order) |

## 5. Everything else — the race-free-read theorem

For the 1 671 remaining load sites the datum is "agree": own/private (pins `PStack`/`PPerCpu`, `cpuStaticAt`)
or chained.  The theorem the walk needs is CHAIN-based, not critical-section-based: xv6 reads some chained
data outside any critical section of the protecting lock (e.g. `log.c`'s commit reads `log.lh` under the
`committing` flag, ordered by `log.lock` hand-offs), so the plan's (G1) "every write inside a CS of its lock"
is too narrow.  Statement shape: along an order respecting po ∪ protocol lock co ∪ fabric ∪ the `started`
hop, if the graph's source `w` of a read `r` is chained to `r` (a sync path at GF) and every co-later write
`w'` is chained from `r`, then `w` is walked before `r`, every `w'` after it, so `w` is the latest walked write
(and `readable`).  The GF-level chain facts come from the realized prefix (the walked writes are the realized
run's, which obeys `chainOkAt`) — the same "facts at the realized prefix" pattern as row 6l.

## 6. Findings

* **F1 — 6m is not separable from 6l.**  Of the sites whose poisoning would be fatal (a differing branch,
  an exit-write address), NONE has a value argument except `holding+0x12` and `ip->ref`; the rest (`holding+0x0`
  from `acquire`, `started` = 1, the four `virtio_disk_intr` reads, the eight device reads) are discharged only
  by an ORDER that walks the read between its GF source and that source's co-successor (rf, plus fr where
  the view can rise).  These rf/fr edges are gmo-forward in GF, so they are consistent with GF, but the order
  of `CertZ17`/`orderSupplyCZ3` (po ∪ protocol co ∪ fabric, acyclic by the κ key) does not contain them and
  the κ key does not extend to them as is (a plain `initlock` store po-before a `holding` read need not be
  gmo-before it).  Recommendation: make the **pinned-read set** (§3 route P, §4) an INPUT of 6l's incremental
  order, i.e. the order chooses each pinned read's position from the realized prefix — one design, sized
  together.
* **F2 — `holding+0x0` from `acquire` is the crux kernel site.**  It is the only lock-word read with no
  value argument, and its two outcomes differ in the hart's EVENTS (frame stores, `lk->cpu` load), not only
  in registers, so no taint relation can absorb it.  Options (spec-first; RVWMO allows the read to return any
  non-overwritten lock value): (a) pin it in the order (FAITHFUL; F1); (b) widen `relW`/`Rel` to let a hart's
  PRIVATE stack events and the `lk->cpu`/`mycpu` reads be skipped or inserted in a re-convergent `holding`
  call (FAITHFUL, a new walk arm, M); (c) assume the read returns the coherence-latest value (STRONGER than
  RVWMO — reject).
* **F3 — the silent step's window is an order obligation.**  `silentOk`'s `q` must exceed every dependency
  predecessor's source; with 6c's faithful bound this is true at GF but needs the order to place those sources
  inside the hold window — the same mechanism as F1 (the failed AMO is a pinned read of the lock word).
* **F4 — the `pte` class needs a custody chain for `uvmcopy+0x36`/`uvmclear+0x10`.**  Seven PTE sites are
  A/D-insensitive (a bit-level dead-taint check); two carry A/D into exit-write data.  xv6 never lets two harts
  write one user table concurrently, but the export exempts `pte` from `chainOkAt`.  Options: (a) a GF-level
  "PTE bytes are process-owned between `p->lock` hand-offs" fact from the realized prefix (FAITHFUL, M);
  (b) a 10th export conjunct chaining live user-table bytes (FAITHFUL, MachCSL lane, M–L); (c) leave the two
  sites poisonable (then the datum is FALSE there — reject).
* **F5 — disk-written and device-read RAM are outside `chainOkAt`** (hart entries only) — their agreement
  rests entirely on the order (F1); the `usedElemGateOk` device premise does not cover read ordering.
* **F6 — the race-free-read theorem must be chain-based** (§5), not CS-based.

## 7. Proof shape (proposed)

1. **Pinned-read set** `pinRd : List Int` (the 6 kernel pcs of route P + the 8 device nodes by program
   position) and the silent slot — a static table, `decide +kernel`-checked against the image (S).
2. **6l's incremental order** takes `pinRd` as input: at a realized prefix, the next event of a hart whose
   next read is pinned is chosen only once its GF source is walked and before its co-successor; progress
   from GF's gmo (the pending pinned read's source is gmo-before it, the co-successor gmo-after).  Also gives
   the silent window (F3).  (Sized under 6l.)
3. **Taint discharge** (route T): a static TAINT WALKER `taintDiesB pc bits fuel` over the image — the
   `KernelPinsDef.pdfs` all-paths DFS with a register/bit taint set driven by `Weak.depsOfBits` roles; sinks =
   store address/data, branch operands, CSR operands, load/store addresses; per site either "dies" or "reaches
   only the listed branch". Sites: `holding+0x12` (sink: the callers' branch on `a0`, cleared by the
   `seqz`-value lemma), the 7 A/D-insensitive PTE sites (bit taint {6,7} dies at `andi`/`srli`), `ilock+0xe`,
   `iunlock+0x1c` (sink: `blez`, cleared by the ≥ 1 lemma).  Generator + `decide +kernel` table, like
   `gen_weak_pins.py`.
4. **Value lemmas at GF** (route T/O): `lkCpu` non-holder (CoWR + CS structure), holder agreement at
   `release`/`sched` (the realized state's holder), `ip->ref ≥ 1` co-interval.
5. **The twin port of CertZ13** (`siteFacts`/`hartStepOfSite` → `hartStepRIS` at `relT`), with the silent
   arm and the shadow `w'` (6c), and the chain-based race-free-read theorem for every other read.

## 8. Sizing (unverified estimates; Weak lane rate 4–8 h per 1k)

| part | Lean lines | worker-h | conf. |
|---|---|---|---|
| 1 pinned-read table + check | 0.05–0.15k | 1–2 | H |
| 3 taint walker + table (generator ≈ 0.2k Python, not counted) | 0.3–0.6k | 3–6 | M+ |
| 4 value lemmas (lk->cpu, holder agreement, ip->ref co-interval) | 0.4–0.9k | 3–8 | M |
| 5 CertZ13 twin port at `relT` + silent arm | 0.5–1k | 4–8 | M |
| race-free-read theorem (chain-based) | 0.8–1.5k | 6–12 | M− |
| F4 (a) PTE custody at the realized prefix | 0.3–0.6k | 2–5 | M |
| **6m without the order** | **2.3–4.7k** | **19–41** | M− |
| 2 pinned reads + silent window inside 6l's order | +0.5–1.5k on row 6l | +4–12 | L (6l's risk) |

The plan's row 6m (1.5–4k, 10–30 h, L+) is in range; its LOW confidence moves to row 6l (F1–F3).

## 9. Open questions (spec-first, one line each)

* **Q-6M-ORDER** (F1/F3): pinned reads + silent window as inputs of 6l's incremental order (a, FAITHFUL,
  recommended) vs. a separate pinned-read order lemma after 6l (b, FAITHFUL, more re-proof).
* **Q-6M-HOLD** (F2): `holding+0x0` from `acquire` by the order (a, recommended) or by a re-convergent
  `holding` arm in `relW` (b); assuming latest-value reads is STRONGER than RVWMO (reject).
* **Q-6M-PTE** (F4): GF-level PTE custody from the realized prefix (a, recommended) vs. a 10th export conjunct
  (b, MachCSL lane).
