# The twin↔machine conformance matrix (route P, P-W6 step 1, [OWN.149])

Worker w2, 2026-10-21.  Design `weakmach/proposal-A7.md` §5.1; litmus file `Weak/SbConfLit.lean` (green, axioms
`propext, Classical.choice, Quot.sound`); spike `Weak/SbRealP.lean` (`PROGRESS-PW6.md` §1).  Read at the w2 tip:
`Weak/SbCand.lean` (`stepE :254`, `land :290`, `SbPol.epoch :114`), `Weak/SbWalk.lean` (`evData :732`),
`Weak/SbOrd.lean` (`fabOk :66`, `enbL :88`, `landG :105`, `DevStOrd :262`, `blkFab :1047`),
`Weak/WeakEvInst.lean` (`pnodeStep`, `pstepDisk`), `Weak/VirtioProg.lean` (node table), `MachCSL/Lang.lean`
(`evStep :1552`, `blockedStep :1607`, `primStep :1828`, `devOpStep :1750`, `storeDma :217`, `landOk :462`,
`landNowOk :490`, `drvOkGuard :1300`), `MachCSL/TsoMem.lean` (`fenceDrainsSb :863`, `fenceEpoch :868`),
`Weak/GraphFabResidue.lean` (`ioResidue :123`).

## 0. Summary (plain words)

* The question per cell: when the realization (the P-W6 state map `rmemP`) meets a twin step of row R, does
  MachCSL's arm C answer it?
* "Machine stronger" means the twin can step and the machine cannot, so the realization is stuck.
* **Seven machine-stronger cells.** Five are known: F-PW6-1, F-PW6-2, the kept `fence.i` drain (the fetch
  marker), and the fetch pair (view 0 against `itv ≤ tvn`, plus the instruments `fetchOk`/`excOk`/`kStuck`,
  which are W4 premises from HSafe).
* **TWO cells are NEW**, both on the I/O and device side:
  * **F-CM-1.** A BUFFERED device store moves the fabric (virtio `isr`, `usedIdx`) at its ISSUE. A
    fabric-later HART MMIO access may be realized before the store LANDS. MachCSL does the device move and
    the DMA landing in ONE transition. The [OWN.148] gate does not cover this, because the reader is a hart
    row.
  * **F-CM-2.** The twin's `LIo` has no counterpart of MachCSL's `drvOkGuard` ([OWN.131], bug #1). The
    walk can realize hart 0's `DRIVER_OK` while the queue-page zeroing stores are pending, and the machine
    is then blocked.
* Each new cell has a Weak-only FAITHFUL walk-gate remedy whose progress comes from a trusted residue item
  already in the base: (R3) for F-CM-1 and (R1) for F-CM-2.
  * Neither needs a new named premise or a MachCSL change.
  * Both edit the merged `SbOrd`, the same file and descent that [OWN.148] already edits.
  * Size: +0.2–0.6k together.
* F-PW6-3 (`fence.tso`) is EQUAL in behaviour. It is only a one-step lag in the state map's epoch counter,
  so it has no litmus.
* Under K2′ (A7 §6), "a twin↔machine gap NOT in the conformance matrix after the audit" does NOT fire,
  because these two are found BY the audit. K6 counts them as two unplanned rows.

Cell codes: **E** EQUAL (under the listed premise) · **T** twin weaker = MACHINE STRONGER (realization stuck
without the premise; litmus in `SbConfLit`) · **M** machine weaker (harmless for the realization) · **O** outside
spec (platform/device/instrument text) · **·** the realization never pairs them.

## 1. The grid (rows: `SbCand` rules; columns: MachCSL arms)

Columns.
* C1: memRead MMIO.
* C2: memRead ifetch.
* C3: memRead plain (explicit and walker).
* C4: memRead exclusive.
* C5: memWrite MMIO (with `drvOkGuard`).
* C6: memWrite plain (`issue`).
* C7: memWrite exclusive (`storeL`).
* C8: barrier.
* C9: the land arm (`landOk`, `¬ kStuck`).
* C10: blocked exclusive read.
* C11: blocked exclusive write or `DRIVER_OK`.
* C12: blocked draining fence.
* C13: `devStep`/`devOpStep` (`dmaWrite` = `storeDma`, `dmaRead`, `step`/`setPin`/`sample`).
* C14: the no-op arms: `tlbi`, `cacheOp`, `translation*`, `take`/`returnException`, `instrAnnounce`,
  `regRead`/`regWrite` (`excOk`), the boundary's `dropResv`, `PowerOn`.

| twin rule ↓ / arm → | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | C10 | C11 | C12 | C13 | C14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R1 `stepE.load` (fwd; walk: top read) | · | · | **E** a | · | · | · | · | · | · | · | · | · | · | · |
| R2 `stepE.issue` | · | · | · | · | · | **E** b | · | · | · | · | · | · | · | · |
| R3 `stepE.fence` (+ `sfence.vma` marker) | · | · | · | · | · | · | · | **E/T** c | · | · | · | **T** d | · | **E** e |
| R4 `stepE.rmw` (AMO / walker A/D pair) | · | · | · | **E** f | · | · | **E** f | · | · | **E** g | **E** g | · | · | · |
| R5 `stepE.io` (hart `LIo`) | **E** h | · | · | · | **E/T** i | · | · | · | · | · | **T** i | · | **E** h | · |
| R6 `land` (`SbPol.epoch`) | · | · | · | · | · | · | · | · | **E/T** j | · | · | · | · | · |
| R7 boot (`initS`) | · | · | · | · | · | · | · | · | · | · | · | · | · | **E** k |
| R8 device row (agent `NCPU`) | **T** l | · | · | · | **T** l | · | · | · | · | · | · | · | **T/E** m | · |
| R9 fetch (`evData` star, view 0) | O n | **T** o | · | · | · | · | · | · | **O** p | · | · | · | · | **O** p |

## 2. The cells

| id | pair | verdict (mark w.r.t. RVWMO / Sail / Zifencei / PMAs) | realization premise | evidence |
|---|---|---|---|---|
| a | load × plain read | **E** at TOP reads: MachCSL `readFwd` at `tvn = σ.ltop` is the twin's forwarded byte (youngest own pending), else the member-latest byte; `tvn = ltop` is always enabled (`cohOk`, `tv ≤ ltop`); the walker's PTE reads are plain on both sides (`akPlain`; `pnodeStep` → `LLoad`); a twin `aq` load needs `noRl`, the machine nothing (M, vacuous: xv6 has no `.rl`). Twin stale reads (views below the top) are outside the walk (its read gate) | `ramBytes` (HSafe, as W4); the walk's read is a top read (`srcGate`/`valGate`, exempt `rdX` reads included) | `SbRealP.byteFwdTop`, `topLoadEnabled`, `rmemPLoad` |
| b | issue × plain write | **E**: both push a pending entry, no guard; `rl = false` (no plain `.rl` store in the ISA; `entRel`) | `ramBytes`, label bytes = `w` | `rmemPIssue` |
| c | fence × barrier | **E** for every barrier but `fence.tso`: drain `pw ∧ sr` = `fenceDrains` (W→R kinds); epoch `pw ∧ sw` = `fenceEpoch`. `fence.tso`: **behaviour EQUAL**, state map lags (machine bumps the epoch at the instruction, the twin at the parked `LFence t t f t`, which fires at the hart's next node before anything else; between them only landings happen, and all pending entries are in the old epoch on both sides, so both land the same set) — F-PW6-3, xv6 has no `fence.tso` (image census), no litmus | image fact "no `fence.tso`" | `rmemPFence`, `fenceEpochOfEbar`, `fenceDrainsOfEbar` |
| d | fence (`LFence false×4` at `fence.i`) × blocked draining fence | **T** (known): the twin does not drain, MachCSL's `fence.i` waits for an empty buffer ([OWN.146] keeps the drain; STRONGER than Zifencei, EX-FENCEI-1). Litmus: MP with `fence.i` on the writer | walk gate at `fence.i` heads (own buffer empty), which needs the distinct fetch MARKER (O-P-W1-a; the twin label is shared with `sfence.vma`); progress: own pending stores are landing targets of the row (the H2-style argument) | `SbConfLit.fiRun`, `fenceIBlocked` |
| e | `sfence.vma` marker × `instrAnnounce`/`tlbi` | **E**: both no-ops on memory (the marker drains nothing, bumps nothing); the walker reads own pending PTE stores by forwarding on both sides | — | `pnodeStep` `.instrAnnounce`/`.tlbi`, `evStep` no-op arms |
| f | rmw × exclusive read + exclusive write | **E**: read at the landed top (`rmwLatest` = `topBytesL`); write lands at once, inserted below the footprint's pending prefix (`storeL`) = appended to the twin's landed log, foreign pending entries land later on both sides; `amoOk` ⇔ `¬ sbOverlaps` ∧ `landNowOk` (current epoch, no hit; `.rl` ⇒ empty); `.aq` epoch guard and the AMO read's same-address drain EQUAL (both STRONGER than RVWMO's AMO read, the ledger's "atomic-read drain", identical on the two sides) | the pair realized contiguously (an item is atomic); R-resv (no reservation between items) for `¬ othersReserve` | `rmemPRmw`, `amoGuardOf`, `topLEq` |
| g | rmw × blocked exclusive read / write | **E**: never needed — when the twin's `rmw` is enabled, `amoOk` and R-resv make both machine guards hold | — | `amoGuardOf` |
| h | io × MMIO read / write (UART, PLIC, virtio registers); the disk agent's UART/PLIC `LDev .dev` moves × `devStep` | **E** on memory (both inert); values by `R-dev` (W4 F6/F9); routing: the twin decodes by `devAddr pa`, the machine by the whole footprint (`devBytes`/`ramBytes`) | `devBytes` from HSafe (`devOfSafe`, as W4) | `rmemPIo`; `MachOfPf` F6/F9 |
| i | io (hart 0's `DRIVER_OK` store) × MMIO-write arm / its blocked arm | **T — NEW, F-CM-2.** MachCSL's MMIO write needs `drvOkGuard` (hart 0 at `drvOkPc`: no pending store to the three queue pages; [OWN.131], STRONGER than RVWMO at that instruction); the twin's `LIo` has no guard; the walk's `LIo` gate is `True` (`SbOrd.enbL`). E at every other MMIO store | **gate (a)**: a hart's I/O head waits until its pending stores have landed (or only at `DRIVER_OK`); progress from the TRUSTED (R1) (RAM access po-before an I/O event ⇒ gmo-before) + H4 `ioOrd` (the head's measure is its own gmo position) | `SbConfLit.drvRun`, `drvOkBlocked` |
| j | land × land arm | **E** on the own side (oldest pending epoch = `fenced`; own older overlapping entry = pending below); **T** across harts (known, F-PW6-1: pending entries of DIFFERENT harts on a byte land in ISSUE order). The arm also needs `¬ kStuck` (O: the instrument, from HSafe as W4 (5)/(6) — a NEW consumer of the same source, at every landing) and no reservation on the bytes (R-resv) | `ForeignBelowLanded` ⇐ `IssueCo` + census (F-PW6-1 (a)); `¬ kStuck` from HSafe | `rmemPLand`, `landBlockedForeign`; `SbConfLit.sRun`/`sLog` (the full S chain, [B6.s4]) |
| k | boot × `PowerOn` | **E** (empty logs, buffers, epochs, reservations; devices reset; registers by `bootFacts`) | — | `rmemPBoot`; `MachOfPf` F3 |
| l | device row's fabric-moving `DWriteDev` × a hart's later MMIO access (C1/C5) | **T — NEW, F-CM-1.** The twin's DWriteDev moves the fabric (`complete`: `isr`, `usedIdx`, in-flight removal) at its ISSUE (`pstepDisk`) while `SbCand` buffers the RAM store; `SbOrd.fabOk` lets a fabric-later hart MMIO access go once the store is ISSUED. MachCSL's `dmaWrite` moves the device state AND lands the store in ONE transition (`dmaWriteAtomic`). Between issue and landing, the realization has either an unmoved machine device (the hart's `InterruptStatus` read answers `0` where the twin's fabric answers `isr ≠ 0`: R-dev broken) or a landed store (R-lp broken). [OWN.148]'s gate is for the device row's OWN head, not hart rows | **gate (a′)**: `fabOk` counts an earlier fabric member that is a STORE as done only once it has LANDED; progress from the TRUSTED (R3) (fabric order ⊆ gmo on memory events, `blkFab`'s `hr3`): the store's landing target sits below the head. **or (b′)**: the device store issues only when its landing gate holds and lands in the same walk unit (subsumes [OWN.148]; progress from `DevStOrd`, as [OWN.148]) | `SbConfLit.fabRun`, `dmaWriteAtomic` |
| m | device row × `devStep` | DWriteDev × `dmaWrite`: **T** (known, F-PW6-2: the twin buffers, MachCSL lands at once; same-epoch device stores land out of order in the twin — litmus `dmaRun`) — ruled [OWN.148]; `DRead` × `dmaRead`: **E** under the gate (no own pending entry to forward from; both read the landed top, `dmaView`, non-memory bytes free on the machine = M); `DFence` × nothing: **E** (the machine has no device fence; its DMA is never pending); `DPop`/START × `step`: **E** (W4 F9); zero-byte DMA: M (the machine's no-op; the twin emits none, `DmWf`) | [OWN.148] gate; the DMA rows realize the machine's `dmaWrite` at the twin's LANDING (`rmemPDma`) | `SbConfLit.dmaRun`, `dmaLandsAtOnce` |
| n | fetch × MMIO | O: fetch from I/O is excluded by the boot PMA table (`sailCycleOrder`, W4 deviation 3) | as W4 | — |
| o | fetch × ifetch arm | **T** (known, the fetch pair): the walk fetches at view 0 of the landed log (every value a byte EVER held, per byte), MachCSL at one `tvn` with `itv ≤ tvn ≤ ltop` (and `fence.i` raises `itv` past the own last landed store); neither forwards (F-6m-1's machine half: a fetch of the row's own PENDING store has no twin source) | `FetchCutP` (rows 6h/6m/(t3)), `FetchProg` | `SbConfLit.fetchStale`, `fenceIItvPub` |
| p | fetch / any row × instruments (`fetchOk` [OWN.144], `excOk` [OWN.115], `kStuck` at the land arm) | O (proof instruments, STRONGER by design; never fire on xv6 runs by the export's non-stuckness) | HSafe (W4 premises (5)/(6), now also at every landing) | `MachOfPf` deviation list |

## 3. The new findings, spec first

### F-CM-1 — a buffered device store's fabric move is visible before its landing

**Spec.**
* RVWMO, riscv.cat, Sail, Zifencei and the PMAs say nothing about device-internal steps.
* The virtio model is platform text. Its model of record is MachCSL's `Virtio.serve`. There, the DMA write
  and the device-state move are ONE guarded transition (`devOpStep .dmaWrite`, `Lang.lean:1759`).

**Mismatch.**
* The pf twin `DWriteDev` mirrors that transition: the log append and the fabric move happen in one step.
* `SbCand` buffers the store but not the fabric move. This is what route P changed against W4.

**Remedy options.**

| option | content | mark | size | progress source |
|---|---|---|---|---|
| (a′) | `fabOk`: an earlier fabric STORE must have LANDED | FAITHFUL | +0.1–0.3k on [OWN.148]'s `SbOrd` edit (`blkFab`: the target becomes the store's landing) | (R3) |
| (b′) **recommended** | a device-row store head is enabled only when its landing gate holds, and issue and landing form one walk unit. It subsumes [OWN.148] and keeps `rmemP`'s "every non-hart buffer empty" at every item boundary, so the DMA row needs no window relation | FAITHFUL | 0.4–1.0k in total, replacing [OWN.148]'s 0.4–0.9k | `DevStOrd` (H4 `stOrd`): the landing gate's dependencies are gmo-before the store |
| (c′) | buffer DMA in MachCSL | — | > 2k | — (K1) |

### F-CM-2 — the `DRIVER_OK` step guard has no twin or walk counterpart

**Spec.**
* RVWMO + PMAs do not order a RAM store before a later MMIO store without `fence w,o`. That is bug #1.
* MachCSL's guard is STRONGER at that one instruction ([OWN.131]).
* The trusted residue (R1) is STRONGER still, at the graph level, for every I/O event. It is kept until the
  capstone [OWN.142].
* So on (R1)-graphs the queue-page stores are already gmo-before `DRIVER_OK`. The gap is only in the walk's
  SCHEDULING: it may run the I/O head before those stores land.

**Remedy options.**

| option | content | mark | size | progress source |
|---|---|---|---|---|
| (a) **recommended** | `enbL`'s `LIo` arm: a hart's I/O head waits for an empty own buffer, or for no pending queue-page store at hart 0's `DRIVER_OK` | FAITHFUL walk scheduling under the trusted (R1) | 0.2–0.4k, same `SbOrd` edit | (R1) + H4 `ioOrd` |
| (b) | name the RVWMO face of [OWN.131] as a GF premise | WEAKER while named | — | — |

Option (b) is not needed: (R1) already gives the ordering.

## 4. What the matrix changes in P-W6

* Row order is unchanged: DMA → hart rows → `SimRelP` → `readAt` → transport residue → `FetchCutP`.
* The DMA item grows by F-CM-1. Under (b′), the [OWN.148] gate is restated as "a device store lands in its
  issue unit".
* The `SbOrd` edit gains the `LIo` gate (F-CM-2).
* The land row gains the HSafe `¬ kStuck` premise. This is a consumer, not a new input.
* No MachCSL ask beyond `PROGRESS-PW6.md` §4.
