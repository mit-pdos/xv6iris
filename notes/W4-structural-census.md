# W4 structural census (PROVISIONAL, read-only, 2026-10-11)

**Status.** Census for W4's STRUCTURAL half (plan `notes/weak-allocproc-plan.md` §C W4 :881-889, §B(10)
:482-640). It does NOT amend the plan of record. Every interface proposal below is an OPEN ITEM for the next
advisory round (§E). No Lean was edited and nothing was built.

**Tip read.** Workspace `/home/bsdinis/dev/xv6iris-weak-w7` (jj workspace `weak-w7`). `reslot.sh` created it on
2026-10-11 at 09:36 from the then-tip `@-` of `xv6iris-weak` (`weak-orch/reslot.sh:12-13`). That was after the 09:23
merge of W-COH, the W5b′ fixes (`itv`), the W13 (E) sweep and W1b (`weak-orch/allocproc_prog.txt`, last two lines).
jj operation id, read from `.jj/working_copy/checkout` bytes 2..65:
`0c7137e80de02bc5422a7c15392454ef4ffdf8b52b2894d65c5ca133642f97a5d62b31654c61c23d866e9c66c9ce4e88b9309a7b10991f78aeb376349ac66cd0`.
I could not record a commit hash because git/jj may not be run. All `file:line` references below are in this tree.
Where the brief's line numbers have drifted, the actual line is cited instead: `powerFork` is `MachCSL/Lang.lean:323`
(`:319` is `cpus`), `hartObsM` is `:471`, `hartStep` `:504`, `devOpStep` `:531`, `devStep` `:575`, `primStep`
`:603`, and the `primStep_*` lemmas are `:637-690`. The iris `Step`/`NSteps` definitions are cited from the shared
lake of the tip checkout, `/home/bsdinis/dev/xv6iris-weak/.lake/packages/iris/Iris/Iris/ProgramLogic/Language.lean`
(written `iris:Language.lean` below), because `-w7` has no `.lake`.

**Marks.** Each semantics point opens with a **Spec:** line and is marked FAITHFUL / STRONGER (the model admits
fewer behaviours than the spec, or the theorem assumes more) / WEAKER (the model admits more), as the owner rule
requires.

## Recommendation in one paragraph

W4's structural half is a **forward simulation by induction on the shadow-carrying step list** (`pfRunST`,
`Weak/TsoShadow.lean` header :38-41). Its relation is `poolRel ∧ R_mem`:
- `poolRel` holds the MachCSL thread pool, the hart expressions and register files, and the UART/PLIC programs plus
  device states.
- `R_mem` is the PARAMETER over `MState`'s memory fields and the prefix shadow.

The run starts with ONE `PowerOn` step, built from `wbootFacts` → `bootShape` (§D). After that, each pf step maps
to **0 or 1** `primStep`s of a thread chosen by the step's KIND, not by its agent index (§A2, §B6). Memory content
comes from the parameter `pfStepTso`. Two extra inputs make this go through:
- a MachCSL-side safety hypothesis **HSafe** ("every thread of every run from boot is `Reducible`"), which supplies
  the bus decode the pf machine lacks (§B5);
- `κs` defined as a function of the pf run (§B7).

This works as stated for **harts, MMIO, UARTs and the PLIC**. It **does NOT work for the disk**. The pf disk agent
runs `Weak/VirtioProg.lean`'s `virtioProg`, a recorded DRIFT from MachCSL's `Virtio.body`/`serve`. They differ in
four unconditional ways: the used element is 2 writes in pf vs 1 in MachCSL, which breaks the log positions; the
used-element `len` value differs; DWild writes vs a stall; and the fabric window between COMMIT and the used-index
write differs (§C4). That needs an owner-level model decision (E-D1) before W4's disk rows can exist. The plan's
stuttering bound `n ≤ |st|` (:883) is false once disk rows are included (§B6).

---

## (A) PowerOn and the pool

**A1. The two pool layouts.** *Spec:* RVWMO, riscv.cat, Sail and the PMAs say nothing about thread pools or power.
The board is QEMU `virt` with 8 harts, 2 UARTs, a PLIC and one virtio-blk. **FAITHFUL**: this is bookkeeping only.
- MachCSL start: `([Expr.power], g)` with `g.gen = 0`, `g.pow = false` (`MachCSL/Adequacy.lean:369`;
  `Xv6/LinkSystemAdequacyClosed.lean:21`, which also has `Hdisk : diskOf g.m.devs = fsImgDisk`).
- The `PowerOn` arm (`Lang.lean:613-617`) emits `[.powerOn]`, forks `powerFork g.gen` and requires
  `bootShape g g'`.
- iris `Step.atomic` appends forks at the END of the pool (`iris:Language.lean:128-130`). So after PowerOn the pool
  is `[power] ++ cpus.map (Loop 0) ++ DevId.all.map (DevLoop 0)` (`Lang.lean:319,323`), where
  `DevId.all = [uart0, uart1, plic, virtio]` (`MachCSL/Dev/DevIds.lean:35`).
- pf side: `Wpcfg` has **NCPU+1 = 9 agents** (`eagsLength`, `Weak/WeakEvPf.lean:292`;
  `epsInit = cpus.map PHart ++ [PDisk none]`, `Weak/WeakEvCapstone.lean:1026-1027`). The UART and PLIC programs are
  NOT agents. They are FABRIC (`Efab`, `WeakEvPf.lean:250-255`; `efInit`, `:269`).
- `epowerFork`'s `[harts; uart0, uart1, disk, plic]` (`Weak/WeakEvLang.lean:201-204`; `epoolTail`,
  `WeakEvPf.lean:182-186`) is the EVENT language's pool. W4's input is the pf configuration
  `wpInit … (epsInit σ0)`, so `epowerFork`'s plic/disk order, which is swapped relative to `DevId.all`, never enters
  W4.

| MachCSL index | expression | pf counterpart |
|---|---|---|
| 0 | `power` | none (stepped once, never again) |
| 1+c (c < 8) | `.hart 0 c m` | agent `c` = `PHart c m rs fn ib` (pstepNode arm) |
| 9 / 10 | `.dev 0 (uart i) 0 m` | `Efab.efU i`, stepped by agent NCPU via `pdiskUart` (`Weak/WeakEvInst.lean:518-524`) |
| 11 | `.dev 0 plic 0 m` | `Efab.efPlic`, stepped by agent NCPU (`pdiskUart` PLIC arm) OR by hart agent `cpu` at a `setPin` node (`pstepPlic`, `WeakEvInst.lean:464-472`; `plicAgent`, `WeakEvPf.lean:385-387`) |
| 12 | `.dev 0 virtio 0 m` (root) | agent NCPU's `PDisk dp` (`pdiskProg`), §C4 |
| 13+k | virtio `serve` task, TaskId k+1 (fork appends, `Lang.lean:550-553`) | a sub-span of one pf burst, §C4 |

**A2. The map is per step KIND, not per agent.** Agent NCPU's step goes to thread 9, 10, 11, 12 or 13+k depending
on which `pstepDisk` disjunct it takes (`WeakEvInst.lean:526-529`). Hart agent `c`'s step goes to thread `1+c` (its
`pstepNode` arm) or to thread 11 (its `pstepPlic` arm, `:475-481`). So `poolRel` needs a function from the pf step
witness to a MachCSL thread index, not a fixed agent→thread map. *Spec:* as A1. **FAITHFUL**.

**A3. `gen` and `threadLive`.** *Spec:* none; this is the SC tree's era bookkeeping. **FAITHFUL**.
- Every forked thread carries `gen = g.gen = 0` (`Lang.lean:617`). `bootShape` keeps `gen` and sets `pow`
  (`:307-308`).
- Only the power arm changes `gen`/`pow` (`:613-617`); hart and device arms set `g' = { g with m := σ' }`
  (`:607,611`). W4 never schedules the power thread again, so `threadLive g 0` (`:273`) holds at every later state.
- Invariant: `g.gen = 0 ∧ g.pow = true`. The corpse arms are never used.

**A4. Single era (D14, plan :1485).** *Spec:* PowerOff/PowerOn are platform events outside RVWMO, which describes
one execution. **FAITHFUL** to RVWMO's scope and **WEAKER** than the SC tree's multi-era conclusions.
- The pf side has no power at all: `Wpcfg` has no `gen`/`pow` (`Weak/WeakPromise.lean:138-142`), `epowerFork`
  forks no power thread (`WeakEvLang.lean:201-204`), and `WeakExec` is single-era by its `gen = 0` premise
  (`Weak/WeakExec.lean:33-36`).
- W4's run is therefore exactly one power step at position 0 followed by simulated steps. Crash and recovery facts
  are not transported (plan :535-536).

## (B) Hart expression and observation alignment

**B1. Shared `riscvStep`.** *Spec:* Sail's `try_step` plus a nondeterministic clock tick (`Lang.lean:206-214`).
**FAITHFUL**: both sides use the same model text. `MachCSL.riscvStep` (`Lang.lean:212-214`) is the constant the pf
boundary arm uses (`m' = riscvStep tick`, `WeakEvInst.lean:284-288`) and the one MachCSL's `hartStep .pure` arm uses
(`Lang.lean:506`). The plan cites `WeakEvInst.lean:286` for this; the shared constant is used at `:287`.

**B2. `R-expr` / `R-regs`.** MachCSL `.hart 0 c m` corresponds to pf `PHart c m rs fn ib` with the SAME `m`.
- `fn` (the parked second fence) and `ib` (dependency bits) have no MachCSL image.
- `σ.regs c = rs`. pf registers live in the PROGRAM state (`Pexv6.PHart`, `WeakEvPf.lean:220-223`); `WGState.wgregs`
  is not in `Wpcfg`.

*Spec:* registers are Sail state. **FAITHFUL**.

**B3. Continuations.** At every node pf takes `m' = k v` (`WeakEvInst.lean:293-397`) and MachCSL takes `m' = k v`
(`Lang.lean:508-510`) with the SAME answer:
- `regRead`: `v = rs r = σ.regs c r` (`Lang.lean:358`).
- `regWrite`: pf `ors = some (rs.set r v)` (`WeakEvInst.lean:297-300`), MachCSL `setReg` (`Lang.lean:359`).
- RAM/MMIO read: `.Ok (w, none)`. RAM/MMIO write: `.Ok (some true)`.
- `barrier`, announces, `cacheOp`, `tlbi`, `translation*`, exception events, `cycleCount`, `message`: `()`.
- `getCycleCount`: `0` on both sides. `choose`: any answer.
- `.error`, `readRam`, `writeRam`: stuck on both sides (`WeakEvInst.lean:282,398-399`; `Lang.lean:383-384,507`).

*Spec:* the Sail outcome interface. **FAITHFUL**.

**B4. Access kinds.** `classify k = ⟨akIfetch k, akExcl k, akAcq k⟩` (`Weak/WeakInterp.lean:306`;
`classifyAkLatest :309` is `rfl`), so pf's `akIfetch`/`akLatest`/`akSync` tests ARE MachCSL's
`akIfetch`/`akExcl`/`akAcq`. `akPlain = !akIfetch && !akExcl` (`MachCSL/TsoMem.lean:538`). Neither side tests the
access kind on the MMIO arm (`WeakEvInst.lean:301,336`; `Lang.lean:361-363,377-378`). *Spec:* Sail's
`Access_kind`. **FAITHFUL**.

**B5. Bus-decode mismatch (pf RAM access outside DRAM).** *Spec:* Sail checks the PMAs before it issues a memory
event. In this tree the PMA set is IO regions plus RAM `[0x80000000, +0x8000000)` (`MachCSL/Platform.lean:200-258`),
and an access outside every region raises an access fault. MachCSL's footprint decode (`ramEnd = 0x88000000`,
`TsoMem.lean:99`) is **FAITHFUL** to the PMAs. The pf arm is **WEAKER**: it admits labels Sail never emits.
- pf branches on `devAddr req.pa`, the START address only (`WeakEvInst.lean:301,336`;
  `devAddr = pa < 0x80000000`, `MachCSL/Dev/Fabric.lean:125-126`).
- MachCSL needs `devBytes pa n` (MMIO) or `ramBytes pa n` (RAM) over the whole footprint (`Lang.lean:361-382`;
  `ramBytes`, `TsoMem.lean:110`).
- So a pf RAM label at or past `ramEnd` (WeakMem is `Int`-keyed and unbounded) has **no MachCSL arm**.

Ways to close it:
- (i) A Sail-level lemma: every memory event `riscvStep` emits has a PMA-covered footprint. Generic over the residual
  monad; XL, unverified.
- (ii) **Recommended:** W4 takes **HSafe**, "every thread of every MachCSL run from `([power], g0)` is `Reducible`",
  as a hypothesis. W5 discharges it from `xv6FsAdequacy_closed`'s first conjunct
  (`Xv6/LinkSystemAdequacyClosed.lean:20-24`). How it closes the gap:
  - At the matched hart (same `m`), `Reducible` gives `devBytes ∨ ramBytes ∨ othersReserve` (`Lang.lean:360-382`,
    `blockedStep :402-409`).
  - `othersReserve` is false under `pairAdjacent`: no other hart is mid-pair when this one steps.
  - **FAITHFUL**: it imports the SC proof's own safety fact.
  - This is not (↑). §B(10)'s "(↑) NOT claimed" (plan :531-533) is about WEAK-side `Reducible`; HSafe is
    MachCSL-side and already a conclusion of the SC tree.

  Open item E-S1. HSafe gives nothing for the disk's `dmaWrite`, whose no-op arm is always enabled
  (`Lang.lean:544-545`); see E-M5.

**B6. 0 vs 1 `primStep` per pf step (the stuttering table).**

| pf step (arm, `WeakEvInst.lean`) | MachCSL steps (`Lang.lean`) | thread |
|---|---|---|
| `LInstr` boundary (`pnodeStep .pure`, :284-288) | 1: `hartStep .pure` (:506) | 1+c |
| `LInstr` at the announce, or the sfence.vma marker `LFence false×4` (`annLabel`, :372-374) | 1: `evStep .instrAnnounce`, `σ' = σ` (:396) | 1+c |
| `LSilent` from `regRead` (:293-296), `branchAnnounce`/`cacheOp`/`tlbi`/`translation*`/exceptions/`cycleCount`/`message`/`getCycleCount`/`choose` (:375-397) | 1, each with `σ' = σ` (:358, :386-399) | 1+c |
| `LRegW`/`LCtrl` (the `erwLabel` of `regWrite`, :297-300) | 1: `setReg` (:359) | 1+c |
| `LSilent` RETRY self-loop of the conditional write, `m' = m` (:363-365) | **0** (MachCSL's `blockedStep` needs `othersReserve`, :407, false under `pairAdjacent`) | — |
| `LFence (ebarNow b)` and `fence.i`'s `LFence false×4` at the barrier node (:367-370) | 1: `MState.fence` (:385) | 1+c |
| parked-fence fire, `fn = some`, `m' = m` (`pstepNode`, :409-412) | **0** (MachCSL applied the whole barrier at the node; the shadow's park is the identity, `TsoShadow.lean:234-238,247-251`) | — |
| `LIFetch`/`LLoad`/`LExLoad`/`LStore`/`LExStore` (RAM, :308-335, :345-362) | 1: RAM arms (:364-375, :379-382); content = `pfStepTso` | 1+c |
| `LDev .rd/.wr` (MMIO, :301-306, :336-344) | 1: MMIO arms (:361-363, :377-378) | 1+c |
| `LDev .dev` PLIC wire at the hart agent (`pstepPlic`, :464-472) | 1: `devOpStep .setPin` (:546-549) | 11 |
| `LDev .dev` UART `i` / PLIC gateway at agent NCPU (`pdiskUart`, :518-524) | 1: `devStep` (§C1) | 9/10/11 |
| disk rows (`pdiskProg`, :485-516) | multi-step, partly NONE (§C4) | 12, 13+k |

*Spec:* the two 0-step rows are pf-ENCODING artifacts:
- Sail emits ONE barrier event for `fence.tso`; pf splits it into `ebarNow` + `ebarPark` (`WeakEvLang.lean:733-750`,
  `efenceBarrierPost :757-759`).
- The retry is a memory-blind stutter of the pf encoding (WeakEvLang (D3)).

Matching them to 0 steps is **FAITHFUL**: nothing is added or removed on the MachCSL side.

Correction to the plan and W2's table: `LSilent` and `LInstr` are 0 TsoMem MEMORY changes but **1 primStep**. Only
the retry `LSilent` and the parked fire are 0 primSteps.

So for hart/MMIO/UART/PLIC rows, `n = |st| − #retry − #parkfire ≤ |st|`. With disk rows the bound `n ≤ |st|`
(plan :883) is **false**: MachCSL's virtio needs internal steps with no pf counterpart (choose/get/guard-pop/fork/
modify/restart, `MachCSL/Dev/Virtio.lean:522-552,559-579`). No consumer in the plan cites the bound (grep: only
:883), and adequacy quantifies over every `n` (`Adequacy.lean:118,386`). Recommend dropping it. Open item E-S6.

**W-RSV (i-a)** ([OWN.22][OWN.23]) turns the `.pure` arm into a reservation-clearing arm. Only the BOUNDARY
`LInstr` maps to `.pure`; the announce `LInstr` maps to `.instrAnnounce` (`σ' = σ`). So W-RSV changes one structural
row. Its content is `R-resv` (E-M9).

**B7. Observations.** *Spec:* `Obs` (user boundary, UART wire) is MachCSL/NI vocabulary, not an RVWMO notion.
**FAITHFUL**.
- **pf has none.** `weakEvLang`'s `Obs` is `Empty` (`WeakEvLang.lean:1007`), `wprimStep`'s `κ : List Empty`
  (`Weak/WeakLang.lean:690`), and `Wlabel` carries no observation.
- MachCSL hart step: `hartObsM c m σ` (`Lang.lean:471-474,604-606`). It is nonempty only at a `cur_privilege` write
  that crosses User (`hartObsPriv :449-453`), and it reads `σ.regs c`. Under `R-regs` it equals `hartObsW c rs r v`
  on pf's pre-state.
- UART step: `obs = os.map Obs.dev` where `g (ds.st d) = some (s', os)` (`Lang.lean:534-536`). The guard is a
  function, so `os` is determined by pf's pre-fabric (`fdevStep`'s `∃ os`, `WeakEvInst.lean:446-447`).
- `setPin`/`get`/`choose`/`sample`/`dma*`/`fork`: `[]` (`Lang.lean:537-554`). Power: `[.powerOn]`.

So W4 can export `κs = .powerOn :: pfObsOf run` as a DEFINED function of the pf run's configurations. "Same
observations" becomes definitional, not a matching obligation (E-S3).

## (C) Devices under D51 (RULED (a), one row)

*Spec (for all of §C):* RVWMO, riscv.cat and Sail say nothing about device threads. The device texts are:
- virtio 1.x: the used element's `len` is the number of bytes written into the chain's device-writable buffers;
  FLUSH succeeds iff `F_FLUSH` is negotiated; the driver MUST NOT publish malformed chains, so the device's
  behaviour on them is unspecified.
- The 16550 datasheet and the PLIC spec for the UARTs and the PLIC.

**C1. UART `i`** (`pdiskUart` uart arm, `WeakEvInst.lean:521-522`). **FAITHFUL**: the same `DevProg` text runs on
both sides.
- `fdevStep (.uart i)` (`:441-455`) is "`wdevStep` at the root task, verbatim, at plain nodes" (header deviation 5,
  `:102-104`). Its arms are `.pure` → body, `.step` (answer or blocked self-loop), `.get`, `.choose`, `.sample`.
- MachCSL `devStep` at thread 9/10, TaskId 0: `.pure` root → body (`Lang.lean:578-580`), `devOpStep`
  `.step/.get/.choose/.sample` (`:534-545`), and the blocked arm through `devBlocked .step` (`:563`).
- The match is **1 to 1 on one thread**. `uartBodyPlain` (`WeakEvInst.lean:1150`) means the UART never reaches a
  `dma*`/`fork`/`join`/`setPin` node.
- `R-fab`: `Efab.efU i` = the thread's `m`, and `efDev = σ.devs`.

**C2. PLIC.** **FAITHFUL**.
- Gateway (`pdiskUart` PLIC arm, `:523-524`): thread 11, 1 step, same argument as C1.
- Wire (`pstepPlic` at hart agent `cpu`, `:464-472`): pf requires `efPlic = .op (.setPin cpu mm b) k` and sets
  `ors = pinSet rs mm b` (`:458-460`). That is MachCSL's `devOpStep .setPin` (`setReg sig_meip/seip`,
  `Lang.lean:546-549`). The match is 1 to 1, but the pf AGENT (hart `cpu`) is not the MachCSL THREAD (plic); see A2.
- `plicBodyPlain` (`WeakEvInst.lean:1162`): the PLIC's only non-plain node is the wire write.
- D49 (a) puts the pin delivery in the hart's row in pf; MachCSL runs it on the PLIC thread. This does not matter
  for pf→MachCSL.

**C3. The one-row coupling (D51 (a), plan :1444-1449).** *Spec:* silent on cross-device order. The one-row model is
**STRONGER** (D51), but harmless for W4.
- pf orders every disk-row step (START/DMA/COMMIT and the UART/PLIC moves) in ONE po. MachCSL runs them on four or
  more independent threads.
- Each one-row step maps to ONE step of a determined thread. **No one-row UART/PLIC step needs a multi-thread
  match.** The coupling only removes interleavings, which MachCSL admits anyway.

**C4. The disk rows: STRUCTURAL MISMATCH (main finding).**
- The pf disk program is `virtioProg` (`Weak/VirtioProg.lean:606-625`). It is the Rocq `VirtioModel` ported
  "Rocq-literal" and recorded as **DRIFT** from MachCSL's device (VirtioProg header deviation 2, `:99-112`;
  `notes/weak-port-architecture.md:40`: "record as a later cleanup").
- MachCSL's virtio is `Virtio.body`/`serve` (`MachCSL/Dev/Virtio.lean:521-587`): forked tasks, a write-back cache
  and a fused completion.

Arm by arm:

| pf arm | pf events | MachCSL steps | match |
|---|---|---|---|
| START (`pdiskProg`, `WeakEvInst.lean:487-488`, `LDev .dev`; snapshot `v := dvirtio d`) | 1 | root: `choose` (`chooseLt`, `DevLang.lean:134-136`) with k=0, then `get` (`Virtio.lean:559-561`) | **1→2** |
| `DRead` avail idx, `aq` (`VirtioProg.lean:375-376`) | 1 | `dma16` = `dmaRead 2` (`Virtio.lean:460-462,563`); `dmaView` at the top (`Lang.lean:189-191,539`) | 1→1 under `candDiskLat` (memory) |
| `DIdle`, or not `live` (`WeakEvInst.lean:513-514`) | 1 | root `.pure` restart (`Lang.lean:578-580`) | 1→1 |
| `DRead` ring | 1 | `dmaRead 2` (`Virtio.lean:565`), `get`, guard-pop (`seen+1`, phase `popped`, `:576-578`), `fork` (`:579`; new thread appended, `devrt.next+1`, `Lang.lean:550-553`) | **1→4 + a NEW THREAD**. MachCSL's `seen` moves NOW, pf's at COMMIT (`vdelta`, `VirtioProg.lean:565-569`), so `R-dev` cannot be equality on `VirtioState` during a burst |
| descriptor: 4 `DRead`s (8,4,2,2; `dreadDesc`, `:381-386`), ×3 | 12 | `serve`'s `get` (`Virtio.lean:522`), then `fetch`'s three `dmaRead 16` (`:469-473`) | **4→1** per descriptor. One MachCSL read at one instant must return four pf reads made at four instants. They are torn if a foreign write lands in between, which is pf-legal even under `candDiskLat` |
| header `ty`(4), `sec`(8) | 2 | `dmaRead 4`, `dmaRead 8` (`:475-476`) | 1→1 |
| malformed chain → `DWild` + `DmWildChain` writes ANYWHERE (`VirtioProg.lean:611-619`; `WeakEvLang.lean:914-917`) | k writes | `fetch` returns `none` → `stall` (`Virtio.lean:457,524`) | **NO MATCH** for the writes. *Spec:* unspecified, the driver MUST NOT publish such chains. `DWild` is WEAKER, `stall` STRONGER |
| IN data: `DWrite r.buf (diskRead v.disk …)` (`:597-598`); none if `len = 0` (`dwriteData`, `:363-367`) | 1 | `modify` (fetched, `Virtio.lean:526`), `fill` = `get` + `dmaWriteIf (cacheView v)` (`:488-492`), `modify` (served, `:534`) | **1→3**. VALUE: pf reads the DURABLE image of the START snapshot; MachCSL reads `cacheView` (`:359-363`) at fill time. Equal only under an `R-dev` invariant "pf `disk` = MachCSL `cacheView`" (pf commits writes at COMMIT; MachCSL caches and drains later, `:429-433,582-586`). `len = 0`: MachCSL's 0-byte `dmaWrite` still APPENDS a log entry (`ramBytes pa 0` is vacuous; `storeDma`, `Lang.lean:172-174`) while pf emits none, which breaks log positions |
| OUT data: `DRead r.buf` (`dreadData`, `VirtioProg.lean:358-361,601`) | 1 | `modify` (fetched), guard on the `taken` latch (`Virtio.lean:529`), `capture` = `dmaRead` + `modify` (`:515-518`) | **1→4** |
| status: `DWrite [vstatus r]` (`dtail :591-593`; `vstatus :557-561`) | 1 | `dmaWriteIf status 1 (statusOf r)` (`Virtio.lean:536`), `modify` (`:537`) | **1→2**. VALUE differs for FLUSH: pf answers UNSUPP, MachCSL OK (`:377-379`). *Spec:* FLUSH is OK iff `F_FLUSH` is negotiated (`deviceFeatures` has bit 9, `:99-100`). MachCSL FAITHFUL, pf STRONGER (wrong status) |
| used element: **TWO** `DWrite`s, `id`(4) then `len`(4) = `r.len` (`dusedTail`, `VirtioProg.lean:586-589`) | 2 | guard `pushed` (`Virtio.lean:539-541`), `get` (`:542`), ONE 8-byte `dmaWriteIf` (`usedLen r ++ head`, `:546-548`) | **2→1 LOG MESSAGES**, which breaks the position-preserving log identification (plan §B(10): pf message k = TsoMem store k+1). VALUE: pf `len = r.len`; MachCSL `usedLen` = `len+1` if device-writable, else 1 (`:382`). For xv6's 1024-byte block: IN writes 1025 vs 1024, OUT 1 vs 1024. *Spec:* virtio "len = bytes written" makes MachCSL **FAITHFUL** and pf **UNFAITHFUL** (wrong value) |
| `DFence` (`VirtioProg.lean:589`) | 1 | none (`DevOp` has no fence op, `weak-port-architecture.md:40`) | 1→0 |
| used idx `DWrite` (`:589`) | 1 | `dmaWriteStep … complete` (`Virtio.lean:552-555`): `isr` raised, `usedIdx+1` and in-flight removal in the SAME transition | 1→1 for memory, but pf moves the fabric only at COMMIT (next row) |
| COMMIT (`WeakEvInst.lean:504-507`, `LDev .dev`, `vdelta`) | 1 | task-end `.pure` (`setRt done`, `Lang.lean:581-584`) | 1→1. In the window between the idx write and COMMIT, MachCSL's `isr` is raised and pf's is not. A hart MMIO read of `InterruptStatus` (`Virtio.read`, `Virtio.lean:268`) or a PLIC `sample` of source 1 (`devLevel`, `Fabric.lean:166`; `Virtio.irq = isr ≠ 0`, `Virtio.lean:245`) inside the window DIVERGES. `R-dev` equality is impossible, and the PLIC sample is a step the pf one-row run can itself take |
| write-through drain | 0 | `completeOk` needs `!reqCached` unless `wce` (`Virtio.lean:412-416`) → root drain steps (`:582-586`) | 0→k |

**Summary of §C.**
- UART, PLIC and hart MMIO match 1 to 1, one thread each.
- The disk is multi-step everywhere (1→2..4) and adds a new thread per burst (TaskIds 1, 2, … in pool order 13+).
- **Four UNCONDITIONAL mismatches** that no structural relation can absorb:
  - (M1) the used element is 2 log messages in pf vs 1 in MachCSL;
  - (M2) the used-element `len` value;
  - (M3) `DWild` writes vs a stall;
  - (M4) the COMMIT-vs-idx-write window on `isr`.
- **Five CONDITIONAL mismatches:**
  - (M5) the 0-length DMA log entry;
  - (M6) the torn 4-part descriptor read;
  - (M7) the FLUSH status;
  - (M8) the durable image vs `cacheView`;
  - (M9) pf's START-snapshot `cfg` vs MachCSL's per-step `cfg` reads.

See E-D1. The `LDev` payload is pattern-wildcard throughout: START/COMMIT/UART/PLIC carry `.dev 0 []` and MMIO
carries `.rd/.wr (paZ pa) bytes` (`WeakEvInst.lean:305,341,470,488,506,520`). W13 (I)/[OWN.27] will change
`projLbl`, which W4 never reads.

## (D) The initial-config bridge

**D1. pf side.**
- `srvwmoXv6M1PfRun` (`Weak/SrvwmoXv6Witness.lean:596-610`) gives
  `pfRunS … (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) st cf`.
- It does so under `srvwmoXv6M1Premises` (`:583-592`), which includes `wbootFacts σ0`, `σ0.wggen = 0`, and
  `σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk`.
- `wbootFacts` (`WeakLang.lean:482-490`) gives: `pow`, `wgimg = bootImage`, an empty log, `wsInit` everywhere,
  `itv = 0`, registers that are boot-run outputs, `wgdev = ds'.reset` and `wgrt` init.
- So plan :882's `wpInit (imgZ bootImage) (efInit ds.reset) (epsInit σ0)` is this configuration, by
  `wbootFacts.2.1` and the premise's `ds`.
- The premise set still says `candSca` (`:591`), not `candScaT`. W4 needs the shadow-carrying run (`pfRunST`); W5
  re-points the premise (plan :891, S).

**D2. MachCSL side.**
- Take `g0 := { m := ⟨σ0.wgregs, imgFlat bootImage, [], 0, 0, HRead.zero, none, ds, DevRt.init⟩, gen := 0,
  pow := false }`. Any `m` works, since `riscvPowerAdequacy` has no premise on initial memory (`Adequacy.lean:262-265`).
  `g0` satisfies `Hgen0`, `Hpow` and `Hdisk`.
- Take `g1` := the same with `devs := ds.reset` and `pow := true`.
- `bootShape g0 g1` (`Lang.lean:307-308`) holds. `bootFacts g1.m` (`:298-303`) needs: memory = `imgFlat bootImage`,
  an empty log, zero `tv/itv/hr/resv`, registers with `∃ f₀, bootRun … f₀ = some ((), regs c)`, and `devrt` init.
  The register clause is `wbootFacts`' clause verbatim (`WeakLang.lean:487` vs `Lang.lean:301`). Also
  `g1.m.devs = g0.m.devs.reset`.
- The step is `primStep_power_on` (`Lang.lean:686-688`), giving the pool of A1.
- *Spec:* `bootFacts`/`bootShape` encode Sail reset, the boot program `bootProg` and the ELF image load, which both
  trees share. **FAITHFUL**; single boot per A4.

**D3. The relation at the bridge.**
- `R-regs`: `epsInit` uses `σ0.wgregs` (`WeakEvCapstone.lean:1026-1027`).
- `R-expr`: `FreeM.pure ()` = `Loop`'s `pure ()`.
- `R-fab`: `efInit`'s residual programs are `.pure ()`, matching `DevLoop`, and `devs = ds.reset`.
- Disk: `PDisk none` ↔ `DevLoop virtio` with no task.
- `R_mem` at boot: `imgFlat_get?` (`TsoMem.lean:201-205`) is
  `if inRam a 1 then image[a]?.map (fun v => [⟨0,0,v⟩]) else none`, an **`Option Hist`**. `TsoOfPf.histOf`
  (`Weak/TsoOfPf.lean:62-66`) is a **`Hist`** that is `[]` when the image has no byte. So W2's `R-hist`, written
  `σ.mem[pa]? = histOf …` (`notes/W2-spike.md`, §R), does not type-check as written. It must read
  `(σ.mem[pa]?).getD [] = histOf …` for RAM `pa` (E-M7).
- `wgib` is left free by `wbootFacts` and has no MachCSL image. Harmless.

*Spec:* initial memory is the loaded image at timestamp 0. **FAITHFUL**.

**D4.** The PowerOn step is the one MachCSL step with no pf counterpart. `κs` starts with `.powerOn`.

## (E) Requirements (OPEN ITEMS only, not plan amendments)

This section states no exact Lean over `HRead.afterLoad`, `MState.store`, `tsoShadow`/`ShSt`/`pfRunST` or the `LDev`
payload.

- **E-M1 (W2, granularity).** `pfStepTso` should be stated per hart EVENT, with the `Outcome` node `o` the hart's `m`
  sits at, plus the label emitted there (base `paZ req.pa`, `|tvs| = n`, data `wbytes n v`). It must give
  `evStep cpu o σ v σ'` (`Lang.lean:355`) for THE answer `v` the pf continuation consumed (`.Ok (w, none)` with
  `nthByte w j = tvs[j].2`), not just "some TsoMem step with the same bytes". (A `hartStep` statement with `m` fixed
  would also do.) *Spec:* Sail outcome semantics; FAITHFUL.
- **E-M2 (W2, frame).** `R_mem` should mention only `MState`'s memory fields (`mem log tv itv hr resv`) and be
  invariant under `setReg`/`setDev`/`setRt`. It should not constrain the pf `Wstate`'s dependency fields
  (`instrPost`/`regwPost`/`ctrlPost`) beyond what the shadow reads. Otherwise the structural half cannot move
  registers, devices and forks independently.
- **E-M3 (W2).** `R_mem` must be preserved with `σ` unchanged across the 0-step rows: the retry `LSilent`, the parked
  fence fire (already the identity on the shadow, `TsoShadow.lean:234-238`) and the disk `DFence`.
- **E-M4 (W2).** `pfStepTso` should TAKE `ramBytes req.pa n` as a hypothesis. The structural half supplies it from
  HSafe (E-S1).
- **E-M5 (W2, disk).** The disk rows are at `MState` level with no cpu: `DRead` → `dmaView` (from `candDiskLat`),
  `DWrite` → `storeDma` with `¬ anyReserve ∧ ramBytes`. A disk `DWrite`'s `ramBytes` is not available from HSafe
  (`Lang.lean:544-545`), so it needs a driver-side fact or E-D1.
- **E-M6 (W5b′).** W4 inducts on the shadow-carrying run. `R_mem`'s view part is stated against the prefix fold
  (`tsoRun`, `TsoShadow.lean:331-333`), so W4's invariant carries the prefix `st`. `pfRunS`/`pfRunST` are
  snoc-built (`Weak/PfRunShape.lean:273-277`), which fits.
- **E-M7 (W2).** The `R-hist` `Option`/`List` shape (D3).
- **E-M8 (W-COH, landed).** The hart `LLoad`/`LStore`/`LExStore` rows are now against the compiled `afterLoad`
  (`loadSrcs`, `Lang.lean:128-131`) and `store` (coh reset, `:151-156`). The instance is `TsoShadow.cohSrc`
  (`TsoShadow.lean:114`).
- **E-M9 (W-RSV, later).** The boundary row's post-state changes. `R-resv` must then say `resv = none` at every
  boundary. Only that one structural row is affected (B6).
- **E-M10 (W13 (E)/(I)).** Every arm matches `LDev` by wildcard. `R_mem` has no `LDev` content because memory is
  unchanged on both sides (`PFDev`, `Weak/WeakPromiseBridge.lean:392-397`).
- **E-S1 (W4/W5 interface).** The HSafe hypothesis (B5). W4 is parametric in it; W5 supplies it from
  `xv6FsAdequacy_closed`. §B(9d)'s `hullRun` use of W4 has HSafe too, because it holds for any MachCSL run from boot.
- **E-S2.** The thread map is per step KIND (A2).
- **E-S3.** `κs` is a function of the pf run (B7).
- **E-S6.** Drop or restate `n ≤ |st|` (B6).
- **E-D1 (owner + W2/W13/W4): the disk model.** *Spec:* virtio 1.x (above).
  - (a) **Align `virtioProg` to MachCSL's `serve`**. Changes: one 16-byte descriptor read; one 8-byte used-element
    write with `usedLen`; `statusOf` including FLUSH; no writes on a malformed chain (replace `DWild`); the completion
    (`isr`/`usedIdx`) folded into the used-idx `DWrite`'s fabric update (`pdiskProg`'s `DWrite` arm gets `d' ≠ d`) and
    `seen+1` at the ring read; data from a cache-overlaid view.
    - Mark: **more FAITHFUL** than today's pf (used `len`, FLUSH, no wild writes).
    - Touches `VirtioProg.lean` (979 lines, including the equivalence theorems `:803-952`), `pdiskProg`/`ediskStep`,
      every `DWild`/`DmWildChain` consumer, W13's disk-row anchors (R2′) and `candDiskLat`.
    - Size L–XL, unverified.
    - Within (a): (M6) disappears with a single 16-byte `DRead`. (M5) needs either "xv6 never issues `len = 0`" or a
      MachCSL skip of 0-byte DMA. (M8) needs an `R-dev` invariant "pf disk = MachCSL `cacheView`", which is fine in
      a single era.
  - (b) **Align MachCSL's device to `virtioProg`.** Re-opens the SC virtio driver proofs (XL) and is **LESS
    faithful** (wrong used `len`). Not recommended.
  - (c) **Relax `R`.** Make `R-hist` agree only up to the used-`len` bytes, with a non-position-preserving log map.
    This breaks the log identification W8/W11 consume, a **WEAKER** chain. Not recommended.
  - (d) **Premise "no disk burst".** Vacuous for the target: every run reaching user code reads the disk. Not
    acceptable.

## (F) File and lemma plan for W4's structural half

`Weak/MachOfPf.lean`, parametric in `R_mem`, `pfStepTso` and HSafe. F1–F8 do not depend on W2's proofs, only on
agreeing the parameter interface (E-M1, E-M2), so they can be built now.

| item | content | size |
|---|---|---|
| F1 | `thrOf` + `poolRel` (expressions, registers, `Efab` programs and device states; the disk part an abstract parameter until E-D1) | S, ≈150 |
| F2 | `NSteps` snoc/append helper. The iris `Language.lean` has none (grep: no `NSteps` trans lemma), and the tree has none | S, ≈40 |
| F3 | boot bridge: `g0`, `g1`, `bootShape`, the one PowerOn step, `poolRel` + `R_mem` init (through the parameter) | S–M, ≈150 |
| F4 | hart non-memory nodes: boundary, announce, silent ops, `regRead`/`regWrite`, barrier node, the 0-step parked fire and retry. About 20 `Outcome` arms, mostly `rfl`-shaped | M, ≈300 |
| F5 | hart RAM/MMIO nodes through `pfStepTso` + the HSafe bus decode | M, ≈250 |
| F6 | `fdevStep` ↔ `devStep` (5 arms + blocked), `pstepPlic` ↔ `setPin` | M, ≈200 |
| F7 | `pfObsOf` + the `κs` lemma | S, ≈100 |
| F8 | the main induction `machRunOfPfRun` over `pfRunST` | M, ≈200 |
| **subtotal** | without disk rows | **≈1.3–1.5k, M–L** |
| F9 | disk rows: BLOCKED on E-D1. After (a): `R-dev` with burst phases ↔ `serve` phases, multi-step expansions, `devrt.next`/TaskId/pool-append bookkeeping | L, ≈0.8–1.5k, unverified |

**Risks.**
- **R1 (blocking).** The disk drift (§C4, E-D1).
- **R2.** The HSafe interface. The alternative, a Sail PMA lemma, is XL.
- **R3.** If W2 states `pfStepTso` at another granularity, it must be reworked (E-M1).
- **R4.** The `n ≤ |st|` bound (E-S6).
- **R5.** `pfRunS` vs `pfRunST` and re-pointing the M1 premises (D1).
- **R6.** The W-RSV re-check (E-M9).
- **R7.** Elaboration cost of the ~30-arm `Outcome` match. Mitigate with local macros, as `WeakEvInst` does (its
  header deviation 9).
