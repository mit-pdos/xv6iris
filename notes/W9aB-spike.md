# W9a (B) spike — discharging `psitesA` (interrupts, `ret`, per-instruction dataflow)

Read-only spike, approved [OWN.68]. Plan rev 48, `notes/weak-allocproc-plan.md:2296-2315`; ruling [OWN.60].
Tree: `xv6iris-weak-w5` (tip copy). Nothing was edited, built or run through git/jj. The census numbers
come from scratch scripts that are not part of the tree:
- they read the disassembly comments in `Xv6/KernelImage.lean`;
- they import `tools/gen_weak_pins.py`'s own `pstep`/`pdfs` port and run it over the flat image, as the
  Lean checker does.

## 0. Findings first

1. **The planned trap crossing is correct but covers only half the problem.** (B2) is rule 12 through
   `kernelvec`'s spill and restore. It correctly orders the load L before the pin's store S *after* `sret`.
   **It does not cover the trap path's own writes.** Those sit in program order between L and the pin, and
   RVWMO does not order L before them. Examples: frame spills, per-cpu `noff`/`intena`, the lock
   `amoswap.w.aq`, `lk->cpu`, `p->state`, `ticks`, `swtch`'s context stores. A cycle segment whose exit is
   one of these is not `segPinC`. It is not `CSchained` either. The kill certifies each segment against its
   predecessor's exit (`CertC`/`chainC`, `Weak/CatLin.lean:210-225`), and it has no arm for this shape.
   Plan :2304 asked "does the kill accept the migration split?". **Checked: not as-is** (§1.3).
2. **`ret` is almost irrelevant.** Exactly ONE certified walk executes a `ret`: `kexec+0x1b4`
   (`0x80004b24`, `PDep … true`, `Weak/KernelPins.lean:1444`). Of the 470 walks:
   - 403 never descend into a call;
   - 67 descend, and every one of them except `kexec+0x1b4` reaches its pin inside the callee.
3. **Interrupts-off restriction is not a cheaper route.** About **246 of 470** certifying sites
   (52%) lie in code that may run with SIE = 1, mostly the syscall, FS and exec paths.
   - 57 of the 58 `own = true` witnesses are among them.
   - The trap path is the same for every site, so restricting sites saves little.
4. **The shared trap path splits cleanly in two** (§1.2):
   - every kernel interrupt path that runs a `release` passes `release+0x16`'s `fence rw,w`
     (`0x80000cf6`) before `sret`, so rule 4 orders every later write after L;
   - only three FENCE-FREE paths need the rule-12 dataflow, and none of them calls `swtch`, so there is no
     migration on them.

## 1. Question (1): a dependency through the trap's register save and restore

### 1.1 Spec first

**Sail.** `run_hart_active` dispatches a pending enabled interrupt BEFORE the fetch
(`model/Lean_RV64D/LeanRV64D/Step.lean:331-333`). `try_step` then calls `handle_interrupt`
(`:424-430`), which runs `trap_handler`
(`SysControl.lean:852`, `:733`):
- SPIE ← SIE, and SIE ← 0 (`:774-775`);
- `sepc` ← pc (`:788`);
- pc ← `stvec` (`prepare_trap_vector`).

An S-mode interrupt is taken only if `sstatus.SIE = 1` (`getPendingSet`, `:685-689`). M-destined
interrupts never happen in xv6:
- `mie ∧ ¬mideleg = 0` is pinned by `kConf` (`MachCSL/KCtx.lean:41-46`; `Weak/AxIntr.lean` §1);
- `kernelvec` is the direct-mode `stvec` throughout kernel execution.

**RVWMO and riscv.cat.** A trap is not an ordering point. No ppo rule mentions trap entry, CSR accesses or
`sret`, so option (D), "trap entry = fence", stays rejected as STRONGER than the spec. Zifencei and PMAs say
nothing about this, except (B4)'s fetch.

**The answer is YES, by rule 12, but only if two facts hold.** Rule 12 is
`[R];(addr|data);[W];rfi;[R]` ⊆ ppo, in the tree as `gppo12` (`Weak/AxGraphCat.lean:177-178`), used by
`segPinCForward` (`Weak/CatLin.lean:202`) and `pdepSegPinCForward` (PinBridge3). The two facts:
- (a) the restore reads FROM the spill (rfi). No foreign write and no own write to the slot may
  intervene. This is the stack-ownership question (2).
- (b) the chain L →data→ spill →rfi→ restore →(addr|data)→ S is in `gdDeps`/`ad`. This is a dataflow fact
  about `kernelvec`'s `sd`/`ld` and every instruction in between, which is (B1)'s machinery.

Which registers make the round trip:
- `kernelvec` spills and restores `ra, gp, t0–t2, a0–a7, t3–t6`, 16 pairs
  (`0x800057c2`–`0x800057e2` / `0x800057e8`–`0x80005808`, kernelvec frame 256 B);
- `sp`, `tp` and `s0–s11` are not spilled there. The trap path's callee-save prologues (`kerneltrap` s0–s3,
  `devintr` s0–s1, …) spill and restore them, which is the same rule-12 pattern;
- the reserve these frames use is the bundle's `trapRes true = kvFrameSlots = 90` slots
  (`MachCSL/KCtx.lean:291-299`), owned exclusively while SIE = 1 (`:17-33`).

**Two-hart example** (LB through a trap; the outcome must be forbidden):
```
A:  L:  lw a5,0(x)        // reads B's x=1
        <interrupt>  kernelvec: sd a5,112(sp)  ...  ld a5,112(sp)  ... sret
    S:  sw a5,0(y)        // the pin (PDep)
B:      lw t0,0(y) ; fence r,w ; sw one,0(x)
```
- rule 12 gives L <ppo `ld a5`;
- rule 10 gives `ld a5` <ppo S;
- B's fence gives Ry <ppo Wx;
- with rf S→Ry and Wx→L, the outcome r(L) = r(Ry) = 1 is a gmo cycle, so it is forbidden.

If a third hart's store to `112(sp)` were gmo-between the spill and the restore, (a) would fail and the
dependency would be cut. That is exactly why stack ownership is needed.

### 1.2 What the plan's (B2) misses: exits inside the trap path

Segments run from an entry read to the next exit write (`Seg`, `Weak/WeakRvwmoKillArms.lean:289`; cycles of
`racy` = pow ∪ com ∪ ppo, `WeakRvwmoAcyc.lean:210`). With an interrupt, A's writes that are po-between L and
the pin include the whole trap path. Under RVWMO, L is ordered before none of them until the first fence.

The trap paths in this image (`kernelvec 0x800057c0`, `kerneltrap 0x800027b8`, `devintr 0x8000262a`):

| path | first ordering point | exits before it |
|---|---|---|
| timer, hart ≠ 0, `myproc() ≠ 0` → `yield` | `release(p->lock)` in `scheduler` after `swtch` | spills, `push_off`/`pop_off` cpu cells, `amoswap.w.aq` p->lock, `lk->cpu` (`acquire+0x28`), `p->state` (`yield+0x16`), `swtch` context, `c->proc` |
| timer, hart 0 (`clockintr`) | `release(&tickslock)` (`clockintr+0x50`) | the same, plus tickslock AMO and `ticks` (`clockintr+0x40`) |
| external: virtio (`virtio_disk_intr`) | its `release` (`+0x92`) | spills, AMO, payload |
| **fence-free** (a) spurious PLIC claim (irq = 0, `devintr+0x48`) | none | spills, the MMIO claim load |
| **fence-free** (b) UART interrupt with nothing to do (`uartintr`, LSR checks, no lock) | none | spills, MMIO loads, `plic_complete` MMIO store |
| **fence-free** (c) timer on hart ≠ 0 in `scheduler`'s window (`+0x96`/`+0x9a`, `myproc() = 0`) | none | spills, `myproc`'s `push_off`/`pop_off` cpu cells |

Notes on the table:
- In this image `acquire` is `amoswap.w.aq` with NO trailing `fence rw,rw` (`acquire+0x1c`), so the first
  fence on a path is a release's `fence rw,w`.
- After that fence, every later write on the hart is ordered after L by rule 4 (`gfenceCovers`,
  `WeakRvwmoGraph.lean:235`). That covers everything that is fenced and resumes on the same hart, with no
  dataflow argument.
- Kernel exceptions panic in `kerneltrap` (`+0x4c/+0x58/+0x64` → `unreachable`), so interrupts are the only
  trap case.

### 1.3 The migration split

Under `yield`, A's spill is read by B's restore (cross-hart). The plan has W11's `chainHyps` certify B's
segment: spill <ppo A's release fence, then →rf B's acquire.aq, then <ppo B's exit. That part is correct.
**A's segment (L, spill) has no certificate:**
- it is not pinned (L ↛ spill);
- it is not `CSchained`, because `gmoLt prev spill` fails.

So the split is NOT accepted by today's `chainC`. **The same gap exists today for the 58 `own = true`
witnesses**: their own-stack exits, when read after a migration.

The fix is a CYCLE RE-ROUTE lemma:
- Setup: an exit E whose cross edge reaches a read R. R is chained (`chainOkAt`) from E through a release
  REL ≥po E and an acquire ACQ ≤po R.
- Effect: replace E→R by REL→rf→ACQ. A's segment becomes (L, REL), pinned by REL's own fence. ACQ's
  segment is pinned by aq.
- Status: FAITHFUL (rules 4 and 5 and the lock chains only). It is W11-side.

How the other exit classes are handled:
- **per-cpu cells**: no foreign reader (cpu-cell custody, `cpuStaticAt`);
- **lock word / `lk->cpu`**: the lock-layer arm (`lockWordDiscAt`, [OWN.64]);
- **MMIO stores**: already gmo-after a po-earlier memory event by the residue's (R1)/(R3)
  (`ioSegPinned`'s proof, `WeakRvwmoKillIO.lean:609`).

## 2. Question (2): does the proof need a stack-ownership fact?

**Yes**, for 1.1(a) on the FENCE-FREE trap windows: the restore reads the spill. **Not for `ret`** if
`kexec+0x1b4` is demoted (§0.2), and **not for migration** under the re-route (§1.3).
- **No current W8 part supplies it.** `chainOkAt` says a foreign entry is CHAINED, not ABSENT. The other
  parts (`lockWordDiscAt`, `pteDiscAt`, `cpuStaticAt`, `cpuProcDiscAt`, `utextDiscAt`) are about other bytes.
- **(s1) (f3-stack)** (plan :2290-2294) would supply it. It is more than needed and has the known feed risk:
  `KCtx` has no stack↔proc link (`MachCSL/KCtx.lean:256`).
- **Minimal new part (s1′) "(f3-trapres)"**:
  - Statement: during a fence-free trap window on hart h, from trap entry to `sret` with no `swtch` on the
    path, every entry on the window's frame bytes (the `trapRes` reserve below the interrupted `sp`) is
    authored by h.
  - Why it is cheap: it is hart custody (`.hart h`, `Cust` in `Xv6/AccessDiscipline.lean:132`), so no
    proc link is needed. The reserve is already exclusive in the bundle while SIE = 1
    (`MachCSL/KCtx.lean:29-33,294-299`).
  - Size: S–M ≈ 0.5–1k, **unverified**.
  - FAITHFUL (a proved fact of xv6, not a model change).
- **(s2) realization**: the slot's rf is the realizing TsoMem run's, where `stackOwn` is exclusive. No
  export is needed, but the window must lie inside W11's realized hull, which is **unverified**. FAITHFUL.

## 3. Question (3): is there a cheaper route?

**Census** (scratch abstract interpretation over the image):
- Lock depth: `acquire`/`push_off`/`allocproc` add one, `release`/`pop_off` subtract one.
- SIE: `csrrci`/`csrci sstatus` clear it; `csrsi`/`csrw sstatus` make it unknown.
- Entries: boot, `kernelvec`, `usertrap` and `forkret` (depth 1) start with SIE = 0. Indirect and syscall
  targets start possibly on.
- Joins are path-insensitive (min depth, SIE "maybe" wins).
- No certified walk touches `sstatus` or passes a lock op. Lock ops store to cpu cells, which `pstep`
  rejects. So a site's stretch is off exactly when its load pc is off.

| class | provably SIE = 0 | possibly SIE = 1 |
|---|---|---|
| PCtrl (289) | 129 | 160 |
| PDep (180) | 94 | 86 |
| PFence (1, `main+0x16`) | 1 | 0 |
| **total 470** | **224** | **246** |

- The possibly-on sites are concentrated in `kexec` 25, `namex` 12, `pipealloc` 11, `fileread` 10,
  `filewrite` 10, `ilock` 9 (including the ip->ref guard `ilock+0xe`) and the sys_* functions, plus the
  software PTE reads in `walk`, `walkaddr`, `mappages`, `uvmunmap`, `freewalk` and `copyout`.
- `allocproc`'s 4 sites are all off.
- This is an estimate. Path-insensitivity can only move sites from off to on.

**Route (C), certify only interrupts-off stretches.** FAITHFUL, but it is not cheaper:
- it moves about 246 sites to W8/W9b's residue;
- it still needs a NEW per-pc export, "at OffPcs, SIE = 0". `KCtx` indexes `k.sie` (`:17-27,52-56`), but
  per-pc facts are not in the state interpretation;
- (B1) and the trap problem stay anyway, because the excluded sites' cycles still need killing.

**Route "trap path inside the certified walk".** FAITHFUL, but the checker rejects it:
- the path is `kernelvec → kerneltrap → devintr → clockintr/yield → acquire → push_off`, which is depth ≥ 4
  against `pinDepth = 2` (`KernelPinsDef.lean:355`);
- it hits unfed cpu-cell stores (`push_off+0x20`, `+0x36`), and `pstep` returns `none`.

So this would need hand-certified trap summaries in the checker, which is generator work that §B(9)
excludes. It also cannot fix §1.2, because those exits really are unordered.

**Cheaper route found: (B′) = (B) re-scoped.** It needs no new export beyond (s1′) or (s2):
1. **fenced paths**: post-fence writes use rule 4 (existing arm);
2. **fence-free paths**: the rule-12 crossing;
3. **pre-fence exits**: the W11 re-route plus the existing lock-layer, cpu and I/O arms;
4. **`ret`**: demote the one walk.

## 4. Question (4): per-instruction dataflow — which `execute` clauses, and can W-SCO be reused?

**The opcode list.** I took the exact pdfs-visited state sets of all 470 walks, plus each pin instruction.
That is 1,631 states, and 387 of the walks have fewer than 5 states.
- **15 base clauses**: RTYPE (`add/and/mv/srl/sub/snez`), ITYPE (`addi/li/andi/xori/seqz/zext.b`), ADDIW
  (`addiw/sext.w`), RTYPEW (`addw/subw`), SHIFTIOP (`slli/srli`), SHIFTIWOP (`slliw/srliw`), UTYPE
  (`lui/auipc`), BTYPE (12 forms), JAL, JALR (`ret`, 1 state), LOAD (`lbu/ld/lh/lhu/lw`), STORE
  (`sb/sd/sh/sw`), REM (`remu`), CSRReg (`csrr`, 2 states), FENCE (the pin).
- **≈ 22–25 compressed wrappers**: C_ADD/ADDI/ADDIW/ADDW/AND/ANDI/BEQZ/BNEZ/J/LD/LDSP/LI/LUI/LW/LWSP/MV/JR/
  SD/SDSP/SLLI/SRLI/SUBW/SW/SWSP.
  - Each one is a pure `ExecuteAs base` (e.g. `InstsEnd.lean:18396-18409`), re-executed once
    (`Step.lean:371,405`), so its lemma is the base lemma plus the operand mapping.
- The fence-free trap paths add CSRReg/CSRImm writes, SRET, AMO (none on fence-free paths) and an indirect
  JALR (`uartintr+0x5a`). That is about 4 more clauses.
- The image has 122 `execute_*` clauses (`InstsEnd.lean`), about 25 base classes in use.

**What each clause owes** (`grpOkb`, PinBridge2 `:277`; `regwSeg` `:233`; DEC-7 `erwSrcs`,
`WeakEvLang.lean:354,402`):
- every decoded `DReg` source is read before the single `LRegW rd`;
- at most one write per destination, in `taintStep`'s order;
- no stray `LRegW` (writes to x0 and CSR writes are not GPR `LRegW`);
- for the trap step, check that `handle_interrupt`'s `nextPC`/CSR writes are provenance-neutral at the
  boundary role (the ibch reset).

**W-SCO reuse.** Partial. `fpB` (`Weak/SailCycleOrderFp.lean:62-84`) is a STATELESS additive footprint.
Dataflow needs a state-indexed one: `dfB rds wrote P m`, whose bind law threads the read set. What carries
over:
- the walker's dispatch skeleton: binds, if/match, `SailME.run`, try-catch, loops, register nodes
  (`fpBInd` `:93`, ≈ 1.15k lines);
- the registration pattern (`@[fp_reg]` one-liners, `SailCycleOrderAllExec{1..4}.lean` ≈ 4 × 195 lines for
  121 clauses).

Estimated cost: ≈ 0.6–0.9k for the stateful walker, ≈ 0.25–0.45k for the about 40 clause lemmas, and
≈ 0.2–0.4k for the emission↔clause glue (`grpOkb`). **B1 ≈ 1.0–1.8k**, below the plan's 1.5–2.5k.

## 5. Question (5): sized plan, rev 48 B1–B5 re-scoped (all sizes unverified)

| part | content | lines | files | deps | spec |
|---|---|---|---|---|---|
| **B1** | stateful dataflow walker + ≈ 15 base / ≈ 22–25 C / ≈ 4 trap-path clauses; `grpOkb` from the clause lemma | 1.0–1.8k | NEW `Weak/PinDataflow{,Exec1,Exec2,Glue}.lean` | W-SCO ✓ | FAITHFUL |
| **B2-census** | decidable static facts over the image: every `kernelvec` path either passes `release+0x16` (`fence rw,w`) before `sret`, or is fence-free (a)/(b)/(c) with no `swtch`; the pre-fence exit table by class | 0.3–0.5k (+ an untrusted generator report, no `KernelPins` change) | NEW `Weak/PinTrapSites.lean` | none | FAITHFUL |
| **B2-fenced** | post-fence exits fence-pinned (rule 4); resumption on the same hart | 0.1–0.2k | `Weak/PinTrap.lean` | census | FAITHFUL |
| **B2-free** | rule-12 crossing on the three fence-free paths (16 `kernelvec` pairs + callee-save pairs); new alignment `reachesT` = `reachesA` + a trap-excursion constructor; `psitesT ⊇ psitesA` | 0.6–1.0k | `Weak/PinTrap.lean` | B1, census, (s1′) or (s2) | FAITHFUL |
| **B2-exit** (NEW, W11 lane) | cycle re-route at chained exits (also closes the 58 `own` witnesses' A-side gap); cpu-cell, lock-layer and I/O exit arms wired | 0.8–1.5k | `Weak/CatLin.lean` (re-route next to `chainC`) or a new `Weak/CatReroute.lean`; W11 files | W8 `chainOkAt` ✓, `lockWordDiscAt` ✓, W11 `chainHyps` | FAITHFUL |
| **B3** | (s3, NEW, recommended) demote `kexec+0x1b4` from the claim (W9b classifies it) → no `ret` obligation. Alternative (s1)/(s2) as in the plan for that one site | ≈ 0.1k (s3) / 0.3–0.6k + (f3-stack) | `Weak/WeakRvwmoPinBridge4.lean` | W9b | FAITHFUL (s3 shrinks the pin set, not the theorem) |
| **stack fact** | (s1′) (f3-trapres) hart custody of the trap reserve, **or** (s2) realization | 0.5–1k (s1′) / 0 (s2) | MachCSL/Xv6 (serial lane) | (f3-cpuproc) | FAITHFUL |
| **B4** | announced word = `kword pc` (as in the plan) | 0.2–0.4k | PinBridge4 | W5d-G G6 | FAITHFUL |
| **B5** | assembly; `psitesA`/`psitesT` absent from W11 (v)'s statements; non-vacuity: one `rcStep` and one trap excursion on real bytes | 0.3–0.5k | PinBridge4 | all | FAITHFUL |

**Totals:**
- graph ≈ 2.6–4.5k plus W11 re-route ≈ 0.8–1.5k;
- stack fact ≈ 0.5–1k (s1′), or 0 under (s2).

Against plan rev 48 (3–5.5k plus (f3-stack) 1.5–3k), this is about the same graph total, but (f3-stack)
is replaced by a smaller hart-local part.

**Order:**
1. B1 ∥ B2-census, both now (graph lane);
2. B2-fenced;
3. B2-free (after the stack decision);
4. B2-exit in W11, after (K-cat′);
5. B3 (s3) with W9b's table;
6. B4 after G6;
7. B5.

**Weaker or stronger options considered and NOT recommended:**
- **(A)** keep `psitesA` as a premise. It is STRONGER than Sail and stays the interim [R42.4].
- **(D)** trap = fence. STRONGER than RVWMO; rejected.
- **"No interrupts in kernel stretches" as a premise.** STRONGER than Sail.

## 6. Open questions for the reviser and owner

- **Q-W9aB-1: the stack fact for B2-free.** Choose (s1′) the NEW hart-local W8 part "(f3-trapres)" (S–M,
  serial MachCSL lane), or (s2) the realization route (no export; hull containment unverified)?
  Recommendation: (s1′). It is a proved fact with a known feed, the `trapRes` bundle cells.
- **Q-W9aB-2: the re-route lemma is new kill machinery** in the W11 lane, not W9a's. It also fixes the
  existing gap for the 58 `own = true` witnesses (A's segment ending at an own-stack exit). Should it be
  folded into W11's `chainHyps` item (re-size W11), or split out as its own item before W9a (B5)?
- **Q-W9aB-3: demoting `kexec+0x1b4` (s3).** It is the only `ret` walk. Accept the demotion, which drops
  the frame-`ret` obligation entirely?
- **Not settled here:**
  - whether the unchained certifying classes in interrupts-on code survive the re-route without a pin.
    These are the software PTE reads (`pteDiscAt`) and the ip->ref guard (`ilock+0xe`, `iunlock+0x1c`,
    [OWN.63]). Their trap exits are re-routed only if the reader side is chained, so W9b should tag them;
  - the 246/224 split is a path-insensitive estimate.
