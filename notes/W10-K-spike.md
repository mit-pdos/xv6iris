# W10-K spike — route K (TSO member with SKIPS + a multi-tick clock boundary), R44 §0.4–0.5

Worker w2, 2026-10-18. Read-only spike: no Lean edits, no builds; every claim below cites file:line in
`../xv6iris-weak-w2` (same tree as the R44 read) unless marked. It includes the coordinator's mid-spike
note: w3's `Weak/LitmusSBAcq.lean` (change `vxrpmmnl`) and the extra option "δ1′ + unsynchronized-read
handling" (§6).

## 0. Verdict in one paragraph

K is **feasible, with no hard blocker found**, but it is **larger than R44's 3.3–6.2k** and has **two
risks R44 did not see**:
- (a) the skipped `holding` long arm writes stack frames that a later UNINITIALIZED stack read (for
  example the 4-byte hole of `struct stat` that `filestat` copies to user space) can observe in `GF`
  but not in the member;
- (b) `minstret` drifts permanently, which the multi-tick clock does not fix.

Both have a route: (a) an uninitialized-read census plus a static overwrite check; (b) a counter
catch-up at the boundary or a relation taken modulo `minstret`. Neither is free. The failed-`amoswap`
skips and the `started` skips are clean (no stores in the window). The `holding` long-arm skip is where
the risk lives (R-K2).

My size for K is **5.3–10.4k lines (MachCSL + pf twin 0.7–1.6k, Weak 4.6–8.8k), 51–104 worker-hours,
confidence M−** (L+ on the `holding` window). P is still XL (11–20k) and has none of the skip risks.
δ1′ + unsynchronized-read handling (§6) is **not sufficient on its own**: a 3-hart residue through the
UART fabric remains. Covering that residue needs K's hardest piece anyway, plus a revived twin
realization. So δ1′ is a fallback, not a replacement.

## 1. Spec first (RVWMO / Sail / platform)

- **Clock.** In the privileged spec, `mtime` is a platform real-time counter that advances at a
  constant frequency, independent of instruction retirement. `mcycle` counts clock cycles, and one
  instruction may take many cycles. So "k ≥ 0 ticks at one instruction boundary" is a behaviour real
  hardware has: **FAITHFUL to the platform**.
  - Sail's `loop` ticks once every `plat_insns_per_tick` instructions (a simulator artifact).
  - MachCSL already weakens this to "at most one nondeterministic tick per boundary"
    (`MachCSL/Lang.lean:305-312`, `:694`).
  - MachCSL already keeps `mtime` per hart (a hart register, `MachCSL/UTick.lean:6-15`,
    `MachCSL/Boot.lean:21-31`), where the platform has one shared CLINT counter. That deviation exists
    today; K does not add to it.
- **`minstret`.** It counts retired instructions. Sail increments it at every retired step
  (`model/Lean_RV64D/LeanRV64D/Step.lean:418,476-480`), gated by `mcountinhibit.IR` and `minstretcfg`
  (`Platform.lean:544-547`). `HwConfig` pins those counter controls to arbitrary values
  (`MachCSL/HwConfig.lean:102,154`), so counting may be on. A spontaneous `minstret` increase is **not**
  a Sail or privileged-spec behaviour: a catch-up of `minstret` is a **WEAKER machine** (more
  behaviours). It is still **FAITHFUL for the GF quantifier**: the weak language, and hence `GF`, is
  unchanged, and the xv6 MachCSL proofs own `minstret` existentially (`clockCells`,
  `MachCSL/Boot.lean:25-31`).
- **Interrupts in the skipped windows.**
  - `acquire` disables interrupts (`push_off`) before `holding` and the spin; the boot `started` spin
    runs with `sstatus.SIE = 0`.
  - M-level interrupts are taken in S-mode regardless of SIE. I found no `MTIE` in `Xv6/`, and the
    image uses Sstc (`stimecmp`, `Xv6/ProofClockintr.lean`). So no trap can occur inside a window, as
    far as I checked. This needs confirming as a per-pc fact of the datum; the existing lag datum
    already needs it.

## 2. Risks R-K1 … R-K4

### R-K1 (clock): needs X — the MachCSL / pf-twin boundary arm, plus a decision on `minstret`

**Why the drift blocked CertZ34.**
- After a skip, the emission (GF's per-hart Sail run) has ticked at boundaries the member never had.
- `relT` compares every non-carrier register EXACTLY (`dregAgree`, `Weak/WeakEvProv.lean:120-121`).
- The carriers are only the CSRs listed in `Weak/WeakEvLang.lean:304-327`: `mtime` and `mip` are
  carriers; `minstret` and `mcycle` are NOT.
- A taint cannot absorb `mtime`/`mip`: every cycle reads `mip` (interrupt dispatch) and `mtime`
  (`tick_clock`).
- `CertZ34.siteStepLag`'s own header says its lag clause is FALSE for exactly this reason
  (`Weak/CertZ34.lean:37-41`).

**What multi-tick fixes.** The member ticks k times at the re-convergence boundary, and `tick_clock`
moves only `mcycle`/`mtime`/`mip` (`MachCSL/UTick.lean:131-154`):
- `mtime` is equalised;
- `mcycle` is equalised: it moves only in `tick_clock` (`Platform.lean:549-554`) and the privilege is
  the same;
- `mip`'s MTIP/STIP bits are recomputed from the final `mtime` by `clint_dispatch`
  (`UTick.lean:86-110`), so they agree once `mtime` agrees.

**What it does NOT fix: `minstret`.** R44 says "`minstret` already has 'no lasting drift' (w3 :803)".
That is wrong: `PROGRESS-W10N2p.md:801-802` says `minstret` drifts permanently; line 803 is about
`minstret_increment`. Two ways out:
- **(i) A catch-up arm that may also advance `minstret`** — WEAKER machine, FAITHFUL header, cheap.
- **(ii) A "modulo `minstret`" relation in Weak.** `relT`'s lockstep arm is `pE = pC`
  (`Weak/CertZ13.lean:41-46`), so after the first skip a hart would never be in lockstep again. Every
  lockstep lemma (`CertZ9.lockstepStep`, `CertZ11.realizeT`, `CertZ12.pairT`, `CertZ13.hartStepOfSite`)
  would need a counters-modulo version, plus a mirror lemma "Sail reads `minstret` only to increment
  it": M–L, 1–2k.
- Recommend (i). It needs an owner ruling (Q-K-INSTRET, §8).

**The MachCSL change (row 1′).** Statement sketch, the least churn I found:
```lean
-- Lang.lean:694, hartStep's boundary arm
| .pure _ => (∃ tick : Bool, m' = riscvStep tick ∧ σ' = σ.dropResv cpu) ∨
             (m' = clockCatchUp ∧ σ' = σ.dropResv cpu)
-- clockCatchUp : SailM Unit := tick_clock ()        -- (+ under Q-K-INSTRET (i):
--                         or `writeReg minstret (minstret + 1)`, chosen nondeterministically)
```
The catch-up is a self-loop: it returns to `.pure`, so k catch-ups are k steps.
- Keep `riscvStep` and its `tick : Bool` type unchanged. Changing its type or body would touch 11
  MachCSL and 37 Weak files that walk its tail (`grep tick_clock`).
- **Only one MachCSL lemma inverts the boundary arm:** `wpLoop_restartB` (`MachCSL/Wp.lean:2731-2756`,
  the `obtain ⟨tick, rfl, rfl⟩` at :2749). It needs:
  - a Löb induction for the self-loop;
  - the clock cells LENT to the boundary: the catch-up writes `mtime`/`mcycle`/`mip`/`minstret`, which
    the continuation owns today (e.g. `WpCycle.lean:110-117`: `clockCells` is destructured before
    `wpLoop_restart`).
- So the four `wpLoop_restart*` lemmas (`Wp.lean:2731-2846`) gain a `clockCells cpu` argument that is
  given back. Their 12 call sites in 7 files lend it (`UCycleSwp` 1, `WpCycle` 3, `WpSmodeCycleB32` 1,
  `WpSmodeCycleBase` 2, `WpSmodeCycleRvc` 1, `WpSmodeCycleT` 2, `WpSmodeWait` 2).
- The tick's WP is reused: `swp_tick_clock_hs` (`MachCSL/WpTick.lean:191`, `WpSmodeWait.lean:37-45`).
- No Xv6 file mentions `riscvStep` or `hartStep` (0 hits).
- Vtest: `hartExec`'s soundness `vtest-lean/Vtest/HartExec.lean:466,478-483` takes `Or.inl` (a
  one-liner; Vtest is not a default target).
- **Pf twin**: the same disjunct in `pnodeStep`'s `.pure` arm (`Weak/WeakEvInst.lean:294-303`).
  Inversions to fix: 16 Weak files, about 47 sites (`AxCert2`, `AxEpiChainSdLd`, `AxRegOnly`,
  `AxSymEngine`, `AxSpinVA`, `AxSymEngine3`, `AxSymCtl`, `PinRelArmRec`, `MachOfPf`, `PinCycRunAsm`,
  `PinRelArmAsm`, `WeakEvCapstone`, `SailCycleOrderK`, `WeakEvInst`, `WeakRvwmoAdm`,
  `WeakRvwmoCert3b`), all mechanical.
  - The catch-up's labels are `LSilent`/`LRegW`, i.e. admin (`lbAdmin`, `Weak/WeakAxRealize.lean:140-144`),
    so no row or graph changes.
  - W4 `simStep`'s boundary case (`Weak/MachOfPf.lean:1062-1075`) gains a case that maps to the MachCSL
    catch-up arm (`MRun 1`).
- Size: MachCSL 0.4–0.9k (4–10 h); pf twin + W4 0.3–0.7k (4–8 h). Risk M (the Löb restructure of
  `wpLoop_restartB` is the only non-mechanical piece).

### R-K2 (private-window agreement): needs X — larger than R44 says, with one possible blocker

Good news first: R44 implies a new slot kind is needed for the member's own `holding+0x0` load (the
member reads 0 where GF read 1). It is not: `lblReidxW`'s Sub arm already allows a plain, non-`aq` load
with different values (`Weak/WeakRvwmoCert2.lean:632-640,655-656`). Also, `agreeW4`'s read-value clause
covers only reads by WRITE events (`Weak/CertZ24.lean:72-76`), so a divergent plain load does not break
`agreeW4`. The work that remains:

1. **The skip set is dynamic.**
   - Today skips are a LABEL predicate: `CertZ26.keepB = !lblFail` (`Weak/CertZ26.lean:21`), and
     `CertZ27.pad`, `CertZ29.keepEv`, `CertZ30`, `CertZ32-34.failRun` are all keyed on `lblFail`.
   - Under K, the long arm and the extra `started` iterations are skipped iff the MEMBER's latest
     value differs from GF's. That is decided by the walk, not by GF's labels.
   - So CertZ24–34 must be re-parametrized by a walk-produced per-slot mask (and `agreeW4`'s `nf` by
     "kept"). This is mostly signature work, 0.6–1.2k.
2. **A lead relation for the window.**
   - After its divergent load, the member's short arm (`lw; bnez; li a0,0; ret`, `kernel.asm` holding,
     same shape as `notes/W10-6m-census.md:85`) puts it at `acquire`'s return point.
   - GF is still at the start of its long arm. The member is AHEAD of the slots it is skipping, while
     `CertZ34.relLag` (`Weak/CertZ34.lean:32-35`) only knows "behind".
   - New relation shape: "related to the emission state at the window's END while the counter is inside
     the window". It is per-site; 0.3–0.6k.
3. **GF-level re-convergence facts for the skipped window** (none of them comes from the member, which
   never executes the window):
   - **GF's restores `ld ra/s0/s1` read their own spills.** X1 (`PinTrapFrame.frameRf`,
     `Weak/PinTrapFrame.lean:7-46,77-84`) proves this only for REALIZED restores, via W2's relation on
     the MachCSL run. A GF-level variant is needed: CoWR, plus "no foreign write to the frame byte"
     obtained from member-level custody (`frameUnexemptAfter`/`frameNoDmaAfter`, still NAMED). M.
   - **GF's long arm returns 0** (`lk->cpu ≠ &cpus[me]`). Otherwise GF panics and there is no
     re-convergence. R44's Q-6M-GFVAL says this rule is needed only when the member also takes the long
     arm. That is wrong: it is needed to re-converge after a skip too. Either gate the skipped
     `holding+0x12` read on "source realized" (a skip step may be gated; progress holds because
     rf ⊆ gmo), or prove the census's GF-level value lemma (`notes/W10-6m-census.md:86`, item 4).
4. **POSSIBLE BLOCKER — dead-frame reads.**
   - The long arm writes holding's frame (`sd ra/s0/s1`) and mycpu's frame. The member never writes
     these bytes. Any later GF read of those bytes OUTSIDE the window returns a value the member cannot
     reproduce, and its effects are visible: the member's label differs, and `agreeW4`'s clause 2 and
     `lblReidx` on stores (verbatim, `WeakRvwmoCert2.lean:597-609,665-672`) fail.
   - C code reads dead stack bytes only through UNINITIALIZED reads. The xv6 proof models one
     explicitly: `filestat` copies `struct stat`'s 4-byte hole to user space
     (`Xv6/FilestatParts.lean:217-221`, the `h : BitVec 32` in `fstatBytes`).
   - R44's condition "true if no foreign hart touches a kernel-stack byte" is the wrong condition: the
     hazard is the hart's OWN later uninitialized read (or the read of a process that migrates onto the
     same kstack).
   - Mitigation, checked on the local build `~/dev/xv6-riscv/kernel/kernel.asm` (same `filestat` frame
     as the tree, `FilestatParts.lean:115-120`):
     - Let `S` be `sys_fstat`'s sp. The hole sits at `S−64…S−57`, and `S−64` is exactly the slot where
       `myproc` (called from `argfd`, whose frame is `[S−48,S)`) spills `s0` (`sd s0,16(sp)`).
     - `argfd` reaches `filestat` only through that `myproc` call, so on every path to the copyout the
       hole's last write is a deterministic, never-skipped spill.
     - So `fstat` is safe in this build. The general obligation is "every uninitialized stack read in
       the image reads bytes definitely overwritten, since the trap/syscall entry, by stores outside any
       `holding`/`mycpu` window". It needs a census of uninitialized reads (the Xv6 proofs' "hole"
       ownership points find them) and a static check: S–M if `fstat` is the only one, a blocker for
       the `holding` skip if one site fails.
   - If it fails: P for that site, or a NAMED premise (WEAKER).
5. **REVERSE divergence (missing in R44).**
   - R44 §2 gates `holding+0x0` on "source realized" and replays LATEST, then says "if the latest value
     differs … SKIP". That covers only GF-extra windows.
   - If the walk realizes another hart's successful acquire `A'` (gate: its source is realized and
     latest) BEFORE hart x's `holding+0x0` read whose GF value was 0, the member reads 1 and takes the
     long arm: an INSERTION. The padded member cannot represent it, because member events must sit at
     GF slots.
   - Fix (a): an fr-gate — a successful AMO waits for GF's `holding+0x0` readers of its source. The fr
     edge is gmo-forward, but progress needs care: the reader's hart may be blocked on a pinned load,
     and RVWMO gives no load→load ppo hop.
   - Fix (b): a walk policy "GF gmo order, with po-forced early appends". My sketch (not proved): the
     early appends are then only release stores and `started` (plain stores; an `.aq` AMO is never
     po-forced past its successors), so divergence on the racy sites is forward-only. The exception is
     the fabric: MMIO reads are not ppo-ordered before later memory loads, so po-forcing could reorder
     device reads against the fabric order. That needs a check against `ioResidueGmo` (R3).
   - Either way: +0.2–0.5k and an order-design item for 6l.

R-K2 total: **1.2–2.5k Weak (items 1–3, 5) + the census/check of item 4 (0.2–0.6k plus a generator)**,
confidence M− (L+ until item 4's census is done). R44 had 0.5–1k.

### R-K3 (registers after a skipped window): OK, conditional on R-K1
- At re-convergence (`acquire`'s return point after `holding`), GF and member agree on:
  - `ra` (the member never overwrote it; GF restores it from the spill — item 3 above);
  - `s0`, `s1`, `sp`;
  - `a0` = 0 (GF needs item 3's value fact).
- They differ on `a5` (GF: `lk->cpu`; member: 0) and on `mycpu`'s scratch registers. `acquire` writes
  `a5` (`mv a5,a4`) before reading it, so `relT TT` with `TT ⊇ {a5, …}` is a per-pc `decide +kernel`
  check, the same shape as the existing taint walker (`Weak/SilSiteTaint.lean`).
- The failed-`amoswap` lag is unchanged (`CertZ34`; GPRs fine per `PROGRESS-W10N2p.md:810-812`).
- The clock cells and `minstret` must be equalised by the catch-up inside the realizing star (R-K1). In
  `CertZ34`'s lag clause, the admin star `ls'` of `CertZ2.stepOkZ` (`Weak/CertZ34.lean:64-67`) is where
  the catch-up steps go.

### R-K4 (the `started` spin): OK
- The window is `lw` + `fence r,rw` + `beqz`: no stores (`notes/W10-6m-census.md` §3.2).
- Policy: skip every GF iteration except the exit one. The member performs only GF's exit iteration,
  gated on "source realized". `started` is written once (one-shot publication, `PinTrapFrame` header
  :49-52), so the latest value there is 1 = GF's value.
- The skipped fence becomes `CertZ24.skipLbl`, itself a no-op fence (`Weak/CertZ24.lean:59`).
- Caveat: the kill must never anchor on a skipped 0-read. This is the same discipline as failed
  acquires, and I expect it to hold, since the `pub` hop uses the reading-1 iteration. It is a check
  item for 6o.

## 3. Does K cover both shapes of F44-1?

- **Litmus 1 (2 harts): yes.**
  - In any TSO-log walk, one of `r1`/`r2` sees the other hart's release (SBAcq: no member under the top
    floor). That hart's member reads latest 0 at `holding+0x0`, or its `amoswap` is a failed acquire;
    GF read 1.
  - The member skips GF's failed iterations (CertZ24–34) and/or the `holding` long arm (R-K2).
  - The later successful `amoswap` is gated "source realized ∧ latest". Its GF source is a release
    store, already appended by TSO, so it agrees.
- **Litmus 2 as R44 states it is NOT an xv6 execution.**
  - If hart 1's read of `d` is `holding`/`amoswap` inside `acquire(d)`, hart 1 reaches `release(y)`
    only after its successful `amoswap.aq` on `d`, which reads (co-after) hart 2's `release(d)`. That
    release's `fence rw,w` orders `w‴` first.
  - So gmo has the cycle `w‴ < R_d2 < A_d1 < R_y < A_y3 < r3 < w‴`. I derived this independently;
    w3 machine-checked it as `SBAcq.l2cNo`.
- **The 3-hart shape is still reachable, through the UART fabric** (my candidate). The coordinator's
  candidate `procdump` is dead code in this image: it has no caller (`notes/W13-io-census.md:284`).
  - Hart 2: `release(z)` [w‴]; then `printk` → `acquire(pr)` → `uartputc_sync` → `acquire(tx)` → THR
    store `0x800009fa` [X]. There is no release, hence no fence, between w‴ and X if nothing else is
    released on the path; that is plausible and the exact path is a check item.
  - The THR write changes `tx`, so it changes LSR bits 5/6 and ISR's transmit id
    (`MachCSL/Dev/Uart.lean:77-95,141-145`). A later ISR/LSR read does not commute with it.
  - Hart 1: in `uartintr`, the UNLOCKED ISR/LSR reads (`0x80000a36/a3a/a5c`, W13-io-census row 3,
    `:197`), ctrl-ordered before → `consoleintr` → `release(cons)` [R_y]. These reads are value-relevant
    and replayed in GF's fabric order (R44 §2 "fabric member").
  - Hart 3: `consoleintr` → `acquire(cons)` [A_y3] → `wakeup` → `acquire(proc[k].lock = z)`, and
    `holding+0x0`/`amoswap` reads z = 1 stale.
  - The member log is forced into `w‴ < X < LSR₁ < R_y < A_y3`, so hart 3's member reads latest 0.
  - **K covers it.** Hart 3 skips its failed spin and, if `r3` is `holding+0x0`, the long arm (R-K2).
    Its later acquire of `z` reads `w‴` (or co-later) at latest. Hart 3's `A_y3` reads `R_y` at latest:
    `R_y` is realized and latest by the AMO gate, since GF's `A_y3` reads it and nothing else wrote
    `cons.locked` in between (atomicity).
  - So yes: the skipped member still produces a hart-3 acquire that reads `R_y`, with latest reads
    everywhere. The cost sits entirely in R-K2.

## 4. Existing pieces under K

| piece | under K |
|---|---|
| CertZ24–30, 32–34 (padded member, skip walk, lag) | **REUSED, re-parametrized** (dynamic mask, lead relation, catch-up in `CertZ34`'s lag clause) |
| CertZ31 (kill from order + datum) | **REUSED as the pattern**; it concludes the untrimmed kill |
| `SilOrd2` (windowed lock co, `csChainedT4W`, `agreeW4N`) | **REUSED** — option-independent (`Weak/SilOrd2.lean` header :2-4) |
| `SilKillT.cycleKillCore` | **NOT reusable as is**: twin-typed (`SilCand.CandS`, `SilAgree.RunDataS`, `SilLang.epowerForkS`, `Weak/SilKillT.lean:98-118`). Only the twin produces `cycleKillCZT` today (`CapFetchProv.lean:146` consumers: Sil* only). Under K a **registered** trimmed kill (CertZ25/31 padded supply → `cycleKillCZT`, with a registered regZero in place of `SilRegZero`'s twin ghost) must be written = R44 row 6o |
| `CapFetchProv` (trimmed hull, `provAll`) | **REUSED** (needed by any kill) |
| `SilSiteTab`, `SilSiteTaint` (static census/taint) | **REUSED** |
| `SilSite` (`silentQ`, `rmwQ`, `ordQ` named premises) | **RETIRED** as premises; the `valQ` shape is re-stated over the registered datum |
| `SilSiteStep` (twin port of `CertZ13.hartStepOfSite`) | **RETIRED** (dead, green): K uses the registered `CertZ13/33/34` datum |
| Sil* twin stack (`SilCand`…`SilWalk2`, `SilLang`, `SilPf*`, `SilEpf`, `SilClose`, `SilRegZero`) | **RETIRED (dead, keep green)** per [R44.s1]; it records that the twin covers the 2-hart shape |
| narrow δ1 inc 15–16b (MachCSL stale silent AMO) | **UNUSED by K** (sound, faithful, harmless); revived only by the δ1′ fallback (§6) |

## 5. Increment plan (K)

| # | increment | lane | lines | worker-h | conf. |
|---|---|---|---|---|---|
| K0 | read-only follow-ups: (a) uninitialized-stack-read census of the image (Xv6 "hole" ownership points + disassembly), with the overwrite argument per site; (b) confirm the UART 3-hart path; (c) owner Q-K-INSTRET | spike | 0 | 3–6 | H |
| K1 | MachCSL row 1′: catch-up boundary arm, Löb in `wpLoop_restartB`, `clockCells` lending at 12 sites, Vtest one-liner | MCSL serial | 0.4–0.9k | 4–10 | M |
| K2 | pf twin boundary arm (16 files / ~47 inversion sites), W4 `simStep` case | Weak | 0.3–0.7k | 4–8 | M+ |
| K3 | dynamic skip mask through CertZ24–34 (`keepB`/`lblFail` → mask; `agreeW4` `nf` → kept) | Weak | 0.6–1.2k | 6–12 | M |
| K4 | lag clause fixed: catch-up in the realizing star; failed-`amoswap` and `started` lag data per pc | Weak | 0.4–0.8k | 4–8 | M |
| K5 | `holding` window (6p): lead relation, GF-level restore/spill + `lk->cpu ≠ me` facts, taint check, the K0(a) static check | Weak | 1.0–2.2k | 10–20 | L+/M− |
| K6 | walk order 6l under K: R44's core + skip arms + reverse-divergence handling (fr-gate or gmo-order policy) + `noStuckK` | Weak | 1.2–2.0k | 10–18 | M− |
| K7 | registered padded trimmed kill (6o): `cycleKillCZT` from the K walk | Weak | 1.2–2.2k | 8–18 | M− |
| K8 | 6b/6j: registered `CapF1.recRealizedH` on the padded member's pf run | Weak | 0.2–0.4k | 2–4 | M |
| Σ | | | **5.3–10.4k** | **51–104** | **M−** |

Order:
- **K0 first** (cheap; it decides whether K5 is S–M or a blocker for the `holding` skip).
- K1 ∥ K3 (different lanes), then K2, then K4.
- K6 core may start now: R44's owner-independent core is unaffected.
- K5 after K0, then K7, then K8.

## 6. Coordinator's extra option — δ1′ (acquire floor = source position) + unsynchronized-read handling

**Spec.** RVWMO orders an acquire's successors after the acquire in gmo, and the acquire after its
source. Writes appended to a TSO log between the source and the acquire need not be gmo-before the
acquire. So "floor := source position" is closer to RVWMO than `tv := top` (`Lang.lean:161`): a WEAKER
machine, FAITHFUL. Writes hb-before the source sit below the floor because TSO appends them first.

**What it buys.** Litmus 1 has a member under δ1′ (`SBAcq.l1MemberSrc`). So every 2-hart shape is
replayed LOCKSTEP and STALE: no skip, no `holding` window, and no R-K2 in the 2-hart case.

**Why it is not enough.** Every floor at or above the source fails Litmus 2 (`SBAcq.l2NoMember`). The
xv6-reachable instances need an unsynchronized hart-1 hop whose value matters. Going through the census
classes:
- lock words: forbidden (`l2cNo`);
- `started`: its writer is fenced (`fence rw,w` before `0x80000f7e`, plan :1679), so no residue;
- `ip->ref`: taint only. There is no residue IF it is left ungated. Q-6M-GFVAL's gate would CREATE
  the forcing, so under δ1′ use the taint/co-interval route instead;
- PTEs: own process only;
- `procdump`: dead code;
- **device reads: residue.** The UART chain of §3 is replayed in fabric order, and the THR write does
  not commute with ISR/LSR (`Uart.lean:88-95,141-145`).

So δ1′ still needs one of:
- K's skip for the residue (including the `holding` long-arm skip whenever `r3` is `holding+0x0`);
- P;
- a NAMED "no fabric-mediated 3-hart chain" (STRONGER).

**Cost.**
- MachCSL floor change in `afterExcl`/`afterExclStale` (`Lang.lean:157-180`): every lock WP rule and
  invariant that uses "after an acquire the view is `top`" must be redone. M–L, 0.8–2.5k; unaudited.
- Twin floor (`SilCand.silentOk`'s `ownExcl ≤ q`, `SilCand.lean:86-94`; `TsoShadow.shFloor :193`)
  re-stated.
- Increment 19's twin W4 revived (R44: 2–3k): stale member loads are not registered candidates, so
  `CertZ4.latestLoadFacts` is unavailable.
- Plus the residue handling (K-lite ≥ K5 + K3, or NAMED).
- **≈ 6–11k + the residue, versus K's 5.3–10.4k**, with the twin's open risks (`silentQ`/`rmwQ`
  truth, F6l-1/2) back on the table.

Verdict: **not recommended as primary**. It is a sensible FALLBACK if K0(a) finds an uninitialized read
that blocks the `holding` skip. In that case use δ1′ for the 2-hart shapes, and K-lite (failed-`amoswap`
and `started` skips only) plus NAMED-or-P for the fabric residue, but only if the residue's `r3` is
always an `amoswap` (it is not, in general).

## 7. K vs P (and δ1′)

| | K | P (store buffer in MachCSL) | δ1′ + residue |
|---|---|---|---|
| faithfulness | FAITHFUL header. Machine: `mtime`/`mcycle` multi-tick FAITHFUL (platform); `minstret` catch-up WEAKER machine (or the relation route) | FAITHFUL, lockstep | FAITHFUL floor; residue as K/P/NAMED |
| MachCSL | 0.4–0.9k (boundary arm) | 8–15k (every store rule, interp, adequacy, W4) | 0.8–2.5k (floor) |
| Weak | 4.6–8.8k + pf 0.3–0.7k | 3–5k + twin W4 2–3k | 5–8k + residue |
| key risk | R-K2 dead-frame reads (K0 decides) and reverse divergence | sheer size; every Xv6 store proof sees buffered stores | twin realization; residue still needs K5 or P |
| keeps registered realization (no twin W4) | yes | no | no |
| time | 51–104 h, mostly parallel lanes | 2–3 months, serial MachCSL lane | ≥ K |

Recommendation: **K, after K0**. If K0(a) blocks the `holding` skip: P for good, or δ1′ + NAMED residue
as a stop-gap (WEAKER, owner's call).

## 8. Things in R44 I believe are wrong or incomplete

1. **`minstret` "no lasting drift" (§0.4 K text)**: wrong. Line :803 of `PROGRESS-W10N2p.md` is about
   `minstret_increment`; `minstret` drifts permanently (`:801-802`, `Weak/CertZ34.lean:37-41`). The
   MachCSL change must cover it, or the relation must be modulo `minstret`. Sizes above include
   Q-K-INSTRET (i).
2. **Litmus 2 as stated is forbidden for xv6** (`SBAcq.l2cNo`; §3). The conclusion "the store side must
   move" survives through the UART fabric instance. `procdump` is not a candidate (dead code).
3. **R-K2's sufficient condition** ("no foreign hart touches a kernel-stack byte") is the wrong
   condition. The hazard is a later uninitialized read of the skipped frame bytes, possibly by the same
   hart (§2 R-K2 item 4).
4. **Reverse divergence** (member reads 1 where GF read 0 at `holding+0x0`) is admitted by R44 §2's
   gates and is not a skip (§2 R-K2 item 5).
5. **Q-6M-GFVAL's `holding+0x12` remark**: the GF value rule (`lk->cpu ≠ me`) is needed whenever the
   long arm is SKIPPED too (GF must return 0 to re-converge), not only when the member takes the arm.
6. **"`SilKillT.cycleKillCore` survives unchanged"** (§0.3 item 5): it is twin-typed. Under K the
   trimmed kill must be re-written for the registered padded member; only the pattern is reused.
7. R44 sizes K at 0.5–1.2k MachCSL + 2.8–5.0k Weak. With the pf-twin boundary, the dynamic mask, the
   lead relation, the GF-level window facts and the registered kill, my range is 5.3–10.4k.

**Owner question Q-K-INSTRET** (only if K is chosen).
- *Background.* When the replay skips instructions the weak run executed, the replay's retired-
  instruction counter (`minstret`) ends up lower than the weak run's. xv6 never reads that counter.
- *Example.* The weak run spins 3 extra times in `acquire` (12 instructions); the replay does not. From
  then on its `minstret` is 12 lower.
- *Options:*
  - **(i) Let the proof machine bump `minstret` at an instruction boundary.** WEAKER machine (not a
    Sail behaviour), FAITHFUL theorem (the weak model is untouched; the xv6 proofs never constrain
    `minstret`). Cost ≈ 0, inside K1/K2. Recommended.
  - **(ii) Compare hart states modulo `minstret` in the proof.** FAITHFUL machine; costs 1–2k across the
    lockstep lemmas.
