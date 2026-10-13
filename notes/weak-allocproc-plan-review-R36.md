VERDICT: NOT SATISFIED

# Review R36 of `notes/weak-allocproc-plan.md` (rev 39)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite below was
read at the working-copy tip of `../xv6iris-weak` (plan rev 39, 5,247 lines) and `../xv6iris-weak-w2` (the W8 (f2-ctx) worker's
tree — `diff -rq` of `MachCSL/`, `Xv6/`, `Weak/` against the tip: NO difference, i.e. the worker's two increments are already in the
tip), `~/dev/weak-orch/parked/PROGRESS-W8f2.md` (2026-10-13 stop), `~/dev/weak-orch/parked/w8f2-s2b-wip/` (9 files, 10,130 lines),
`~/dev/weak-orch/allocproc_W8f2_cont_prompt.txt`, and `~/dev/xv6-riscv/kernel/{pipe,kalloc,string,spinlock}.c`.  Scope per the R36
brief: rev 39's record of W-SCO (A) DONE (§A/§B(11) honesty), the M2 CLOSE paragraph (launchable?), the first Stage 2 launch set
(deps, pairwise file-disjointness incl. against the W8 (f2-ctx) lane, sizes), and the W8 (f2-ctx) worker's latest stop (D1, F-B, F-C).
Items (a)/(b)/(d) of the standing brief were settled in R1–R35 and are not re-opened; R35's two required changes are applied
correctly in §D and the RELAUNCH paragraph (checked below).

**Sign-off.**  NO — FOUR required changes, all plan TEXT on the W8 (f2-ctx) lane (no memory-model change, no shrinking, no change
to M2 CLOSE or the Stage 2 set, which are correct up to cosmetic cites).  (i) Rev 39 still says the W8 (f2-ctx) continuation is
RUNNING with S1 merged; in fact S1′ (the time-indexed registry) and S2-pre (`started` reserved, the gate at the read) are MERGED in
the tip, the worker has STOPPED GREEN, and the WIP moved — the plan must record it and carry a relaunch paragraph that decides F-B
and F-C — [R36.1].  (ii) The merged dynamic registry's one constant is WRONG: `pipeLockNameStr` is the address of the string
`"0123456789abcdef"`, not of `"pipe"` (the `addi` immediate is −146, not +222; the image file's own disassembly comment says so) —
no pipe lock will ever be a hop byte until it is fixed — [R36.2].  (iii) Deviation D1 (the NAME-WORD window) is FAITHFUL and the
proof side is sound, but the plan's "W11's release-site pin per hop is what makes a claimed hop real" is NOT enough for it: the
σ-side window admits `kfree`'s junk-fill store as a shape-"acquire" sitting on a GENUINE release (same value 1, name word still
intact because `memset` runs low-to-high), and an existential export cannot be rescued by a consumer's pin at all — the
σ-predicate itself must exclude it; the fix is small (word-shaped hop entries) and must be in the brief, together with the fact
that the merged D1/D2 depart from the RULED (a′) text [OWN.46] — [R36.3].  (iv) F-C's option (i) is coherent but under-specified
and under-sized (27 client files touch the box's stamps/registers, not ≈ 15); the brief must state the new rows as invariants
before the worker wires them, and size (ii) as the fallback — [R36.4].

## What was checked and holds

- **R35 applied correctly.**  §D Q-F2-PIPEHOP (`:4173-4224`) carries (a′) with the time-indexed `isLk b r`, the `dynLk`
  parametrisation, the `rsvName`-untouched clause, the second (last-`pipeclose`) example and the release-site risk sentence;
  Q-F2-BOOTGATE (`:4225-4283`) carries the history-aware reserved store over `rsvStoreOk`, the five `Xv6/` files + `RsvCell`, and the
  "every acquiring hart needs its gate" sentence; the RELAUNCH (`:1871-1920`) names both and the size additions; [R35.s1]–[R35.s6]
  are in (`pub :123`, `CtxId :432-441`, "AT LEAST" + the 11-file grep, the parked path authoritative, drift CLOSED, no `coh` receipt,
  the second example) ✓.  The continuation brief (`allocproc_W8f2_cont_prompt.txt`) carries [R35.1]/[R35.2] as provisional
  amendments ✓.
- **W-SCO (A) DONE — honest.**  `theorem SailCycleOrderK.cycleOkBoot_holds : cycleOkBoot` (`Weak/SailCycleOrderCycle.lean:128`,
  `good_walk` under `maxHeartbeats 3000000`), `theorem sailCycleOrder_holds : sailCycleOrder := sailCycleOrderOfCycle cycleOkBoot_holds`
  (`:137`), `srvwmoXv6M1 :148` and `srvwmoXv6M2 :179` = the cores applied to `sailCycleOrder_holds` (direct application) ✓;
  `sailCycleOrder` restated under `wbootFacts σ0` (`Weak/SrvwmoXv6Adequacy.lean:139`), `Rboot` pins `pma_regions = bootPMA` AND
  `htif_tohost_base = none` (`SailCycleOrderK.lean:238`), `cycleOkBoot :251`, `rbootInit :531` from `wbootFacts`,
  `sailCycleOrderOfCycle :551 : cycleOkBoot → sailCycleOrder` ✓; 16 files `Weak/SailCycleOrder*.lean`, 4,085 lines (plan: ≈ 4.1k) ✓;
  122 `def execute_` in `InstsEnd.lean` ✓; no `sorry` in the chain/registry files.  Registration: `roots-weak.txt:22 Weak.srvwmoXv6M1`,
  `baseline-weak.json:148` with EXACTLY the core's axioms/opaques ✓, `audit.sh:49,56` list `Weak.SailCycleOrderCycle` ✓.  §A(6)
  (`:636-642`) and the statement comment (`:671-675`) say "a THEOREM … NOT a trusted item … dropped from the statement" ✓; §B(11)
  (`:1450`, `:1462-1470`) says "a THEOREM since rev 39" ✓ — one stale clause survives inside it, [R36.s2].
- **M2 CLOSE — LAUNCHABLE as written** (cosmetic cites aside, [R36.s1]).  Deps real: `srvwmoXv6M2Core` (`PfRunUnpinned.lean:652`,
  takes `hsco`), `srvwmoXv6M2` (`SailCycleOrderCycle.lean:179`, docstring `:176-178` "NOT registered (M2 CLOSE registers it, §C W5d)"),
  `srvwmoXv6M2Satisfiable :758` ✓; `lint.sh:53-57` checks `roots-weak.txt` ↔ `baseline-weak.json` ✓; `Weak.SailCycleOrderCycle` is
  already in both `audit.sh` lists, so (3) "UNCHANGED" is right ✓; the item touches `tools/` + headers only — disjoint from w2
  (`MachCSL/`, `Xv6/`, `Weak/WeakAdequacy.lean`) and from every Stage 2 file ✓.  S, hours ✓.
- **Stage 2 first launch set — deps met, pairwise disjoint up to the named S rebases, sizes consistent with §C.**  Every cite
  resolves: W12's `topoLinearizes :436`/`topoExists :583`/`normalizeOfAcyclic :598` (`WeakRvwmoTopo`), `normalizeOfAcyclic' :378`
  (`Dec`), `topoSupply :954` (`Supply`), `hullRun :282` (`Glue`), `topoLinearizesF :909` (`Fab`), `racyD :200` (`Acyc`); the spike
  `CatOfMinusSpike.lean` `rvwmoCatAD :31`/`segPinC :163` MERGED ✓; W13 (L)'s `ptraceRel :130`/`gtraceLinearizationMin :634`/
  `fconfSupply' :1006` (`Lin2`), `gnxw :440`/`linCand :471` (`Lin`), `trDevOrdered :464` (`FabInd`), `linGmoEmitBefore :144`/
  `linLogEmitted :172` (`Sca`), its dep `gfexecConfIO` (`WeakRvwmoFab.lean:844`) ✓; (F-dep)'s owners `AxDeps`/`WeakRvwmoConf`/
  `WeakEvInst` ✓.  Disjointness: W12 ∩ (L) = ∅ ✓; W12 ∩ (F-dep) = `Supply`/`Fab` at different sites (named, rebase S) ✓;
  (F-dep) ∩ (L) = `FabInd` at different sites (named) ✓; none touches `MachCSL/`, `Xv6/` or `Weak/WeakAdequacy.lean` (the
  (f2-ctx) lane) ✓.  One unnamed edge: W12 DEPENDS on `AxDeps` (`CatOfMinusSpike.lean:20 import Weak.AxDeps`; `catADOfCatT :37`
  consumes `rvwmoCatConsistentT`/`gtAd`), which (F-dep) EDITS — rebuild/re-elaboration only, [R36.s3].  The plan correctly says the
  set waits for the owner's batch approval (`:1928-1929`; [OWN.44] covered three other items).
- **S1′ / S2-pre are in the tip, as PROGRESS describes** (rev 39 does not yet say so — [R36.1]): `ChainDefs.lean` 413 lines,
  `ChainEnv.isLk : PAddr → Nat → Prop` (`:266`), `ext` keeps past registrations (`:274-276`), `hopChain` checks `isLk b a` at the
  ACQUIRE position (`:177-183`, deviation D2), `syncHop :171`, `pubCover :288`, `gateOk :301`, `valid :351`, `valid_hop :392`,
  `memGrow`/`memGrow_writeBytes :116-158`; `Reserved.lean` `latestAt :224`, `nameLockAt :236`, `nameLockAt_mono :240`,
  `KernelRsv.names :258`; `Resources.lean:1062-1063 chainEnvAt rs names σ` with `isLk b a := lockByteIn rs b ∨ nameLockAt names σ.mem
  σ.top b a`, `MachFixedGS.rsvNames :406`, `Adequacy.lean:229 rsvNames := KernelRsv.names`; `WpAtomic.lean` `hopHead :608`,
  `hopRegAt :613`, `HopData :620`, `hopIn :623`/`hopOut :630`, `exclWriteAU` with the optional request (`:657-669`), `rtIn :453`/
  `rtOut :458`, `memModel_rtIssue :550`; `ChainCert.lean` `memModel_chainHop :173` (`hlk : (chainEnv σ).isLk b a`, `ha : σ.top = a`),
  `memModel_chainRetimeL :205`, `memModel_chainHopL :230`; `ReadAUr.lean` `RdIssue :36`, `rdIn :42`/`rdOut :50`, `memModel_rdIssue
  :121`, run by `WpSmodeFenceFloor.lean:259`; `Xv6/KernelRsv.lean:52 xv6StartedR = ⟨started, .pub 0⟩`, in `xv6PreLockRegions :57`;
  `StartedInv.lean` `startedWin :152`, `startedCell :184` (D4's `⌜rsvStatic = KernelRsv.static⌝`), `xv6Pub_only :120`, `startedSeen`
  carrying `gatePassed cpu` (`:269`); `WpStoreOrd.lean:45` the RESERVED `writeAUT` arm over `rsvStoreOk` ✓.  The S2b WIP is at
  `~/dev/weak-orch/parked/w8f2-s2b-wip/` (`Lock.lean.txt:546 lockRec`, `:560 lockPay`, `:625 lockRec_hopReq`; `WpLock.lean.txt`
  179,777 bytes) — PROGRESS's `claude-notes/w8f2-s2b-wip/` exists in neither tree (stale path, as in rev 38).
- **F-B is SOUND and FAITHFUL** (with one guard, folded into [R36.1]).  RVWMO: `h`'s store at `t` → `h`'s `fence rw,w` → its release
  → (hops, each `rf` + `.aq`/fence) → hart 0's acquire at `a` → hart 0's `fence rw,rw` → `started` store at `r > a` → `rf` → `j`'s load →
  `j`'s fence: PPO 4–7 + rf chains compose in the total gmo; Sail/Zifencei/PMAs silent.  In the chain layer the new arm
  `(h = w ∧ t < r) ∨ ∃ a < r, hopChain X.m X.isLk h t w a` is monotone under `ChainEnv.ext` (`hopChain_mono :191`, the coherence clause
  `:276`), `valid_hop :392`'s boot-hop case re-runs unchanged (the gate gives `B` the same one-shot entry), `valid_retime` and `valid_le`
  (`hopChain_prefix :199`) unchanged in shape — ≈ 0.1k is right.  The guard: the coherence-monotonicity clause of `ext` is stated for
  `j ≠ w` (the publication's WRITER), so the generalised `pubCover` must require `j ≠ w`, not `h ≠ j` (today's `:289`).

## REQUIRED changes

- **[R36.1] Rev 39's W8 (f2-ctx) status is stale; the plan needs the RESULTS record and a second RELAUNCH paragraph that decides
  F-B and F-C.**
  *What is wrong (evidence).*  Header `:28` "W8 (f2-ctx) continuation RUNNING (w2)", `:1871-1874` "LAUNCHED 2026-10-12 in w2, RUNNING
  [rev 39]", `:1925-1927` "W8 (f2-ctx) continuation RUNNING"; but `PROGRESS-W8f2.md` (2026-10-13) is "STOPPED GREEN after two
  increments; S2 lock layer parked; one design gap (F-C) needs a decision", and the tip already HOLDS both increments (the file:line
  list in "What was checked" above; `diff -rq` w2 ↔ tip empty).  Nothing in the plan records S1′/S2-pre, deviations D1–D4, findings
  F-A–F-D, the moved WIP or the new size (+2–3.5k).  FAITHFUL/mark not applicable (bookkeeping).
  *Exact change.*  (1) Header + `:1871` + `:1925`: "RUNNING" → "STOPPED GREEN 2026-10-13; S1′ + S2-pre MERGED (tip); RELAUNCH 2 below".
  (2) After the rev-38 RESULTS block (`:1858-1870`) add **"W8 (f2-ctx) RESULTS (rev 40) — S1′ + S2-pre MERGED"**: S1′ = the time-indexed
  registry (`ChainDefs.lean:266` `isLk : PAddr → Nat → Prop`; `hopChain :177-183` checks `isLk b a` at the ACQUIRE position — deviation
  D2; `memGrow`); the dynamic registry = the lock's NAME word (`Reserved.lean:236 nameLockAt`, `KernelRsv.names :258`, `Xv6/KernelRsv.lean:111
  names := [pipeLockNameStr]`, `MachFixedGS.rsvNames`, `Adequacy.lean:229`; `chainEnvAt rs names σ`, `Resources.lean:1062` — deviation D1 =
  (a″), see [R36.3]); the hop request inside the AMO's step (`WpAtomic.lean:608-669`: `hopHead`, `hopRegAt` static/dynamic, `HopData`,
  `hopIn`/`hopOut`, `memModel_hopIssue` over `ChainCert.memModel_chainHopL :230`) and the release's retime request (`rtIn :453`/`rtOut
  :458`, `memModel_rtIssue :550`) — deviation D3 = the plan's "new continuation field", on `exclWriteAU`/`writeAU`/`readAUr`/`writeAUT`;
  S2-pre = `started` reserved `.pub 0` (`Xv6/KernelRsv.lean:52,57`, `rsvCpuIdx` 7 → 8), the publication-read issue request (`ReadAUr.lean:36-65`,
  `memModel_rdIssue :121`, run by `WpSmodeFenceFloor.lean:259` — the gate is issued INSIDE the load's step [R35.s5]), `writeAUT`'s RESERVED
  arm over `rsvStoreOk` (`WpStoreOrd.lean:45` — the [R35.2] history-aware store landed there, not as a `RsvCell` variant), `StartedInv`
  restated over the half window (`startedWin :152`, `startedCell :184` with `⌜rsvStatic = KernelRsv.static⌝` — deviation D4, `xv6Pub_only :120`,
  `startedSeen` carries `gatePassed cpu` `:269`), `BootRsv.bootPreHalves`, `BootShared`/`BootSharedText`/`MainSecondaryParts`/`DiskAcc` adapted;
  builds + `lint`/`audit`/`audit --weak`/`tcb` PASS per the worker (not re-run here); no root statement changed; `expected.json` unchanged.
  The S2b WIP (lock layer: `lockRec`/`lockPay`/`lockRec_hopReq`/`lock_pay_born(_hook)`, `WpLock`'s AMO hop + release retime, `LockPayIff`/
  `LockBornHook` re-proved) is parked at `~/dev/weak-orch/parked/w8f2-s2b-wip/` (9 files; PROGRESS's `claude-notes/…` path is STALE
  again — say so).  Findings F-A (= D1), F-B, F-C, F-D transcribed; per-row table: rows 13–18, 22 wait on F-C, row 27's absorb on F-B.
  (3) **RELAUNCH 2 — W8 (f2-ctx) continuation (rev 40; serial MachCSL lane; w2 or a fresh workspace on the tip)**: brief = the rev-38
  RELAUNCH text as amended by [R36.2]–[R36.4] + `PROGRESS-W8f2.md` (its "Design"/S1′/S2-pre sections BINDING) + the parked S2b WIP
  (authoritative).  Order: **S0 fix `pipeLockNameStr` [R36.2] and the hop shape [R36.3] (S, one `MachCSL`+`Xv6` increment, no cone
  rebuild needed beyond `KernelRsv`'s cone)**; **S2b** the lock layer from the WIP (with F-B: `pubCover` gains the chain arm, guard
  `j ≠ w`; `started_absorb` closes row 27); **S2 CtxBox** per [R36.4]; **S3**, **S4** as in rev 38.  Rules unchanged (stop green on a
  wrong clause; spec-first options; per-row table current).  Size: remaining ≈ 5–8k of the rev-38 total **+ ≈ 2–3.5k (F-C)**; 3 cone
  rebuilds.  Parallel-lane rule: W-SCO (A) is DONE — drop the "do NOT edit `Weak/SailCycleOrder*` …" clause; keep "`Weak/WeakAdequacy.lean`
  is the only `Weak/` file (f2-ctx) may edit" (M2 CLOSE and the Stage 2 set never touch `MachCSL/`/`Xv6/`).  (4) `:1925` WAITS: W8 (f3-rest)
  still after (f2-ctx).

- **[R36.2] The merged dynamic registry names the WRONG string: `pipeLockNameStr` is `"0123456789abcdef"`, not `"pipe"`.**
  *What is wrong (evidence).*  `Xv6/KernelRsv.lean:104`: `def pipeLockNameStr : BitVec 64 := KA.«pipealloc» + 0x48#64 + 0x3000#64 + 222#64`
  with the docstring "`auipc a1,0x3 ; addi a1,a1,222` at `pipealloc+0x48`".  The image: `Xv6/KernelImage.lean:13326-13329` — `auipc a1,0x3`
  = `⟨0x80004652, 4, 0x00003597⟩` ✓, then **`addi a1,a1,-146 # 800075c0 <etext+0x5c0>` = `⟨0x80004656, 4, 0xf6e58593⟩`** (imm[11:0] = `0xf6e`
  = −146 in two's complement; `rd = rs1 = a1`).  So the loaded address is `0x80004652 + 0x3000 − 146 = 0x800075c0`, which IS the string
  `"pipe"` (`KernelImage.lean:18120-18121`: `/-- `pipe` at `0x800075c0` -/ def KernelStr.«pipe» : Nat := 0x800075c0`; BitVec form
  `KS.«pipe» :18837` with the `k_addr` lemma `:18838`).  The constant as written evaluates to `0x80007730` = `KernelStr.«digits»`
  (`:17905`: "`digits` … size 0x11", `:18152` "`0123456789abcdef` at `0x80007730`").  Consequence: `nameLockAt [pipeLockNameStr]`
  (`Reserved.lean:236`) is never true of a real pipe lock — the S4 export's pipe hops and `lockWordDiscAt`'s pipe arm become UNPROVABLE
  (the worker would meet it only at `PipeBirth`, two increments from now).  No unsoundness (no kernel word holds `&digits` at `lk->name`;
  a registry only RESTRICTS hops).  FAITHFUL once fixed.  Nothing in the tree ties the constant to the image — no `rfl`/`decide` lemma.
  *Exact change (RELAUNCH 2, S0; §D Q-F2-PIPEHOP *Definitions*).*  "`pipeLockNameStr := KS.«pipe»` (`KernelImage.lean:18837`, `= 0x800075c0`;
  the hand-computed `KA.«pipealloc» + 0x48 + 0x3000 + 222` at `KernelRsv.lean:104` is `KernelStr.«digits» = 0x80007730` — the `addi`
  immediate is −146, `KernelImage.lean:13328-13329`); add `theorem pipeLockNameStr_eq : pipeLockNameStr = KS.«pipe» := rfl` and a
  `decide`/`rfl` fact that the image bytes at `KS.«pipe»` are `"pipe\0"` (documentation; the `pipealloc` proof computes the same value from
  `auipc`/`addi`)".  Add to the brief's acceptance: "`PipeBirth` establishes `nameLockAt … (pi.lock) a` from the `initlock` name store".

- **[R36.3] Deviation D1/D2 (the name-word window, indexed at the acquire) departs from the RULED (a′) [OWN.46] text and leaves a
  σ-side hole the plan's "W11's release-site pin" does not close; the brief must state the shape fix and the honest limit of the pin.**
  *What is wrong (evidence).*  (i) *Departure.*  [OWN.46] (`:4170-4171`, `:4201-4216`) rules (a′) = "`pipeLockAt` from the `f->pipe` slot
  history + the reclaim entry; `isLk b r` at the RELEASE's position; `dynLk : MState → PAddr → Nat → Prop` client-supplied"; the RELAUNCH
  `:1874` says "[OWN.46]/[OWN.47] RULE the two provisional options exactly as the brief implements them".  The MERGED registry is the lock's
  NAME word (`nameLockAt`, `Reserved.lean:236`: "`b + 8` holds, as of `a`, one of the client's registered names"), indexed at the ACQUIRE
  (`hopChain :180,183 isLk b a`; `memModel_chainHop :173 hlk … isLk b a`, `ha : σ.top = a`), with a MachCSL-fixed shape (`names : List (BitVec 64)`,
  `KernelRsv.names :258`) rather than a client `dynLk`.  The worker's reason is sound — F-A: the generic acquire holds the lock words, not
  `ftable`'s slots, and there is no persistent history-entry receipt — but the plan records (a′) as RULED and the brief as implementing it.
  Mark: (a″) is FAITHFUL (a registry only restricts the chains the proof claims; RVWMO/Sail/Zifencei/PMAs are silent on how a proof names
  its hop words, exactly as the question's *Spec (FIRST)* says); D2 is FAITHFUL (a real hop has `r < a` inside one live window, so
  indexing at `a` or at `r` accepts the same real hops).  (ii) *The hole.*  `syncHop :171-173` is pure byte-history SHAPE: `⟨a, B, va⟩`
  (`va ≠ 0`) immediately above `⟨r, A, 0⟩` above a nonzero entry.  xv6 frees a pipe as `release(&pi->lock); kfree(pi)` (`kernel/pipe.c:70-71`);
  `kfree` is `memset(pa, 1, PGSIZE)` (`kalloc.c:55`), a byte loop low-to-high (`string.c:4-12`; `Xv6/ProofMemset.lean:99` "`sb a1,0(a5)`"),
  and `struct pipe` starts with the lock (`lk->locked` at `+0`, `lk->name` at `+8`, `spinlock.h:2-7`).  So the first junk store writes byte
  `b` with value **1** — the SAME low byte an `acquire` AMO writes — at a timestamp when `b+8..b+15` still hold `"pipe"`: `nameLockAt … b a`
  is TRUE at that `a`, `syncHop` holds (the release at `r` is a GENUINE release over a held entry), and `hopChain` accepts a hop from the last
  releaser `A` to the freeing hart `C` — spurious in RVWMO terms (`C`'s store is a plain `sb`, nothing orders `C`'s later loads behind it;
  with `A ≠ C` — the closing thread can migrate between `release` and `kfree` — the conclusion happens to hold through `p->lock`, but not
  through THIS hop).  The RELEASE-site pin (`:4218-4219`, `:3943-3944` "the static release-site fact `fence rw,w; sw`") passes here;
  only an ACQUIRE-side check (the entry at `a` is an `amoswap.w.aq` at `acquire`'s site) would reject it — and no pin can: the export is
  `chainOkAt σ = ∀ racy read, ∃ chain` (`:4187-4190`), so W11 receives SOME chain, possibly this one, and can derive nothing from it.
  Two further shape artefacts of the same kind: at BIRTH `initlock` stores `lk->name` FIRST, then `lk->locked = 0` (`spinlock.c:16-18`), so the
  creator's plain zero sits inside the window above `kalloc`'s junk `5` bytes (`kalloc.c:80`) and reads as a "release from held"; and a
  USER page can be written with a word `0`/`1` alternation plus `&"pipe"` at `+8` (the note in `PROGRESS-W8f2.md` "bounded to bytes whose
  name word holds the `"pipe"` literal" is true but the user controls that too).  (iii) *The custody conjunct meets the same window.*
  `lockWordDiscAt σ := ∀ b t, xv6LockWord σ b t → lockRegionOk … σ.mem b` (`Xv6/AccessDiscipline.lean:104-105`) with `lockRegionOk`
  WHOLE-history (`Reserved.lean:108-110`: `wordHistAt m lk 4 W Hold … lockDiscW`): a dynamic arm `xv6LockWord σ b t := nameLockAt …` makes the
  consequent a claim about the pipe word's entire history (pre-birth junk, post-death junk) — FALSE on every run that frees a pipe.  The
  (a′) text (`:4213` "`syncPath` (S4) and `xv6LockWord`'s dynamic arm hop through `isLk b r`") and the RELAUNCH's S4 sentence
  (`:1906-1907` "`custAt`/`xv6LockWord` (static + the live-pipe arm)") do not say the consequent must be WINDOWED.
  *Why the shape fix works.*  Every lock-protocol write to a pipe lock word is a 4-byte store at ONE timestamp (`amoswap.w.aq`, `amoswap.w
  zero`/`sw zero` at release, `sw zero` at `initlock`; `σ.store cpu pa 4 w excl` pushes four entries with the same `t`, `memGrow_writeBytes
  :156`), while `memset`'s junk (`kfree` AND `kalloc`) is one byte per timestamp, and the only other stores to the first 8 bytes of a free
  page (`r->next`) happen after the name word is junk.  So "the hop's three entries at `a`, `r` and the held entry are each the low byte of
  a WORD-sized entry (an entry at the same timestamp on `b+1..b+3`)" excludes the junk-fill "acquire", the junk "held" entry under the
  `initlock` zero, and the kalloc junk — σ-readably, inside `ChainDefs`.  The user-forged word alternation is NOT excluded by shape; it IS
  excluded by (a′)'s kernel-controlled `f->pipe` slot history, and by nothing else σ-readable short of "no user PTE maps the page".
  *Exact change (§D Q-F2-PIPEHOP — a new paragraph after (a′); RELAUNCH 2 S0/S2b/S4; the question goes back to OPEN-provisional, see the
  owner question below).*  "**(a″) AS MERGED (S1′, deviation D1/D2; FAITHFUL; provisional under the non-blocking rule, owner informed):**
  the dynamic registry is the lock's NAME word — `nameLockAt names m top b a` (`Reserved.lean:236`: `lk->name` at `b+8` holds a registered
  name as of `a ≤ top`), `KernelRsv.names = [pipeLockNameStr]` (= `KS.«pipe»`, [R36.2]), checked at the hop's ACQUIRE position
  (`hopChain :180,183`, `memModel_chainHop :173`); `rsvName` untouched; the AMO's step proves it from the name word's histories the lock
  invariant lends (`hopRegAt :613`).  Differs from (a′) in the WINDOW (name store → name overwrite, instead of `f->pipe` write → reclaim) and
  the INDEX (acquire, not release).  **Shape fix (REQUIRED before S4): `syncHop` requires its three entries to be WORD-sized** — `wordEntAt m b t`
  := `∀ i < 4, ∃ e ∈ m[b+i], e.t = t` (same agent), for `a`, `r` and the held entry — so `kfree`'s junk byte `1` on `b` (inside the still-open
  name window: `memset` low-to-high, `kalloc.c:55`, `string.c:8-10`) and `kalloc`'s junk `5` under the `initlock` zero are not hops;
  `syncHop_mono`/`hopChain_*`/`memModel_chainHop`'s `hb` gain the word-shape hypothesis, discharged at the AMO from the lock invariant's
  `WordHist 4` (S ≈ 0.1k).  **`lockWordDiscAt`'s dynamic arm is WINDOWED**: for a dynamic `b`, `lockRegionOk` is stated on the sub-history
  from the `initlock` zero (the first word-sized entry inside the name window) to the last word-sized entry before the name overwrite —
  not on the whole history (`Reserved.lean:108` is whole-history; `AccessDiscipline.lean:104` as written would be FALSE at every `kfree` of
  a pipe).  **Honest limit:** a user page can be written to LOOK like a live pipe lock (word alternation + `&"pipe"` at `+8`); (a″) + shape
  does not exclude it, (a′)'s kernel-only `f->pipe` history does; neither W11's release-site pin nor an acquire-site pin can repair an
  existential `chainOkAt` after the fact.  Options for the residual: **(a″-s)** accept it — FAITHFUL (the export says "a chain of lock-shaped,
  name-tagged word hops exists"; it is the DOCUMENTED meaning of `chainOkAt`, and W11's robustness proof must then carry the user-page
  exclusion itself from `custAt`/the page tables — ≈ 0.3–0.5k moves into W11, mark it there); **(a′-r)** add the kernel-side anchor —
  a persistent entry receipt `entryAt pa e` (one MachCSL ghost over the append-only histories, S–M ≈ 0.2–0.4k) so `PipeBirth` can hand the
  lock the `f->pipe` slot's entry and the hop request carries it — FAITHFUL, closes the user-page case σ-readably, is the RULED (a′) with
  the worker's objection answered.  RECOMMENDED: (a″) + shape NOW (unblocks S2b), (a′-r) as a NAMED S4 follow-up decided by the owner
  (question below); the release-site sentence of (a′) `:4218-4219` is rewritten: 'W11's release-site pin identifies release STORES; it cannot
  select among chains an existential export offers — the σ-predicate must be tight by itself'."  In the RELAUNCH's S4 sentence (`:1906-1907`)
  add "(windowed `lockRegionOk` for dynamic locks)".

- **[R36.4] F-C: option (i) is coherent but the brief must state its rows as invariants and size it against the real client surface
  (27 files, not ≈ 15), with (ii) sized as the fallback.**
  *What is wrong (evidence).*  F-C (`PROGRESS-W8f2.md` "F-C") is right that X2 as written is scalar: `boxRows` (`CtxBox.lean:1117-1121`)
  rows (C) `(∀ p live, T ≤ p.2) ∨ T ≤ s.tp` and (D) `T ≤ r.td ∨ ∃ p live, p.2 = T` cover the box's STAMP `T`; `boxRefDecr :1617` raises
  `td := max td (maxStamp mD)` — a TSO move (visibility by time) with no vector analogue (the decrementer need not be chained to the last
  parker: `idup`/`iput` never check out); `ctxDeposit :156-162` stamps at `max T (max K W)`, so two deposits can share a stamp and the
  `(id, stamp)` key cannot name an epoch.  Option (i) — `vd`/`vp` vector registers, a `lastL1` bit, an epoch token with mass per reference,
  a persistent epoch ↦ deposit-vector snapshot at `refIncr`, a per-park token returned at the parker's `refDecr` — is the right SHAPE:
  the taker's cover of the parked vector `V` is `V ≤ vd ⊔ vp`, `vd` reached through the L1-lock lineage from the epoch's deposit (the
  epoch token proves the reference was minted after it), `vp` through the `lk->lk` hop from the last park (every later parker's vector
  dominates the earlier ones by the same lineage), and `vd ⊔= vp` only at the PARKER's `refDecr` (its token), so the L1 withdraw at
  refcount 0 is covered.  But (1) the PROGRESS text states none of this as rows, and the "exclusive" per-park token is ambiguous when two
  parties have parked since the deposit (one token per park event, collected by the next park? by the parker's `refDecr`?); (2) the
  epoch token "carried with mass" must split under the icache's M-5 shares (`mscale`, `reference_split`/`reference_join`) — a fractional
  per-epoch resource, i.e. the SAME camera shape as the stamps map already keyed by `(id, stamp)`: (i) adds a second map where (ii)
  re-keys the existing one by deposit index — the "larger client churn" claim for (ii) is unsupported; (3) the client surface is larger than
  "≈ 15 `Xv6/` files": 27 `Xv6/` files mention `reference γ`/`unitStamp`/`maxStamp`/`slotdHalf`/`slotpHalf` (grep; 60 mentions of
  `unitStamp`/`maxStamp` alone: `BcacheInv`, `BioInit`, `BufEscrow`, `FileDefs`, `FilePay`, `FileOffProto`, `Fileread*`, `Filewrite*`,
  `IcacheBox`, `IcacheBoxSites`, `IcacheCover`, `IcacheRef`, `IlockCheckout`, `IlockMain`, `IputEntry`, `IputEntryGhost`, `IputLockedC`,
  `IputStages`, `OffBox`, `ProofBrelse`, `ProofBwrite`, `ProofIput`, `SysOpenParts`).  All three options FAITHFUL (proof-internal; the
  spec is silent).  Not a shrink: the decision is needed for S2 to start.
  *Exact change (RELAUNCH 2, the "S2 CtxBox" sentence; §C W8 (2); size line).*  "**F-C RULED by the coordinator (non-blocking, both
  FAITHFUL): option (i), stated as rows BEFORE wiring.**  The brief's first S2 deliverable is the new `boxRows` as Lean definitions in
  `CtxBox.lean` (no proofs yet): (Σ) unchanged; (I) unchanged; (C′) the parked vector `V ≤ vp` when a park has happened since the current
  deposit, else `V ≤ vd` (`lastL1`); (D′) at refcount 0, `V ≤ vd` — maintained by `vd ⊔= vp` at the refDecr of the party holding the
  CURRENT park token (one token per park, the next park takes it over; say which); (E) every live reference's epoch token names the current
  deposit index, and the persistent snapshot `epoch e ↦ vd_e` is minted at the deposit; the taker's obligations listed per transition
  (`boxWithdrawL1`: (D′); `boxCheckout`: the epoch's `vd_e` by L1-lock lineage + `vp` by the `lk->lk` hop; `boxL1ToL2`: own vector;
  `boxRefIncr`/`boxRefDecr`: token/snapshot bookkeeping; the icache shares: the token is fractional).  If the rows do not close on paper
  within the first increment, switch to **(ii)** (re-key the stamps map by deposit index — the `(id, stamp)` key is already a per-reference
  epoch witness except for stamp collisions, `ctxDeposit :162`), whose client churn is bounded by the 27 files above — report the choice.
  Size: MachCSL ≈ +1–1.5k, `Xv6/` ≈ +1–2k over 27 (not 15) files; total (f2-ctx) ≈ 9–13.5k."

## SUGGESTIONS

- **[R36.s1] M2 CLOSE — three cosmetic cites.**  (4) quotes a `PfRunUnpinned.lean` header sentence "NOT registered — M2 closes after W-RSV
  and [R32.1]" that does not exist (`grep -i regist Weak/PfRunUnpinned.lean`: nothing) — write "ADD a registration sentence to the header";
  `MachOfPf.lean:66-67` → the W-SCO sentence is at `:73-77`; (2)'s fix of `baseline-weak.json:3`'s module list should read
  "…,Weak.SrvwmoXv6Adequacy,Weak.SailCycleOrderCycle" (keep both, as `audit.sh:49` has).  Also say once whether M2 CLOSE needs the owner's
  nod: it is bookkeeping of items already ruled ([OWN.3] M2, W5d, [OWN.42] W-SCO (A)); "LAUNCHABLE NOW" (`:1930`) and "launches beside
  them" (`:2002`, the batch that WAITS for approval) read differently.
- **[R36.s2] §B(11)'s stale clause.**  `:1463-1464` still says `sailCycleOrder` is "a premise of `machRunOfPfRun`, M1, M2 and §A's statement";
  write "a hypothesis of `machRunOfPfRun` (`Hyps.fi`) and of the CORES `srvwmoXv6M1Core`/`M2Core`, discharged in `srvwmoXv6M1`/`M2`; gone from
  §A".
- **[R36.s3] One dependency edge in the Stage 2 map.**  W12's spike imports `Weak.AxDeps` (`CatOfMinusSpike.lean:20`) and `catADOfCatT :37` is
  stated over `rvwmoCatConsistentT`/`gtAd`; (F-dep) edits `AxDeps`' tagger arms.  Not a file conflict, but W12 re-elaborates after each
  (F-dep) merge — add "W12 depends on `AxDeps` (rebuild only)" to the W12 parallel-safety line.  Also `WeakRvwmoFab.lean:516` is a theorem
  body line, not the `Gfexec` bundle; relocate by name.
- **[R36.s4] The hop's docstring claim.**  `ChainDefs.lean:17-23` says "the region discipline lets only the lock rules write the byte" —
  true for RESERVED lock words, not for a dynamic one; after [R36.3] write "…or, for a dynamic lock, the word-shape + name window".
- **[R36.s5] `Rboot`'s honesty line is good; add the two-register note to roots-weak's gloss** (`roots-weak.txt:21-22` says "THEOREM after
  W-SCO (A)" — add "(under `wbootFacts σ0`: `pma_regions = bootPMA`, `htif_tohost_base = none`)" so the registered line states the platform
  premise the theorem rests on).
- **[R36.s6] PROGRESS path.**  `PROGRESS-W8f2.md` again names `claude-notes/w8f2-s2b-wip/`; the parked copy is the real one — the relaunch brief
  should ask the worker to write the parked path in PROGRESS from now on.

## Owner questions the plan is missing

- **Q-F2-PIPEHOP-2 — the merged registry (a″) versus the RULED (a′): which window may `chainOkAt`'s pipe hops use, and must the
  export exclude user-forged lock shapes by itself?**  *Spec (FIRST).*  RVWMO (chapter "RVWMO Memory Model", PPO rules 4–7 and the
  load-value axiom): a store ordered by a FENCE or `.rl`, read by a load the reader orders behind it (`.aq`/FENCE), orders the writer's
  earlier accesses before the reader's later ones — AT ANY ADDRESS; the spec has no notion of "lock", "name" or "page owner".  The Sail model
  in this tree executes the AMO as `execute_AMO` (`model/Lean_RV64D/LeanRV64D/InstsEnd.lean:18663`) and the fence through
  `effective_fence_set` (`:18299-18313`); a plain `sb` and an `amoswap.w.aq` differ only in width/atomicity/`aq`, not in what the byte
  history records (`MachCSL/TsoMem.lean:76-80 HEnt = ⟨t, tid, v⟩`).  Zifencei silent.  PMAs: pipe pages and user pages are both
  `MainMemory` (`MachCSL/Platform.lean:240-254`).  So WHICH words are hops is a proof-partitioning question the spec is silent on: an option
  that RESTRICTS claimed chains is FAITHFUL; one that removes bytes from the predicate is WEAKER.  *Plain language.*  The theorem's chain
  conjunct says "every cross-hart read of pipe data is reached by a chain of lock hand-offs".  The proof needs a rule for recognising, in the
  final memory trace alone, which words were pipe locks and when.  The merged rule reads the lock's own debug NAME field: a word is a pipe lock
  while the 8 bytes after it hold the address of the string `"pipe"`.  The ruled rule reads the kernel's open-file table: a word is a pipe
  lock from the moment a file slot pointed at its pipe until the page was recycled.  *Example.*  Hart A: `acquire(&pi->lock); pi->data[0] = 'x';
  release(&pi->lock)`.  Hart B: `acquire(&pi->lock); c = pi->data[0]` — both rules accept this hop (real).  Counter-example for the merged rule:
  hart A `release(&pi->lock)` (last use), the closing thread migrates to hart C, which runs `kfree(pi)`: `memset` writes byte value 1 to the
  lock word FIRST (the name field, 8 bytes later, is still `"pipe"`) — the trace shows "0 by A, then 1 by C" under a `"pipe"` name, the SAME
  shape as B's acquire; the merged rule calls it a hop (RVWMO does not: C's store is a plain byte store, nothing orders C's later loads).
  A second one: a user program writes `1`, `0`, `1` as words to its own page and `&"pipe"` eight bytes on — the merged rule calls it a hop;
  the ruled rule does not (no file slot ever pointed there).  *Definitions.*  `chainOkAt`/`syncPath` = the export's σ-readable chain conjunct
  (`Xv6/AccessDiscipline.lean`, S4); `syncHop` (`MachCSL/ChainDefs.lean:171`) = three adjacent entries of a lock byte's history (held, release
  `0`, acquire nonzero); `isLk b a` (`:266`) = "`b` is a hop byte for an acquire at `a`"; `nameLockAt` (`MachCSL/Reserved.lean:236`) = the
  merged name-word window; `pipeLockAt` = the ruled `f->pipe` slot-history window; `lockWordDiscAt` (`AccessDiscipline.lean:104`) = the
  custody conjunct "lock words are written only by the lock code"; W11 = the Stage 2 item that consumes `chainOkAt` to prove robustness;
  "σ-readable" = decidable from the final memory trace without ghost state.  *Why it matters.*  The published theorem's chain conjunct is
  only as strong as its hop rule: a rule that accepts shapes RVWMO does not order makes `chainOkAt` TRUE for the wrong reason, and W11
  cannot pick the real chain out of an existential.  A reviewer of the paper will ask exactly "what stops a user page from being a lock".
  *Options.*  **(a″+shape) — the merged name window, hops restricted to WORD-sized entries** (RECOMMENDED for now; [R36.3]): what changes —
  `syncHop` gains the word-shape clause, `lockWordDiscAt`'s dynamic arm is windowed; FAITHFUL (restricts chains); kills the `kfree`/
  `initlock` shapes, NOT the user-forged word shape, which the export then leaves to W11 (≈ 0.3–0.5k there, from `custAt`/page tables);
  cost S ≈ 0.1k now; unblocks S2b at once; risk: a paper caveat "hop words are name-tagged lock-shaped words" until (a′-r).
  **(a′-r) — the ruled `f->pipe` window, made provable by a persistent entry receipt**: what changes — one MachCSL ghost `entryAt pa e`
  over the append-only histories, handed out by every store rule; `PipeBirth` passes the slot's entry to the lock handle; the hop request
  carries it; `isLk` = static ∨ `pipeLockAt` as RULED; FAITHFUL; excludes the user-forged shape σ-readably (file slots are kernel memory);
  cost S–M ≈ 0.2–0.4k MachCSL + the pipe files, one more cone rebuild; unblocks S4's clean statement; risk: the receipt ghost touches
  every store rule (the lane is serial anyway).  **(a″-s) — accept (a″) as the export's meaning**: FAITHFUL, cheapest (0), WEAKER in
  documentation only (the conjunct says "a chain of name-tagged lock-shaped word hops"); risk: the paper caveat above becomes permanent and
  W11 carries the exclusion.  **(c) exempt pipe bytes** — WEAKER, as in rev 38.  The coordinator may adopt (a″+shape) under the non-blocking
  rule and park (a′-r) as a named S4 option; the owner's ruling is wanted before S4 fixes the export's text.
