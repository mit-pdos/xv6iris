VERDICT: NOT SATISFIED

# Review R23 of `notes/weak-allocproc-plan.md` (rev 26)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak`.  Scope per the R23 brief: verify rev 26's application of
R22's three required changes, then decide whether W-DISK and the W8-design spike are launchable as written.  Items
(a)/(b) of the standing brief were settled in R1–R22 and are spot-checked, not re-litigated.

**Sign-off.**  NO — two required changes, both S text, one revision.  **[R23.1]** is substantive and sits in the
W8-design brief: W8's class (i) ("bytes a hart OWNS — no foreign writer", fed by "(f3) … a function of `HEnt.tid` over
the byte's history given a STATIC ownership map") is FALSE for the 1,034 `PStack` sites it is said to cover — xv6's
process kernel stacks MIGRATE between harts at `swtch`, and the SC tree transfers `stackOwn` across harts in the
context payload (`Xv6/SpecSwtch.lean:35-58`, `Xv6/ProofSwtch.lean:140`, `MachCSL/KCtx.lean:256`); the brief must
name the dynamic owner (ownership handed off under `p->lock`) before the spike sizes W8 and answers the (β) question,
or it will size W8 on a fact the kill cannot use.  **[R23.2]** is an incomplete application of [R22.2]: the
UNSATISFIABLE rev-25 formula survives in two places, one of them inside W-DISK's binding MECHANISM text (`:1676`), the
other in §C W13 (M) (`:2086`), plus four "fabric MOVES" wordings.  W-DISK is launchable once [R23.2]'s one sentence in
its text is fixed (nothing in it instructs the worker wrongly, but it is binding text); W8-design is launchable once
[R23.1] is in its brief.  No owner question is needed (both are plan text in the sound direction; neither is a
memory-model question — see the last section).

## What was checked and holds

- **[R22.1] applied.**  §C W8-design carries deliverables (4) the FEEDING path (f1)/(f2)/(f3) with a COUNT and (5) the
  ROOT path (r1)/(r2) (`:2232-2247`); §C W8 makes "one cone rebuild" CONDITIONAL on (f2)/(f3) and records (f1) as the
  XL outcome re-opening [OWN.36] (`:2255-2258`); the FOUR SERIAL line says the same (`:1796`); D24 (`:3012-3017`) and
  §A(6) (`:271-273`, the (r1) "text unchanged, meaning strengthened" note) are updated.  The cites hold: `mmOk`
  (`MachCSL/Resources.lean:779`) inside `memModelAt :951-956` (`⌜mmOk σ⌝` at `:956`); `xv6TracePure`
  (`Xv6/SystemSlot.lean:135-136`) is `fsBootPure … ∧ (g.pow = true → mmOk g.m)`; the W3 twins are exactly 734 / 250 /
  196 / 580 / 35 lines (1,795 total); `Xv6/AccessDiscipline.lean` does not exist; `rhist :57`/`rmem :62`
  (`Weak/PfStepTsoMem.lean`); `wprotAt :1040`/`wlpAt :543`/`wlpAlt :699` (`Weak/WeakGhost.lean`); `lockWordByte :340`
  (`Weak/WeakRvwmoKillArms.lean`); `HEnt` has fields `t`, `tid`, `v` (`MachCSL/TsoMem.lean:74-77`); `procHeld` is the
  abbrev at `Xv6/SchedCtx.lean:1590` (of `procHeldAt :663`).  See [R23.1] for what (1)/(3)/(4) must ALSO say.
- **[R22.2] applied where it is load-bearing.**  The clause `(i, k) ∈ gfDev ↔ (gisIo (i, k) = true ∨ dvi k ≠ dvo k)`
  is in §A(†) (`:375-391`), §A(6)'s reworded trusted-surface sentence (`:268-270`), §C W-DISK (M4) (`:1450-1453`) and
  (iv) (`:1681-1686`), §C W13 (I) (`:2096-2099`), W-DISK-Q2 (`:2577-2580`, `:2596`), Status (`:2318-2321`), §B(11) (vi)
  (`:936-938`) and the new §D Q-GFDEV-delta (`:2368-2407`, REPORT level, in the 2026-10-10 format: Spec first, plain
  language, tiny example, definitions, why it matters, options marked and costed).  The code facts behind it hold at
  the tip: UART `read` returns `some (lsr u, u)` for LSR (`MachCSL/Dev/Uart.lean:120`; IER/LCR/MCR/MSR/SCR likewise,
  only RBR with a non-empty FIFO and ISR with THRI move); `Virtio.write` answers `offQueueNotify` with `some v`
  (`Virtio.lean:310`); `readN` returns `(…, v)` unchanged (`:337-339`); PLIC prio/pending/enable/threshold reads return
  `p` unchanged, only the claim moves (`Plic.lean:123-136`).  `completeOk` (`Virtio.lean:412-416`) is
  `taken = some h && (wce || !reqCached)` for OUT, `cache.isEmpty` for FLUSH, `true` otherwise — so "TRUE after
  `drainAll`" (`:1609-1610`) is right, and `complete :423-426` frees the latch.  `gisIo` is `lbIsIo` of the event's
  label (`GraphFabResidue.lean:67-70`).  See [R23.2] for the two leftovers and [R23.s1] for a wording point about
  `hemitf`'s endpoints.
- **[R22.3] applied.**  The authority line (`:466-476`) matches the tip of `MachCSL/Lang.lean` (719 lines):
  `MState.afterLoad :128`, `store :151`, `fence :161`, `storeDma :181-183`, `storeDma_zero :186`, `storeDma_of_ne
  :191`, `anyReserve :212`, `dmaView :218`, `setDev :222`, `bootShape :336`, `blockedStep :431` (arms `:433-436`),
  `hartStep :533` (`.pure` `:535`), `devOpStep :560`, the `dmaWrite` arm's `anyReserve` guard `:572` and skip disjunct
  `:574`, `devBlocked :590` (`.step` arm `:592`), `devStep :604` (root restart `:609`, done-marking `:610-612`, `.op`
  step `:614`, blocked `:615`), `primStep :632`, `primStep_power_on :715`.  Two numbers are off by one (`dmaRead` is
  `:568`, the `dmaWrite` arm starts at `:569`) — [R23.s3].  The binding W-DISK cites (`Lang.lean:574` at `:1406`,
  `:1499`, `:1556`, `:1562`; `:570-574` at `:1622`; `devBlocked :592`/`devStep :615` at `:1376`, `:1391`, `:1560`,
  `:1567`, `:1577`; `:609`/`:610-612` at `:1403`, `:1406`, `:1638`) and the W-RSV `hartStep .pure :535`/`:533-538`
  (`:1888`, `:1891`) are the tip's.  Also confirmed against the code: for a `DevM.guard` whose `g s = none` the `.step`
  arm of `devBlocked` is VACUOUSLY true (no `s'` with `g s = some`), so the only enabled transition is the `:615`
  self-loop — the plan's "blocked arm = a stutter the schedule never needs, `devBlocked` vacuous for `g = none`"
  (`:1567-1568`) reads the code correctly; for `.dmaWrite` with `g = none`, `devBlocked` needs `(g s).isSome`, so the
  task is NOT blocked and takes the `:574` skip — the plan's SKIP-and-continue twin [R16.1-alt] is right.
- **R22's suggestions adopted.**  `simWire :1295-1354` (`:1317`; `hdev` consumed at `:1353`); `pdevEvFalse`'s proof is
  `cases l` (`WeakRvwmoSupply.lean:164-167`), recorded at `:1649-1650` as a NEW proof; W5 CORE's instantiations
  (`:1765-1769`); the "moves the fabric?" column (`:1739-1741`); §B(11) (vi) (`:936-938`).
- **W-DISK's MECHANISM against `serve`/`body` at the tip** (`MachCSL/Dev/Virtio.lean`, 600 lines): `get :522`,
  `setPhase .fetched :526`, OUT: `guard taken :529` then `capture :530` (`capture :515-518`: `dmaRead :516`, the fused
  `cacheReq ∘ setPhase .served` `modify :517-518`); IN: `fill :533` (`fill :488-492`: `get :489`, `dmaWriteIf … r.buf n
  :491`) then `setPhase .served :534`; status `dmaWriteIf :536`, `setPhase .status :537`, gate `:539-541`, `get
  :542-544`, used element `:546-548`, `dmaWriteStep … complete :552-554`; `body :558-587` (`chooseLt 3 :559`, `get
  :561`, `dma16`s `:563`/`:565`, `get :567`, guard-pop `:576-578`, `fork :579`, drains `:582-586`); `reset :260-262`
  clears `cfg`, `isr`, `seen`, `inflight`, `usedIdx`, `cache`, `taken` and keeps `disk`/`cap` (the plan's "`cache :=
  []` on BOTH sides" and "`inflight := []`, `taken := none`" at a reset are right); `reqOf :454` = `(phase v h).bind
  VPhase.req` with `phase :247` = `alistGet v.inflight h`; `alistSet :233`, `alistDel :236`, `cacheReq :496`,
  `reqSectorLen :371`, `statusOf :377`, `usedLen :382`, `pushOk :419`, `drain :429-432`, `stall :457`, `deviceFeatures
  :100`.  `DevM.guard :125`, `dmaWriteIf :157`, `dmaWriteStep :163` (`MachCSL/Dev/DevLang.lean`).  `pdiskProg`
  (`WeakEvInst.lean:485-516`: START `:488` requires `dp = none` and keeps `d' = d`; `DRead :491-494`; `DWrite
  :497-500` with `LStore false (paZ pa) bs [] []`; `DFence :503`; COMMIT `:505-508`; `DWild :510-511`; `DRet DIdle
  :514`), `pdiskUart :518-524`, `pstepDisk :526`, the label-only `pdevEv :544-547`, `pdevEvOk :1694`,
  `pdiskProgDevFree :1670`, `pstepDiskDevFree :1686`, `pdiskProgLatFree :1400`, `pdiskProgTsLoad :1423`;
  `VirtioProg.lean` (979 lines): `virtioProg :606`, `dreadData :358`/`dwriteData :363`, `dreadAvailIdx :375`,
  `dreadDesc :381`, the two 4-byte used writes `:586-589` (`dusedTail`, with the `DFence` before the idx write),
  `runVirtioProg :664`, the Rocq-model fragment `:224-317`, `:751-895`, `dmWfDwriteData :919`; `WeakEvLang.lean`
  (`DmWildChain :914`, `ediskStep :927`, DWild arm `:956-958`, `ediskStepWf :1324`, `eprimStepDiskReducible :1347`,
  `:1359`); `WeakEvCapstone.lean:651-653, :936, :1052, :1183`; `WeakRvwmoFab.lean` (`lbIsdev :119`, `emDev :144`,
  `isDevBlock :152`, `hemitf :239-262`, `hemitfStatesQ :347`, `hartConffStatesQ :471`, `Gfexec :517`/`gfDev :520`,
  `gfexecConf :524-536` with the `isDevBlock` clause `:533` and the endpoint clause `:534`, `gfexecConfOfQconf :649`,
  `supplyOfFconf :690`, `fconfRowsPin :786`); `WeakRvwmoSupply.lean` (`pdevEvFalse :164`, `pstepEvDevfree :169`,
  `admRunDevfree :175`, `hemitDevfreeConst :202`, `hemitDevfreeRefab :241`, `emDevfree :284`, `emFetchImg :288`,
  `gdexecQconf :292`); `WeakRvwmoLin2.lean` (`fconfSupply' :997`, `fconfTraceRealize :1014`); `WeakRvwmoFabInd.lean`
  (`fconfRealize :413`); `WeakRvwmoCapstone.lean` (`xboot :90`, `xN :94`; `xv6RvwmoSafeModuloF` is `:228`, see
  [R23.s3]); `pdevOk` (`WeakPromiseFact.lean:613-614`); `pfDWriteRowMem :669`/`rowDiskWrite :797`.  The `fill` data
  is computed from the `get :489` state while the guard is evaluated at the write — the plan's "evaluated at the
  write's own `pre`-state" is sound because `cacheView` is invariant under a root-loop `drain` (cache → disk keeps the
  overlay) and a reset between `:489` and `:491` empties `inflight`, so the guard fails on both sides.
- **W5 CORE / MachOfPf.**  `SimRel :305` (`dev :315`), `Hyps :620` (`tso :622`, `safe :623`, `cut :625`, `fi :635`,
  `disk :644`), `simDev :1193` (`devStepOfFdev … hdev.symm` at `:1253`, `:1266`), `simWire :1295`, `simRun :1497`,
  `machRunOfPfRun :1535`, `winPristine :1559`, `cutOfPristine :1588`; header deviation 3 "its owner is OPEN" at
  `:58-60` (W5 CORE corrects it to [OWN.35], `:1780`).
- **(a)/(b) spot checks.**  `tools/audit/baseline.json:11-14` lists the three opaques; `roots.txt:6` and `:19` are
  `xv6FsAdequacy_closed` and `xv6TextAdequacy_closed`.  §0 F1's sRVWMO description is unchanged from R21/R22's check.

## REQUIRED changes

- **[R23.1] W8-design's class (i) presumes a STATIC owner; xv6's kernel stacks have a DYNAMIC one.  The brief must say
  so before the spike sizes W8 and answers the (β) question.**
  *What is wrong (evidence).*  §C W8 states (i) as "bytes a hart OWNS — no foreign writer (covers `PStack`/`PPerCpu`,
  the 58 `own = true` witnesses…)" (`:2249-2250`), §B(9d) classes "`PStack`/`PPerCpu` (1,037) and the 58 `own = true`
  witnesses = W8's ownership (i)" (`:663-664`), and W8-design's (f3) reads "derived from `σ` alone for (i) ('no
  foreign writer' is a function of `HEnt.tid` over the byte's history given a static ownership map — the (β)
  question)" (`:2239-2240`); the pin checker's own gloss is the same ("[PStack]/[PPerCpu] are the no-other-writer
  cases", `Weak/KernelPinsDef.lean:33`; "`[sp]` addresses the hart's own frame", `:89`).  But a process's kernel
  stack (`p->kstack`, `Xv6/SpecProcinit.lean:66` `kstackVa`) is written by WHICHEVER hart runs the process:
  `scheduler` on hart B `swtch`es into a context last run on hart A, and the SC tree models exactly that — `wp_swtch_body`
  resumes under `∀ (h : CPU) … kctx h … -∗ … wpLoop h` (`Xv6/SpecSwtch.lean:35-58`), the stack cells travel in the
  context payload (`ProofSwtch.lean:140`: `ctxCells newc … ∗ stackOwn w1 av`), and `stackOwn` is `DFrac.own 1` per
  word (`MachCSL/KCtx.lean:256-257`), i.e. EXCLUSIVE ownership that CHANGES HANDS.  Over a byte's `HEnt.tid` history
  the writers are several harts; "no foreign writer" is false, and no static map recovers it.  What is true is "no
  foreign writer SINCE the last handoff", where the handoff is `p->lock`'s release (by A's scheduler after its `swtch`
  returns) → acquire (by B's scheduler before its `swtch`) — a LOCK-PROTECTED TRANSFER, (ii)-shaped with a dynamic
  owner, not (i)-shaped.  Only `PPerCpu` (`cpus[tp]`) and the fixed per-hart boot/scheduler stacks (`stack0`; `main`
  → `scheduler` never returns, so scheduler-context code runs on hart `c`'s own stack forever) are statically owned.
  The target function runs on BOTH kinds (hart 0's boot stack in `userinit`, the caller's `p->kstack` in `fork`).
  Consequences if left as is: the spike may answer (3) "(β) covers (i)" and (4) "(f3) for (i), no `Xv6/` sites", W8's
  export (i) is then stated in a form W11's kill cannot use on `PStack` segments (the cross-hart edge INTO a stack read
  comes from the previous owner's writes, killed only through the `p->lock` handoff), and [OWN.36]'s "one rebuild"
  sizing is wrong in the other direction.
  *Exact change (§C W8-design `:2225-2247`; §C W8 (i) `:2249-2250`; §B(9d) `:663-664`; D24 `:3012-3017`).*  (1) the
  export skeleton for (i) carries a PER-BYTE OWNER that changes at HANDOFF events — "every write to the byte since the
  last handoff is by the current owner; a handoff is `swtch` under `p->lock` (release by the old hart's scheduler,
  acquire by the new one's)" — or classes process-context `PStack` sites under (ii) with `p->lock` as the protecting
  lock ACROSS the handoff (the access itself is made with the lock released, so `wprotAt`/`wlpAt`'s "held" shape must
  be checked for fit — a third shape "owned since the lock handoff" is the likely answer); (3)/(4): (f3) "derived from
  `σ` alone" can cover only `PPerCpu` and the fixed per-hart stacks; the spike COUNTS the 1,034 `PStack` sites by
  context (scheduler/boot stack vs `p->kstack`, via the pin table's pcs) and names the handoff's "doors" (`procHeld`
  `Xv6/SchedCtx.lean:1590`, `stackOwn` `MachCSL/KCtx.lean:256`, the `swtch` payload `Xv6/SpecSwtch.lean:35-58`) as
  the (f2) wrapper layers; §B(9d)/§C W8 (i): "no foreign writer since the last ownership handoff" in place of "no
  foreign writer".  S text.  Not a memory-model question (every option FAITHFUL; the published statement is unchanged;
  what changes is the SHAPE of an internal export and W8's size), so no owner question.
- **[R23.2] The UNSATISFIABLE rev-25 `gfDev` formula survives in W-DISK's binding text and in §C W13 (M).**
  *What is wrong (evidence).*  §C W-DISK (ii)(c) (`:1676`): "until (I) replaces `isDevBlock` by the endpoint criterion
  `(i,k) ∈ gfDev ↔ dvi k ≠ dvo k` and DELETES clause (a)" — the criterion WITHOUT the `gisIo` disjunct, which [R22.2]
  showed excludes every non-moving MMIO access (LSR polls, NOTIFY) from `gfDev` while (R3) and `gfIoDev`'s
  I/O-by-class reading need them in.  §C W13 (M) (`:2086-2087`): "(I) RESTATES it per [OWN.31] as `(i,k) ∈ gfDev ↔ dvi k
  ≠ dvo k` ∧ `gisIo → gfDev`" — the exact rev-25 conjunction R22 proved unsatisfiable for xv6 (an LSR read is `gisIo`,
  hence "must" move, and moves nothing).  Both contradict §A(†) `:375-391`, (iv) `:1682`, (I) `:2097`.  Wording
  leftovers that still say "fabric MOVES" where the set is now "I/O-class by CLASS plus fabric-moving stores": `:375`
  ("lists the FABRIC MOVES in fabric order — `(i,k) ∈ gfDev ↔ (gisIo … ∨ …)`"), `:1457` ("`gfDev` lists FABRIC MOVES"),
  `:2336` ("`gfDev` = FABRIC MOVES [OWN.31]"), Q3's definitions `:2614` ("row items that MOVE the fabric"); and Q3 (b)
  `:2631-2632` records the needed weakening as "`gisIo ∧ dvi ≠ dvo ↔ gfDev`" — under (b) too the right form is the
  DISJUNCTION (a pure-read `dev` event is a member by class).
  *Exact change.*  `:1676`: "the endpoint criterion `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` (§A(†))";
  `:2086-2087`: "(I) RESTATES it per [OWN.31][R22.2] as `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` —
  I/O-class by CLASS plus every fabric-moving row item (§A(†))"; `:375`, `:1457`, `:2336`, `:2614`: "fabric
  TRANSACTIONS (I/O-class events by class, plus fabric-moving stores)"; `:2632`: "`(gisIo ∨ dvi ≠ dvo) ↔ gfDev` — the
  form (a) now carries anyway".  S text; W-DISK's brief is otherwise launchable.

## SUGGESTIONS

- **[R23.s1] `hemitf`'s endpoints bracket the ADMIN BLOCK and the event.**  `HFone` is `admRun true p (dvi k) ls pa da
  → hlblRealizes … → pstepEv pa da l p' (dvo k)` (`WeakRvwmoFab.lean:242-247`; `HFpair` likewise `:248-259`), so
  `dvi k ≠ dvo k` says "the block (admin run + tagged step) moved", not "the step moved".  §A(†) `:379` ("every
  non-I/O item whose step moves the fabric") and (I) `:2098` should say BLOCK.  The reachable case: an (α) ABORT
  (`LSilent`, `dp' = none`, fabric moved by `pre`) is followed by START, whose own step keeps `d' = d`
  (`WeakEvInst.lean:488`) — START is a member by class and its endpoints then DIFFER (`fab (n+1) ≠ fab n` at that START),
  so the sentence "at a non-moving member `fab (n+1) = fab n`" needs "unless its admin block moved".  Own-guard SKIPs
  with `pre` moves are unreachable (after `pre`'s `setPhase`, `reqOf s h = some r` holds), so no non-I/O item gets a
  member status from an admin move.  S text for (I)'s brief; nothing for W-DISK.
- **[R23.s2] W-DISK bookkeeping: the FLUSH/unknown-type request and the pf-only `DFence`.**  `serve` takes `pure ()`
  then `setPhase .served :534` for a non-IN, non-OUT type (`Virtio.lean:531-534`), so such a request has NO data node
  and its status write's `pre` carries `:526` and `:534` — 1 → 3; `completeOk`'s FLUSH arm (`cache.isEmpty`) is true
  after `drainAll`.  xv6 never issues one, but F9's standard is "no driver fact", so list the row beside "IN 1 → 5 / OUT
  1 → 5" (`:1400-1402`, `:1521-1527`).  The pf `DFence` before the idx write (`dusedTail`, `VirtioProg.lean:586-589`;
  (M4) `:1454-1456`) has NO `serve` counterpart (`:546` → `:552` directly) — name it in the "Deviations from `serve`"
  header line (`:1737-1739`) as the one pf-only node (0 MachCSL steps), since §A(†)'s "(R1)'s disk use … ordered by the
  device-side `DFence` (rule 4)" rests on it.
- **[R23.s3] Cite drift.**  `Lang.lean`: `dmaRead :568`, the `dmaWrite` arm `:569-574` (`:470`); `xv6RvwmoSafeModuloF
  :228` (`:1669`, `:1732`); `cacheView :359` (`:1477`); the `DRead` arm is `WeakEvInst.lean:491-494` (`:203` says
  `:489`, which is START); `Gfexec :517`/`gfDev :520` (`:375`, `:473`); `supplyOfFconf :690`; `hemitfStatesQ :347`;
  `simDev :1193` (the plan cites only its `:1253`/`:1266` uses — fine, but name the theorem).
- **[R23.s4] W8-design: name the doors.**  `procHeld` is the abbrev `Xv6/SchedCtx.lean:1590` of `procHeldAt :663`;
  `stackOwn` `MachCSL/KCtx.lean:256`; the handoff `wp_swtch_body` `Xv6/SpecSwtch.lean:35-58`.  One line each saves the
  spike a search and makes (f2)'s count checkable.
- **[R23.s5] W-DISK acceptance "`grep DWild Weak/` empty".**  Header prose mentions `DWild` (`WeakEvInst.lean:33`,
  `VirtioProg.lean:48,74-76,148`); say "no `DWild` constructor, arm or lemma; header prose rewritten", or the grep
  will fail on comments.

## Owner questions the plan is missing

None.  [R23.1] is not a memory-model question: RVWMO, riscv.cat, the Sail model in this tree, Zifencei and the PMAs say
nothing about how a proof states ownership of kernel-stack bytes (per the OWNER RULE: silent); every form of the export
is FAITHFUL (the published quantifier and conclusions are unchanged — what changes is an INTERNAL export's shape and W8's
size, which [OWN.36] already lets the spike re-open under the (f1) outcome).  It is plan text in the sound direction,
so it is REQUIRED of the plan, not put to the owner; if the spike finds that the handoff shape forces (f1) (an `Xv6/`
sweep), the plan's existing rule applies (re-open [OWN.36]).  [R23.2] is a text fix of an applied ruling.  The plan's
RULED questions keep their "Spec:" lines; Q-GFDEV-delta meets the 2026-10-10 format.
