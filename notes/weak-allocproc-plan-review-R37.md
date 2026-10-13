VERDICT: SATISFIED

# Review R37 of `notes/weak-allocproc-plan.md` (rev 40)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite below was
read at the working-copy tip of `../xv6iris-weak` (plan rev 40, 5,461 lines), `~/dev/weak-orch/parked/PROGRESS-W8f2.md` (2026-10-13
stop, 97 lines), `~/dev/weak-orch/parked/w8f2-s2b-wip/` (9 files), `~/dev/weak-orch/allocproc_W8f2_cont_prompt.txt` (8 lines) and
`~/dev/xv6-riscv/kernel/{kalloc,spinlock,pipe}.c`.  Scope per the R37 brief (narrow): rev 40's application of [R36.1]–[R36.4] and
[R36.s1]–[R36.s6], the M2 CLOSE DONE record, and whether **RELAUNCH 2 (W8 (f2-ctx))** is executable as written against the tip +
PROGRESS + the parked WIP.  Items (a)/(b)/(d) of the standing brief were settled in R1–R36 and are not re-opened; rev 40 changes no
root, no statement and no memory-model text.

**Sign-off.**  YES — I would launch the W8 (f2-ctx) worker on RELAUNCH 2 as written.  Every substantive decision it carries checks
out against the code: the `pipeLockNameStr` constant IS wrong and the fix IS `"pipe"` at `0x800075c0`; the word-shape fix IS sound
and has a discharge path (the lock invariant's `WordHist 4` projects every word store to four same-timestamp byte entries); the F-B
guard `j ≠ w` IS the right one; F-C's rows are stated as invariants with the (ii) fallback sized; the S2b WIP exists, is a strict
superset of the tip's nine files and has no `sorry`.  What remains is REFERENCE/COST accuracy in the brief text — five suggestions,
two of which ([R37.s1], [R37.s2]) I would apply when the worker prompt is cut, because the worker will otherwise look for a section
that does not exist and type a Lean name that does not elaborate.  Neither changes what is built; no required change.

## What was checked and holds

- **R36 applied correctly.**  [R36.1]: header `:3-37` (rev 40 status, "STOPPED GREEN", RELAUNCH 2, Q-F2-PIPEHOP-2), `:63` (the
  RUNNING clause tagged with the rev-40 outcome), `:1827-1828` (the §C W8 heading), **RESULTS (rev 40)** `:1912-1948` (S1′ / S2-pre
  file:line record, D1–D4, F-A–F-D, per-row table, the parked path with the stale-`claude-notes/` note), **RELAUNCH 2** `:1949-1987`,
  the rev-38 RELAUNCH re-labelled as the BASE TEXT `:1988-1990`, WAITS (rev 40) `:2042-2047`, history line `:526` ✓.  [R36.2]: the
  S0 (i) fix `:1952-1956`, the §D *Definitions* sentence `:4386-4389`, the acceptance item `:1977-1978` ✓.  [R36.3]: S0 (ii) `:1956-1962`,
  the (a″) paragraph in Q-F2-PIPEHOP `:4416-4433` (shape fix, windowed `lockRegionOk`, honest limit, the release-site sentence
  rewritten `:4414-4416`), the S4 sentence `:1975-1977` and `:2023` ✓.  [R36.4]: `:1963-1973` ((C′)/(D′)/(E) stated, the token "ONE per
  park event; the next park takes it over", the fractional epoch token, per-transition obligations, the (ii) switch rule), the size
  line `:1979-1983`, §C W8 (2) `:1845-1846` ✓.  Suggestions: [R36.s1] `:2053-2062` (DONE; the rev-39 record kept with its two
  mis-cites named) ✓; [R36.s2] `:1499` ✓; [R36.s3] `:2099-2100`, `:2122` ✓; [R36.s4] `:1961-1962` ✓; [R36.s5] `:2059-2061` (housekeeping,
  next `tools/` touch) ✓; [R36.s6] `:1950-1951` ✓.
- **M2 CLOSE DONE — honest.**  `tools/ci/roots-weak.txt:25 Weak.srvwmoXv6M2` with the gloss as specified; `tools/audit/
  baseline-weak.json:163 "Weak.srvwmoXv6M2"` after `M1Core :137` / `M1 :150`, `comment :12-13` added, the module list `:3` names both
  `Weak.SrvwmoXv6Adequacy` and `Weak.SailCycleOrderCycle`; 13 roots ↔ 13 baseline names (the `lint.sh` agreement check, not run here);
  `tools/ci/audit.sh:49,56` unchanged (both lists end `…SrvwmoXv6Adequacy,SailCycleOrderCycle`; the optional core NOT registered);
  headers `PfRunUnpinned.lean:55` "M2 CLOSED: registered as `Weak.srvwmoXv6M2`", `SailCycleOrderCycle.lean:176-178` "registered (M2
  CLOSE …)", `MachOfPf.lean:73-77` and `SrvwmoXv6Adequacy.lean:18-21` "proved: `sailCycleOrder_holds`" ✓.  Stage 1b CLOSED is the
  right reading; "INTERNAL, NOT published [OWN.2]" kept ✓.
- **[R36.2]'s arithmetic re-done independently.**  `KA.«pipealloc» = 0x8000460a` (`KernelImage.lean:17864`); `+0x48 = 0x80004652` is
  the `auipc a1,0x3` (`:13326-13327`); the next word `0xf6e58593` (`:13328-13329`) is `addi a1,a1,-146` (imm `0xf6e` = −146); so a1 =
  `0x80004652 + 0x3000 − 146 = 0x800075c0 = KernelStr.«pipe»` (`:18120-18121`).  The tip's `+ 222` (`Xv6/KernelRsv.lean:104`) gives
  `0x80007730 = KernelStr.«digits»` (`:17905`, `:18152`).  The constant is wrong exactly as recorded; the docstring `:98-103`
  ("`addi a1,a1,222`") is wrong too.  **The tree ALREADY holds the tie the plan asks S0 to add**: `Xv6/ProofPipealloc.lean:487
  theorem pipealloc_br_2fb6 : KA.«pipealloc» + 0x2fb6#64 = KStr.«pipe» := by decide` (`0x2fb6 = 0x48 + 0x3000 − 146`) — see [R37.s2].
- **The word-shape fix (S0 (ii)) is sound and dischargeable.**  `syncHop :171-173` is pure byte shape; `memModel_chainHop
  (ChainCert.lean:173-180)` and `memModel_chainHopL :230` take `hb : σ.mem[b]? = some (⟨a,B,va⟩ :: ⟨r,A,0⟩ :: e0 :: H2)` and feed
  `syncHop_of_head (ChainDefs.lean:220-223)`; `memModel_hopIssue (WpAtomic.lean:1142-1152)` builds `hb` from `hopHead (Hs 0) A r`
  (`:608-609`, byte 0 only) and `hb0`.  The AMO's accessor holds ALL `n` histories (`histBytes pa n … Hs`, `:657-669`), and the lock
  invariant's `WordHist 4` projects each word entry to four byte entries with the SAME `t` (`WordHistDefs.lean` `WEnt.proj`,
  `WordHist.hist W Hold j = W.map (WEnt.proj j) ++ Hold j`; the minted `initlock` zero sits in `Hold` at one position `lo`, `tailOk`),
  so "`wordEntAt` for `a`, `r` and the held entry, discharged from `WordHist 4`" is right: the acquire entry comes from the store's own
  `pushed Hs t`, the release and the held (an earlier AMO) from `W`.  xv6 side: `kfree` = `memset(pa, 1, PGSIZE)` (`kalloc.c:55`), the
  image's `memset` loop is `sb a1,0(a5)` (`KernelImage.lean:2402 0x00b78023`; `ProofMemset.lean:99`), so the junk is one byte per
  timestamp; `initlock` stores `lk->name` BEFORE `lk->locked = 0` (`spinlock.c:16-17`), so the creator's zero sits over `kalloc`'s
  byte-sized `5`s; `kfree`'s only word-sized store to the first 8 bytes (`r->next`, an `sd`, low byte 0 since pages are 4 KiB-aligned)
  comes AFTER the memset has junked the name word, so `nameLockAt` is false there and the entry under it is a byte-sized `1` — the
  shape clause excludes every junk-derived hop, as R36 said.  The user-forged word alternation stays as the recorded honest limit.
- **F-B's guard is the right one.**  `pubCover :288-290` opens with `h ≠ j`; `ChainEnv.ext :274-276`'s coherence clause is `X.isPub f w →
  j ≠ w → X.coh j f ≤ Y.coh j f`, and `pubCover_mono :292-297` uses it with `h` as the writer.  After the arm `(h = w ∧ t < r) ∨ ∃ a < r,
  hopChain X.m X.isLk h t w a` the writer is `w`, so `j ≠ w` is what `pubCover_mono` needs; `hopChain_mono :191-197` gives the arm's
  monotonicity (memExt + `isLk` growth) ✓.  RVWMO reading as in R36 ✓.
- **F-C's cites and counts.**  `boxRows` `CtxBox.lean:1117-1121` (rows (C)/(D) over the scalar `T`), `ctxDeposit :156-162` (`max T (max K
  W)`), `boxRefDecr :1617` (`td := max td (maxStamp mD)`) ✓; 27 `Xv6/` files match `reference γ|unitStamp|maxStamp|slotdHalf|slotpHalf`,
  60 mentions of `unitStamp|maxStamp` ✓.
- **The parked S2b WIP is what the brief says.**  `w8f2-s2b-wip/`: `Ctx` (966 vs tip 961), `CtxBoot` (100/85), `CtxKeyMint` (104/96),
  `CtxLaws` (1,449/951), `Lock` (1,431/1,239: `lockRec :546`, `lockPay :560`, `lockRec_hopReq :625`, `lkName :911` in the dynamic body
  `:926`, `gateFloor curCtx` at creation `:1198,1305`), `LockBornHook` (224/200), `LockPayIff` (96/95), `Wp` (2,143/2,134), `WpLock`
  (3,617/3,547); no `sorry`/`admit`; the imports are the tip's.  The S2a dir `w8f2-s2-wip/` holds the five context files only — S2b is the
  superset, "AUTHORITATIVE" is right.
- **Q-F2-PIPEHOP-2 (`:4321-4366`) meets the owner-question standard**: Spec FIRST (RVWMO PPO 4–7 + load-value axiom, Sail `execute_AMO`
  `:18663` / `effective_fence_set :18299-18313`, Zifencei silent, PMAs `MainMemory`), plain language, three concrete examples (the real
  hop, `kfree`'s junk, the user page, the birth zero), every internal name defined, why it matters, four options each marked
  FAITHFUL/WEAKER with what changes, cost, unblocks, risk ✓.  Q-F2-PIPEHOP and Q-F2-BOOTGATE unchanged from R35/R36 ✓.

## REQUIRED changes

None.

## SUGGESTIONS (apply [R37.s1]–[R37.s2] when the worker prompt is cut)

- **[R37.s1] RELAUNCH 2 binds a PROGRESS section that no longer exists.**  `:1950` "`PROGRESS-W8f2.md` (its "Design", S1′ and S2-pre
  sections BINDING …)" and the base text `:1991` "(its "Design" section is BINDING for S2–S4)".  The parked `PROGRESS-W8f2.md` (the
  2026-10-13 rewrite) has the sections `Status`, `S1′`, `S2-pre`, `S2 lock layer — parked WIP`, `Findings`, `Per-row table`, `Deviations`
  — NO `Design`; no copy of the S2a-era file survives under `~/dev/weak-orch` (grep `## Design`: none), and the 8-line
  `allocproc_W8f2_cont_prompt.txt` never cited it.  Its content lives on in the plan's own base text (`:1992-2001` "Resume: re-wire …
  `keyAt = (ctxFloor ∗ chainKey) ∨ dirty`, `ownCtxAt … ∗ chainTokAt` …; S2b … free arm = `ctxStamped ξL T V g` + the release record …")
  and in the WIP code.  Write: "`PROGRESS-W8f2.md` (its S1′, S2-pre and `S2 lock layer` sections BINDING; the S2–S4 design = the base
  text's *Resume*/S2b sentences below + the parked WIP, which supersede the overwritten rev-38 "Design" section)".
- **[R37.s2] `KS.«pipe»` is not a Lean name in this tree — the namespace is `MachCSL.KStr`; and the tie lemma already exists.**
  `KernelImage.lean:18657 namespace MachCSL.KStr` … `:18837 def «pipe» : BitVec 64` … `:18902 end MachCSL.KStr`; nothing defines `KS`
  (grep `abbrev KS|namespace KS|export`: none).  The plan writes `KS.«pipe»` at `:1953`, `:1955`, `:4381`, `:4418` and in the
  proposed `theorem pipeLockNameStr_eq : pipeLockNameStr = KS.«pipe» := rfl`.  Write `KStr.«pipe»` (visible from `Xv6/KernelRsv.lean`
  through `Xv6.Geom → Xv6.KernelImage`, `Geom.lean:15`, as `KA.«pipealloc»` already is), and replace the asked-for `rfl` lemma by a
  pointer to the EXISTING `Xv6/ProofPipealloc.lean:487 pipealloc_br_2fb6 : KA.«pipealloc» + 0x2fb6#64 = KStr.«pipe» := by decide` —
  the `pipealloc` proof's own computation of the `initlock` argument — so S0 (i) is: `def pipeLockNameStr : BitVec 64 := KStr.«pipe»`,
  the docstring `KernelRsv.lean:98-103` corrected to "`addi a1,a1,-146`", and `pipealloc_br_2fb6` cited as the tie.  The "image bytes at
  `KS.«pipe»` are `"pipe\0"`" fact: `bootImage` is `bootImageSealed.1` (`BootImage.lean:27,31`, an `opaque`), so it is stateable only
  through `BootImageSpec`'s `bootByte` (`:41-42`) — keep it as optional documentation ("if `bootByte` is `decide`-able at `.rodata`,
  else drop"), not as a deliverable.
- **[R37.s3] S0's cost line is wrong: it is a FULL cone rebuild, the lane's 4th, not "no cone rebuild beyond `KernelRsv`'s".**  `:1952`.
  S0 (ii) edits `MachCSL/ChainDefs.lean`, imported by `MachCSL/Resources.lean:50` (the state interpretation every `MachCSL/`, `Xv6/`
  and `Weak/` file sits on), plus `ChainCert.lean` and `WpAtomic.lean` (`hopHead :608`, `hopIn :623`, `memModel_hopIssue :1142` and its
  two call sites `:1275`, `:1338` must supply the four-byte shape — name them in S0's file list); and `Xv6/KernelRsv.lean` is imported
  by `Xv6/Image.lean`, `KernelMap.lean`, `AppIface.lean`, `BootRsv.lean`, `StartedInv.lean`, `AccessDiscipline.lean` — i.e. most of
  `Xv6/` anyway.  Write "S0 is one full cone rebuild (≈ 17.5 min per PROGRESS); 4 cone rebuilds remain (S0, S2, S3, S4)" at `:1952` and
  `:1984`, and in the Stage 2 preamble `:2090` (and `:1880`) "3–4" → "4".  Scheduling only; nothing else changes.
- **[R37.s4] `hopHead`'s docstring and `memModel_hopIssue`'s will be stale after S0.**  `WpAtomic.lean:606-609` ("headed by the release
  entry … over a nonzero entry") and `:1136-1141` describe byte-0 shape; S0 should restate them as "word-sized entries" together with
  `ChainDefs.lean:17-23` ([R36.s4]).  Also `KernelRsv.lean:98-103`'s "`[R35.1]`" tag should read "[R35.1]/[R36.2]".
- **[R37.s5] One cosmetic cite.**  `:1915` lists `valid :350` — correct (`ChainDefs.lean:350 def ChainCert.valid`); R36 had written `:351`.
  Nothing to change in the plan; noted so the next reviewer does not "fix" it back.

## Owner questions the plan is missing

None.  Q-F2-PIPEHOP-2 is the only open question and it is in the owner format (checked above); no new memory-model/ISA question
arises from rev 40 (S0's two fixes are proof-internal and FAITHFUL under every option of Q-F2-PIPEHOP-2 — the plan says so at
`:4365-4366`).  The coordinator's provisional (a″+shape) under the non-blocking rule is consistent with the owner's standing
instruction; the ruling is wanted before S4 fixes the export's text, as the plan states.
