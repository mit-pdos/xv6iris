VERDICT: SATISFIED

# Review R9 of `notes/weak-allocproc-plan.md` rev 11 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R8's four required changes and s1–s5 applied; (2) can the Stage 0 and Stage 1 work items (W3, W1,
W2 spike, W5b, W5c; W4, W5, W5d) be handed to workers AS WRITTEN — every cite a worker would follow re-checked;
(3) do the owner questions meet the OWNER RULE (spec reading FIRST, each option marked faithful / stronger /
weaker).  `file:line` cites `../xv6iris-weak`; Sail cites `model/Lean_RV64D/LeanRV64D/`.  Advisory only; no
proofs or builds; no git/jj; no subagents.

**Sign-off.**  Launch Stage 0 now (W3 serial first, then W2 spike ∥ W1 ∥ W5b ∥ W5c, per plan:773-778).  The two
REQUIRED items below are text fixes confined to §D's standing questions and to five file paths; neither changes a
statement, an acceptance gate or a dependency, so they are to be applied in rev 12 WHILE Stage 0 runs, not before
it.  Per [OWN.10] this verdict releases W5d-G's day-one merge of `GraphFetchSpike.lean` (plan:38-40).

## R8 application check

[R8.1] every OPEN semantics question D41, D45–D52 opens with "Spec:" and marks each option (plan:832-919; 14
"Spec:" lines); D48 (a) is now "WEAKER than the prose, Sail-FAITHFUL" and names D46 (b) as the prose-faithful form
(plan:863-869) ✓.  [R8.2] (a) one sequential device row named in "Machine-model choices" (plan:455-458); (b) the
(R1) list gains "EVERY RAM store po-before a PLIC pin delivery" and both lists gain the DMA-around-UART/PLIC
coupling (plan:443-448); (c) D49 (a′) with the realizability caveat (plan:876-879); D51 (plan:890-896) ✓.
[R8.3] §B(11b) opens with the appendix "I/O Ordering" and lists (c1)–(c5) + the FENCE and DEVICE sentences
(plan:468-480); (F6) carries the DEVICE sentence and `dmaView` as the stronger form (plan:495-499); §A(†) names
rule 5 over I/O as a strengthening condition (c1) excludes, subsumed by (R1), → D52 (plan:182-186); the FIOM clause
is in §A(†) (plan:178-181) ✓.  [R8.4] "~35 files (34 by arm-regex, 50 files mention the name)" (plan:686-687) —
re-measured this round: 34 / 50 exactly ✓.  s1 (plan:98-100), s2 (plan:13-14), s3 (W14, plan:730-733), s4 (D48 (b),
plan:868-869), s5 (plan:477-478) adopted ✓.

## What was verified for launchability (not to re-litigate)

**Header/F1**: `Allocproc` (`Xv6/LinkAllocproc.lean:14-16`), `allocproc_proof :3623-3639`, `allocprocPost
SpecAllocproc.lean:118`, `wp_allocproc_body :204-224` with exactly the premise list of §A(1) (`allocprocSlots = 48`,
`:52`); roots `tools/ci/roots.txt:6`, baseline axioms/opaques `baseline.json:11-14`; `LinkSyscall.lean:84`/
`LinkMain.lean:53`; `NCPU = 8` (`TsoMem.lean:54`), `cpus`/`powerFork` (`Lang.lean:315-320`); fences `fenceDrains`/
`fenceAcq` (`TsoMem.lean:356-364`: `rw,w`/`w,w`/`r,w` no-ops ✓); reservation blocking (`Lang.lean:366-378,395-403`),
`.aq` off-by-one (`:150`).  **W3**: `powerInterp_mmOk Adequacy.lean:481` → `xv6TraceHook SystemSlot.lean:590-612`
(sees `powerInterp` and `▷ xv6Slot` only, `:606-607`) → `xv6TracePure :135-136` → `xv6FsAdequacy_closed
LinkSystemAdequacyClosed.lean:20-26`; `imgByte Ctx.lean:433-436`, `kernelText KernelText.lean:30`,
`kernelText_intro BootCarve.lean:582`, `Wp.lean:1478,1490`, i-fetch arm `Lang.lean:360-362`, DMA `own 1`
`WpDma.lean:142-145`; `tools/ci/tcb.sh --update` and `tools/tcb/expected.json` exist.  **W1**: `xv6NiAdequacy
LinkNiAdequacy.lean:82-90`, `xv6NiPhi NiAdequacy.lean:91-92`, `NiClassLaw NiTrace.lean:660`, fork row `:646`,
`niOk NiLedger.lean:319-322`, `forkOk`/`usysForkAns UsysDet.lean:293-302`, `Pev PidEv.lean:50-55`, `nextOf :77`,
`cycAt :132`, `pidPick :136`, `cycAt_zero :158`, `cycAt_period :179`, `pidPick_spec :200` (no `pidPick_range` —
W1 proves it, as the plan says); `Kev KallocEv.lean:45-52`, `poolEmpty :72`.  **W2/W5b**: `wpPfStep
PromiseBridge.lean:339`, `PFStore :355-366`, `PFDev :392-396`, `PFIFetch :441-449`, `projLbl :529-545`; `primStep
Lang.lean:599`; `lbNobarex AxRealize.lean:97-103`, `lbAdmin :130-134`, `fetchPinIfetchOk :167-176`, `wpPfRunPinSub
:225`, `lblRealizes :240-243`, `lblRealizesPair :305-313`, `admStar :343-344`, `execProgOk' :373-386`,
`execWfPfRunProg :802-808`; `admRun Conf.lean:374-381`, `hemit :712-722`; `execProgOk'Snoc Cert.lean:413`
(+ `SnocPair`, `Cert3.lean:689`); NONE of the NEW names (plan:145-150) exists in any merged file ✓; WeakMem
`readable :400-402`, `fwdView :585-591`, `exloadPostRunD :834`, `fencePost :674-678,684,688`.  **W5c**:
`epsInit WeakEvCapstone.lean:1026-1027`, witness `ConfWit.lean:11-22`, `smC`… `Cert.lean:522-546`, `snocRdAdm
:257`, `esil WeakEvLift.lean:897`, `pevrunAdmRun Cert2.lean:180`, `ConfWit2.lean:26-28`, `gtraceSnocReadImage
Floor.lean:1025-1035`, `SpecMain.lean:6-15`, `KernelImage.lean:14-17`, `MachCSL/BootRun.lean` exists.  **W4/W5/
W5d**: `bootFacts`/`bootShape Lang.lean:294-304`, `wbootFacts WeakLang.lean:482-490`, `srvwmoConsistent
WeakAxiomatic3.lean:2073`, `srvwmoRealizable :2077`, `unionAdequacyClosed LinkUInitUnion.lean:163-164`,
`efetchItvOk WeakEvCapstone.lean:681-685`, `wpPfRtcEpfRtc :1008-1011`, `ifetchOk` use `WeakEvInst.lean:564`,
`itvPostMachCSL WeakInterp.lean:378-384`, `t2Ev WeakEvInst.lean:2046`.  **Stage 2 cites spot-checked** (all
correct): `gwf`/`gfenceCovers`/`gacqPo`/`gloadValue`/`grule14` (`Graph.lean:168-179,204-209,214-215,238-243,
257-258`), `rvwmoCatConsistentT AxDeps.lean:208-211`, `dstepT :461-463`, `rowDepsSubT :690`, `twCatT :876`/
`twNotCatForget :883`, `gppo1-3`/`grcsc AxGraphCat.lean:146-163`, `minusImpliesCat :274`, `hemitf Fab.lean:238-260`,
`Gfexec`/`gfexecConf :516-535`, `gdevAdj`/`gfexecConsistent :539-544`, `gfexecConfOfQconf :648`, `supplyOfFconf
:686-701`, `emDevfree`/`emFetchImg`/`gdexecQconf Supply.lean:273-289`, `ptraceRel Lin2.lean:124`,
`gtraceLinearizationMin :623`, `gfexecConsistent' :761-762`, `fconfSupply' :995`, `gnxw Lin.lean:440`, `gmsg
:461-468`, `linCand :471`, the W13 spike lemmas (`W13Spike.lean:35,55,66,83-95,109,116`), `KernelPins.lean:22-23`
census, `racyDSplit Glue.lean:103`, `segPinGmo :233`, `RunData :272`, `wpPackage :338`, `protReg :364-368`,
`badRun`/`noBadRun :384-391`, `l2ClaimAt :440-447`, `rawChainChain :453`, `walkSupply Glue2.lean:453`,
`cycleKillOfL2'' :521`, `t2linOfL2''' Walk3.lean:77`, `walkPolicy Walk.lean:897`, `wsegSupply Walk2.lean:453`,
`cycleKill LinInd.lean:155`, `lockWordByte`/`csChained KillArms.lean:340,499`, `gpow`/`racyD Acyc.lean:192-200`,
`hullOk Hull.lean:557-560`, `gdHull :714`, `retime Topo.lean:120`, `normalizeOfAcyclic :594`, `gvisUb Floor.lean:
100-101`, `greadSrcUb :442`, `finvStep :605,619`, `cyBackwardNotAq Cert4.lean:587`, Cert3 `:311,391,428,468`,
`violationHart WeakRobust.lean:100-107`, `clsOf`/`pubOf RobustMain.lean:390-400`, `robustMain :1520`, `Dlbl
AxDevGraph.lean:134-142`; Sail `execute_FENCE InstsEnd.lean:18299-18313` (+ `execute_FENCEI :18295-18297`),
`effective_fence_set BaseInsts.lean:568-573`, `PMA Defs.lean:549-566`, `bootPMA Platform.lean:199-239`
(`IOMemory`, non-idempotent), `menvcfg = 0 BootBoard.lean:30`; image words `KernelImage.lean:17301,17311,17441,
17451` = `0x0ff0000f`, NOTIFY `:17315` = `sw zero,80(a5)` (decoded), ACK `:17439`, `uartinitone` entry `:1515`,
`sb zero,1(a5)` `:1525` (decoded), `end :17935`; `ProofVirtioDiskIntr.lean:92-99`, `ProofRelease.lean:83-86`;
spike file sizes 399 / 145 / 226 ✓.  The three spike reports agree with §B(4)(iii), §B(9), §A(†) as cited.

## REQUIRED changes (both non-gating: rev 12, in parallel with Stage 0)

**[R9.1] Three STANDING semantics questions lack the OWNER RULE's "Spec:" line and marks — D19 (fused pairs /
reservations), D20 (`candSca`), D7 (W2's STOP suspects); and §B(10) overclaims "ISA-faithful" for `candSca`.**
Evidence: plan:926-927 (D7), plan:935-937 (D19, D20) carry (Rec)/(b)/(c) with no spec reading and no marks; the
plan's own rule text (plan:782-786) scopes "Spec:" to "every OPEN semantics question" and lists D41, D45–D52, but
D7/D19/D20 are un-RULED ("provisional" per [OWN.4]'s last line) and ARE memory-model questions; D19/D20 are
consumed by Stage-0 items (W5b defines `execProgOk'S` and `candSca`; W2's STOP rule names D7's suspects).
plan:399-400 says "The ISA guarantees single-copy atomicity for naturally aligned accesses ≤ XLEN, so the premise is
ISA-faithful" — `candSca` ranges over EVERY `LLoad`, alignment unchecked.  Change — prefix each with:
- **D19 Spec:** RVWMO chapter, atomicity axiom — constrains only PAIRED (successful) aligned LR/SC: no store from
  another hart to the byte between the LR's source and the SC in gmo; Zalrsc — the SC "succeeds only if the
  reservation is still valid"; a reservation is invalidated by another hart's store to the reservation set or the
  hart's own SC, and an implementation MAY invalidate it at any time (spurious failure allowed; only constrained
  loops are guaranteed eventual success); NOTHING says a live reservation blocks or delays other harts' stores.
  Sail in this tree — `load_reservation`/`cancel_reservation` are no-op stubs (`Xv6Extras.lean:65-68`);
  `match_reservation`/`valid_reservation` ARE the two opaques `xv6_resv_matches`/`xv6_resv_is_valid` (`:75-80`;
  both SC arms theorems, `Xv6/UserMemLrsc.lean:7-12`) — the ISA model is silent on reservation semantics; PMAs —
  RAM `reservability := RsrvEventual`, `atomic_support := AMOCASQ` (`Platform.lean`, RAM region), I/O `RsrvNone`.
  Marks: TsoMem's reservation serialisation (`Lang.lean:366-378,395-403`) — STRONGER than the spec (excludes the
  spec-allowed execution where a foreign store lands mid-pair and the SC fails), already named in F1; (Rec)
  `execProgOk'S` fused pairs — a quantifier RESTRICTION (executions with a dangling LR or a failing SC are outside
  the theorem; STRONGER as a premise, honestly named, D19/§B(11)); (b) MachCSL change so dangling reservations do
  not block — moves TsoMem TOWARD the spec (FAITHFUL direction), L, serial, re-opens whatever Xv6 proof consumes
  blocking (`MachCSL/UWait.lean:20-24` names `valid_reservation`; census unverified); (c) a user-mode fact —
  unavailable.  D17 (the SC-failure model) shares this Spec line.
- **D20 Spec:** RVWMO chapter "Memory Model Primitives" — a NATURALLY ALIGNED load/store of ≤ XLEN bytes is
  single-copy atomic; a misaligned access may be split into byte operations, not SCA; Sail in this tree — `mem_read`
  splits misaligned accesses via `split_misaligned` (`Mem.lean:414,511,547`; `SplitAccessUtils.lean:256`), RAM PMA
  `misaligned_exceptions.load_store := none` (no fault, so the split path IS reachable); TsoMem reads EVERY load's
  bytes at one `tvn` regardless of alignment (`Lang.lean:363-367`); the cat model's `gloadValue` gives one gmo
  position per load EVENT regardless of alignment (mixed-size N10, already "out of scope", plan:123).  Marks: (Rec)
  `candSca` over every `LLoad` — FAITHFUL for naturally aligned loads ≤ 8 bytes, STRONGER for misaligned ones
  (kernel loads are compiler-aligned — unverified as a census; user code may misalign); (b) atomicity axiom in
  sRVWMO — same mark, XL.  And change plan:399-400 to "ISA-faithful for naturally aligned accesses; a misaligned
  user load is covered by N10's out-of-scope note".
- **D7 Spec:** per suspect — (i) parked release fence: WeakMem's `fence rw,w` sets `wRelp` and the NEXT store
  publishes (`WeakMem.lean:684,634-647`), TsoMem's is a no-op (`TsoMem.lean:356-364`); RVWMO rule 4 makes it an
  ordering edge; TsoMem's no-op is sound only because sRVWMO rule 14 already puts `[M];po;[W]` in gmo — TsoMem
  STRONGER globally, WeakMem FAITHFUL at the fence; (ii) `wRes := none` at any non-trivial fence (`WeakMem.lean:688`)
  vs TsoMem keeping the reservation (`Lang.lean:155-163`): Zalrsc lets an implementation invalidate at any time and
  does not make FENCE cancel — BOTH FAITHFUL (the SC outcome is an opaque oracle on both sides); (iii) tearing —
  D20; (iv) `.aq` off-by-one: rule 5 orders the whole AMO before later accesses; a view at the WRITE's timestamp
  (TsoMem, `Lang.lean:150`) is STRONGER than at the READ's (WeakMem `:834`, FAITHFUL) — `R` carries `≤`.  Marks for
  the options: (Rec) change WeakMem's event instance toward MachCSL's shape — moves the pf machine to the STRONGER
  side; sound only where T1 (`srvwmoRealizable`) is re-established for the changed instance; (b) a MachCSL change —
  toward the FAITHFUL side, owner-gated, serial.  Costs after the marks (as today).

**[R9.2] Five cite paths a worker would follow do not resolve as written.**  Evidence: plan:209 "`BootSharedDev.
lean:283`" — the file is `Xv6/BootSharedDev.lean` (line ✓); plan:109-112 `Dev/Fabric.lean:122-123` and plan:789
`Dev/Fabric.lean:126`, plan:158/499 `Dev/DevLang.lean:20-21`, plan:534 `Dev/Uart.lean:88,132,184`, `Dev/Plic.lean:
85-93` — all live under `MachCSL/Dev/` (lines ✓; `devBound :125`, `devAddr :126`); plan:164 "`weak-memory-route-b.
md:1009-1020`" and plan:353 "`route-b.md:1456-1460`" — the file is `claude-notes/design/weak-memory-route-b.md`
(lines ✓); plan:375 "`projLbl :545`" in a `WeakAxRealize` context — the `LExLoad → LLoad` arm is `WeakPromiseBridge.
lean:543` (`:545` is the `LIFetch` arm); plan:250 cites `ifetchOk` at its USE (`WeakEvInst.lean:564`) — the
definition is `WeakPromise.lean:222-224`.  Change: fix the five paths/lines.

## SUGGESTIONS

- [R9.s1] W1: add `cycAt` (`Xv6/PidEv.lean:132`) beside the `cycAt_zero`/`cycAt_period` cites, since
  `pidPick_range` is proved from its codomain.
- [R9.s2] W5c: cite `WeakEvStarted.evX2` at `Weak/WeakEvStarted.lean:668`.
- [R9.s3] The header's "Spec:" claim (plan:7-8) should read "every OPEN or STANDING semantics question" once
  [R9.1] lands, so the rule's scope is visible.
- [R9.s4] W2's report (plan:584-587) could carry the faithful/stronger/weaker mark per label as a column of the
  per-label (↓) table — it is the natural place to record [R9.1]'s D7 marks against evidence.

## Owner questions the plan is missing

None new.  D7/D19/D20 need the Spec lines of [R9.1]; nothing else is un-asked for Stage 0–1.  For Stage 2 the open
set (D41–D43, D45–D52) is complete and now meets the OWNER RULE.
