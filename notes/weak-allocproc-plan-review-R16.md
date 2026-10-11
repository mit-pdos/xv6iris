VERDICT: NOT SATISFIED

# Review R16 of `notes/weak-allocproc-plan.md` rev 19 (adversarial, evidence-based; 2026-10-11)

Scope (per the R16 brief): rev 19 = rev 18 + Stage-1 RESULTS + [OWN.26]–[OWN.29] + the W4/W13 censuses + the NEW
W-DISK item + W-DISK-Q1/Q2.  Audited: (1) every DONE record against the landed Lean (line by line); (2) W-DISK's
(M1)–(M9), its file list, retire-vs-redo, sizing and sequencing; (3) W2 CLOSE and W4 F1–F8 as launch texts; (4) the
W13 census fold-in (addresses spot-checked against `Xv6/KernelImage.lean`); (5) W-DISK-Q1/Q2.  Mid-review the
coordinator relayed two NEW rulings — **[OWN.30] W-DISK-Q1 = (b)**, **[OWN.31] W-DISK-Q2 = (a)**
(`../weak-orch/allocproc_revise3_extra.txt`, last two lines) — treated as RULED below; the plan must record them.
`file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  NO — not as written.  W2 CLOSE and W4 F1–F8 are launchable modulo one seam ([R16.6]); the DONE
records are correct except that two items landed AFTER rev 19 was written and must be recorded ([R16.4]); the W13
census fold-in is faithful.  **W-DISK is NOT launchable as written**: its (M4) (a RAM `DWrite` that moves the
fabric, now RULED [OWN.31]) and (M9) (an `LSilent` node that READS the fabric) both contradict the tree's
fabric-marker invariant `pdevOk` — "a non-`LDev` step neither moves nor depends on the fabric" — which the T2
capstone and the realization chain consume ([R16.1]); and the plan's one line on the W13 cost ("no proof impact
beyond one more `gfDev` member kind") is understated.  The W-DISK-Q1 (b) item, if "folded into W-RSV's brief" as
§C suggests, DEADLOCKS M1 ([R16.3]).  One factual error about the image (xv6 DOES clear `VIRTIO_BLK_F_FLUSH`) and one
honesty gap (the device model's strengthenings vanish from §B(11) when the pf-drift entry is deleted) complete the
required list ([R16.5]).

## What was verified (holds as cited; not to re-litigate)

**(1) DONE records.**  `Weak/TsoShadow.lean` (996 lines): every cite in §A "Names" and §C W5b′ is exact —
`CohStamp :98`, `cohFoot :104`, `cohSrc :114`, `cohOff :128`, `ShSt :160`, `shTvn :190`, `ShFull :292`, `tsoRun
:326`, `tsoShadow :500`, `shadowOf :508`, `scaOkT :513`, `diskLatOk :523`, `execScaT/execDiskLat :527,534`,
`candScaT :540`, `candDiskLat :542`, `execProgOk'ST :559`, `pfStepFactsT :576`, `pfRunST :584`,
`execPrefixPfRunProgShapedT :660`, `:789`, `:808`, `g1NotScaT :879`, `g1NoRunT :890`, `g2ScaTSrc :925`, `g2RunT
:953`, `itvFenceI :990`, `itvSfence :992` ✓.  `Weak/PfStepTsoMem.lean` (781): `midPair :46`, `logAuthor :52`, `rhist
:57`, `rmem :62`, `histOfSnoc :207`, `histOfFind :250`, `histOfTop :330`, `histOfWriteBytes :400`, `rmemBoot :424`,
`resvOthersNone :464`, `pfLoadRowMem :540` … `pfFrameRowMem :762` ✓ (header deviations as the plan records).
`Weak/PfStepTsoView.lean` (807): `hartRel :127`, `viewRel :135`, `sameRead :139`, `StampOk :293`, `cohSrcOk :301`,
`shLoadSrcs :338`, `minView :517`, `minViewLeSca :524`, `rowLoad :603` … `rowDiskWrite :797` ✓; the (↓) TABLE with
the faithful/stronger/weaker column IS in the header (`:33-76`) — W2's acceptance [R9.s4] delivered ✓.
`Weak/GraphFetchSpike.lean` (339): `gwlog :100`, `gfcut :104`, `fetchCutOk :114`, `fetchCutOkLit :123`,
`fetchCutPrefix :146`, `fetchCutEdge :161`, `fetchRelOk :183`, `fetchRelCut :215`, `fetchCutRel :248`, `gzFetchCut
:264`, `gzContrib :272`, `gzFetch :278`, `emSlot :293`, `emSlotAdm :297`, `emZifencei :312`, `fetchPinCutOk :322` ✓.
`Xv6/AllocprocTrace.lean` (447): `pidHistWf_nextOf :129`, `pidPick_range :152`, `:161`, `pidPick_badHist :179`,
`badWord :184`, `pidHistWf_nodup :209`, `forkCite :260`, `forkStep :269`, `forkHist :318`, `foldLonger_spec :324`,
`forkCite_facts :343`, `forkHist_spec :367`, `allocprocTraceAns :402`, `forkPev_comparable :437` ✓.  W-COH:
`Hist.readEnt :127`, `read_eq_readEnt :130`, `readSrc :135` (plan :136), `readSrc_foreign_le :139`, `LoadSrcs :308`,
`FlatMem.loadSrcs :320`, `loadSrcs_stampAt_le :324`, `HRead.afterLoad :354` (per-byte `srcs : LoadSrcs`),
`HRead.resetCoh :361`; `MState.afterLoad` `Lang.lean:128-131`, `MState.store :149-155` (`clearAcq.resetCoh pa n`
at `:153`) ✓; the TsoMem header `:17-27` records the foreign-only stamp and the reset ✓.  `Weak/TsoOfPf.lean` (312):
`histOf :62`, `tsoAfterLoadCoh :179`, `g2TsoSched :251`, `m0 :270`, `g2OwnLog :272`, `fenceRow :303` ✓.  W13 (E):
`IoKind` `WeakMem.lean:110`, `Lbl.LIo` `WeakAxiomatic.lean:96`, `lbIsIo :184` (plan :186), `execStepNotIo :320` (plan
:318), `Wlabel.LDev` `WeakPromise.lean:89`, `projLbl .LDev = none` `WeakPromiseBridge.lean:538` ✓ (still `none`),
`unprojLbl :962` ✓, MMIO arms `WeakEvInst.lean:305,341`, `pstepPlic :470`, `pdiskProg` START `:488` / COMMIT `:506`
/ `DWild :509-511` / `pdiskUart :520` ✓.  `Weak.lean:622-629` imports all eight Stage-0/1 files ✓.  `Weak/PfStepTso.
lean`, `Weak/MachOfPf.lean`, `Weak/ExistWitness.lean` ABSENT ✓ (W2 CLOSE / W4 / W14 outputs).
**(a) `Xv6.Allocproc`**: `LinkAllocproc.lean:14-16` ✓; `wp_allocproc_body` `SpecAllocproc.lean:204-224` with exactly
§A(1)'s premises ✓; `roots.txt:6,19` ✓; `baseline.json:11-14` = 3 axioms + 3 opaques ✓.  **(b) TsoMem vs sRVWMO**:
the residue table `WeakAxiomatic3.lean:2054-2078` (1–5, 7, 14 IN; 6 OMITTED; 9-load OMITTED by D-8; 12 omitted), `def
srvwmoConsistent :2084`, `srvwmoRealizable :2088` (plan :2077 — drift); litmus divergences LB and reader-fence-only MP
`WeakSrvwmoLitmus.lean:1663-1695` ✓; nothing relates TsoMem to `srvwmoConsistent` (as the plan says) ✓.
**(4) W13 census fold-in**: every address the plan copied exists at the right instruction — `0x80000c74` =
`0x0cf4a7af` (`amoswap.w.aq`, `KernelImage.lean:2266`), `0x80000cf6` = `0x0310000f` (`fence rw,w`, `:2362`),
`0x80000ee6` = `0x0230000f` (`fence r,rw`, `:2748`), `0x80005d54`/`0x80005d66` = `0x0ff0000f` (`:17441,17451`),
`0x8000085e` = `c.j 0` (`panic`'s self-jump, `:1473`), `0x80000f7e` = `c.sw` (`started := 1`, `:2828`), `0x80000ee4` =
`c.lw` (`:2746`), LSR/THR/NOTIFY/ACK/STATUS/claim/complete pcs (`:1677,1687,1769,1827,1851,17315,17433,17439,16638,
16668`) ✓; the symbol table has `pr` size `0x18` (`:17921`), `started` (`:17915`), no `panicked`/`uartstart` ✓
(`notes/W13-io-census.md` b.4) — the §B(9)/(11) corrections are right.  `KernelPins.lean:255` `(0x80000c04,
PResidue)` ✓.  The (R1)/(R2)/(R3) omission lists in §B(11) match census §(c) items 1–7 ✓; R5's re-assessment matches
census b.0–b.3 ✓.
**(2) W-DISK facts**: `virtioProg :606-625` ✓ (two 4-byte used writes `dusedTail :586-589` with `r.len`; `vstatus
:557-559` UNSUPP for FLUSH; separate COMMIT `DRet (DDone (vdelta …))`, `vdelta :565-569` START-snapshot `seen+1`/
`usedIdx+1`; `dreadDesc :381-386` FOUR reads; `dreadAvailIdx :375-376` `aq = true`; data from `v.disk` `:597`) ✓;
MachCSL `usedLen :382` (`len+1`/`1`) ✓, `statusOf :377-379` ✓, `deviceFeatures :100` bit 9 ✓, `fetch :466-481`, `fill
:488-492` (`cacheView`), `capture :515-518`, `serve :521-555` (status `:536`, `pushed` guard `:539-541`, ONE 8-byte
used element `:546-548`, `dmaWriteStep … complete` `:552-555`), `body :558-587` (`chooseLt 3 :559`, guard-pop `:576-578`,
`fork :579`), `complete :423-427`, `completeOk :412-416`, `stall :457` ✓; `storeDma` `Lang.lean:171-173` appends for
ANY `n` ✓; `dmaWrite`'s no-op arm `:544` ✓; `DmWf.write … bs ≠ []` and `ediskStep`'s `bs ≠ []` (`WeakEvLang.lean:
338-343, 940`) ✓.  **Retire-vs-redo**: the §7–§8 equivalence theorems (`:664-895`) are consumed by NOTHING outside
`VirtioProg.lean` (grep) ✓; `virtioProgWf :952` IS consumed (`WeakEvLang.lean:1331`) ✓; `virtioProg` consumers =
`WeakEvLang.ediskStep :930`, `WeakEvDisk :372-380`, `WeakEvInst.pdiskProg :488`, `WeakEvCapstone :645,936` ✓.  (M8)'s
"`wce = false` for xv6" ✓ (`Xv6/ProofVirtioDiskInit.lean:559` `vdi_wce_15 … = false`).
**(3)** W2 CLOSE's E-M1–E-M4 texts match the census (`notes/W4-structural-census.md` §E) ✓; `evStep :355` ✓; `MState`'s
memory fields `mem log tv itv hr resv` ✓; W4's boot bridge: `bootFacts :298-303`, `bootShape :307-308`,
`primStep_power_on :686`, `powerFork :323` (`cpus.map (Loop 0) ++ DevId.all.map (DevLoop 0)`), `hartObsM :471`,
`devOpStep .setPin :546-549`, `dmaView :189`; `wbootFacts` `WeakLang.lean:482-490` (register clause `:487` = `Lang.
lean:301`) ✓; `weakEvLang`'s `Obs = Empty` (`WeakEvLang.lean:1007`) — as the census says ✓.

## REQUIRED changes

- **[R16.1] W-DISK (M4)/(M9) contradict the fabric-marker invariant `pdevOk`; the brief must carry the mechanism
  and the W13 (I) cost must be re-sized.**  *What is wrong.*  `WeakPromiseFact.pdevOk pstep pdev` (`:613-614`) says:
  for EVERY step with `pdev p l p' = false`, `d' = d` (the fabric does not move) AND `∀ d0, pstep p d0 l p' d0` (the
  step does not DEPEND on the fabric).  The instance marker is a function of the LABEL ALONE — `pdevEv _ l _ := l is
  LDev` (`WeakEvInst.lean:543-547`, docstring "THE FABRIC MARKER, a function of the LABEL alone") — and the header
  states the convention: "every arm that READS OR MOVES the device fabric carries `LDev`" (`:30-33`; START is `LDev
  .dev` precisely because it reads `dvirtio d`, `:488`).  `pdevEvOk : pdevOk pstepEv pdevEv` (`:1694`) is proved from
  `pdiskProgDevFree :1670-1684` ("`l ≠ LDev → d' = d ∧ ∀ d0, pdiskProg dp d0 l dp' d0`").  Consumers ON THE PATH:
  `WeakEvCapstone.lean:1183` (`wpBehaviorFulfilOnceDev pstepEv pdevEv … pdevEvOk`, inside the T2 event capstone) and
  `WeakRvwmoSupply.pstepEvDevfree :169-171` (via `pdevEvFalse :164`: "`l ≠ LDev → pdevEv = false`") → `admRunDevfree
  :175`, `hemitDevfreeConst :202`, `hemitDevfreeRefab :241` (the realization's fabric blindness; `WeakRvwmoFab.lean:
  17,47` name this dependency).  Now: **(M4)** — RULED [OWN.31] — makes the used-idx `DWrite` (label `LStore`,
  `pdiskProg`'s arm `:499-503`) satisfy `d' = setDvirtio d (complete …) ≠ d`: `pdiskProgDevFree` and `pdevEvOk` become
  FALSE as stated.  **(M9)** — "a fabric-READING node `DM.DGet` (`LSilent`, `dp' = some (k (dvirtio d))`)" — violates
  the SECOND conjunct (`p'` depends on `d`, so `∀ d0, pstep p d0 l p' d0` fails); the plan's own convention says such a
  node must be `LDev`.  The plan's W-DISK file list (:1129-1137) names none of `pdevEv`/`pdevEvOk`/`pdiskProgDevFree`/
  `pstepDiskDevFree`/`pdevEvFalse`/`pstepEvDevfree`, and W-DISK-Q2 (a) prices the W13 side as "S–M of (I)/(T) text, no
  proof impact beyond one more `gfDev` member kind" (:1675) — the graph side ALSO cannot see the fused write from the
  emission: `isDevBlock`/`emDev` are label-based (`lbIsdev` `WeakRvwmoFab.lean:119-122`, `emDev :144-150`, `isDevBlock
  :152`), so "`gfDev` lists fabric MOVES, the used-idx `LStore` among them" needs a NON-label criterion.
  *Exact change (add to §C W-DISK as "(M4)/(M9) MECHANISM", before the file list; update the file list, Size and
  W-DISK-Q2's recorded cost; mirror in §A(†)'s `gfDev` sentence and W13 (I)):*
  (i) a NEW node `DM.DWriteDev (g : VirtioState → Option VirtioState) (pa) (bs) (k)` — the pf twin of
  `DevM.dmaWriteStep` (`MachCSL/Dev/DevLang.lean:164-167`): `pdiskProg`'s arm reads the CURRENT fabric at the write
  (`g (dvirtio d) = some s' → l = LStore false (paZ pa) bs [] [] ∧ d' = setDvirtio d s'`; `g … = none → ` the stall
  self-loop) — so the completion's `cfg = c ∧ usedIdx = ui` guard is re-checked at the write exactly as `serve :553`
  does, with NO separate fabric-reading node; `ediskStep` sets BOTH `ewgLog` and `ewgDev` (`edlabApply :665-666`
  already takes `d'`, so `ediskStepFactor`/`WeakEvCapstone :650-664` adapt);
  (ii) `pdevEv` becomes STATE-AWARE: `pdevEv p l p' := lbIsdev l || (p = .PDisk (some (DWriteDev ..)))` (the signature
  `P → Wlabel → P → Bool` already allows it; `pdevOk` is parametric in `pdev`); `pdevEvOk` re-proved;
  `pdevEvFalse`/`pstepEvDevfree` restated with `pdevEv p l p' = false` as the hypothesis (S); `admRunDevfree`/
  `hemitDevfree*`/`gfexecConfOfQconf :649` keep their label-based `emDevfree` via ONE new lemma "a row with no `LDev`
  item never leaves `PDisk none` (no START ⇒ no burst ⇒ no `DWriteDev`)" (S–M; the devfree emissions are exactly the
  quiescent witnesses);
  (iii) (M9) RE-SPECIFIED: NO `LSilent` fabric-reading node.  The START snapshot is kept for `cfg` (as `serve` keeps
  `c`, `:545`) and every fabric-dependent decision is a GUARD at a fabric step: the completion's guard inside
  `DWriteDev` (i); the `seen+1` pop as its OWN `LDev .dev 0 []` step right after the ring `DRead` — MachCSL's guard-pop
  IS a separate step (`Virtio.lean:576-578`), so W4 F9 maps it 1→1 — NAMED in §B(11) as one more `dev`-kind event in
  the disk row (D49 (a)/D51: STRONGER than the spec's silence by (R1)–(R3)'s coupling of the pop to the row's DMA
  accesses; EQUAL to MachCSL's step structure); the used-element write's guard (`reqOf s h = some r ∧ usedIdx = ui ∧
  cfg = c`, `:546-547`) likewise as a `DWriteDev` with `g s = some s` (a move-free guarded write: `d' = d`, `pdevEv =
  true` is harmless — or `DWrite` plus the START snapshot, with the guard checked only at the idx write, WEAKER on
  a mid-burst config write and still EQUAL on xv6: name the choice);
  (iv) W13 (I)'s text: `(i,k) ∈ gfDev ↔ dvi k ≠ dvo k` taken from `hartConff`'s endpoints (`WeakRvwmoFab.lean:
  238-262`), NOT from `isDevBlock`; `gisIo (i,k) → (i,k) ∈ gfDev` stays; the (I) delta is **M** (the `isDevBlock`
  clause `:533` and its `hblkQ` consumers `:318-503` change shape), not "S–M text";
  (v) file list additions: `WeakEvInst.lean` `pdevEv :544`, `pdevEvOk :1694`, `pdiskProgDevFree :1670`,
  `pstepDiskDevFree :1686`, `pdiskProgLatFree :1400`, `pdiskProgTsLoad :1423`, `:1184`; `WeakRvwmoSupply.lean:164-171`;
  `WeakEvLang.lean` `eprimStepDiskReducible :1351-1370` (a DWild arm the plan does not list), `ediskStepWf :1325-1348`;
  `WeakEvCapstone.lean:1183`.  Correct the DWild count: **21 occurrences** (`VirtioProg` 14, `WeakEvLang` 3,
  `WeakEvDisk` 2, `WeakEvInst` 2), not "26 … WeakEvLang 8".
- **[R16.2] Record [OWN.30] and [OWN.31].**  W-DISK-Q1 = (b) (MachCSL `storeDma pa 0 w` is a no-op; serial MachCSL
  lane, before/with W-RSV; `Dev/Virtio.lean` and the driver proofs untouched) and W-DISK-Q2 = (a) (the pf used-idx
  `DWrite` carries the completion's fabric delta in the same step; `gfDev` lists FABRIC MOVES, one RAM store per
  completed request a member; STRONGER than virtio, EQUAL to MachCSL).  Change: header Status line, §C top ("W-DISK-Q1/
  Q2 gate only F9 and W13 (I)" → "RULED"), §C W-DISK (M4)/(M5) marks, Status (:1582 "Gated … W-DISK-Q1/Q2"; :1588
  "OPEN owner questions: W-DISK-Q1, W-DISK-Q2" → "none"), §D (both entries → RULED, tags [OWN.30]/[OWN.31], the
  recommendation lines → "RULED as recommended"), D26's sequence.  W13 (I) then waits for W13 (M) + W-DISK only.
- **[R16.3] The W-DISK-Q1 (b) item is a STANDALONE serial MachCSL S item launched NOW — NOT "folded into W-RSV's
  brief".**  *What is wrong.*  §C (:1167-1169) and Status (:1585) say (b) is "best folded into W-RSV's brief if ruled";
  W-RSV waits for M1 (D26, :1310-1311); M1 = W5 needs W4 F9 (:1159); F9 "BLOCKED on W-DISK + W-DISK-Q1" (:1068-1069) —
  under (b) that means the MachCSL change must LAND before F9 can prove `R-log` across a 0-length DMA write.  Folding
  (b) into W-RSV therefore puts F9 → M1 → W-RSV → (b) → F9 in a cycle.  *Exact change.*  Add a §C item **W-DMA0** (S,
  serial MachCSL, launchable NOW — the lane is free: W-COH DONE, W-RSV after M1): `MState.storeDma` (`Lang.lean:
  171-173`) or the `dmaWrite` arm (`:540-544`) gains the `n = 0 → σ' = σ.setDev d s'` (no log entry) case; consumers to
  re-prove: `Resources.mmOk_storeDma :862`, `WpDma.lean` (19 sites: `hartViews_storeDma :55`, `memModel_storeDma :64`,
  `machInterp_of_storeDma :118`, `machInterp_storeDma :142`), `WpDevDisk.lean` (3), the `Vtest` twins
  (`vtest-lean/Vtest/XState.lean` 3, `DevExec.lean` 1 — `vtest.sh check`), and on the weak side `Weak/PfStepTsoView.
  lean` (6: `sameReadStoreDma :155`) and `PfStepTsoMem.pfDWriteRowMem :669` (case `n = 0`; W-DISK's `(M5′)` arm then
  mirrors it: `n = 0` is pf-`LSilent`, MachCSL-no-op, 1→1); acceptance `lake build Xv6 MachCSL Weak Vtest` ([R14.1]
  pattern) + `--weak` audit unchanged.  Spec line (owner rule): RVWMO's gmo is over "the primitive load and store
  operations generated by memory instructions" — a zero-byte access generates none; Sail has NO DMA model and its own
  `mem_read`/`mem_write_value` take `width : Nat` with the Sail-source `0 < 'n` bound ERASED in Lean (`model/Lean_RV64D/
  LeanRV64D/Mem.lean:496,614`); Zifencei/PMAs silent — (b) is FAITHFUL, the removal of a model artifact.  Update D26
  (":→ W4 F9 (after W-DISK + W-DMA0)") and the "two serial MachCSL items" paragraph (:1161-1169) to three, ordered
  W-COH ✓ → W-DMA0 → (M1) → W-RSV.
- **[R16.4] Record W5-pre and W11 (iv)a as DONE (both landed after rev 19 was written) and fix their cites.**
  *W5-pre* (`Weak/SrvwmoXv6Witness.lean`, now 805 lines, header `:17-24`): `srvwmoXv6M1Premises :599-607` is
  `… ∧ execProgOk'ST (pstepPin …) pclsEv (candKfetch …) TsoShadow.cohSrc pst dv (candExec c) ∧ candScaT cohSrc c ∧
  candDiskLat c` — STRONGER than W5c's set, `SrvwmoXv6Witness.m1PremisesS :611` recovers the old conjuncts;
  `srvwmoXv6M1PfRun :624-633` returns a `pfRunST … cohSrc` run PLUS the projection lemma (`∀ i, (tsoShadow cohSrc st
  i).mem = shadowOf cohSrc c.cdTr i`); `srvwmoXv6M1Satisfiable :733`; `esilAdmRun :169`; `execProgOk'SNil/SSnoc
  :272/280`.  Plan cites `:583,596,672,157,260,268` and "730 lines" (:242-243, :1006-1012, :1150-1153) are stale; §A
  M1 text (:343-347) must quote the NEW definition; W4 census D1/R5 ("the premise set still says `candSca`") is
  CLOSED; §C top's IN-FLIGHT list and D26 drop W5-pre.  *W11 (iv)a* (`Weak/RvwmoXv6Sca.lean`, 327 lines, `Weak.lean:
  629`): `tvnSca :50`, `gwixLeTvnSca :116`, `tvnScaMono :133`, `linGmoEmitBefore :144`, `linLogEmitted :172`,
  `linTvnScaLe :194`, `linScaOk :241`, **`linCandSca :314`** (`rvwmoMinusConsistent G → grule14 G → candSca (linCand
  G)`; no exhaustive `Lbl`/`Wlabel` match, per its header).  Move `linCandSca`/`tvnSca` OUT of the "NOT in any merged
  file" list (:273) into "LANDED"; mark **W11 (iv)b `linCandScaT` LAUNCHABLE NOW** (its stated gate "once (iv)a
  merges" is met); update Status/D26 (IN FLIGHT = W13 (T)+(M) only).
- **[R16.5] Fix the F_FLUSH fact and keep the device model's strengthenings in §B(11) after W-DISK.**  *(a) Factual.*
  §C W-DISK's Spec line (:1082-1083) says "MachCSL's `deviceFeatures` offers bit 9 and xv6 does not clear it";
  THIS image's driver DOES clear it: `Xv6/SpecVirtioDiskInit.lean:10` ("negotiate features (clear RO/SCSI/FLUSH/
  CONFIG_WCE/MQ/ANY_LAYOUT/EVENT_IDX/INDIRECT)"), `ProofVirtioDiskInit.lean:935` ("DRIVER_FEATURES := 0"), `vdi_wce_15
  :559` (`Virtio.wce … = false`).  So `VIRTIO_BLK_F_FLUSH` is NOT negotiated; the correct mark for (M7)/E-D1/§0 F1/
  §B(11) is: "virtio 1.x: a driver MUST NOT issue FLUSH unless `F_FLUSH` is negotiated, so the device's answer to an
  un-negotiated FLUSH is UNSPECIFIED — MachCSL's `statusOf` OK (`Virtio.lean:377-379`) and pf's UNSUPP are BOTH
  model choices on unspecified behaviour; xv6 never issues FLUSH — vacuous" (replace "FAITHFUL iff `F_FLUSH`
  negotiated" at :149, :778, :1082, :1107, :1704, :1707).  *(b) Honesty (d).*  §B(11) says the pf-drift entry "is
  deleted" after W-DISK (:783, :1148) — but that entry is the ONLY place naming MachCSL's device-model choices that
  are STRONGER than virtio: the FUSED used-idx/ISR completion (`complete :423-427`, `serve :552-555`; spec "MAY then
  notify"), STALL on a malformed chain (`stall :457`, `serve :524`; spec unspecified), ONE 16-byte descriptor read
  (spec silent on burst granularity), FLUSH OK regardless of negotiation (above), plus the already-named reads-at-the-
  top (F6).  Add them PERMANENTLY to §B(11)'s "Machine-model choices" list (beside "ONE sequential device row", "DMA
  as a store-order agent") with marks, so deleting the drift entry loses nothing; cross-reference from §A(5)/(6).
- **[R16.6] Pin the `pfStepTso` parameter's Lean statement before W2 CLOSE and W4 F1–F8 launch in parallel.**  The
  plan says F1–F8 "may start BEFORE W2 closes — only the parameter INTERFACE must be agreed, E-M1/E-M2" (:899-901),
  but E-M1–E-M4 are PROSE (:966-975); two parallel workers will each write a signature.  Write it into §C W2 CLOSE
  (and have W4 take it as a `variable`), e.g.:
  `pfStepTso (c : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU) (o : Outcome Register
  RegisterType) (l : Wlabel) (p' : Pexv6) (d' : Efab) : pairAdjacent (st ++ [(hartAgent cpu, l)]) → pfStepFactsT
  TsoShadow.cohSrc st c (hartAgent cpu) l → pstepEv (.PHart cpu m rs fn ib) c.pcDev l p' d' → ramBytes req.pa n →
  rmem c st σ ∧ viewRel cohSrc σ st → ∃ v σ', evStep cpu o σ v σ' ∧ v = ⟨the answer the pf continuation consumed⟩ ∧
  rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧ viewRel cohSrc σ' (st ++ …)` — with `o`/`m`/`req`/`n` as E-M1 fixes them
  and `R_mem` restricted to `mem log tv itv hr resv` (E-M2); the 0-step and `σ' = σ` rows as separate named lemmas
  (E-M3).  Also assign W2 CLOSE's item (3) (the `fiArm`-from-instruction-structure lemma, :963-966) to ONE worker:
  §C W2 lists it as W2's, `PfStepTsoView.lean`'s header deviation (4) says "W4's to supply" — pick W2 CLOSE (it is a
  `pfRunST` step-list fact) and say so in both places.

## SUGGESTIONS

- **[R16.s1] Cite drift after W-COH in `MachCSL/TsoMem.lean`/`Lang.lean`** (harmless for workers who grep names, but
  §0/§A/§B quote them as evidence): `NCPU :57` (plan :54), `hartAgent/diskAgent/ifetchAgent :62-64` (plan :59-61),
  `HEnt.visible :116-118` (plan :115-116), `Hist.read :122-123`, `Resv := Mem :240` (plan :208), `HRead :288`, `HRead.
  zero :293`, `fencePost :489` (plan :345), `fenceDrains/fenceAcq :500-505` (plan :356-364); `Lang.lean`: `MState.store
  :149-155` (plan writes both `:147-153` and `:156`), `MState.fence :158-165` (plan :155-163), `storeDma :171-173`,
  `dmaView :189` (plan :185), `hartStep :504-506` (plan :499-506 in three variants), `blockedStep` ≈ `:402-409`
  (census), `dmaRead :539` (plan :536), `anyReserve` guard `:542`, `devBlocked :561`, `devStep :575`; `WeakRvwmoSupply.
  emDevfree :284`, `emFetchImg :288` (plan :273, :277-278); `WeakRvwmoFab.gfDev :518-520`, `isDevBlock ↔ gfDev :533`,
  `emFetchImg :537`, `gfexecConfOfQconf :649`; `WeakAxiomatic3.srvwmoRealizable :2088`.
- **[R16.s2] Record W-DISK-Q1/Q2 with the Spec line FIRST and complete** (the owner rule says "FIRST state what the
  RVWMO chapter, the Sail model (file:line), Zifencei and the PMA rules say"): Q1's Spec is fourth and cites no Sail
  line; Q2's Spec names virtio only.  Use [R16.3]'s Spec line for Q1; for Q2: "RVWMO/riscv.cat: no device-internal
  events; Sail: no device/DMA model (`MachCSL/Dev/*.lean` only); Zifencei/PMAs: silent; virtio 1.x: the device writes
  the used index and MAY then notify".
- **[R16.s3] (M8) durability note.**  Under `wce = false` (`vdi_wce_15`) MachCSL's `completeOk` needs `!reqCached`
  (`:412-414`), i.e. a WRITE completes only after the root loop drains it (`body :582-586`), while the aligned pf
  program (no cache) commits at the used-idx step; `R-dev` "pf `disk` = `cacheView`" is right, but say explicitly
  that `diskOf` (the durable image) differs mid-run and that this is invisible in a single era (D14) — a crash-row
  consumer would see it.
- **[R16.s4] W-DISK's "AFTER W13 (T) merges"**: (T) is in flight on the chain files; W-DISK touches `WeakEvInst`/
  `WeakEvCapstone` which (M)'s `gmem` sweep may reach — the plan says "serialize the MERGE, not the work" ✓; add the
  same clause for `WeakRvwmoSupply.lean:164-175` ([R16.1] (ii)), which (M) also edits.
- **[R16.s5] W4 F6/F9 and the forked `serve` threads**: after [R16.1] (iii) the pop is a separate pf `LDev .dev`
  step, so the census's "1→4 + a NEW THREAD" row (`W4-structural-census.md:250`) becomes `DRead` 1→1 (`dma16`), pop
  1→2 (`get`, guard) + `fork` 1→0 (the fork is the START of the next pf burst's `serve`-span); restate F9's
  bookkeeping line (:1069-1070) accordingly.
- **[R16.s6] §C top "MAY LAUNCH NOW" after this round**: W2 CLOSE ∥ W4 F1–F8 ∥ W11 (iv)b ∥ **W-DMA0** (serial MachCSL
  lane) ∥ W-DISK (after [R16.1] is written into the brief).  W13 (I) after (M) + W-DISK.

## Owner questions the plan is missing

- **W-DISK-Q3 — how the device's mid-burst fabric READS and the ring POP are encoded (raised by [R16.1]; the plan
  may decide it without the owner, but it changes `gfDev`'s membership and so belongs here).**  *Spec*: the RVWMO
  chapter, riscv.cat and Sail have NO device-internal events (Sail has no device/DMA model; `MachCSL/Dev/*.lean` is the
  only device text); Zifencei and the PMAs are silent; virtio 1.x says the device reads the available index, the ring
  entry and the descriptors, and after writing the used index MAY notify — it says nothing about when the device
  re-reads its own configuration registers.  Every option is beyond the spec's silence (device-MODEL text, D45/D49).
  *Plain language*: the pf disk program must now behave like MachCSL's `serve`, which re-reads the device state
  (`get`) and tests it (`guard`) at several points; in the pf machine every step carries ONE label, and the tree's
  invariant `pdevOk` says a step that is not labelled `LDev` neither changes the devices' state nor depends on it.
  *Tiny example*: the disk has popped request `h` and is about to write the used index when hart 2 writes the
  `QUEUE_SEL`/`STATUS` registers (`Virtio.write`); MachCSL's `dmaWriteStep` re-checks `s.cfg = c` at the write and
  refuses (stall); a pf program that decided from a START snapshot would write anyway — the two diverge unless the pf
  write also reads the current fabric.  *Definitions*: FABRIC = the devices' registers/ISR lines (`Efab`); `LDev
  kind base vs` = the pf label for a fabric-touching step, projected to the graph event `LIo` under W13; `gfDev` = the
  list of row items that move the fabric, in fabric order; (R3) = the platform assumption ordering `gfDev` members as
  the fabric serializes them.  *Why it matters*: nothing in the published CONCLUSIONS changes; what changes is how
  many device-internal events enter `gfDev`/(R1)–(R3) (the trusted-surface text) and whether the one-row artifact D51
  couples more device-internal steps to the row's DMA accesses.  *Options*: **(a) guards folded into the fabric-moving
  writes (`DWriteDev`), the pop as ONE `LDev .dev` step, no pure re-read node** — the graph gains exactly one `dev`
  event per request (the pop) beyond today's START (COMMIT retired); STRONGER than the spec only by (R1)–(R3) on that
  event (D51-class, device-internal), EQUAL to MachCSL's step structure; cost: inside W-DISK (S–M over [R16.1]);
  unblocks W4 F9's 1→1 pop match; risk: none beyond [R16.1].  **(b) a pure fabric-READ node labelled `LDev .dev` with
  `d' = d`** — every config re-read becomes a graph event: STRONGER (more (R1)–(R3) coupling, more `gisIo` events that
  are NOT fabric moves — so (I)'s "`gisIo → gfDev`" must be weakened to "`gisIo ∧ dvi ≠ dvo ↔ gfDev`"); cost +S on (I)
  text; no benefit over (a).  **(c) a pure fabric-READ node labelled `LSilent` with a STATE-AWARE `pdevEv`** (the plan's
  (M9) as written, repaired) — NOT a graph event, EQUAL to MachCSL; but the devfree-emission lemmas (`emDevfree` is
  label-based) need the "no START ⇒ no burst" invariant of [R16.1] (ii) to cover these nodes too; cost +S–M; risk: a
  fabric-dependent step invisible to the emission is exactly the shape `pdevOk` exists to exclude — the reviewer's
  recommendation is (a).
