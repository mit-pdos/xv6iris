# Weak-memory development: Rocq → Lean port map

Generated 2026-10-05 by scripts (python) over the Rocq tree at jj `xxvzwolszwmp` (commit `1cc222280`, read from `/home/bsdinis/dev/xv6iris-spinlock`, whose working copy is identical to it), the fork point `nrymuwtz` (`f25c0e3aa`, 2026-08-09), Rocq main `7d988ae13` (the Lean port's source, 2026-09-30) and this Lean tree. The machine-readable DAG is [`weak-port-dag.json`](weak-port-dag.json): `{file: {lines, weak_deps, other_deps, layer, set, wp}}`.

**Method.** For every `.v` file the comments and strings are stripped, then every `[From X] Require [Import|Export] m1 m2 … .` is parsed. A bare or `From xv6iris` name that resolves to `iris/<m>.v` is a local module; anything else is external. A file's **layer** is the length of its longest import chain to a file with no weak imports: layer 0 imports no weak file, and a file at layer n imports some file at layer n-1 and none higher. Files in the same layer never import each other. Line counts are newline counts of the file as checked in.

## 0. Summary

* **546 Weak\*/Ax\* files (339,305 lines)**, plus **26 non-Weak/Ax files the weak line added (21,719 lines)**, which are part of the same development and so are in the DAG. They are marked † below: `Wk*.v` (21), `KernelPins{,Def}.v`, `KernelSites{,Def}.v` and `VirtioProg.v`. Weak files import 6 of them: `VirtioProg` (24 importers), `WkEntryEff` (5), `WkEntryNew`, `WkStartedLoad`, `KernelPinsDef` and `KernelSitesDef`. Four of those six themselves import Weak files, so leaving them out would hide real Weak→Weak dependencies. None of the 26 exists on Rocq main or in Lean.
* **61 layers (0–60).** The import graph is acyclic. 85 files are imported by no other weak file (roots).
* **Widest layers.** By file count: L51 (27 files), L16 (21 files), L11 (18 files), L14 (18 files). By lines: L12 (19,289), L16 (18,943), L11 (18,324), L3 (13,605).
* **Critical path: 50,425 lines through 53 files** (`WeakMem` → … → `AxSpinJ2`). The rest of the work can run beside it, so the best possible parallel speedup is about 7.2×. Gating at the level of whole ~18k-line packages, where a package waits for all its prerequisite packages to finish, gets only about 1.3×: the package-level critical path is about 280k lines, because neighbouring layers are densely connected. The plan in §4 therefore gates on individual files inside a phase.
* **The base semantics differ (a design decision to make before porting).** Rocq's `RiscvLang` is SC. Each step runs a whole `try_step` through the `exec` interpreter (`RiscvExec`), and the weak line builds its own machines on top of that: `WeakMem`/`WeakPromise` (promising), `WeakAxiomatic`/`WeakRvwmo*` (RVWMO graphs), `WeakEvLang` (event-granular), `AxOpsem`/`AxWp` (AxSL). Lean's `MachCSL/Lang.lean` is already event-granular: a free monad over Sail `Outcome` events, over `MachCSL/TsoMem.lean`, which has a store order, per-hart views, forwarding and a non-coherent icache. So the weak port has no Rocq-literal base to target. `RiscvExec`/`ExecCommon` are MISSING (204 and 85 weak importers), and the weak tier must either be rebuilt over Lean's event language or get its own `exec` interpreter.
* **The Lean model lacks the weak line's model change.** The weak line regenerated the Sail model with `-D SYMBOLIC`, so `riscv_step` emits `InstrAnnounce`/`BranchAnnounce` events. 64 weak files mention those events. Rocq main never took this change, and Lean's model and lean-sail `Outcome` have neither event (§3).
* **Lean counterparts that are MISSING** (§2): the exec interpreter (`RiscvExec`, `ExecCommon`), `VcGen`, `UserBits`, and, by design, the generated kernel decode catalogs (`KernelDecode00–31`, `KernelRvcDecode`, `Code*`), which Lean replaces with `Xv6/KernelText`+`KernelTree` and decode-at-proof-time tactics. Most other shared modules have a Lean *analog* with a different structure, not a 1:1 file (Rule D21: one file per Rocq file only where Lean kept the split).
* **Shared modules drifted on Rocq main after the fork.** The weak files import the 08-09 versions. Lean ports the 09-30 versions, and many of those changed statements (§2, column "main drift"; e.g. `IntrDefs` +3008/−650, `WpSconf*` thousands of lines, `RiscvPtsto` +1953/−416, `RiscvLang` +1513/−116).

## 1. Import DAG: topological layering

Format: `file:lines`. † marks a non-Weak/Ax file the weak line added; `*` marks a file on the critical path. Within a layer, files are sorted by size.

| layer | files | lines | cum. lines | files |
|---:|---:|---:|---:|---|
| 0 | 9 | 5,982 | 5,982 | WeakMem*:3001, VirtioProg†:842, AxReuseProbe:577, KernelSitesDef†:559, WeakView:479, AxSymReg:280, AxSpinSpikeRun:180, WkGprAcc†:62, AxSlice:2 |
| 1 | 7 | 7,749 | 13,731 | WeakAxiomatic:1836, WeakPromise*:1599, WeakLitmus:1535, WeakDeps:1132, WeakInterp:1015, WeakViewMono:499, KernelSites†:133 |
| 2 | 7 | 5,102 | 18,833 | WeakAxiomatic2:1447, WeakPromiseFact*:1167, WeakLang:913, KernelPinsDef†:607, WeakInterpProj:412, WeakLitmusProj:290, WeakPromiseLitmus:266 |
| 3 | 7 | 13,605 | 32,438 | WeakGhost:3818, WeakAxiomatic3:2716, WeakEvLang:1679, KernelPins†:1672, WeakRobustTrace:1486, WeakPromiseBridge*:1399, WeakRvwmoGraph:835 |
| 4 | 10 | 10,356 | 42,794 | WeakSrvwmoLitmus:1899, WeakRvwmoLin:1751, WeakRvwmoXchg:1380, WeakSailLTS:1332, WeakVProp:1248, WeakAxRealize:1005, WeakErase:879, WeakExec:392, WeakViolation:256, WeakRobust*:214 |
| 5 | 11 | 8,954 | 51,748 | WeakSailLTS2:1531, WeakRvwmoNorm:1137, WeakRobustGraph*:1071, WeakRetag:930, WeakRefuse:890, WeakBridge:874, WeakRvwmoRestr:650, WeakCtx:627, WeakRvwmoLock:506, WeakFence:448, WeakAdequacy:290 |
| 6 | 13 | 8,564 | 60,312 | WeakRobustProv*:1611, WeakRobustAcyc:1136, WeakInstr:1056, WeakRobustSer:747, WeakCtxPt:706, WeakRvwmoAcyc:623, WeakRobustLin:611, WeakRvwmoLockWit:455, WeakRvwmoProbeSwap:422, WeakRvwmoProbeK1:376, WeakRvwmoKill:322, WeakPtPub:280, WeakRvwmoProbeRestr:219 |
| 7 | 8 | 8,837 | 69,149 | WeakCert:1810, WeakRvwmoKillArms:1661, WeakStore:1548, WeakRobustOrd*:1321, WeakRvwmoHull:948, AxGraph:732, WeakRvwmoTopo:656, WeakLockPayload:161 |
| 8 | 7 | 7,384 | 76,533 | WeakRobustSim*:2147, AxGraphCat:1475, WeakWord8:1032, WeakLock:916, WeakEff:864, WeakRobustAcyc2:583, WeakRvwmoDec:367 |
| 9 | 7 | 5,298 | 81,831 | WeakRobustMain*:1962, WeakEffSkel:850, AxGraphDec:731, WeakStarted:688, AxTieProc:570, AxLockGraph:336, WkStackOwn†:161 |
| 10 | 14 | 10,404 | 92,235 | WeakRobustDisc:1459, WeakRacy:1449, WeakRobustBlocks:1303, WeakCompose:1131, WeakAcquire:823, WeakEvPf*:737, WeakLeafEffCommon:607, AxGraphWit:553, AxLitmus:537, AxLockSerial:433, AxViol:410, WeakTickEff:397, WeakPmpEff:358, WeakPmpTorEff:207 |
| 11 | 18 | 18,324 | 110,559 | WeakSailComplete:2829, WeakRobustCone:2010, WeakEvInst:1799, WeakLeafAmo4:1372, WeakRobustL2:1118, WeakVariant:1021, WeakFunnel:940, WeakEvAdequacy*:932, WkOwnPingPong†:909, AxViolSubsume:864, AxGhost:760, WeakVarCert:697, WeakLeafEff8s:654, AxBridge:635, WeakLeafEff8:591, WeakCtxLock:484, WkStartedLoad†:433, WeakBranch:276 |
| 12 | 16 | 19,289 | 129,848 | WeakSailCone:3916, WeakStale:2625, WeakEvLift*:2264, WeakLeafBase4:1579, WeakShape:1504, WeakRvwmoConf:1317, WeakFetchEff:1239, WeakEvCapstone:1106, WeakRobustL2b:1042, WkYieldFrame†:845, AxPtProt:636, WeakFunnelCfg:351, WeakCertify:338, WkStartedMp†:267, AxCovMono:181, AxStepDet:79 |
| 13 | 15 | 10,246 | 140,094 | WeakWalkEff:1607, WeakEvProv:1087, WeakEvStarted*:1069, AxDeps:909, WeakRvwmoSupply:868, WeakEvExecEff:718, WeakEvDisk:673, WkCtxSurface†:654, AxPtProt2:621, WeakShapeOverrides:620, WeakFetchRvc:406, WeakShapeLive:381, WeakLeafWin:287, WeakSrvwmoCapstone:184, AxCovClose:162 |
| 14 | 18 | 10,862 | 150,956 | WeakUpdEff:1173, WeakFetch2:1057, WeakRvwmoFab:961, WeakLeafAmo4Leaf:900, AxSfence:691, WeakLeafSd8:644, WeakLeafLd8:626, AxSpinSpike:617, WeakLeafCsrw:599, WeakLeafSw4:521, WeakShapeOverrides2:514, WeakLeafLw4:510, WeakRvwmoLinInd:440, AxCutProbe:439, AxPtProt3:429, WeakShapeGen01:292, AxGate:275, WeakRvwmoConfWit*:174 |
| 15 | 12 | 8,741 | 159,697 | WeakKpt:1630, WeakLeafTor:1335, WeakWalkStale:1071, AxSched:694, WeakRvwmoFabInd:670, WkEntryEff†:651, WeakRvwmoCert:642, WeakRvwmoConfWit2*:642, WeakShapeAst:474, AxScCat:399, WeakLeafRegOnly:323, WeakShapeGen02:210 |
| 16 | 21 | 18,943 | 178,640 | WeakLeafCsrw2:2055, WkEntryNew†:1781, WeakKptStale:1753, WeakRvwmoCert2:1461, WeakLeafCsrw3:1348, WeakLeafUtypeShift:1236, WeakRvwmoFloor:1230, WeakLeafRtypeW:1075, WeakEvFunnel:1030, WeakRvwmoAdm*:903, WeakLeafItype:796, WeakLeafMret:671, WeakShapeWin:614, WeakLeafStimecmp:583, WeakLeafCsrrTime:569, WeakLeafSdspOff:478, WeakLeafPmpcfg0:477, WeakShapeDec:353, WkClipAdvance†:306, WeakViewRacy:142, WeakShapeGen03:82 |
| 17 | 9 | 10,149 | 188,789 | WeakRvwmoCert3:2716, WkFetchPeel†:1892, WeakLeafCsrrM:1640, WeakRvwmoLin2:1259, WeakEvProv2*:856, WeakLeafJump:746, WeakEvWire:537, WkUnmapMp†:421, WeakShapeGen04:82 |
| 18 | 5 | 6,259 | 195,048 | AxPair*:1977, WeakLeafM:1925, WkStepPeel†:1266, WeakRvwmoCert4:1009, WeakShapeGen05:82 |
| 19 | 9 | 9,828 | 204,876 | WeakLeafO:2488, WkStartAux†:1892, WkWalkTails†:1322, AxOpsem*:1302, WkTimerinitAux†:1034, WeakRvwmoGlue:881, WkWalkRule†:461, WeakSmodeFrame:366, WeakShapeGen06:82 |
| 20 | 8 | 6,395 | 211,271 | AxWp*:1642, WkWalkCapstone†:1390, WeakRvwmoGlue2:892, AxDevGraph:792, WkTimerinit†:708, WeakRvwmoPinBridge:483, WkMemmoveLoop†:406, WeakShapeGen07:82 |
| 21 | 10 | 4,465 | 215,736 | WkStartNew†:1045, WeakRvwmoPinBridge2:743, AxToken:603, AxLifting*:468, WeakRvwmoCapstone:403, AxReadAll:310, AxDevGraphWit:300, AxInstrFacts:265, AxGateWp:246, WeakShapeGen08:82 |
| 22 | 7 | 5,753 | 221,489 | WeakRvwmoWalk:2888, AxAdequacy*:827, AxInstr:653, AxProt:594, AxWpD:449, AxLockOwn:260, WeakShapeGen09:82 |
| 23 | 11 | 10,493 | 231,982 | AxFetch:4951, WeakRvwmoCycWit:1343, AxSpinProt:1010, WeakRvwmoProgress:690, AxAdequacyL*:619, AxWpDSteps:528, AxProtLock:440, AxAdequacyChk:371, AxSchedIris:340, AxWpdLift:119, WeakShapeGen10:82 |
| 24 | 14 | 6,199 | 238,181 | WeakRvwmoWalk2:1348, WeakRvwmoCycWit2:1116, AxProtLock2:478, AxSchedGD*:429, AxDefer:397, AxRunClose:361, AxRegOnly:334, AxLockWp2:317, AxWpDHarts:303, AxGraphAgree:293, AxLockRace:292, AxLockWp:255, AxCov:194, WeakShapeGen11:82 |
| 25 | 15 | 7,372 | 245,553 | AxLockAdeq:1892, WeakRvwmoPreNorm:1093, AxLock3:777, AxBoundaryWpd:444, AxLockGen:436, AxTierA2:389, AxSymLd:356, AxProtInst*:339, AxCjrWpd:308, AxLockRace3:289, AxLockWpD:261, AxTierA:244, AxGateAdeq:239, AxSchedFwd:223, WeakShapeGen12:82 |
| 26 | 12 | 4,532 | 250,085 | WeakRvwmoPreNorm2:961, AxLockN:863, AxProtLock3:659, AxTierA3:365, AxEpiProbe:345, AxLockRace2:311, AxLockWitness:243, AxCondM:225, AxGateAdeq2:169, AxProtCov*:157, AxLockSmell:152, WeakShapeGen13:82 |
| 27 | 7 | 2,277 | 252,362 | AxLockSlice:445, AxProtCov2*:437, AxLock3Wp:430, AxLockMutex:358, AxLockN2:323, AxSchedSH:202, WeakShapeGen14:82 |
| 28 | 5 | 2,103 | 254,465 | AxProtCov3*:792, AxTierA4:481, AxLockN3:443, AxLockMutex2:345, WeakShapeGen15:42 |
| 29 | 4 | 3,015 | 257,480 | AxProtGate*:1773, WeakShapeMem:952, WeakShapeExecGen01:191, WeakShapePeel:99 |
| 30 | 2 | 1,181 | 258,661 | AxProtBytes*:989, WeakShapeExecGen02:192 |
| 31 | 4 | 2,461 | 261,122 | AxEpilogue*:1140, AxTokLedger:885, AxProtGateN:260, WeakShapeExecGen03:176 |
| 32 | 5 | 2,774 | 263,896 | AxTokLedgerWp:1074, AxDefer2:519, AxLdspWpd:493, AxEpiShape*:347, WeakShapeExec:341 |
| 33 | 6 | 3,603 | 267,499 | AxEpiChain*:1406, AxEpiLedger:979, AxDefer3:462, AxClsStep:320, AxEpiSat:261, WeakShapeTop:175 |
| 34 | 8 | 5,415 | 272,914 | WeakComposeLang:2231, AxEpiLedgerSd:688, AxSmodeProbe:657, AxCjrReach:516, AxDefer5:413, AxRowConf*:382, AxEpiCjrSym:286, AxDefer4:242 |
| 35 | 5 | 2,882 | 275,796 | AxEpiLedgerTick:986, AxLedgerG:949, AxSpinGate:518, AxRunGV*:281, AxEpiSdLdSat:148 |
| 36 | 9 | 4,495 | 280,291 | AxScRun:1194, AxEpiCjrFrame:898, AxLock3Prog*:656, AxSpinJ:381, AxRunGV2:355, AxReuseProbe2:307, AxEpiChainSdLd:303, AxLedgerG2:285, AxEpiLdX1:116 |
| 37 | 8 | 3,932 | 284,223 | AxTokLedgerMp*:871, AxEpiLdJr:857, AxEpiOwned:623, AxSymEngine:436, AxLdgSeal:429, AxLock3Wp3:258, AxLock3Wp2:252, AxSpinRow:206 |
| 38 | 8 | 5,655 | 289,878 | AxClsStep2*:1441, AxLock3Writer:1363, AxEpiAdeq:986, AxSymEngine2:674, AxSpineOk:423, AxLdgSealArith:380, AxFwdSource:217, AxSpinRow4:171 |
| 39 | 12 | 6,851 | 296,729 | AxLock3Reader:1810, AxSymEngine3:1329, AxSpinWit*:1126, AxWpcAdeq:653, AxSpinVA:509, AxLedgerG3:329, AxEpiRun:286, AxSpineOk5:273, AxEpiRace2:227, AxSpineOk2:186, AxEpiTrivial:105, AxRelease6:18 |
| 40 | 10 | 4,766 | 301,495 | AxSymCtl:1153, AxLock3Race:569, AxSpinProt2*:562, AxSpineOk3:525, AxSymMem:475, AxScRun2:468, AxLock3Thm:447, AxEpiSound2:269, AxSpinVA2:267, AxSpinVA6r:31 |
| 41 | 10 | 4,366 | 305,861 | AxSpinProt3*:717, AxSpineOk4:596, AxDataX:563, AxSpinX3:536, AxSymMem2:434, AxCert:419, AxEpiSound3:362, AxScRun3:313, AxSymMem4:219, AxLock3Cert:207 |
| 42 | 11 | 4,813 | 310,674 | AxAllHarts:647, AxEpiSoundFwd:644, AxCert2:608, AxSymMem3:595, AxSpinProt5*:588, AxEpiRace2Run:406, AxCert3:318, AxSpinProt4:316, AxDataX2:265, AxSpineOk6:217, AxDataX9:209 |
| 43 | 8 | 2,338 | 313,012 | AxSkel:431, AxWalk:398, AxSpinProt6*:368, AxDataX3:249, AxDataX10:231, AxSpineOk7:228, AxEpiTwinExact:223, AxCertP:210 |
| 44 | 11 | 6,699 | 319,711 | AxSymCtl4:1393, AxSpinProt7*:1062, AxSymCtl2:915, AxWalk3:748, AxSpinX:612, AxEpiRetCert:527, AxWalk2:425, AxSkelCert:388, AxIntr:356, AxWalk5:139, AxSpineOk8:134 |
| 45 | 12 | 4,831 | 324,542 | AxEpiRet:1117, AxSpinX2:784, AxSpinH*:574, AxCert4:478, AxSpinProt8:413, AxSpinX4:374, AxSymCtl3:287, AxIntr2:223, AxDataX6:168, AxDataX4:160, AxWalk7:158, AxPtwModel:95 |
| 46 | 13 | 4,205 | 328,747 | AxSpinH4*:836, AxSpinX5:727, AxEpiRetFwd:561, AxIntr3:496, AxSpinH2:368, AxDataX7:260, AxSymCtl5:247, AxIntr5:221, AxDataX5:132, AxDataX8:108, AxSpinX8:95, AxRelease7:77, AxRelease8:77 |
| 47 | 6 | 2,700 | 331,447 | AxSpinH5*:654, AxSpinH3:477, AxSpinX6:432, AxIntr4:421, AxLeafS:401, AxWalk4:315 |
| 48 | 7 | 3,791 | 335,238 | AxSpinU*:882, AxSpinVA3:726, AxSpinE:614, AxSpinH6:588, AxSpinX7:502, AxLeafS2:283, AxWalk6:196 |
| 49 | 11 | 4,687 | 339,925 | AxSpinE2:605, AxCondM2:540, AxLeafS4:519, AxSpinE3:516, AxSpinVA6:406, AxSpinVA4:400, AxRelease2:399, AxSpinU2*:392, AxSpinH7:389, AxLeafS3:330, AxSpinE7:191 |
| 50 | 17 | 3,835 | 343,760 | AxLeafS5:924, AxSfence2:488, AxCondM3:375, AxSpinVA7:362, AxSpinAm:330, AxSpinU3*:252, AxSpinE4:246, AxSpinAp:140, AxSpinVA5:140, AxSpinHd:139, AxSpinPO:122, AxSpinE9:100, AxSpinE7d:69, AxSpinE7f:40, AxSpinE7e:38, AxSpinE7b:36, AxSpinE7g:34 |
| 51 | 27 | 4,039 | 347,799 | AxRelease:820, AxCertP2:579, AxSpinU4*:465, AxSpinVA8:450, AxRelease3:314, AxCondM4:272, AxSpinE5:230, AxSpinPOc:197, AxSpinAp2:43, AxSpinE7c:43, AxSpinPOd:43, AxSpinPOd2:43, AxSpinPOt1:40, AxSpinPOt2:40, AxSpinPOt3:40, AxSpinPOt4:40, AxSpinHd3:39, AxSpinHd5:39, AxSpinHd4:37, AxSpinPOt5:36, AxSpinHd2:35, AxSpinAp3:34, AxSpinPOt6:34, AxSpinAp4:32, AxSpinAp5:32, AxSpinHd2b:31, AxSpinHd2c:31 |
| 52 | 11 | 2,695 | 350,494 | AxSpinJ2*:603, AxSpinCtl2:484, AxRelease4:357, AxCertP3:337, AxSpinE6:283, AxSpinXP:260, AxRelease5:162, AxSpinAp6:87, AxSpinHd6:54, AxSpinHd6b:36, AxSpinHd6c:32 |
| 53 | 8 | 2,526 | 353,020 | AxSpinE8:560, AxSpinAm2:395, AxSpinRow2:385, AxSpinPOm:338, AxSpinCtl:336, AxSpinXP2:216, AxSpinHd7:163, AxSpinE8e:133 |
| 54 | 5 | 1,700 | 354,720 | AxSpinHd8:458, AxSpinE8d:440, AxSpinAm3:287, AxSpinCtl3:270, AxSpinPOr:245 |
| 55 | 5 | 1,799 | 356,519 | AxSpinE8f:524, AxSpinRow3:443, AxSpinHd9:370, AxSpinPOx:352, AxSpinAp7:110 |
| 56 | 2 | 737 | 357,256 | AxSpinPO3:398, AxSpinHdA:339 |
| 57 | 2 | 885 | 358,141 | AxSpinHdB:483, AxSpinPO1:402 |
| 58 | 6 | 1,517 | 359,658 | AxSpinPO5:444, AxSpinHdC:337, AxSpinAp8:252, AxSpinPO2:243, AxSpinAm4:137, AxSpinAq:104 |
| 59 | 5 | 775 | 360,433 | AxSpinAp9:341, AxSpinPO4:322, AxSpinAqd:40, AxSpinAqt1:36, AxSpinAqt2:36 |
| 60 | 2 | 591 | 361,024 | AxSpinPO6:481, AxSpinAqr:110 |

**Critical path** (50,425 lines): `WeakMem` → `WeakPromise` → `WeakPromiseFact` → `WeakPromiseBridge` → `WeakRobust` → `WeakRobustGraph` → `WeakRobustProv` → `WeakRobustOrd` → `WeakRobustSim` → `WeakRobustMain` → `WeakEvPf` → `WeakEvAdequacy` → `WeakEvLift` → `WeakEvStarted` → `WeakRvwmoConfWit` → `WeakRvwmoConfWit2` → `WeakRvwmoAdm` → `WeakEvProv2` → `AxPair` → `AxOpsem` → `AxWp` → `AxLifting` → `AxAdequacy` → `AxAdequacyL` → `AxSchedGD` → `AxProtInst` → `AxProtCov` → `AxProtCov2` → `AxProtCov3` → `AxProtGate` → `AxProtBytes` → `AxEpilogue` → `AxEpiShape` → `AxEpiChain` → `AxRowConf` → `AxRunGV` → `AxLock3Prog` → `AxTokLedgerMp` → `AxClsStep2` → `AxSpinWit` → `AxSpinProt2` → `AxSpinProt3` → `AxSpinProt5` → `AxSpinProt6` → `AxSpinProt7` → `AxSpinH` → `AxSpinH4` → `AxSpinH5` → `AxSpinU` → `AxSpinU2` → `AxSpinU3` → `AxSpinU4` → `AxSpinJ2`.

**Non-Weak/Ax files the weak line added (†):**

| file | lines | layer | imported by weak files | imports weak files |
|---|---:|---:|---:|---:|
| KernelSitesDef | 559 | 0 | 5 | 0 |
| VirtioProg | 842 | 0 | 24 | 0 |
| WkGprAcc | 62 | 0 | 3 | 0 |
| KernelSites | 133 | 1 | 0 | 1 |
| KernelPinsDef | 607 | 2 | 3 | 3 |
| KernelPins | 1672 | 3 | 0 | 2 |
| WkStackOwn | 161 | 9 | 3 | 8 |
| WkOwnPingPong | 909 | 11 | 2 | 15 |
| WkStartedLoad | 433 | 11 | 2 | 16 |
| WkStartedMp | 267 | 12 | 0 | 17 |
| WkYieldFrame | 845 | 12 | 1 | 16 |
| WkCtxSurface | 654 | 13 | 0 | 20 |
| WkEntryEff | 651 | 15 | 11 | 15 |
| WkClipAdvance | 306 | 16 | 1 | 11 |
| WkEntryNew | 1781 | 16 | 1 | 25 |
| WkFetchPeel | 1892 | 17 | 4 | 22 |
| WkUnmapMp | 421 | 17 | 0 | 13 |
| WkStepPeel | 1266 | 18 | 3 | 22 |
| WkStartAux | 1892 | 19 | 1 | 41 |
| WkTimerinitAux | 1034 | 19 | 1 | 24 |
| WkWalkRule | 461 | 19 | 1 | 25 |
| WkWalkTails | 1322 | 19 | 1 | 24 |
| WkMemmoveLoop | 406 | 20 | 0 | 12 |
| WkTimerinit | 708 | 20 | 1 | 46 |
| WkWalkCapstone | 1390 | 20 | 0 | 30 |
| WkStartNew | 1045 | 21 | 0 | 46 |

`KernelPins.v` and `KernelSites.v` are generated by `tools/gen_pins.py` and `tools/gen_sites.py`, and `WeakShapeGen01–15.v` and `WeakShapeExecGen01–03.v` (19 files, 2,142 lines) by `tools/gen_shape.py`. These should be regenerated by a Lean generator, not ported by hand.

## 2. Non-weak Rocq modules imported, and their Lean counterparts

Status: **1:1** means a Lean file of the same name, or one whose header names this module as its source. **ANALOG** means the same content exists in Lean in differently organised files, so the weak port retargets onto those names. **MISSING** means there is no Lean counterpart. "main drift" is `git diff --numstat f25c0e3aa 7d988ae13` on that file: the change between the version the weak files were written against and the version Lean ported. The counterparts were found by scanning every Lean file in `MachCSL/`, `Xv6/` and `model/` for the module name, and by checking the definitions where no file cites it.

### 2a. Project modules (`iris/`, logical `xv6iris`)

| Rocq module | weak importers | Rocq lines | main drift | status | Lean counterpart | note |
|---|---:|---:|---|---|---|---|
| BootConfig | 9 | 595 | +93/-26 | 1:1 | Xv6/BootConfig.lean |  |
| ByteCursor | 1 | 530 | +4/-5 | 1:1 | Xv6/ByteCursor.lean |  |
| CalleeSaved | 7 | 208 | +51/-0 | ANALOG | MachCSL/CallConv.lean (`calleeSaved`) | no header cite |
| CodeCpuid | 1 | 79 | +11/-10 | MISSING (by design) | -- (Xv6/KernelText.lean + KernelTree + KernelTac/CodeTactics decode at proof time) | generated decode catalog; Lean has no catalogs (DU3) |
| CodeEntry | 4 | 69 | +12/-11 | MISSING (by design) | -- (cited by Xv6/ProofEntry.lean) | generated decode catalog |
| CodeEntryAux | 4 | 167 | +10/-11 | MISSING (by design) | -- | decode vocabulary over the catalog |
| CodeRelease | 5 | 122 | +26/-25 | MISSING (by design) | -- | generated decode catalog |
| CodeStart | 2 | 227 | +46/-45 | MISSING (by design) | -- | generated decode catalog |
| CodeStartAux | 2 | 361 | +45/-42 | MISSING (by design) | -- | decode vocabulary |
| CodeTimerinitAux | 4 | 222 | +23/-22 | MISSING (by design) | -- | decode vocabulary |
| ColdBoot | 5 | 402 | +15/-8 | ANALOG | MachCSL/BootRun.lean + BootReset/BootPeel/ArchReset (`resetValRun`) | Rocq runs `RiscvExec.exec` over the cold-boot chain; Lean runs `bootRun` |
| CommonWalk | 102 | 695 | +1004/-17 | ANALOG | MachCSL/UWalk.lean (header: "Rocq: `CommonWalk`"), MachCSL/UTlb.lean |  |
| CpuOwn | 5 | 246 | +251/-107 | ANALOG | MachCSL/KCtx.lean (`cpuOwn`) |  |
| DevModel | 360 | 809 | +872/-198 | ANALOG | MachCSL/Dev/{DevLang,Fabric,Uart,Plic,Virtio,DevIds}.lean | cited by Dev/Uart, Dev/Plic, Dev/Virtio |
| ExecCommon | 85 | 353 | +1/-2 | MISSING | -- (no whole-cycle `exec` interpreter in Lean) | `exec e s = Some (v,s')` reductions; Lean steps the free monad event by event (`swp_*`) |
| HartTp | 31 | 98 | +35/-4 | ANALOG | MachCSL/KCtx.lean (`tpPin`) |  |
| InstrBytes | 47 | 1289 | +383/-384 | 1:1 | MachCSL/Instr.lean (header: Rocq `InstrBytes.instr`) |  |
| IntrDefs | 42 | 1648 | +3008/-650 | ANALOG | MachCSL/KCtx.lean (sie index, `sieArm`), MachCSL/CtxLaws.lean, Xv6/HandlerEnv.lean | D27: no SIE ghost in Lean |
| KMap | 2 | 213 | +45/-24 | 1:1 | MachCSL/KMap.lean |  |
| KernelRvcDecode | 30 | 2179 | +37/-12 | MISSING (by design) | -- (decode at proof time) | pure RVC decode facts per word |
| KernelText | 8 | 234 | +197/-49 | 1:1 | Xv6/KernelText.lean (+ Xv6/KernelTree.lean) | lives in Xv6/, not MachCSL/ |
| KptGhost | 2 | 85 | +70/-6 | ANALOG | MachCSL/KptInv.lean | no 1:1 ghost-agreement file |
| KptPt | 27 | 1060 | +82/-35 | ANALOG | Xv6/KernelMap.lean, Xv6/KptBoot.lean, MachCSL/KptInv.lean |  |
| KptShare | 2 | 342 | +186/-46 | ANALOG | MachCSL/KptInv.lean (header cites KptShare) |  |
| KptTree | 2 | 1289 | +205/-88 | ANALOG | MachCSL/KptInv.lean (header cites KptTree; `tlbInvPt`) |  |
| MbootVocab | 2 | 105 | +2/-2 | ANALOG | Xv6/SpecEntry.lean / SpecStart.lean (own vocabulary) | no 1:1 |
| MemAccessGen | 11 | 1009 | +14/-9 | ANALOG | MachCSL/UMemAccess.lean, MachCSL/UMemPhys.lean (header cites it) |  |
| MinstretInv | 45 | 564 | +132/-293 | ANALOG | MachCSL/HwConfig.lean (existential counters), MachCSL/UCycleDefs.lean | Lean has no minstret invariant (counters existential) |
| MstatusBits | 7 | 346 | +43/-2 | ANALOG | MachCSL/KCtx.lean + WpTrap.lean (`trapMs`), WpSmodeSret.lean (`sretMs`) |  |
| MstatusFacts | 2 | 61 | 0 | ANALOG | MachCSL/KCtx.lean / MConf.lean | no named fact bundle |
| ProcGeom | 28 | 1188 | +322/-161 | 1:1 | Xv6/ProcGeom.lean |  |
| Pt4kWalk | 30 | 762 | +33/-34 | ANALOG | MachCSL/UTlb.lean, UWalk.lean, WpPtWalk.lean, Translate.lean |  |
| PtAdBits | 19 | 528 | +189/-40 | ANALOG | MachCSL/PteClass.lean (`pte_set_ad`) | weak-line additions (write-back discriminator) NOT in Lean, see §3 |
| PtTree | 133 | 2022 | +679/-114 | 1:1 | MachCSL/PtTree.lean (+ Xv6/PtOwn.lean) |  |
| PtTreeAdue | 25 | 956 | +1769/-112 | ANALOG | MachCSL/UWalk.lean, UTlb.lean (Svadu arm) |  |
| PtreeType | 7 | 30 | 0 | ANALOG | MachCSL/PtTree.lean |  |
| RegFile | 64 | 127 | +4/-4 | ANALOG | MachCSL/Lang.lean (`RegFile` = BootRun.`BootRegs`) |  |
| RiscvAdequacy | 13 | 1113 | +1727/-606 | 1:1 | MachCSL/Adequacy.lean (+ AdequacyDisk, Power) |  |
| RiscvExec | 204 | 914 | +1057/-316 | MISSING | -- (partial: MachCSL/BootRun.lean `bootRun`, register-only; MachCSL/URunRW.lean `runRW`, user-tier walker; lean-sail `PreSailM.interp`) | the run/exec interpreter, determinism bridge, `wp_exec_step`; 204 weak importers |
| RiscvExtras | 170 | 1807 | +279/-139 | ANALOG | MachCSL/ModelFacts.lean, BvLemmas.lean, AluFacts.lean | no 1:1 |
| RiscvFetchExec | 142 | 1601 | +159/-23 | ANALOG | MachCSL/HwConfig.lean (`hw_config`), WpSmodeFetch*.lean, UFetch*.lean | exec-level fetch engine has no Lean twin |
| RiscvLang | 375 | 857 | +1513/-116 | ANALOG | MachCSL/Lang.lean (+ TsoMem, BootImage, Dev/DevLang) | Lean language is event-granular (free monad) with TSO + icache memory; Rocq is SC, whole `try_step` per step |
| RiscvModelBytes | 364 | 202 | +105/-0 | ANALOG | MachCSL/ByteWordDefs.lean, ByteWord.lean, TsoMem.lean (`nthByte`) |  |
| RiscvPtsto | 214 | 1987 | +1953/-416 | 1:1 | MachCSL/Resources.lean (+ Ctx.lean, WordPointsTo.lean) |  |
| RiscvTryStep | 133 | 1618 | +25/-69 | ANALOG | MachCSL/UCycleDefs.lean, UCycle.lean, WpCycle.lean |  |
| SRegime | 4 | 496 | +1409/-39 | ANALOG | MachCSL/Ctx.lean (`CurCtx` tiers), PmpXv6Defs.lean |  |
| SmodeCore | 76 | 1396 | +68/-144 | ANALOG | MachCSL/WpSmode*.lean (WpSmodeFetch, WpSmodeRules, WpSmodeIntr) |  |
| SmodePte | 103 | 498 | +42/-12 | ANALOG | MachCSL/WpPtWalk.lean, Translate.lean, WpSmodePmp.lean |  |
| SpecCpuid | 2 | 121 | +17/-16 | 1:1 | Xv6/SpecCpuid.lean |  |
| SpecHolding | 5 | 112 | +47/-24 | 1:1 | Xv6/SpecHolding.lean |  |
| SpecPushOff | 5 | 116 | +84/-27 | 1:1 | Xv6/SpecPushoff.lean |  |
| SpecRelease | 5 | 173 | +221/-41 | 1:1 | Xv6/SpecRelease.lean |  |
| StackOwn | 12 | 534 | +166/-58 | ANALOG | MachCSL/KCtx.lean (`stackOwn`), StackOwnBounds.lean |  |
| UserBits | 32 | 645 | +24/-26 | MISSING | -- | no cite, no `pa_window` twin found |
| UserPtTree | 5 | 588 | +1629/-30 | ANALOG | Xv6/UPtDefs.lean, Xv6/UserExec.lean |  |
| UserretDefs | 1 | 683 | +193/-81 | 1:1 | Xv6/UserretDefs.lean |  |
| UservecPt | 4 | 765 | +413/-374 | 1:1 | Xv6/UservecPt.lean |  |
| VcGen | 8 | 627 | +24/-14 | MISSING | -- | reflective VC generator; nothing like it in Lean |
| VirtioModel | 1 | 1308 | +1876/-486 | ANALOG | MachCSL/Dev/Virtio.lean |  |
| WpAmo | 11 | 720 | +2/-0 | ANALOG | MachCSL/WpSmodeAtomic.lean, WpAtomic.lean, WpLock.lean (amoswap) |  |
| WpAuipc | 5 | 62 | +2/-2 | ANALOG | MachCSL/WpMmodeAlu.lean / WpSmodeAlu*.lean |  |
| WpDecode | 26 | 378 | +8/-5 | ANALOG | MachCSL/DecodeBridge.lean, UDecode.lean |  |
| WpDecodeBridge | 45 | 239 | +51/-2 | 1:1 | MachCSL/DecodeBridge.lean (header cites it) |  |
| WpEntryNew | 1 | 352 | +46/-34 | ANALOG | Xv6/ProofEntry.lean + SpecEntry.lean |  |
| WpGpr | 136 | 287 | +14/-8 | 1:1 | MachCSL/WpGpr.lean (+ WpGprDefs, GprLit, KCtxGpr) |  |
| WpGprCsrrA | 9 | 493 | +310/-187 | ANALOG | MachCSL/WpCsr.lean, WpMmodeCsr.lean |  |
| WpGprCsrrB | 8 | 577 | +419/-178 | ANALOG | MachCSL/WpCsr.lean, WpCsrS.lean |  |
| WpGprCsrrCommon | 6 | 215 | +24/-56 | ANALOG | MachCSL/WpCsrFacts.lean |  |
| WpGprCsrwA | 9 | 1163 | +601/-227 | ANALOG | MachCSL/WpMmodeCsr.lean, WpCsr.lean |  |
| WpGprCsrwB | 7 | 1170 | +795/-321 | ANALOG | MachCSL/WpMmodeCsr.lean, WpCsr.lean |  |
| WpGprCsrwC | 9 | 1280 | +529/-109 | ANALOG | MachCSL/WpMmodeCsr.lean, MConf.lean |  |
| WpGprCsrwCommon | 15 | 301 | 0 | ANALOG | MachCSL/WpCsrFacts.lean |  |
| WpGprMret | 1 | 219 | +1/-0 | ANALOG | MachCSL/WpMmodeMret.lean |  |
| WpGprMretWp | 5 | 115 | +2/-1 | ANALOG | MachCSL/WpMmodeMret.lean |  |
| WpIntrCore | 7 | 576 | +543/-58 | ANALOG | MachCSL/WpSmodeIntr.lean, WireInv.lean |  |
| WpLoad | 57 | 520 | +51/-3 | ANALOG | MachCSL/WpSmodeMem*.lean (MemLd, MemLw, ...) |  |
| WpLock | 14 | 530 | +1764/-214 | 1:1 | MachCSL/WpLock.lean (+ Lock.lean, LockFacts.lean) |  |
| WpMmodeItype | 2 | 170 | +39/-102 | ANALOG | MachCSL/WpMmodeAlu.lean |  |
| WpMmodeJal | 4 | 134 | +45/-62 | ANALOG | MachCSL/WpMmodeCtl.lean |  |
| WpMmodeJalr | 2 | 121 | +41/-68 | ANALOG | MachCSL/WpMmodeCtl.lean |  |
| WpMmodeLeafBase | 127 | 2422 | +29/-35 | ANALOG | MachCSL/WpMmode.lean (`execSpec`, `wpLoop_m_instr`) |  |
| WpMmodeLoad | 2 | 394 | +454/-278 | ANALOG | MachCSL/WpMmode.lean |  |
| WpMmodeMul | 4 | 231 | +29/-75 | ANALOG | MachCSL/WpMmodeAlu.lean |  |
| WpMmodeRtype | 2 | 250 | +59/-175 | ANALOG | MachCSL/WpMmodeAlu.lean |  |
| WpMmodeShiftiop | 40 | 338 | +43/-98 | ANALOG | MachCSL/WpMmodeAlu.lean |  |
| WpMmodeStore | 2 | 348 | +655/-235 | ANALOG | MachCSL/WpMmode.lean |  |
| WpMmodeUtype | 3 | 154 | +42/-87 | ANALOG | MachCSL/WpMmodeAlu.lean |  |
| WpNext | 30 | 149 | +160/-16 | ANALOG | MachCSL/KCtx.lean (`wpNext`) |  |
| WpPushOffCsr | 1 | 234 | +4/-3 | ANALOG | MachCSL/WpSmodeCsr.lean |  |
| WpRvcBridge | 2 | 249 | 0 | ANALOG | MachCSL/DecodeBridge.lean |  |
| WpSconfAlu | 8 | 1523 | +1065/-791 | ANALOG | MachCSL/WpSmodeAlu2/Alu4/RegOps.lean (rules over `kctx`) | Lean merges sconf+sie_cap into the KCtx index |
| WpSconfBtype | 5 | 1781 | +696/-1358 | ANALOG | MachCSL/WpSmodeCtl.lean |  |
| WpSconfCsr | 1 | 1857 | +3695/-980 | ANALOG | MachCSL/WpSmodeCsr.lean, WpSmodeStvec.lean, WpSmodeTrapCsr.lean |  |
| WpSconfCtl | 7 | 621 | +271/-437 | ANALOG | MachCSL/WpSmodeCtl.lean, WpSmodeJalr.lean |  |
| WpSconfLock | 5 | 783 | +2172/-450 | ANALOG | MachCSL/WpLock.lean (header cites WpSconfLock) |  |
| WpSconfMem | 8 | 1752 | +3589/-1168 | ANALOG | MachCSL/WpSmodeMem*.lean, WpStoreFree4.lean, WpSmodeLwKey.lean (cite it) |  |
| WpSmodeGpr | 12 | 1179 | +11/-7 | ANALOG | MachCSL/WpSmode*.lean |  |
| WpSmodeMemGen | 9 | 682 | DELETED/RENAMED in main | ANALOG | MachCSL/WpSmodeMem.lean, WpSmodeMemPhys.lean | deleted on Rocq main by 09-30 |
| WpStartNew | 2 | 1596 | +132/-115 | ANALOG | Xv6/ProofStart.lean + SpecStart.lean |  |
| WpTimerinit | 4 | 553 | +114/-56 | ANALOG | Xv6/ProofTimerinit.lean + SpecTimerinit.lean |  |
| KernelDecode00–31 (32 files) | 332 (import edges) | 14951 | each about +350/−180 (catalog regenerated) | MISSING (by design) | -- (Xv6/KernelText.lean + KernelTree.lean, decode at proof time: KernelTac/CodeTactics) | generated per-instruction decode catalog of the kernel text |

### 2b. Model, kernel image, Sail library, standard libraries

| Rocq module | weak importers | Lean counterpart | status / note |
|---|---:|---|---|
| Riscv.rv64d | 406 | model/Lean_RV64D (`LeanRV64D.*`, generated) | ANALOG. The Lean model is not generated with `-D SYMBOLIC`: no `instr_announce`/`branch_announce` events, no `__monomorphize_reads/writes` registers (§3) |
| Riscv.rv64d_types | 433 | model/Lean_RV64D (`LeanRV64D.*` types) | ANALOG, same caveat |
| Riscv.riscv_extras | 94 | model/Lean_RV64D handwritten `RiscvExtras.lean` + `model/Xv6Extras.lean` | ANALOG. The weak line's `mark_register` stub (SYMBOLIC only) is absent |
| Kernel.KernelSyms | 81 | Xv6/KernelImage.lean (`KernelSyms` namespace) + MachCSL/SimpAttr.lean (`k_addr` simp set) | 1:1 in content |
| Kernel.KernelInstrs | 15 | MachCSL/KernelElf.lean (header: Rocq `KernelInstrs.kernel_bytes`) + Xv6/KernelImage.lean | 1:1 in content |
| SailStdpp.ConcurrencyInterface | 143 | vendor/lean-sail `Sail/ConcurrencyInterfaceV1.lean` (`Outcome`, `PreSailM` = `FreeM`) | ANALOG. **No `InstrAnnounce`/`BranchAnnounce` constructors**, no `ExtraOutcome`/`Discard` (failure is `Except`) |
| SailStdpp.ConcurrencyInterfaceBuiltins | 85 | vendor/lean-sail `Sail/ConcurrencyInterfaceV1.lean`, `Sail/Sail.lean` | ANALOG |
| SailStdpp.ConcurrencyInterfaceTypes | 330 | vendor/lean-sail `Sail/ConcurrencyInterfaceV1.lean` (`Access_kind`, `Mem_read_request`, …) | ANALOG |
| SailStdpp.Base | 173 | vendor/lean-sail `Sail/Common.lean`, `Sail/Sail.lean` | ANALOG |
| SailStdpp.Values | 213 | vendor/lean-sail `Sail/Common.lean`, `Sail/BitVec.lean` | ANALOG |
| SailStdpp.TypeCasts | 176 | Lean `BitVec` / `Sail/BitVec.lean` | ANALOG |
| SailStdpp.MachineWord | 153 | Lean `BitVec` | ANALOG |
| SailStdpp.Operators_mwords | 390 | Lean `BitVec` + `Sail/BitVec.lean` | ANALOG (`mword n` ↦ `BitVec n`) |
| SailStdpp.Instances | 1 | vendor/lean-sail `Sail/Common.lean` | ANALOG |

**stdpp / Stdlib / iris.** The Lean side is Lean core, Batteries and iris-lean (`.lake/packages/iris`). Every iris module the weak files use has a counterpart:

| Rocq | weak importers | Lean |
|---|---:|---|
| iris.algebra.agree | 82 | Iris.Algebra.Agree |
| iris.algebra.auth | 107 | Iris.Algebra.Auth |
| iris.algebra.csum | 2 | Iris.Algebra.Csum |
| iris.algebra.dfrac | 146 | Iris.Algebra.DFrac |
| iris.algebra.excl | 8 | Iris.Algebra.Excl |
| iris.algebra.functions | 4 | Iris.Algebra.Functions |
| iris.algebra.gmap | 29 | Iris.Algebra.GenMap / Heap |
| iris.algebra.gmap_view | 59 | Iris.Algebra.HeapView / View |
| iris.algebra.gset | 103 | Iris.Algebra.LeibnizSet / Iris.Std.GenSets |
| iris.algebra.lib.excl_auth | 6 | Iris.Algebra.Lib.ExclAuth |
| iris.algebra.lib.gmap_view | 1 | Iris.Algebra.HeapView |
| iris.algebra.lib.mono_list | 8 | Iris.Algebra.Lib.MonoList / Iris.BI.Lib.MonoList |
| iris.algebra.local_updates | 1 | Iris.Algebra.LocalUpdates |
| iris.algebra.numbers | 4 | Iris.Algebra.Numbers |
| iris.algebra.stepindex_finite | 65 | Iris.Algebra.StepIndex |
| iris.algebra.updates | 1 | Iris.Algebra.Updates |
| iris.base_logic.bi | 52 | Iris.BI / Iris.Instances.UPred |
| iris.base_logic.iprop | 1 | Iris.Instances.IProp |
| iris.base_logic.lib.fancy_updates | 205 | Iris.Instances.Lib.FUpd / WSat |
| iris.base_logic.lib.gen_heap | 9 | Iris.BI.Lib.GenHeap |
| iris.base_logic.lib.ghost_map | 145 | Iris.Instances.Lib.GhostMap |
| iris.base_logic.lib.ghost_var | 87 | Iris.Instances.Lib.GhostVar |
| iris.base_logic.lib.invariants | 70 | Iris.Instances.Lib.Invariants |
| iris.base_logic.lib.iprop | 67 | Iris.Instances.IProp |
| iris.base_logic.lib.mono_nat | 42 | Iris.BI.Lib.MonoNat / Iris.Algebra.Lib.MonoNat |
| iris.base_logic.lib.own | 154 | Iris.Instances.IProp (own) |
| iris.base_logic.lib.saved_prop | 83 | Iris.Instances.Lib.SavedProp |
| iris.bi.lib.fractional | 6 | Iris.BI.Lib.Fractional |
| iris.bi.monpred | 5 | Iris.BI.MonPred |
| iris.program_logic.adequacy | 12 | Iris.ProgramLogic.Adequacy |
| iris.program_logic.language | 237 | Iris.ProgramLogic.Language |
| iris.program_logic.lifting | 54 | Iris.ProgramLogic.Lifting |
| iris.program_logic.weakestpre | 58 | Iris.ProgramLogic.WeakestPre |
| iris.proofmode.monpred | 54 | Iris.ProofMode.MonPred |
| iris.proofmode.proofmode | 331 | Iris.ProofMode |
| stdpp.{gmap,finite,list,relations,sorting,namespaces,list_numbers} | 1937 (import edges) | Lean core + Batteries + Iris.Std (`PartialMap`, `GenSets`, `Relation`, `Namespaces`, `List`); `List.mergeSort` |
| stdpp.bitvector.{definitions,tactics} | 623 (import edges) | Lean core `BitVec` + `bv_decide`/`omega` |
| Stdlib.{ssr.ssreflect,ZArith,Lia,Bool,List,Zquot,Zwf,Wf_nat,Eqdep_dec,FunctionalExtensionality} | 694 (import edges) | Lean core (`Int`, `omega`, `funext`, well-founded recursion); ssreflect has no counterpart and is not needed |

## 3. Non-weak files the weak line changed since the fork

Source: `jj diff --from nrymuwtz --to xxvzwolszwmp --summary/--stat`, restricted to `iris/` (excluding Weak\*/Ax\*), `model-xv6iris/` and `kernel-rocq/`. `kernel-rocq/` is unchanged. `nrymuwtz` is the merge base of the weak line with `7d988ae13`; the weak line's one `merge origin/main` (`tksyvszu`) merged `nrymuwtz` itself, so this diff contains only weak-line work. The user's example, "WPd made parametric in the consistency model", happens inside weak files (`AxWpD*.v`) and changes no shared definition. The only shared definitions that changed are the regenerated model and the lemmas that go with it.

| file | change | what changed | on Rocq main @7d988ae13? | in Lean? |
|---|---|---|---|---|
| model-xv6iris/rv64d.v | +72/−99 (`git diff --numstat`; most lines are renamed binders) | **Model regenerated with `-D SYMBOLIC`** (`tools/regen_sail_model.sh`, 2026-08-17). `sail_instr_announce`/`sail_branch_announce` (pure `unit`) become the monadic `instr_announce`/`branch_announce` events (`liftR (instr_announce w) >> …` after every fetch, `branch_announce xlen pc >> write_reg nextPC …` at every PC redirect). `sail_mark_register` becomes the extern `mark_register`. `__monomorphize_reads/writes` become registers written at init. **This is the change the weak tier needs: `WeakEvInst` reads operand fields off the announced opcode.** | **No.** Main still has `sail_instr_announce` as pure `unit` | **No.** The Lean model is generated without SYMBOLIC (`Step.lean:341` `let _ : Unit := sail_instr_announce h`), and lean-sail `Outcome` has no announce constructors. The weak port needs both: regenerate the model, and add the events to `Outcome`, to `MachCSL.Lang.evStep` (as silent events) and to the swp rules |
| model-xv6iris/rv64d_types.v | +22/−10 | `register_bool` gains `__monomorphize_reads`/`__monomorphize_writes`, which renumbers it (`num_of_register_bool`) and adds `_ref`s; the dummy instance changes | No | No (same regeneration) |
| model-xv6iris/riscv_extras.v | +6 | No-op `mark_register` stub (`tools/riscv_extras_symbolic.v`, appended by the regen script) | No (main added the reservation/`plat_term_*` axioms instead) | No (Lean needs it only with SYMBOLIC) |
| iris/RiscvExec.v | +12 | `exec_instr_announce`, `exec_branch_announce`: the announcements are silent for `exec` | No | N/A: Lean has no `exec`. The counterpart is a silent `evStep` arm plus a `swp` rule per event |
| iris/ExecCommon.v | +2 | proof fix in `exec_set_next_pc` (rewrite past the branch announce) | No | N/A |
| iris/RiscvFetchExec.v, RiscvTryStep.v, SmodeCore.v (×2), UserStep.v (×2) | +2 each site | the same one-line proof fix after `ext_fetch_hook` (rewrite past the instruction announce) | No | N/A (Lean fetch-cycle proofs would each need the matching step over the new event) |
| iris/PtAdBits.v | +97 | **Write-back discriminator**: `pte_flags_A_bit6`, `pte_flags_D_bit7`, `update_PTE_Bits_A1` (a write-back always sets A), `update_PTE_Bits_ne` (`Some` only when a bit flips). These license `WeakPromise.ad_shaped`'s `data ≠ read` conjunct | No (0 occurrences at 7d988ae13) | No (`MachCSL/PteClass.lean` has `pte_set_ad`, but neither lemma) |
| iris/_CoqProject | +573 | file list for the new weak files | N/A | N/A (lakefile globs) |
| iris/KernelPins.v (gen), KernelPinsDef.v, KernelSites.v (gen), KernelSitesDef.v | +1672, +607, +133, +559 (new) | kernel pin/site catalogs and their definitions for the RVWMO pin bridge (`WeakRvwmoPinBridge*`); generated by `tools/gen_pins.py` and `tools/gen_sites.py` (+ `pins.json`/`sites.json`) | No (absent) | No |
| iris/VirtioProg.v | +842 (new) | "THE DEVICE PROGRAM (M5)": the virtio device as a program, imported by 24 AxEpi/AxAllHarts files | No (absent) | No |
| iris/Wk*.v (21 files) | +17,906 (new) | weak-tier whole-function proofs of the boot and kernel code (start, timerinit, entry, walk capstone, memmove, ping-pong, …) | No (absent) | No |

The weak line also changed, outside `iris/`: `Makefile` (+74), `tools/regen_sail_model.sh` (+17/−2, the `-D SYMBOLIC` flag), `tools/riscv_extras_symbolic.v` (new), the generators `tools/gen_{pins,sites,shape}.py` (new), and the `gcp-rocq/` build scripts.

## 4. Recommended porting order for parallel workers

**Constraint.** Neighbouring layers are densely connected, so no partition into ~20k-line packages leaves packages fully independent. If every package waits for all its prerequisite packages to finish, the package-level critical path is about 280k of the 361k lines. The plan below therefore uses **3 phases × 6 lanes = 18 packages of about 20k lines**:

* A phase starts only when the previous phase is fully ported (a hard barrier).
* Inside a phase, the six packages run at the same time. A worker ports its package's files **in the order listed**. Before starting a file, the worker waits until that file's imports from peer packages of the same phase exist (the "waits on" column counts those import edges per peer package; the waits are at file level).
* A simulated schedule (one unit of time = one Rocq line) finishes in **64.0k** time units. The lower bound for 6 workers is 361k/6 = 60.2k, and the critical path alone is 50.4k. Without the barriers, file-level gating alone gives 62.6k.
* Packages were built by list scheduling: each free worker takes the ready file that has the longest remaining chain of importers after it, with a bonus for staying in the same file family. Each package is that worker's files within one phase, so files of a family tend to stay together.
* Critical-path files (`*`) set the finish time. Give them to the strongest or earliest worker and port them first within their package.

**Before phase A** (shared with every package, not part of any line count): decide how the weak tier sits on Lean's event language (§0); regenerate the Lean model with `-D SYMBOLIC` and add `InstrAnnounce`/`BranchAnnounce` to lean-sail `Outcome` and to `MachCSL.Lang` (§3); port the `PtAdBits` write-back lemmas; settle the `RiscvExec`/`ExecCommon` replacement and the decode-catalog question for weak leaves (§2). Each of these blocks layer 0–3 files: `WeakMem`, `WeakInterp`, `WeakLang`, `WeakEvLang`, `WeakSail*`.

| package | phase | lines | files | layers | main families | waits on (same-phase package: import edges) |
|---|---|---:|---:|---|---|---|
| **A1** | A | 21,449 | 20 | 0–14 | WeakRobust 4, WeakPromise 3, WeakFetch 3, WeakRvwmo 2, WeakFunnel 2 | A2: 24, A3: 50, A4: 10, A5: 18, A6: 9 |
| **A2** | A | 19,509 | 26 | 0–15 | WeakRvwmo 4, WeakLeaf 4, WeakAxiomatic 3, AxLock 2, WeakPmp 2 | A1: 50, A3: 77, A4: 35, A5: 32, A6: 9 |
| **A3** | A | 18,743 | 15 | 0–13 | WeakRvwmo 2, Virtio 1, WeakInterp 1, WeakLang 1, WeakGhost 1 | A1: 27, A2: 15, A4: 10, A5: 8, A6: 3 |
| **A4** | A | 18,409 | 21 | 0–13 | WeakRvwmo 6, WeakEv 5, AxGraph 4, Kernel 2, AxReuse 1 | A1: 31, A2: 26, A3: 24, A5: 15, A6: 15 |
| **A5** | A | 17,867 | 22 | 0–15 | WeakLeaf 6, WeakRvwmo 2, WeakEff 2, WkGpr 1, AxSpin 1 | A1: 42, A2: 18, A3: 55, A4: 5, A6: 4 |
| **A6** | A | 18,051 | 14 | 0–13 | WeakRobust 8, Kernel 1, WeakLitmus 1, WeakInterp 1, WeakAx 1 | A1: 62, A2: 13, A3: 3, A4: 7, A5: 6 |
| **B1** | B | 20,924 | 36 | 13–37 | AxLock 12, AxEpi 5, WeakLeaf 4, AxWp 3, AxTier 3 | B2: 49, B4: 77, B5: 11, B6: 21 |
| **B2** | B | 20,717 | 34 | 5–38 | AxLock 11, WeakLeaf 6, AxDefer 5, AxProt 4, AxGate 2 | B1: 50, B4: 79, B5: 26, B6: 14 |
| **B3** | B | 21,263 | 19 | 14–37 | WeakRvwmo 18, AxTok 1 | B1: 3, B2: 6, B4: 7, B6: 20 |
| **B4** | B | 20,385 | 18 | 13–36 | WeakEv 3, AxAdequacy 3, AxTok 2, AxPair 1, AxOpsem 1 | B1: 17, B2: 8, B3: 2, B5: 12, B6: 6 |
| **B5** | B | 21,246 | 28 | 11–36 | AxProt 7, WeakLeaf 6, AxSched 3, AxEpi 2, AxRun 2 | B1: 27, B2: 39, B4: 76, B6: 15 |
| **B6** | B | 20,625 | 41 | 5–30 | WeakShape 24, WeakRvwmo 8, AxSpin 2, AxGate 1, AxSched 1 | B1: 4, B2: 1, B3: 6, B4: 4 |
| **C1** | C | 20,075 | 48 | 12–58 | AxSpin 30, AxEpi 14, WeakLeaf 1, AxWalk 1, AxSfence 1 | C2: 56, C3: 231, C4: 178, C5: 67, C6: 188 |
| **C2** | C | 19,920 | 25 | 6–45 | AxLock 4, AxCert 4, AxWalk 4, WkWalk 3, WkStart 2 | C4: 28, C5: 20, C6: 12 |
| **C3** | C | 20,317 | 69 | 11–60 | AxSpin 61, AxEpi 2, AxCls 1, WeakBranch 1, WkClip 1 | C1: 84, C2: 53, C4: 290, C5: 134, C6: 358 |
| **C4** | C | 20,677 | 60 | 5–53 | AxSpin 21, AxSym 10, AxRelease 8, AxData 4, AxPt 3 | C1: 10, C2: 25, C3: 46, C5: 70, C6: 218 |
| **C5** | C | 20,242 | 31 | 11–52 | AxIntr 5, AxSc 4, AxCert 3, AxLedger 3, AxSym 2 | C1: 18, C2: 8, C3: 4, C4: 37, C6: 43 |
| **C6** | C | 20,605 | 45 | 10–51 | AxSpine 6, AxData 6, WeakShape 5, AxSpin 5, AxLeaf 4 | C1: 19, C2: 27, C3: 43, C4: 80, C5: 31 |

Prerequisites: every phase-B package needs all of phase A, and every phase-C package needs all of phases A and B. Within a phase, a worker only ever waits on a file that the schedule starts earlier, so file-level waiting cannot deadlock.

### Package contents, in porting order

Format: `file:lines`. `←Xn` means the file imports files from peer package Xn of the same phase and must wait for them. `*` marks the critical path, † a weak-line-added non-Weak/Ax file.

- **A1** (21,449 lines, 20 files): WeakMem*:3001; WeakPromise*:1599; WeakPromiseFact*:1167; WeakPromiseBridge*:1399 ←A2; WeakRobust*:214; WeakRobustGraph*:1071 ←A2,A6; WeakRobustProv*:1611 ←A2,A6; WeakFence:448 ←A2,A3; WeakRvwmoTopo:656 ←A2,A4; WeakRvwmoDec:367 ←A2,A4; WeakRobustAcyc2:583 ←A2,A5,A6; WeakSailLTS2:1531 ←A3,A6; WeakSrvwmoLitmus:1899 ←A2,A6; WeakAcquire:823 ←A2,A3,A5; WeakFunnel:940 ←A2,A3,A5; WeakFunnelCfg:351 ←A2,A3,A5; WeakFetchEff:1239 ←A2,A3,A5; WeakFetchRvc:406 ←A2,A3,A5; WeakFetch2:1057 ←A2,A3,A5; WeakEvProv:1087 ←A3,A4,A5
- **A2** (19,509 lines, 26 files): WeakView:479; AxSlice:2; KernelSites†:133 ←A6; WeakAxiomatic:1836 ←A1; WeakAxiomatic2:1447 ←A1; WeakAxiomatic3:2716 ←A1; WeakRobustSer:747 ←A1,A6; WeakRvwmoLin:1751 ←A1,A4; WeakRvwmoRestr:650 ←A1,A4; WeakRvwmoProbeRestr:219 ←A1,A4,A6; WeakRvwmoHull:948 ←A1,A4,A6; AxTieProc:570 ←A1,A4,A5,A6; WeakWord8:1032 ←A1,A3; AxBridge:635 ←A1,A4,A5,A6; AxLockGraph:336 ←A1,A4,A5,A6; AxLockSerial:433 ←A1,A4,A5,A6; WeakTickEff:397 ←A1,A3,A5; WeakPmpEff:358 ←A1,A3,A5; WeakPmpTorEff:207 ←A1,A3,A5; WkStartedLoad†:433 ←A1,A3,A5; WkStartedMp†:267 ←A1,A3,A5; WeakVariant:1021 ←A1,A3,A6; WeakLeafWin:287 ←A1,A3,A5; WeakLeafLd8:626 ←A1,A3,A5; WeakLeafSd8:644 ←A1,A3,A5; WeakLeafTor:1335 ←A1,A3,A5
- **A3** (18,743 lines, 15 files): VirtioProg†:842; WeakInterp:1015 ←A1; WeakLang:913 ←A1; WeakGhost:3818 ←A1,A2,A4; WeakVProp:1248 ←A1,A2; WeakExec:392 ←A1; WeakBridge:874 ←A1,A2; WeakInstr:1056 ←A1,A2; WeakStore:1548 ←A1,A2; WeakLock:916 ←A1,A2; WeakStarted:688 ←A1,A2; WeakRacy:1449 ←A1; WeakEvInst:1799 ←A1,A4,A5,A6; WeakRvwmoConf:1317 ←A1,A2,A4,A5,A6; WeakRvwmoSupply:868 ←A1,A2,A4,A5,A6
- **A4** (18,409 lines, 21 files): AxReuseProbe:577; WeakViewMono:499 ←A1; KernelPinsDef†:607 ←A1,A5,A6; KernelPins†:1672 ←A6; WeakRvwmoGraph:835 ←A1,A2,A6; WeakRvwmoXchg:1380 ←A1,A2; WeakRvwmoNorm:1137 ←A1,A2; WeakRvwmoAcyc:623 ←A1,A2; WeakRvwmoProbeK1:376 ←A1,A2,A6; WeakRvwmoKill:322 ←A1,A2; AxGraph:732 ←A1,A2,A5,A6; AxGraphCat:1475 ←A1,A2,A5,A6; AxGraphDec:731 ←A1,A2,A5,A6; AxGraphWit:553 ←A1,A2,A5,A6; AxGhost:760 ←A1,A2,A5,A6; AxViol:410 ←A1,A2,A5,A6; WeakEvPf*:737 ←A1,A3,A5,A6; WeakEvAdequacy*:932 ←A1,A3,A5,A6; WeakEvLift*:2264 ←A1,A3,A5,A6; WeakEvStarted*:1069 ←A1,A2,A3,A5,A6; WeakEvExecEff:718 ←A1,A3,A5
- **A5** (17,867 lines, 22 files): WkGprAcc†:62; AxSpinSpikeRun:180; AxSymReg:280; WeakDeps:1132 ←A1; WeakPromiseLitmus:266 ←A1; WeakLitmusProj:290 ←A1,A2,A6; WeakEvLang:1679 ←A1,A3,A6; WeakErase:879 ←A1,A2; WeakRefuse:890 ←A1,A2; WeakRobustAcyc:1136 ←A1,A2,A6; WeakViolation:256 ←A1,A3; WeakRvwmoLock:506 ←A1,A2,A4; WeakRvwmoKillArms:1661 ←A1,A2,A3,A4,A6; WeakCert:1810 ←A1,A2,A3; WeakEff:864 ←A1,A2,A3; WeakEffSkel:850 ←A1,A2,A3; WeakLeafEffCommon:607 ←A1,A2,A3; WeakLeafEff8:591 ←A1,A2,A3; WeakLeafEff8s:654 ←A1,A2,A3; WeakLeafAmo4:1372 ←A1,A2,A3; WeakLeafBase4:1579 ←A1,A2,A3; WeakLeafRegOnly:323 ←A1,A2,A3
- **A6** (18,051 lines, 14 files): KernelSitesDef†:559; WeakLitmus:1535 ←A1; WeakInterpProj:412 ←A1,A2,A3; WeakRobustTrace:1486 ←A1; WeakAxRealize:1005 ←A1,A2; WeakSailLTS:1332 ←A1,A3; WeakRobustLin:611 ←A1; WeakRobustOrd*:1321 ←A1,A2,A5; WeakRobustSim*:2147 ←A1,A2,A5; WeakRobustMain*:1962 ←A1,A2,A5; WeakRobustBlocks:1303 ←A1,A2; WeakRobustCone:2010 ←A1,A2; WeakRobustDisc:1459 ←A1,A2,A5; AxDeps:909 ←A1,A2,A3,A4,A5
- **B1** (20,924 lines, 36 files): WkEntryEff†:651; WkEntryNew†:1781; WeakLeafJump:746; WeakLeafRtypeW:1075; WeakLeafStimecmp:583 ←B5; WeakLeafLw4:510; WeakWalkEff:1607; WeakUpdEff:1173; AxGateWp:246 ←B4,B6; AxReadAll:310 ←B4; AxWpD:449 ←B4; AxWpDSteps:528 ←B4; AxWpDHarts:303 ←B4; AxWpdLift:119 ←B4; AxRunClose:361 ←B4,B6; AxTierA2:389 ←B4,B5,B6; AxTierA3:365 ←B4,B5,B6; AxTierA:244 ←B4; AxLockOwn:260 ←B2; AxLockWp2:317 ←B2,B4; AxLockWp:255 ←B2,B4; AxLockWpD:261 ←B2,B4; AxLockAdeq:1892 ←B2,B4; AxLockSlice:445 ←B2,B4; AxLockGen:436 ←B2,B4,B5,B6; AxLockRace2:311 ←B2; AxLockRace3:289 ←B2,B4; AxLockWitness:243 ←B2,B4; AxLockMutex:358 ←B2,B4; AxLockMutex2:345 ←B2,B4; AxLdspWpd:493 ←B2,B4,B5,B6; AxEpiLedger:979 ←B2,B4,B6; AxEpiLedgerSd:688 ←B2,B4,B6; AxEpiLedgerTick:986 ←B2,B4,B6; AxEpiChainSdLd:303 ←B2,B4,B6; AxEpiOwned:623 ←B2,B4,B5,B6
- **B2** (20,717 lines, 34 files): WeakLeafSdspOff:478; WeakLeafCsrrM:1640 ←B5; WeakLeafCsrw3:1348 ←B5; WeakLeafItype:796 ←B1; WeakLeafPmpcfg0:477 ←B5; WeakLeafM:1925 ←B1,B5; WeakSrvwmoCapstone:184 ←B6; WeakCtx:627; AxToken:603 ←B4; AxProt:594 ←B4; AxProtLock:440; AxProtLock2:478 ←B4; AxDefer:397 ←B4,B6; AxGateAdeq:239 ←B1,B4,B5,B6; AxGateAdeq2:169 ←B1,B4,B5,B6; AxCjrWpd:308 ←B1,B4,B6; WeakKpt:1630 ←B1; AxProtLock3:659 ←B1,B4; WeakPtPub:280; AxLock3Wp:430 ←B1,B4; AxLockRace:292; AxLock3:777; AxLockN:863 ←B1,B4,B5,B6; AxLockN2:323 ←B1,B4,B5,B6; AxLockN3:443 ←B1,B4,B5,B6; AxLockSmell:152 ←B1,B4; AxDefer2:519 ←B4,B6; AxDefer3:462 ←B1,B4,B6; AxDefer5:413 ←B1,B4,B5,B6; AxDefer4:242 ←B4,B6; AxLock3Prog*:656 ←B1,B4,B5; AxLock3Wp3:258 ←B4; AxLock3Wp2:252 ←B1,B4; AxLock3Writer:1363 ←B1,B4
- **B3** (21,263 lines, 19 files): WeakRvwmoConfWit*:174; WeakRvwmoConfWit2*:642; WeakRvwmoAdm*:903; WeakRvwmoCert:642; WeakRvwmoCert2:1461; WeakRvwmoFloor:1230; WeakRvwmoCert3:2716; WeakRvwmoCert4:1009 ←B6; WeakRvwmoGlue:881 ←B6; WeakRvwmoGlue2:892 ←B6; WeakRvwmoCapstone:403 ←B2,B6; WeakRvwmoWalk:2888 ←B6; WeakRvwmoCycWit:1343; WeakRvwmoProgress:690 ←B2,B6; WeakRvwmoWalk2:1348 ←B2,B6; WeakRvwmoPreNorm:1093 ←B2,B6; WeakRvwmoCycWit2:1116 ←B4,B6; WeakRvwmoPreNorm2:961 ←B2,B6; AxTokLedgerMp*:871 ←B1,B2,B4
- **B4** (20,385 lines, 18 files): WeakEvFunnel:1030; WeakEvDisk:673; WeakEvProv2*:856 ←B3; AxPair*:1977 ←B3; AxOpsem*:1302; AxWp*:1642; AxLifting*:468; AxAdequacy*:827; AxAdequacyL*:619 ←B6; AxAdequacyChk:371; AxFetch:4951 ←B1,B2,B5,B6; AxRegOnly:334 ←B1,B2,B5; AxTokLedger:885 ←B1,B2,B5,B6; AxTokLedgerWp:1074 ←B1,B5,B6; AxClsStep:320 ←B1,B6; AxEpiSat:261 ←B1; WeakLeafO:2488 ←B2; AxReuseProbe2:307 ←B1
- **B5** (21,246 lines, 28 files): WeakLeafCsrw:599; WeakLeafCsrrTime:569; WeakLeafCsrw2:2055; WeakLeafUtypeShift:1236 ←B1; WeakLeafMret:671; WeakLeafSw4:521; WeakVarCert:697; WeakStale:2625; AxInstr:653 ←B2,B4; AxSchedIris:340 ←B2,B4,B6; AxSchedGD*:429 ←B4,B6; AxSchedFwd:223 ←B4,B6; AxProtInst*:339 ←B2,B4,B6; AxProtCov*:157; AxProtCov2*:437 ←B2,B4,B6; AxProtCov3*:792 ←B1,B2,B4,B6; AxProtGate*:1773 ←B1,B2,B4,B6; AxProtBytes*:989 ←B1,B2,B4,B6; AxProtGateN:260 ←B1,B2,B4,B6; AxEpilogue*:1140 ←B1,B2,B4; AxEpiShape*:347 ←B1,B2,B4; AxEpiChain*:1406 ←B1,B2,B4; AxRowConf*:382 ←B1,B2,B4; AxRunGV*:281 ←B1,B2,B4; AxRunGV2:355 ←B1,B2,B4; AxSpinGate:518 ←B1,B2,B4,B6; AxSpinJ:381 ←B1,B2,B4,B6; WeakWalkStale:1071 ←B1
- **B6** (20,625 lines, 41 files): AxGate:275; AxSched:694; WeakSailComplete:2829; WeakRetag:930; WeakEvCapstone:1106; WeakRvwmoLinInd:440; WeakRvwmoFab:961; WeakRvwmoFabInd:670; WeakRvwmoLin2:1259 ←B3; WeakRvwmoLockWit:455; WeakRvwmoPinBridge:483 ←B3; WeakRvwmoPinBridge2:743 ←B3; WeakRvwmoProbeSwap:422; AxBoundaryWpd:444 ←B1,B4; AxEpiProbe:345 ←B4; AxSpinProt:1010 ←B1,B2; AxSpinSpike:617; WeakShape:1504; WeakShapeOverrides:620; WeakShapeOverrides2:514; WeakShapeGen01:292; WeakShapeGen02:210; WeakShapeAst:474; WeakShapeGen03:82; WeakShapeGen04:82; WeakShapeGen05:82; WeakShapeGen06:82; WeakShapeGen07:82; WeakShapeGen08:82; WeakShapeWin:614; WeakShapeGen09:82; WeakShapeGen10:82; WeakShapeGen11:82; WeakShapeGen12:82; WeakShapeGen13:82; WeakShapeGen14:82; WeakShapeGen15:42; WeakShapeMem:952; WeakShapeExecGen01:191; WeakShapeExecGen02:192; WeakShapeDec:353
- **C1** (20,075 lines, 48 files): AxEpiSdLdSat:148; AxEpiAdeq:986; AxEpiCjrSym:286; AxEpiRace2:227; AxEpiSound2:269; AxEpiCjrFrame:898; AxEpiSound3:362; AxEpiRun:286; AxEpiRace2Run:406; AxEpiLdX1:116; AxEpiLdJr:857; AxEpiTwinExact:223; AxEpiRetCert:527; AxEpiTrivial:105; AxSpinRow:206; AxSpinX3:536 ←C3; AxSpinProt8:413 ←C3; AxSpinE3:516 ←C2,C3,C4,C5,C6; AxSpinH4*:836 ←C3,C4; AxSpinH5*:654 ←C3,C4,C6; AxSpinU*:882 ←C3,C4,C6; AxSpinU2*:392 ←C3,C4,C6; AxSpinU3*:252 ←C3,C4,C6; AxSpinU4*:465 ←C3,C4,C6; AxSpinJ2*:603 ←C3,C4,C6; AxSpinPOx:352 ←C2,C3,C4,C5,C6; AxSpinPO3:398 ←C2,C3,C4,C5,C6; AxSpinHd9:370 ←C2,C3,C4,C5,C6; AxSpinPO1:402 ←C2,C3,C4,C5,C6; AxSpinVA6:406 ←C3,C4,C5,C6; AxSpinHdB:483 ←C2,C3,C4,C5,C6; AxSpinE8d:440 ←C3,C5; AxSpinVA7:362 ←C2,C3,C4,C5,C6; AxSpinE8f:524 ←C2,C3,C4,C5,C6; AxSpinCtl2:484 ←C2,C4,C5,C6; AxSpinXP:260 ←C2,C3,C4,C5,C6; AxSpinXP2:216 ←C2,C3,C4,C5,C6; AxSpinAp8:252 ←C2,C3,C4,C5,C6; AxSpinHdC:337 ←C2,C3,C4,C5,C6; AxSpinAm3:287 ←C2,C3,C4,C5,C6; AxSpinAm4:137 ←C2,C3,C4,C5,C6; AxSpinCtl:336 ←C4,C5,C6; AxSpinCtl3:270 ←C2,C4,C5,C6; AxSpinRow3:443 ←C2,C3,C4,C5,C6; WeakLeafAmo4Leaf:900 ←C3; AxWalk5:139 ←C2,C4,C6; AxSfence2:488 ←C2,C4,C5,C6; WeakCertify:338 ←C6
- **C2** (19,920 lines, 25 files): AxLock3Reader:1810; AxLock3Thm:447; AxLock3Race:569; AxLock3Cert:207; AxCert:419 ←C4,C5,C6; AxCert2:608 ←C4,C5; AxCert4:478 ←C4,C5,C6; AxCertP:210 ←C4,C5; WeakSailCone:3916 ←C6; AxWalk:398 ←C4,C5,C6; AxWalk3:748 ←C4,C6; AxWalk2:425 ←C4,C5; AxWalk7:158 ←C4,C5; WkStackOwn†:161; WkStartAux†:1892; WkWalkTails†:1322 ←C5; WkWalkRule†:461 ←C5; WkWalkCapstone†:1390 ←C5; WeakCtxPt:706; WeakCtxLock:484; WkYieldFrame†:845 ←C5; WkStartNew†:1045 ←C5; WkCtxSurface†:654 ←C5; WkMemmoveLoop†:406 ←C4; WeakLockPayload:161
- **C3** (20,317 lines, 69 files): AxClsStep2*:1441; AxSpinWit*:1126; AxSpinProt2*:562; AxSpinProt3*:717; AxSpinProt5*:588; AxSpinProt6*:368; AxSpinProt7*:1062; AxSpinProt4:316; AxSpinE:614 ←C2,C4,C5,C6; AxSpinX2:784 ←C4; AxSpinX4:374 ←C1,C4; AxSpinE5:230 ←C1,C2,C4,C5,C6; AxSpinE6:283 ←C1,C2,C4,C5,C6; AxSpinHd:139 ←C4,C5,C6; AxSpinHd3:39 ←C4,C5,C6; AxSpinHd5:39 ←C4,C5,C6; AxSpinHd4:37 ←C4,C5,C6; AxSpinHd2:35 ←C4,C5,C6; AxSpinHd2b:31 ←C4,C5,C6; AxSpinPO:122 ←C4,C5,C6; AxSpinPOd:43 ←C4,C5,C6; AxSpinPOt1:40 ←C4,C5,C6; AxSpinPOt3:40 ←C4,C5,C6; AxSpinPOd2:43 ←C4,C5,C6; AxSpinE9:100 ←C1,C4; AxSpinPOt4:40 ←C4,C5,C6; AxSpinPOt5:36 ←C4,C5,C6; AxSpinPOt6:34 ←C4,C5,C6; AxSpinVA6r:31 ←C4,C6; AxSpinE8e:133; AxSpinAm:330 ←C2,C4,C5,C6; AxSpinH7:389 ←C1,C4,C6; AxSpinRow4:171 ←C1; AxSpinE7d:69 ←C4,C5,C6; AxSpinE7c:43 ←C4,C5,C6; AxSpinE8:560 ←C1,C2,C4,C5,C6; AxSpinPOr:245; AxSpinHd6:54 ←C4,C5,C6; AxSpinHd6b:36 ←C4,C5,C6; AxSpinHd6c:32 ←C4,C5,C6; AxSpinHd8:458 ←C1,C2,C4,C5,C6; AxSpinPOc:197 ←C4,C5,C6; AxSpinPOm:338 ←C1,C2,C4,C5,C6; AxSpinVA3:726 ←C1,C2,C4,C5,C6; AxSpinHdA:339 ←C1,C2,C4,C5,C6; AxSpinVA4:400 ←C1,C2,C4,C5,C6; AxSpinPO2:243 ←C1,C2,C4,C5,C6; AxSpinPO5:444 ←C1,C2,C4,C5,C6; AxSpinPO4:322 ←C1,C2,C4,C5,C6; AxSpinAp7:110 ←C6; AxSpinPO6:481 ←C1,C2,C4,C5,C6; AxSpinVA8:450 ←C1,C2,C4,C5,C6; AxSpinRow2:385 ←C1,C2,C4,C5,C6; AxSpinAm2:395 ←C1,C2,C4,C5,C6; AxSpinAp6:87 ←C4,C5,C6; AxSpinAp9:341 ←C1,C2,C4,C5,C6; AxSpinAq:104 ←C1,C4,C5,C6; AxSpinVA5:140 ←C1,C4,C5,C6; AxSpinAqr:110; AxSpinAqd:40 ←C4,C5,C6; AxSpinAqt1:36 ←C4,C5,C6; AxSpinAqt2:36 ←C4,C5,C6; WeakBranch:276; AxEpiSoundFwd:644 ←C1,C5; AxEpiRetFwd:561 ←C1,C4,C5; WkClipAdvance†:306; WeakEvWire:537; AxSymLd:356 ←C5; AxStepDet:79
- **C4** (20,677 lines, 60 files): AxSymEngine:436; AxSymEngine2:674; AxSymEngine3:1329; AxSymMem:475; AxSymMem2:434 ←C5; AxSymMem3:595 ←C5; AxSymCtl4:1393 ←C5,C6; AxDataX6:168 ←C5,C6; AxDataX7:260 ←C2,C6; AxDataX9:209 ←C2,C5,C6; AxDataX10:231 ←C2,C5; AxSpinX:612 ←C3; AxSpinH*:574 ←C3; AxSpinE2:605 ←C2,C3,C5,C6; AxSpinE4:246 ←C1,C2,C3,C5,C6; AxSpinE7:191 ←C3,C5,C6; AxSpinE7f:40 ←C3,C5,C6; AxSpinE7e:38 ←C3,C5,C6; AxSpinE7b:36 ←C3,C5,C6; AxSpinE7g:34 ←C3,C5,C6; AxSpinVA:509 ←C1; AxSpinHd2c:31 ←C3,C5,C6; AxSpinHd7:163 ←C1,C2,C3,C5,C6; AxSpinPOt2:40 ←C3,C5,C6; AxSpinX8:95 ←C3; AxSpinH6:588 ←C1,C3,C6; AxSpinAp:140 ←C3,C5,C6; AxSpinAp2:43 ←C3,C5,C6; AxSpinAp3:34 ←C3,C5,C6; AxSpinAp4:32 ←C3,C5,C6; AxSpinAp5:32 ←C3,C5,C6; AxSpinVA2:267 ←C1,C5,C6; AxRelease6:18; AxRelease2:399 ←C2,C5,C6; AxRelease7:77 ←C6; AxRelease8:77 ←C6; AxSpineOk8:134 ←C5,C6; AxSymCtl3:287 ←C5,C6; AxSymMem4:219 ←C5,C6; AxSymCtl5:247 ←C5,C6; WeakAdequacy:290; AxPtProt:636; AxPtProt2:621; AxPtProt3:429; AxCjrReach:516; AxSchedSH:202; AxRelease:820 ←C2,C5,C6; AxRelease5:162 ←C6; AxRelease4:357 ←C2,C6; AxRelease3:314 ←C6; AxViolSubsume:864; AxDevGraph:792; AxDevGraphWit:300; AxSfence:691; AxLeafS3:330 ←C2,C5,C6; WeakSmodeFrame:366; AxLitmus:537; AxCovMono:181; AxCovClose:162; AxPtwModel:95 ←C1,C2
- **C5** (20,242 lines, 31 files): WeakKptStale:1753; AxSpineOk5:273 ←C4; AxSymCtl:1153 ←C4,C6; AxSymCtl2:915 ←C4,C6; AxIntr:356 ←C4,C6; AxIntr2:223 ←C4,C6; AxIntr3:496 ←C4,C6; AxIntr4:421 ←C4,C6; WkFetchPeel†:1892; WkStepPeel†:1266; AxSmodeProbe:657; AxScCat:399; AxScRun:1194; AxScRun2:468 ←C1; AxScRun3:313 ←C1; WkTimerinitAux†:1034; WkTimerinit†:708 ←C2; WkOwnPingPong†:909; AxTierA4:481 ←C4; AxCertP2:579 ←C1,C2,C3,C4,C6; AxCertP3:337 ←C1,C2,C3,C4,C6; AxCert3:318 ←C2,C4,C6; AxEpiRet:1117 ←C1,C4; AxFwdSource:217 ←C1; AxLedgerG:949; AxLedgerG3:329 ←C3; AxLedgerG2:285; AxGraphAgree:293; WkUnmapMp†:421 ←C3; AxIntr5:221 ←C4,C6; AxInstrFacts:265
- **C6** (20,605 lines, 45 files): WeakShapeExecGen03:176; WeakShapeExec:341; WeakShapeLive:381; WeakShapePeel:99; WeakShapeTop:175; AxSpineOk:423 ←C4; AxSpineOk2:186 ←C4; AxSpineOk3:525 ←C4; AxSpineOk4:596 ←C4; AxSpineOk6:217 ←C4,C5; AxSpineOk7:228 ←C4,C5; WeakCompose:1131; AxDataX:563 ←C4; AxDataX2:265 ←C2,C4; AxDataX3:249 ←C4,C5; AxDataX4:160 ←C2,C4,C5; AxDataX5:132 ←C2,C4,C5; AxLeafS:401 ←C2,C4,C5; AxLeafS2:283 ←C2,C4,C5; AxLeafS4:519 ←C2,C4,C5; AxLeafS5:924 ←C4; AxSpinH2:368 ←C3,C4; AxSpinX5:727 ←C1,C3,C4; AxSpinX6:432 ←C1,C3,C4; AxSpinX7:502 ←C1,C3,C4; AxSpinH3:477 ←C1,C3,C4; AxCondM2:540 ←C2,C4,C5; AxCondM:225; AxCondM3:375 ←C2,C4,C5; AxCondM4:272 ←C2,C4; AxDataX8:108 ←C4,C5; AxWalk4:315 ←C2,C4,C5; AxWalk6:196 ←C2,C4,C5; WeakComposeLang:2231 ←C2,C4; WeakRobustL2:1118; WeakRobustL2b:1042; AxWpcAdeq:653 ←C1,C4,C5; AxAllHarts:647 ←C1,C4,C5; AxSkel:431 ←C4,C5; AxSkelCert:388 ←C1,C4,C5; AxLdgSeal:429 ←C1; AxLdgSealArith:380 ←C1; AxCutProbe:439; AxCov:194; WeakViewRacy:142

### If fewer workers are available

The same scripts give these simulated makespans with file-level gating: 5 workers 74.0k, 6 workers 62.6k, 7 workers 54.8k, 8 workers 50.5k (8 workers already reach the critical path). So more than 7–8 parallel workers do not help, whatever the packaging. **Scope.** The union of the import cones of the 130 `AxSpin*` files (the current spinlock focus, including `AxSpine*`) is 348 files and 214,941 lines. The other 224 files (146,083 lines) feed none of them. They include most of `WeakRvwmo*` (26.5k of 39.4k lines) and `WeakLeaf*` (20.3k of 26.6k), all of `WeakShape*` (8.1k), 13.8k lines of `AxLock*` variants, every `Wk*` proof, `KernelPins`, and the probe and litmus files. If the port only needs the AxSpin capstones, cutting those files saves about 40% of the work. The cone can be recomputed from `weak-port-dag.json`.

