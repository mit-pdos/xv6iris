# Weak port: O2 Stage C — the fetch leaves the graph tier

*Design-advisor note, 2026-10-07 (advisory; no proofs, no edits outside this file).  Owner decision
Stage C (`weak-port-architecture.md`, last entry): D1 reversed — instruction fetches leave the
AxSL/RVWMO graph tier and go through the per-hart i-cache view (`itv`, `fence.i`), as the Lean machine
tier (Stage B) already does.  Goals: verify the assumptions; make the result AS SIMPLE AS POSSIBLE.*

Line references are to `/home/bsdinis/dev/xv6iris-weak/Weak/*.lean` unless a `.v` or `.md` path is given.

## A. Assumption check

### A1. RVWMO + Zifencei: fetches are unordered except via `fence.i` — modelling them outside the graph is faithful.  HOLDS.

- riscv.cat has no instruction-fetch events; the Rocq design already states the faithful treatment:
  "Instruction fetch is an ORACLE on the physical text region T … the fetch returns the boot image"
  (`claude-notes/design/weak-memory-lb-axsl.md:125-134`), and the fetch review concludes "The fetch does
  not need to be in ob or gmo at all … Keeping fetch out of `rvwmo_cat_consistent_t` avoids the whole
  audit" (`claude-notes/design/weak-memory-lb-axsl-review-fetch.md:76-77`).
- What the Rocq graph tier actually did was STRONGER than hardware, not weaker: the fetch was a row
  `LLoad false pc ts vs` (Rocq `AxOpsem.v` `AStepFetch` at `WeakPromise.LLoad aq lat base tvs asrc`), so it
  entered po-loc rules 1-3, `fr`, and `dstep_t`'s `dt_ld`/`dt_adr` (`DTtrans fetch→W` edges) — the review's
  Q2 lists exactly these OUTGOING fetch edges as sound only because "T is never written"
  (`…review-fetch.md:51-60`).  Removing them makes the graph admit MORE executions (closer to hardware);
  no obligation of the memory model is lost.  rf INTO the fetch was already an oracle (`AStepFetch`,
  `fetch_answers`): the value is the image; that pin is kept (A3, B).
- No Lean proof consumes a fetch-sourced dependency edge: `dtLd` is read only inside `AxDeps`, `AxGate`,
  `AxScCat` and `WeakRvwmoConf` (grep), and `AxGate.lean:30-31` records that fetches leave `dtCtl` alone.
  The `DTtrans fetch→W` edges exist today only as REQUIRED edges in `gdexecQconf`'s `rowDeps ⊆ gdDeps`
  clause (`WeakRvwmoSupply.lean:271-278`), i.e. on the premise side; dropping them weakens a premise.

### A2. The Lean machine (Stage B) already gives fetches no data-view effect and reads text through `itv`.  HOLDS.

| where | evidence |
|---|---|
| MachCSL | `MachCSL/Lang.lean:337-339`: a fetch "reads every byte … as the hart's instruction-cache agent at one view between the hart's instruction view and the top, and moves nothing"; `TsoMem.lean:61` `ifetchAgent`, `:389-390` `akIfetch` |
| `WeakInterp.classify` | `WeakInterp.lean:287-306`: `AkInfo ⟨akIfetch k, akExcl k, akAcq k⟩`; `Wmstate.wmItv` `:262`; `itvPost` (`fence.i`) `:363-364` |
| admissibility | `wbyteOk` `:411-415`: the `akIfetch` branch is `¬ writesIn s.wmLog a t (max t s.wmItv)` — no `readable`, no view floor |
| post-state | `wreadPost` `:493-494`: `if ak.akIfetch then s else …` (identity) |
| event language | `WeakEvLang.lean:684-691`: the `akIfetch = true` arm checks `ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) (paZ req.pa) tvs`, `σ' = σ` |
| instance | `WeakEvInst.lean:304-313` emits `LIFetch (paZ pa) tvs` (no aq/lat/asrc, `d' = d`); `elabOk` `:564` = `ifetchOk … (σ.wgitv c)`; `elabWs`/`elabLog` `:595,:603` identity |
| lift | `WeakEvLift.lean:1558-1566` `ewpEvFetch`: premise `(classify req.access_kind).akIfetch = true`, `hartWs c ws` handed back unchanged (Rocq's `efetch_ws` gone) |
| promise machine | `WeakPromise.lean` `WPIFetch`: `ifetchOk cfg.pcImg cfg.pcLog 0 base tvs`, state/log unchanged |
| fetch-view premise | `WeakEvCapstone.lean:681-686` `efetchItvOk`: a view-0-admissible emitted fetch is admissible at `σ.wgitv c`; discharged by `efetchItvOkOfUnwritten` `:688` |

### A3. What xv6 actually needs.  No theorem depends on the fetch being a graph event SEMANTICALLY; several depend on it SYNTACTICALLY (row shapes, counts).

- **Spike graphs** (`AxSpinSpike.lean`): fetch reads are class-1 events (`aeCls` `:365-371`) pushed into
  rows as `LLoad false … (bs.map Prod.fst) (bs.map Prod.snd)` and into `aGmo` (`doEv` `:541-547`); the
  `decide +kernel` pins `countsHart00/11` (499/503 fetch reads, `:801-804`), `gsizeGA/GA'/GB` `:809-811`,
  `fastG40PpoG10` `:819`, `fastG601`/`fastRevG601`, and `AxScCat.g10Sc` `:260` all CHANGE VALUE and are
  recomputed (seconds to ~1 min each, `:63-66`).  Nothing proved ABOUT them needs the fetch events.
- **Hand-built graphs with literal fetch items** `LLoad false pc [0,0,0,0] …`: 23 Rocq files, 12 already
  ported (`AxDeps`, `AxGraphCat`, `AxLitmus`, `AxScCat`, `AxGraphWit`, `AxOpsem`, `AxSfence`, `AxPtProt2`,
  `WeakRvwmoProbeSwap`, `WeakRvwmoLockWit`, `WeakRvwmoProbeRestr`, `WeakSrvwmoLitmus`).  Their fetch items
  become admin items (positions shift; `decide` verdicts recomputed).  None of their THEOREMS is about
  the fetch.
- **Row identity**: `AxPair.lblIdent (LIFetch base tvs) = some ⟨.IKload, …⟩` (`AxPair.lean:161`),
  `AxOpsem.wlRd (LIFetch) = some (false, base, n)` (`:225`), `AStepFetch` (`:691-697`) and `rdLabel`'s `fe`
  flag (`:493-495`) exist ONLY to let a fetch realize a row read.  With no fetch row item they go to
  `none`/are deleted; the `rdLabel` flag stays (the instance still emits `LIFetch`).
- **The fetch-inertness family** (`lbFetchInert`, `candFetchInert(F)`, `emFetchInert`, `hullRunFetchInert`,
  `t2linFetchInert`, `fconfFetchInert`, `wfetchSite`, Q5) exists ONLY because a fetch realizing an
  axiomatic `LLoad` has the identity post-state while `MStepLoad`/`lblPost` apply `loadPostRun`
  (`WeakAxRealize.lean:42-49`, `WeakRvwmoConf.lean:328-347`, `lblPost` `:231-233`).  With no fetch row item
  there is nothing to be inert against: the family is deleted outright (Q5 closes).
- **Does xv6 execute freshly written code?**  The KERNEL never writes kernel text ("xv6 never writes
  kernel text (`fence.i` only on the U-mode trampoline path)", `weak-memory-lb-axsl.md:134`; text is
  era-image at timestamp 0, `claude-notes/design/icache.md:27-29`).  USER text is written by `exec` and
  made visible by `userret`'s `fence.i` (`Xv6/SpecUserret.lean:6`, `Xv6/ProofUserret.lean:9,135`,
  `icache.md:83-87`: the stamp is minted at that `fence.i`); the kernel does NOT rely on `sfence.vma`/`sret`
  for the i-cache.  All weak capstones are at `gen = 0` kernel-mode runs, where the fetched bytes are
  never-written kernel text.  **Nothing breaks.**

### A4. What remains of Q4 after Stage C.

- `efetchItvOk` (`WeakEvCapstone.lean:681`) stays as THE fetch premise of `xv6RvwmoSafeModulo(Gen)(F)`,
  `xv6SrvwmoSafe` and the Ev capstone: "the fetched bytes are not written below the hart's instruction
  view".  It is the i-cache form of "kernel text never written"; the lifting lemma
  `efetchItvOkRunOfUnwritten` (`:697`) already exists.  Q4's owner decision (leave as premise) is unchanged.
- `fetchSrcOk` (`WeakRobustSim.lean:530`) stays: it lives on the ROBUSTNESS line (promise machine over
  instance traces), which Stage C does not touch.
- The graph-side oracle "a fetch returns the image at timestamp 0" moves from the rows' rf-from-init
  (`gloadValue` at `t = 0`, `WeakRvwmoGraph.lean:238-244`) into ONE clause of `gdexecQconf` (B3).  It is a
  relocation, not a new assumption; the capstone clause "no write targets T" is no longer needed.
- Deletable on the robustness-line bridges: `pfFetchLoadOk` (`WeakPromiseBridge.lean:875`) and
  `pstepNoFetch` (`:1055`; `WeakErase`/`WeakRefuse`) — the pf↔axiomatic bridge now treats a fetch as a
  stutter (no axiomatic step), like `LSilent`.

## B. The simplest design: the fetch is an ADMINISTRATIVE label with an image pin

**Principle.** In the graph tier the fetch is not an event at all (riscv.cat).  `LIFetch` stays the
instance label (machine tier untouched) and becomes ADMIN for the graph tier: no row item, no projection,
no identity, no edges.  Its only graph-tier content — the bytes are the boot image at timestamp 0 — is
stated ONCE, on the emission (`gdexecQconf`), and carried into the realized run by instantiating the
(already parametric) `execProgOk'` at a pinned program LTS.  Nothing is added to `Lbl`, `Gexec`, `Mstate`,
`mstep`, `hlblRealizes` or `lblRealizes`.

Why not the design-§2 `Lbl.LFetch` row item: it preserves row positions but adds a constructor to an
alphabet matched exhaustively in ~38 merged files (`WeakAxiomatic/2/3`, `WeakRvwmoGraph/Norm/Lin/Hull/
Topo/Dec/Acyc/Floor/Xchg`, `AxGraphDec/Cat`, …), plus a new identity kind in `AidentT`/`AxPair.Ident`/
`AxGraphCat.IdentT`, an `MStepFetch`, a `candValues` clause and a graph clause `gfetchValue`, and a zero-tag
gate in `projLbl`.  All additions; the admin route is all deletions plus one clause.

### B1. Pivotal definitions and theorems (new statements)

```lean
-- WeakAxRealize (generic P D, pstep)
/-- The graph tier's fetch oracle: image bytes, timestamp 0.  `True` off the fetch. -/
def fetchPin (img : Image) : Wlabel → Prop
  | .LIFetch base tvs => (∀ t ∈ tvs.map Prod.fst, t = 0) ∧
                         ∀ j, j < tvs.length → img (base + j) = (tvs.map Prod.snd)[j]?
  | _ => True
/-- The program LTS with its fetches pinned (a sub-LTS of `pstep`). -/
def pstepPin (img : Image) (pstep : P → D → Wlabel → P → D → Prop) : P → D → Wlabel → P → D → Prop :=
  fun p d l p' d' => pstep p d l p' d' ∧ fetchPin img l
theorem pstepPinSub : pstepPin img pstep p d l p' d' → pstep p d l p' d'

def lbAdmin (instr : Bool) : Wlabel → Prop
  | .LSilent | .LDev | .LRegW .. | .LCtrl _ => True
  | .LInstr | .LIFetch .. => instr = true        -- a fetch sits where `LInstr` sits (never inside a fused pair)
  | _ => False
def lblRealizes (p : P) (σ : Mstate) (i : Nat) (lb : Lbl) (l : Wlabel) : Prop :=   -- Rocq's four conjuncts
  lbNobarex l ∧ latFree l ∧ lbRfoldfree l ∧ projLbl (pcls p l (σ.msWs i)) l = some lb
-- deleted: lbFetchInert, lbNoFetch, the `lbNoFetch` premise of lblRealizesUnproj, the LIFetch arm of mstepWpPfStepProg

-- WeakPromiseBridge
def projLbl … | .LIFetch .. => none          -- was `some (LLoad false …)`
-- deleted: pfFetchLoadOk, pfRunFetchOk's fetch content, pfFetchLoadOkInit; the bridge's PFIFetch arm is a stutter

-- WeakRvwmoConf
theorem hlblRealizesAx : lblRealizes pclsEv p σ i lb l ↔ hlblRealizes p (σ.msWs i) lb l := Iff.rfl
-- deleted: hlblRealizesAxNoFetch;  elbIsR (LIFetch ..) = false;  dstep's LIFetch arm = (s, []) (no dsLd push);
-- wlblRen π (LIFetch base tvs) = LIFetch base tvs   (fetch tags are not graph write indices; projLblWren/pstepEvWren trivial)

-- WeakRvwmoSupply
/-- Every admin fetch item of the emission reads the booted image at timestamp 0. -/
def emFetchImg (im : Image) (em : Hemission) : Prop := ∀ l ∈ emLabels em, fetchPin im l
def gdexecQconf (boot) (d0) (im) (nh) (GD) : Prop :=
  GD.gdG.gxImg = im ∧ GD.gdG.gxProg.length ≤ nh ∧
  (∀ i row, GD.gdG.gxProg[i]? = some row →
    ∃ em, hartConf i row (boot i) (fun _ => d0) em ∧ emDevfree em ∧ emFetchImg im em ∧
          (∀ jk, jk ∈ rowDeps em.emItems → ((i, jk.1), (i, jk.2)) ∈ GD.gdDeps))
theorem supplyOfQconf … :  -- THREE premises (candFetchInert gone); conclusion at the pinned LTS
    … → ∃ pst, pst 0 = … ∧ execProgOk' (pstepPin (c.cdImg) pstepEv) pclsEv pst (fun _ => d0) (candExec c)
-- deleted: emFetchInert, candFetchInert; hullSupply/topoSupply/t2linSupply unconditional

-- AxOpsem
def wlRd : Wlabel → Option (Bool × Int × Nat) | LIFetch .. => none | …     -- wlRvals/wlReval: wildcard arms
inductive AxOpsem.astepProg (row : List Lbl) : Athread → Wlabel → Athread → Prop
  | AStepAdmin … lbAdmin true l → pstepProg p d l p' d' → astepProg row ⟨p,k⟩ l ⟨p',k⟩   -- covers the fetch
  | AStepWrite … | AStepFence …                                                           -- AStepFetch DELETED
-- `T`/`fetchImg`/`fetchAnswers` deleted from astepProg/astep/astepAny/astepOwn/reducible/consumed/hemitAstep;
-- AxWp.AxirisG.axText (L0) deleted.  rdLabel keeps `fe`; pnodeStepReadAny/Inv now exclude the fetch node.

-- AxPair:  lblIdent (LIFetch ..) = none.      AxDeps: dstepT (LIFetch ..) = (s, [])  (no dtLd push, no edges)

-- WeakRvwmoCapstone (the Rvwmo capstone), premises after Stage C:
theorem xv6RvwmoSafeModulo … : freshEra gen σ0 → wpPackage … → (∀ a base, P a base → wpPackageProt …) →
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →          -- Q4, the ONLY fetch premise
    l2Claim … → walkSupply … → ∀ GD, rvwmoMinusDepsConsistent GD → gdexecQconf … GD →
    (∀ x, ¬ tc (racyD GD) x x) ∧ ∃ c pst P' σ', srvwmoConsistent c ∧ … ∧
       execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst (fun _ => efInit σ0.wgdev) (candExec c) ∧ …
-- deleted: WeakRvwmoCapstone.t2linFetchInert, fconfFetchInert, t2linSupplyRows (if only used for them)

-- WeakSrvwmoCapstone: hypothesis (c) `execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst dv (candExec cd)`;
-- deleted: execProgOkNf', execProgOkNf'Ok, xv6SrvwmoSafeNoFetch, lbFetchInertOfNoFetch, lblRealizesOfNoFetch (deviation 4)
```

### B2. How the lift works without the row item

`execWfPfRunProg` (WeakAxRealize) turns `execProgOk'` into a `wpPfRun`; admin steps go through
`admStarPf`/`admStarPfRun` (`WeakAxRealize.lean:414-440`).  Stated at `pstepPin img pstep`, the `LIFetch`
admin step yields `PFIFetch` with `ifetchOk img log 0 base tvs`: zero tags + image bytes give
`logByte img log 0 a = img a` (`WeakPromise.ifetchByteOk0`/`ifetchByteOkImg`, `:244,:264`) and the window
`¬ writesIn log a 0 0` is vacuous.  `wpPfRtcEpfRtc` (`WeakEvCapstone.lean:1008`) then lifts view 0 to
`σ.wgitv c` by `efetchItvOk`, exactly as today.  Where the pinned run comes from: `supplyOfQconf` has
`hartConf`'s `admRun` steps (`pstepEv`) plus `emFetchImg im em` on the same items, so each admin step is a
`pstepPin im pstepEv` step (`admRunPin`, a 10-line lemma).  `cfgMatchd`, `mstep`, `candExec`,
`srvwmoRealizable`, `promiseFreeCompleteClean` are untouched (no fetch in `Lbl`).

### B3. Why the pin sits in `gdexecQconf` and not in `lbAdmin`/`admRun`

`admRun`/`admStar`/`hemit`/`hartConf` have no image in scope; threading one changes 21 signatures.
`gdexecQconf` already carries `im` (`WeakRvwmoSupply.lean:271`) and is the "graph conformant to the booted
program" bundle, whose rows' fetch items under D1 were pinned to the image by rf-from-init; moving that
content next to `emDevfree em` keeps every other statement's shape.  Stability: `emFetchImg` is over
`emLabels em`, and with `wlblRen` fixing `LIFetch` it is invariant under `emRen` (`gdexecConfRen` unaffected).

### B4. Consequences for the spike and the witnesses

- `AxSpinSpike.doEv`: a class-1 read pushes NO row item and NO `aGmo` entry (one `if e.aeCls = 1` guard);
  `counts` keeps the fetch count as a trace statistic.  Recompute the 9 kernel-checked theorems (`:801-828`)
  and `AxScCat.g10Sc`/`tw2Sc`; expect `gsize` to drop by the fetch count and `ppo ≤ gmo` to stay true
  (fewer ppo edges).  `AxSpinSpikeRun` classifies the pc reads it already knows (`:35-39`) — no new input.
- Hand-built rows lose their fetch items and positions shift (`OpaxWit.wtFetch`/`wtPf0` in `AxOpsem`,
  `WeakRvwmoAdm` `laWl1`, `WeakRvwmoConfWit2.hemitOneFetch`, the 9 witness files of A3).  The fetch
  appears as an `(LIFetch pc tvs, none)` emission item preceding `LInstr`.

## C. Rework list (merged Lean files)

Legend: D = delete premise/definition, R = restate, K = recompute `decide +kernel`.  Sizes S < 1 h, M ≈ half a day, L ≈ a day.

**Lane 1 — the seam (sequential, first):**

| # | file | change | size |
|---|---|---|---|
| 1 | `WeakPromiseBridge` | R `projLbl` fetch arm → `none`; D `pfFetchLoadOk`, `pfFetchLoadOkInit`, fetch content of `pfRunFetchOk`; bridge `PFIFetch` = stutter; D `pstepNoFetch` (or keep, vacuous) | M |
| 2 | `WeakAxRealize` | D `lbFetchInert`/`lbNoFetch`; R `lblRealizes` (4 conj.), `lbAdmin` (fetch arm `instr = true`), `lblRealizesUnproj` (drop premise); D `mstepWpPfStepProg` fetch arm; ADD `fetchPin`, `pstepPin`, `pstepPinSub`, `admStarPf` at the pinned LTS | M |
| 3 | `WeakRvwmoConf` | R deviation 3: `elbIsR` false, `dstep` arm `(s, [])`, `wlblRen` fixes `LIFetch`, `hlblRealizesAx` = `Iff.rfl`; D `hlblRealizesAxNoFetch` | S/M |
| 4 | `AxPair` | R `lblIdent` fetch arm → `none` (`:161`) | S |
| 5 | `AxOpsem` | R `wlRd`/`wlRvals`/`wlReval` arms; D `AStepFetch`, `fetchAnswers`, `T`/`fetchImg` params; R `pnodeStepReadAny/Inv`, `hemitAstep(Aux)`, `OpaxWit.wtFetch`/`wtPf0` (fetch = admin item) | L |
| 6 | `AxWp` | D `axText` (L0), the `AStepFetch` case (`:207`), `T`/`img` params of `astepProgGraphData` etc. | S/M |
| 7 | `AxDeps` | R `dstepT` fetch arm `(s, [])` (`:471-474`); R `tw` witness rows (fetch literals out); K 10 checks | M |
| 8 | `AxGate`, `AxScCat` | header text; K `g10Sc`, `tw2Sc` (after 15) | S |

**Lane 2 — route B (after 1-3; sequential):**

| # | file | change | size |
|---|---|---|---|
| 9 | `WeakRvwmoSupply` | D `emFetchInert`, `candFetchInert`; ADD `emFetchImg` clause in `gdexecQconf`, `admRunPin`; R `supplyOfQconf` (3 premises, pinned LTS), `hullSupply`/`topoSupply` unconditional | M |
| 10 | `WeakRvwmoCert` | R the `hlblRealizesAx` use | S |
| 11 | `WeakRvwmoCert2` | R `hlblRealizesLoadShape` (drop 3rd case); D `certBlockSnoc`'s `lbFetchInert` premise, `Hpol` conjunct, `lbFetchInertOfStoreNe` | M |
| 12 | `WeakRvwmoCert3`, `Cert3b`, `Cert4` | D the `lbFetchInert` conjunct of their policies / `candFetchInert` conditionals | S each |
| 13 | `WeakRvwmoWalk`, `Walk2`, `Walk3` | D `wfetchSite` from `wsiteOk`/`wsiteOk'`/`wsiteSupply`, the `lbFetchInert` returns of `wpol`/`wblkPolAt`, Walk3's `t2linFetchInert` premise | M, S, S |
| 14 | `WeakRvwmoLinInd`, `Lin2`, `Fab`, `FabInd` | D `candFetchInert(F)` conditionals (`∃ pst` unconditional again); R at the pinned LTS | S/M each |
| 15 | `WeakRvwmoGlue`, `Glue2` | D `hullRunFetchInert` and its discharge (`hullRunZcut`, `cycleKillZ` simplify); `cycleKillOfL2'`/`''`, `t2linOfL2''` keep only `efetchItvOk` | M, S/M |
| 16 | `WeakRvwmoCapstone` | D `t2linFetchInert`, `fconfFetchInert` (+ `t2linSupplyRows` if orphaned); R the three capstones | M |
| 17 | `WeakRvwmoConfWit2`, `WeakRvwmoAdm` | R the hand-built programs (fetch = admin item before `LInstr`); D `mpCandFetchInert`, `hemitOneFetch` | M each |
| 18 | `WeakSrvwmoCapstone` | D deviation 4 (5 Lean-only decls); R hyp (c) at the pinned LTS; lift via the new `admStarPf` | M |

**Lane 3 — witnesses and the spike (after 5, 7; parallel with lane 2):**

| # | file | change | size |
|---|---|---|---|
| 19 | `AxGraphCat`, `AxLitmus`, `AxGraphWit`, `AxSfence`, `AxPtProt2`, `WeakRvwmoProbeSwap`, `WeakRvwmoLockWit`, `WeakRvwmoProbeRestr`, `WeakSrvwmoLitmus` | R fetch literals out of rows (positions shift); K their `decide` checks | S each (9) |
| 20 | `AxSpinSpike`, `AxSpinSpikeRun` | R `doEv` (class-1 reads not pushed); K 9 + 1 theorems (~4 min CPU) | M, S |
| 21 | `WeakErase`, `WeakRefuse` | optional: D `pstepNoFetch` premises (if 1 deletes it) | S |

**Unchanged** (they mention `LIFetch` but are machine- or robustness-tier): `WeakInterp`, `WeakEvLang`,
`WeakEvInst`, `WeakEvLift`, `WeakEvPf`, `WeakEvCapstone` (`efetchItvOk` stays), `WeakPromise`,
`WeakPromiseFact`, `WeakCertify`, `WeakRetag`, `WeakRobust*` (`fetchSrcOk`, `leIfetch` stay),
`WeakRvwmoGraph`, `WeakAxiomatic/2/3`, `WeakRvwmoNorm/Lin/Hull/Topo/Dec/Acyc/Floor/Xchg`, `WeakRacy`,
`WeakRvwmoConfWit`, `WeakRvwmoPinBridge` (no signature change under this design), and every `akIfetch`
leaf/certificate file.

Total: 39 files (lanes 1-3 incl. the 9 witnesses), of which ~24 are mostly deletions.

## D. Impact on the UNPORTED Rocq files

| class | files | one-line porting instruction |
|---|---|---|
| opax lifting | `AxLifting`, `AxAdequacy`, `AxAdequacyChk` | The header FINDING closes: there is no `AStepFetch`; drop `wlabel_is_fetch`/`astep_any_nf`'s exclusion — a fetch is an `AStepAdmin` step (`wp_skip_step`, `at_k` unchanged). |
| gate | `AxGateWp` | Port as is (the gate never involved the fetch; cites review Q2 for context only). |
| cycle witnesses / progress | `WeakRvwmoCycWit`, `CycWit2`, `WeakRvwmoProgress`, `PreNorm` | `wsiteOk`/`wsupply` have no `wfetchSite` conjunct; "a fetch before its next memory event" (`CycWit.v:38`) is literally an administrative node now. |
| track F | `AxFetch` (4,951 l.), `AxInstr`, `AxInstrFacts` | `af_astep_fetch_of_memread` → the fetch node is an admin step (`lbAdmin true (LIFetch ..)`); `awp_fetch` → the admin skip; §7 rows lose their two fetch items (positions 0..3 → 0..1).  Split `AxFetch` as the map says; its §2 shrinks. |
| row/certificate files | `AxRowConf`, `AxRegOnly`, `AxEpiChain*`, `AxSpinRow*`, `AxSpinGate`, `AxLedgerG*`, `AxDefer*`, `AxEpi*` (11 with literal fetch rows) | Rocq `LLoad false pc [0;…] vs` row items are DROPPED (re-index later positions); the emission item is `(LIFetch pc tvs, none)`; `wak_plain` at the fetch ↦ `wakIfetch` (as the O2 map). |
| AxSym engine / ledgers | `AxSymMem`, `AxSymLd`, `AxSymEngine*`, `AxSymCtl*`, `AxSmodeProbe` | As the O2 design §2: the coherent-read arm becomes the i-cache arm; ledgers/probes recomputed (`decide +kernel`); no row item for the fetch. |
| FirstRd family | `AxSpinE3.FirstRd` and its 18 users | No change (`ak_latest = false` only). |
| robustness line | `WeakRobust*` remaining, `WeakErase`/`WeakRefuse` consumers | Unchanged by Stage C (`fetchSrcOk` carried as today). |

## E. Cost, risks, owner questions

**Cost.** 39 merged files; ≈ 700-900 lines deleted (the fetch-inert family and its discharges, `AStepFetch`
and the oracle parameters, deviation-4 corollaries), ≈ 200-300 added (`fetchPin`/`pstepPin`/`emFetchImg`/
`admRunPin`, the admin-fetch lift arm, witness re-indexing), ≈ 25 `decide +kernel` recomputations (~6 min
CPU, dominated by the spike).  Effort ≈ 3 agent-days: lane 1 (1 day) then lanes 2 and 3 in parallel
(1-1.5 days), one squash on the pin.  Held files (`AxLifting`, `AxGateWp`, `AxInstr`, `WeakRvwmoCycWit`,
`WeakRvwmoProgress`) can start after lane 1 + file 13.

**Risks.**
- R1 `pstepPin` ripples into every `execProgOk' pstepEv …` statement (≈ 10, lanes 2 and 18) — a token
  change each, proofs project with `pstepPinSub`.  Mitigation: do 2 → 9 first, then the rest mechanically.
- R2 Fewer required `DTtrans` edges (no fetch in `dtLd`) weaken `gdexecQconf`; a proof that used a
  fetch-sourced edge would break.  Grep says none (`dtLd` consumers: AxDeps/AxGate/AxScCat/Conf only);
  the spike's `ppo ≤ gmo` only gets easier.
- R3 Hand-built programs (`OpaxWit`, `Adm`, `ConfWit2`) need a fresh witness shape (fetch admin item
  then `LInstr`); each is M, none is load-bearing for a capstone.
- R4 Row re-indexing in the 9 witness files and the 11 unported literal-row files is mechanical but
  error-prone; `decide` catches value drift, not mis-numbered positions in hand proofs.
- R5 `lbAdmin` is widened; `hlblRealizesNotadm` and `lbAdminMono` still hold (`projLbl` is `none` on the
  fetch), but every `cases l` over admin labels gains a trivial goal.

**Owner questions (crisp, with the recommended option).**
- **Q-C1** Fetch representation: (Rec) ADMIN label — no row item, pin via `emFetchImg` in `gdexecQconf` +
  `pstepPin` (this note); or (alt) design-§2 `Lbl.LFetch` row item preserving row positions (≈ 38 more
  files touched, five additions instead of deletions).  Recommend (Rec).
- **Q-C2** Delete the opax oracle parameters `T`/`fetchImg`/`fetchAnswers` and `AxWp.axText` now (Rec), or
  keep them as dead parameters until `AxLifting` ports?  Recommend delete now — `AxLifting`'s header FINDING
  is about exactly this arm.
- **Q-C3** Robustness-line bridges: delete `pstepNoFetch`/`pfFetchLoadOk` (the fetch is a bridge stutter)
  in the same lane (Rec, S), or leave them vacuous?  Recommend delete.
- **Q-C4** `wlblRen` fixes `LIFetch` (fetch tags are not graph indices) — Rec yes; the alternative keeps
  renaming them and needs `π 0 = 0` where `emFetchImg` is transported.
