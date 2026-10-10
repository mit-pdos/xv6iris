VERDICT: NOT SATISFIED

# Review R10 of `notes/weak-allocproc-plan.md` rev 13 (adversarial, evidence-based; 2026-10-09)

Scope (per the R10 brief): the rev-13 Layer-2 redesign after the W2 spike's D7 STOP — `tsoShadow` + `R-view`
equality, G1 (e) `candScaT` and its Stage-2 derivation, the G2 options, G3 (a″) `candDiskLat` + (R2′), the G-question
Spec lines, the re-sizings and the launchable/blocked split; the [OWN.16] and W3-DONE records.  `file:line` cites
`../xv6iris-weak` unless prefixed; Sail cites `model/Lean_RV64D/LeanRV64D/`.  Advisory only; no proofs or builds; no
git/jj; no subagents.

**Sign-off.**  NOT as written.  Four REQUIRED changes: one semantic (G2-Q option (a) is mis-specified and, as
specified, breaks the very derivation G1 (e) rests on), one derivation gap (W11 (iv) under G2-Q (b) is not
graph-derivable — the plan's own `g2Run` is the counterexample), one statement-shape error in the item marked
"launchable now" (W5b′'s `pfStepFacts` cannot carry `candScaT` as described), and one missing artefact (the W5d-G
spike's Lean file is in NO working copy).  All four are text/spec fixes of size S in the plan; none changes the
published statement.  W1b and W2's store/exstore/fence/fetch-M1/silent/regw/ctrl/dev rows may launch regardless;
W5b′ must wait for [R10.1]+[R10.3] (one rev), and G2-Q must not go to the owner until [R10.1] lands, or the owner rules
on a wrong option.

## What was verified (holds as cited; not to re-litigate)

**W2 spike / `Weak/TsoOfPf.lean`**: 239 lines, imported at `Weak.lean:624`; `histOf`, `tsoAqPairTv` (floor `top+1`
after the pair's write), `tsoExclRv` (`rv := top` at any exclusive read), `g1St/g1Shape/g1Run/g1Tso`,
`tsoAfterLoadCoh`, `g2St/g2Shape/g2Run/g2Tso`, `fenceRow` (the one positive row) all present.  **TsoMem**:
`MState.afterExcl` `tv := if acq then top` (`Lang.lean:134-138`), `MState.store` `tv := top+1` iff `excl && acq`
(`:147-153`), `MState.fence` = `fencePost (fenceDrains b) (fenceAcq b) tv rv pub`, `fence.i` → `itv := max itv
(fencePost true false …)` (`:155-163`), `dmaView` (`:185`, used `:535`), plain-load arm `tv ≤ tvn ≤ top ∧ cohOk ∧
readBytes` + `afterLoad` (`:363-367`), i-fetch arm `itv ≤ tvn ≤ top` (`:360-362`), `blockedStep :395-403`;
`HRead.afterLoad` stamps the whole footprint with `tvn` (`TsoMem.lean:268`), `cohOk :263`, `fencePost :345`,
`fenceDrains/fenceAcq :356-364`, store forwarding by author (`:16-18`).  **WeakMem/WeakPromise**: `readable
:400-402`, `fwdView :585-591` (`aq → t`), `loadPostAt :608-626` (aq arm `wVrNew := max wVrNew vpost`, `wCoh := max
coh (max vpost t)`), `storePost :648` (`wCoh := max coh t`), `fencePost :674-688` (`wRes := none` at any non-trivial
fence), `exloadPostRunD :834`; `readOkD :183-188` with the `lat = true → ¬ writesIn log a t |log|` clause;
`ifetchByteOk :222-224` — the window `(t, max t itv]` IS empty for `t > itv`, so the plan's cut-form correction (i)
(`t ≤ q` per byte) is right; `itvPostMachCSL WeakInterp.lean:378-384`.  **W5b**: `scaVis/scaByte/scaOk
PfRunShape.lean:61-72` (`tvn ≤ |log|`, visible = `≤ tvn ∨ own`), `candSca :85`, `pairAdjacent :95`, `execProgOk'S
:242`, `pfStepFacts :265-269`, `pfRunS :273-277`, 625 lines.  **Disk row**: `pdiskProg` DRead = `LLoad aq false`
(`WeakEvInst.lean:489`), START/COMMIT = `LDev` (`:484,502`); `dreadAvailIdx` aq (`VirtioProg.lean:375-376`), ring/
desc reads plain (`:378-386`), `virtioProg :606-619`; `latFree WeakPromiseFact.lean:61` in exactly 16 files, 26
sites in `WeakPromiseFact`; `pstepEvLatFreeProg WeakEvCapstone.lean:1052`; `lblRealizes` requires `latFree`
(`WeakAxRealize.lean:240-243`).  **Graph side**: `ptraceRel = po ∪ rf ∪ gmo|W` (`Lin2.lean:124`), `glinPtraceExt`
needs `grule14` (`:742`), the candidate's log is `gwrites` in gwix order (`:740-741`); `gnxw Lin.lean:440`, `grank` =
gwix of the next own write, `rblocks :316` keeps po within a block; `gacqPo Graph.lean:214-215` (`lbIsR ∧ lbAq`,
`LRmw` is R and W, `WeakAxiomatic.lean:164-175`), `gloadValue :238-243` (`gvisible = gmoLt ∨ gpo`), `grule14
:257-258`; `gppo1/gppo2 AxGraphCat.lean:146-156` (rule 2 exempts SAME-source reads; no W→R po-loc ppo);
`rvwmoCatConsistentT AxDeps.lean:208-211`; `srvwmoConsistent WeakAxiomatic3.lean:2073`.  **Image**: `acquire`'s
`amoswap.w.aq … sd a0,16(s1); ld …` (`KernelImage.lean:2265-2290`), `release`'s `fence rw,w; sw zero,0(s1)`
(`:2361-2364`), retry self-loop `WeakEvInst.lean:360-364`.  **Sail (G1-Q Spec)**: `execute_AMO InstsEnd.lean:18663`,
`AS_rel_or_acq PhysMemInterface.lean:315,364`.  **G1-Q (b) cost**: `viewLbAt`/`acq_view` in exactly 13 files,
`Ctx.lean` 20 sites, `WpAtomic.lean:166-167,225-226`, `WpLock.lean:63`.  **G2-Q (a) cost**: `cohOk`/`afterLoad` in
exactly 7 MachCSL files (Lang, TsoMem, Resources :788-800, Wp :1257-1282,1729-1745, WpAtomic, WpSmodeFenceFloor
:92-119,239-260, UIcache :233-249); NO Iris resource exposes `coh` (`Resources.lean`/`Ctx.lean`/`Wp.lean` mention it
only through `cohOk`/`afterLoad`), so the change is mechanical as claimed.  **W3 DONE**: `TextPristine.lean` `textWin
:34`, `textPristine :38`, `_read :60`, `_readBytes :72`, `textRo :88`, `powerInterp_textPristine :123`; twins
`PowerText` 734 + `BootSharedText` 250 + `SystemBootEraText` 196 + `SystemAdequacyText` 580 = 1,760 lines (≈ 1.76k
✓); root `xv6TextAdequacy_closed LinkTextAdequacy.lean:26`, `roots.txt:19`, `baseline.json:63`,
`tcb/expected.json:2194`; PROGRESS-W3's unsoundness argument for rev 11's slot-stash is as recorded.  **W1 interim**:
`AllocprocTrace.lean` 274 lines, `pidPick_range :111`, `_of_wf :120`, `pidPick_badHist :141`, `badWord :146`,
`allocprocTraceAns :254` with exactly the plan's conclusion; PROGRESS-W1's (a)/(b)/(c) match W1-Q.  **[OWN.16]**
records (W1-Q (c), Q-W3a (A), D41 (a), D45 (a)) match `allocproc_revise3_extra.txt:18`.  **W5c** 730 lines; spikes
399/145 ✓.  **The `R-view` equality + minimal view is SOUND for hart loads, exclusive pairs, fences and the M2 cut**
(derivation below); **G3 (a″) + (R2′) + disk-read anchors is sound and realization-necessary** (the anchor trace
exists: disk-row po is gmo-ordered by (R1)/(R3)/(R2′)/rule 14, reads vs reads need no order; `candDiskLat` then
follows from `gloadValue` because every write in the log at the anchor is gmo-before it).  **(R2′) also couples
UART/PLIC `dev` moves to later DMA reads** — named (D51 extension, plan:940) ✓.

**Why the shadow works (recorded so W2/W4 workers do not re-derive it).**  Hart load `r` of agent `i` at the
shadow's minimal view `tvn := max(F, max_{foreign j} t_j)`, `F := max(tv_S, coh_S over the footprint)`: `tv_S ≤ tvn`,
`cohOk` and `tvn ≤ top` hold by construction (`t_j ≤ |log|`); `Hist.read` at `tvn` returns `t_j` per byte iff no
visible later write to byte `j` — own later writes are excluded by `scaByte` (visible = own), foreign ones in
`(t_j, tvn] ⊆ (t_j, tvn_sca]` by `scaByte` at `tvn_sca` once `candScaT`'s `F ≤ tvn_sca` holds (foreign `t_j ≤
tvn_sca` by `scaVis`).  So (★) is discharged by `candScaT` ALONE (plan:498-500 says "+ G2 (a)" — G2 (a) matters for
whether `candScaT` is TRUE/derivable, not for (★)).  Stage 2, `tv` part: the SCA witness `tvn_sca := #writes
gmo-before r` is a legal `scaOk` witness — `tvn_sca ≤ |log|` at `r`'s trace position because every write `w <gmo r`
has `w <gmo nxw(r)` (rule 14 on `GD'`), hence `gwix w < gwix (nxw r)` and `w` sits in an earlier `rblocks` block; its
bytes are co-maximal by `gloadValue`.  `tv_S` after an aq pair `= gwix(LRmw)` and `LRmw <gmo r` by rule 5 (`gacqPo`,
`LRmw` is `lbIsR ∧ lbAq`); `tv_S` raised by `fence r,*`/`rw,*` to `rv`/`pub`: every contributor (earlier load's
minimal view ≤ its own `tvn_sca`; `top` at an exclusive read `= gwix(LRmw) − 1`; `ownPub = gwix` of the last own
store) is a gmo position of an event rule 4 puts gmo-before `r`.  **The `coh` part is where [R10.1]/[R10.2] bite.**

## REQUIRED changes

**[R10.1] G2-Q option (a) is mis-specified: "stamps each byte with ITS source timestamp" is NOT faithful for
own-forwarded bytes, introduces a NEW cross-byte strengthening through `cohOk`, and FALSIFIES `linCandScaT` on a
cat-consistent candidate.**  Evidence: TsoMem reads a hart's own latest store at ANY view (`TsoMem.lean:16-18`;
`HEnt.visible`), so a forwarded byte's source timestamp `t_a` may EXCEED the load's `tvn`; `cohOk` (`Lang.lean:365`,
`TsoMem.lean:263`) is footprint-WIDE (every byte's floor ≤ the ONE view); riscv.cat has no `W;po-loc;R` ppo (`gppo1
AxGraphCat.lean:146-147` is `M;po-loc;W`; the manual's rule 1 "b is a store"), rule 2 exempts same-source reads
(`gppo2 :151-156`), `gloadValue` makes a po-before own write visible (`Graph.lean:236,238-243`).  WeakMem's own
stamp is PER BYTE (`loadPostAt WeakMem.lean:609` `wCoh a := max coh (max vpost t)`) and has no cross-byte effect.
**Counterexample** (RVWMO-consistent, TsoMem-under-(a)-as-written cannot realize it, `candScaT` fails): hart A:
`sb j` = `w1`; `lh (j,m)` = `r1` reading `j` from `w1` (forwarded) and `m` from foreign `w5` (gwix 10); `lh (j,k)` =
`r` reading `j` from `w1`, `k` from the image, while foreign `w3` writes `k` at gwix 5.  gmo `r <gmo w3 <gmo w5 <gmo
r1 <gmo w1` is cat-consistent (`r`/`r1` share byte `j` with the SAME source → no rule 2; `w1` po-before both but
`W;po;R` is not ppo; `gloadValue` ✓ for all).  Shadow under (a)-as-written: `r1` at `tvn ≥ 10` stamps `coh j := gwix
w1 (> 10)` (or `10` under a `min` variant); `cohOk` forces `r`'s view `≥ 10`, so `r` reads `w3` for `k`.
`candScaT` at `r`: `F ≥ 10 > tvn_sca(r) = 0`, and no larger `scaOk` witness exists (`w3 ∈ (0, 10]`).  So G2-Q (a)
as written is STRONGER than riscv.cat (not "FAITHFUL (= rule 2)", plan:913-914) and the §B(10) sentence "the `coh`
part by rule 2 (`gppo2`) once G2 (a) stamps per byte" (plan:486) is false in the forwarding case.  **Change** (G2-Q
and §B(10)): (a′) `afterLoad` stamps `coh a := max (coh a) t_a` ONLY when `t_a ≤ tvn` (the source is a global
entry) and leaves own-forwarded bytes (`t_a > tvn`) UNSTAMPED — FAITHFUL (= rule 2 + load-value, same-source
exempt); derivation case split for W11 (iv): same foreign source → `t_a ≤ tvn_sca(r)` by `gloadValue`; different
source → rule 2 gives `r_prev <gmo r` and `gloadValue` gives `gwix w' > t_a`; own-forwarded → no stamp.  (a‴) DROP the
coherence floor altogether (`afterLoad` = `rv := max rv tvn` only) — WEAKER than rule 2 on TsoMem, SOUND (the
composition needs only TsoMem ⊇ realized runs; no Iris resource exposes `coh`, `Resources.lean`/`Ctx.lean`/`Wp.lean`
grep), S, the same 7 files, deletions; then `F = tv_S` and (★)'s `coh` part vanishes outright.  Mark the
unconditional source stamp STRONGER (a NEW cross-byte strengthening via `cohOk`) and keep the current footprint
stamp as (iii) of §0 F1.  Fix the cite `WpAtomic.lean:516-520` → `:509-530`.

**[R10.2] W11 (iv) `linCandScaT` is NOT graph-derivable under G2-Q (b); the plan presents it as graph-only.**
Evidence: plan:860 "≥ per-byte `coh` by rule 2", plan:898-899 "(e) FAITHFUL at Stage 2 (derived: `linCandScaT`,
rule 5/4 + `ptraceRel ⊇ gmo|W`)", plan:482-486.  Under (b) TsoMem keeps the footprint stamp (`TsoMem.lean:268`) and
the plan's OWN witness refutes derivability: `TsoOfPf.g2Run`/`g2Tso` (`Weak/TsoOfPf.lean:160-199`) is cat-consistent
(plan:78) and its second load has `F = coh b = 2 > tvn_sca = 0` (`g2Tso`'s first conjunct), so `candScaT` is FALSE on
a `rvwmoCatConsistentT`-consistent candidate.  Under (b) the `coh` part can only come from W8's census (vi)
TRANSPORTED to the candidate through `R`'s log identification (as `protReg`/`badSeg` are), with a po-induction
("every load's `F` ≤ the gmo position of every later load sharing a footprint byte": `tv` part by rules 4/5 as above;
`coh` part by the census — same footprint ⇒ same or rule-2-ordered sources).  **Change**: §C W11 (iv) — "graph-only
under G2-Q (a′)/(a‴); under (b) takes W8 (vi) as a transported hypothesis (+S–M)"; W11 Deps gain "G2-Q; W8 (vi)
under (b)"; §D G1-Q (e)'s FAITHFUL mark reads "derived at Stage 2 given G2-Q (a′)/(a‴), or (b) + W8 (vi)"; §B(10)
plan:486 per [R10.1]'s case split; §C W8 "Design gate" (plan:839-843): under (b) W8 exports (vi) AND it feeds W11
(iv), not only (★).

**[R10.3] W5b′ as specified cannot carry `candScaT`: `pfStepFacts` reads the pre-CONFIGURATION, the shadow is a
function of the step-list PREFIX.**  Evidence: `pfStepFacts (c : Wpcfg P D) (i : Nat) (l : Wlabel)`
(`PfRunShape.lean:265-269`) and `pfRunS.snoc … → pfStepFacts fok c1 i l → …` (`:273-277`) see `c1` only; a `Wpcfg`
holds the log (writes only), the WeakMem `Wstate`s and program states — TsoMem's `tv/rv/coh/acq/itv` are NOT a
function of it (fences, plain loads and the aq pairs that move them leave no trace in `pcLog`; `MState.fence
Lang.lean:155-163`, `afterLoad :127-129`, `afterExcl :134-138`).  Plan:680-681 "`pfStepFacts` carries both — the
replay `execPrefixPfRunProgShaped` threads them unchanged (facts are read at the pre-configuration)" is therefore
false for `scaOkT`/`candScaT` (true for `diskLatOk`, which is log-only).  **Change**: W5b′ defines `tsoShadow` over
`List (Nat × Wlabel)` (parametric in the `coh` stamp per [R10.1]), changes `pfStepFacts` to `pfStepFacts fok st c i l`
(or indexes `pfRunS` by the shadow), states `execProgOk'S`'s clause (iii)′ over `shadowOf (E.exTr.take k)`, and
re-proves the snoc of `execPrefixPfRunProgShaped :512` (the replay already produces `st`) — S, inside W5b′'s S–M;
say so in §C W2/W5b′ and in the "Deviations" record of W5b.

**[R10.4] The W5d-G spike's Lean file does not exist in ANY working copy; the plan cites it as existing.**
Evidence: `ls ../xv6iris-weak-w3/Weak/` has no `GraphFetch*` (the `-w3` workspace was re-used by W3: it holds
`TextPristine`'s tree); a search of the main tree and all 27 `../xv6iris-weak-*` workspaces finds no
`GraphFetchSpike.lean` and no `fetchCutOk`/`gzFetch`/`emZifencei` under any name.  Plan:44-46 ("ONLY in the `-w3`
workspace", "W5d-G's day-one merge … is RELEASED"), plan:276 (`GraphFetchSpike.lean:36`), plan:291 (`:189`),
plan:303-305 (`:63,83,140,213`, `:206`), plan:749 (day one: merge it).  **Change**: record the file as NOT IN ANY
WORKING COPY (2026-10-09); owner action: recover it from jj (the W5d-G spike worker's change / `jj op log` of the
`-w3` workspace) or accept re-creation from `notes/W5dG-spike.md`'s recorded statements (S–M, before W5d-G's G1);
W5d-G's "Day one" becomes "recover or re-create, then merge"; §B(4)(iii)'s `:N` cites point at the report until then;
[OWN.10]'s record: nothing left to merge.

## SUGGESTIONS

- **[R10.s1]** plan:479-480 gives the wrong reason for the minimal view ("`rv_T := max rv tvn` would outrun `wVrOld`
  and break `R` at the next `fence r,*`") — moot under `R-view` EQUALITY.  The real reason: `rv` feeds `tv` at
  `fence r,*` (`Lang.lean:155-160`, `fencePost TsoMem.lean:345`), and Stage-2 derivability needs every contributor to
  `F` to be ≤ the gmo position of a later load, which rule 4 gives for the EARLIER LOAD's gmo position, i.e. for its
  `tvn_sca`, not for an arbitrary larger view.
- **[R10.s2]** Under equality-`R`, `fenceRow` (TsoMem's post-fence floor ≤ WeakMem's `wVrNew`) is no longer the
  fence row's content — TsoMem's fence step always exists and the shadow IS its view.  Say the positive rows reduce to
  "a TsoMem step exists at the shadow's view with the pf bytes"; keep `fenceRow` as the spike's record.
- **[R10.s3]** plan:78 "witness `TsoOfPf.g2Run`/`g2Tso` (cat-consistent, no TsoMem schedule)": cat-consistency is BY
  INSPECTION (`W2-spike.md:36-38`), not in Lean; mark it, as §A(3) marks fidelity "by litmus".
- **[R10.s4]** If G2-Q = (a‴), `candScaT` is `scaOk ∧ tv_S ≤ tvn` and the `coh` field of `tsoShadow` disappears;
  size W5b′ at S and W11 (iv) at S–M in that branch.
- **[R10.s5]** The W2 report's faithful/stronger/weaker column [R9.s4] is still owed (plan:450); add it to W2's
  acceptance so it is not forgotten a third time.

## Owner questions the plan is missing

- **G2-Q sub-choice (a′) vs (a‴)** (needed before the G2-Q ruling; OWNER RULE form).  Spec: RVWMO rule 2 / riscv.cat
  rule 2 orders two same-hart reads of a common BYTE only when they return DIFFERENT writes and no same-hart write
  to that byte lies po-between (`gppo2 AxGraphCat.lean:151-156`); load-value makes a hart's own po-earlier store
  visible at any gmo position (`gvisible Graph.lean:236`); there is NO `W;po-loc;R` ppo (store-buffer forwarding is
  legal); Sail: `mem_read` per access, no coherence state (external model); Zifencei/PMAs: silent.  Options: (a′)
  per-byte stamp `coh a := max (coh a) t_a` for global sources only, own-forwarded bytes unstamped — FAITHFUL (the
  spec's executions on same-hart byte reads), cost S–M (7 files), keeps TsoMem's documented CoRR (`relaxed-rr.md`);
  (a‴) no coherence floor — WEAKER than rule 2 on the strong model, SOUND for the composition, S, changes TsoMem's
  documented semantics (no proof consumes `coh`); (a) as currently written — STRONGER (cross-byte via `cohOk`),
  rejected by [R10.1]; (b)/(c)/(d) as in the plan.  Recommendation: (a′), unless the owner prefers the smaller
  trusted surface of (a‴).
- **W5d-G spike recovery** (not a semantics question): recover `GraphFetchSpike.lean` from jj, or re-create (S–M)?
