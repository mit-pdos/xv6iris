VERDICT: NOT SATISFIED

# Review R12 of `notes/weak-allocproc-plan.md` rev 15 (adversarial, evidence-based; 2026-10-10)

Scope (per the R12 brief): rev 15 = R11's four required changes (+ [R11.1-alt]) + [OWN.20]/[OWN.21]; audited hardest:
(1) G2-Q's corrected (a′) against riscv.cat rule 2 + load-value and against TsoMem's existing proofs; (2) W-RSV form
(i) against in-flight AMO atomicity, `Reducible`, the acquire proof, the census and the `wpLoop_restart`/`ctxTok`
cost; (3) `itvOf` for W5d's M2 cut; (4) W13 (F-dep) `asrc`; plus every RULED mark against
`~/dev/weak-orch/allocproc_revise3_extra.txt`.  `file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or
builds; no git/jj; no subagents.

**Sign-off.**  NOT as written.  Two REQUIRED changes, both text/size fixes of size S in the plan, neither changing the
published statement: (1) W-RSV form (i)'s ghost cost is mis-described — `wpLoop_restart` cannot be "re-stated over
`ctxTok`", because the seven cycle rules it lives in do not hold `ctxTok` (that token rides inside `kctx` and the user
walker's `uResvTok`, two layers up), so the fragment must be threaded through the cycle rules' STATEMENTS and their
callers (≈ 27 MachCSL files + 8 `Xv6/` files) or moved into an invariant — the item the plan sells to the owner as "L,
`Xv6/` untouched" is not; (2) the plan predates [OWN.21] and still says "coordinator to confirm" at every W-COH gate,
and it never states that the foreign-only restriction [R11.1-alt] is LOAD-BEARING for route (9d) (without it a
cat-consistent candidate has no TsoMem realization), nor that [OWN.21] confirmed only the reset.  Everything else
audited holds: the corrected (a′) IS exactly rule 2 (both exemptions) + load-value, sound for every existing TsoMem
proof; form (i) IS consistent with in-flight AMO atomicity and `Reducible`; `itvOf` has a carrier; (F-dep) is right.
W5b′, W13 (E)/(T), W5d-G G0, W1b and W-COH (with [R12.2]'s status fix) may launch; W-RSV must wait for [R12.1].

## What was verified (holds as cited; not to re-litigate)

**RULED marks**: every RULED tag matches the extra file through [OWN.20] (G2-Q (a′) in the corrected form; W-RSV-Q
NEW; D19 (b), D20 (a), D9 (a), D8 (a) [OWN.19]; D42–D43, D51–D52 [OWN.18]; G1-Q (e), G3-Q (a″), D46–D50 [OWN.17];
W1-Q (c), Q-W3a (A), D41, D45 [OWN.16]).  [OWN.21] (08:11, after the plan's last write) is NOT in the plan — [R12.2].
**(a)** `Xv6.Allocproc : ALLOCPROC` (`LinkAllocproc.lean:14-16` → `allocproc_proof`), `allocprocPost`
(`SpecAllocproc.lean:118-132`: slot `j < NPROC`, `1 ≤ pid ≤ PIDMAX`, `procHeld … USED`, trapframe/pagetable/context
cells, or the `0` arm with `kallocAvail` returned), `wp_allocproc_body :204-224` with the premises as listed (`k.tier =
kpt`, `allocprocSlots ≤ k.avail`, `k.noff + 2 < 2^31`, the three `∉ k.locks`, `procsInv`, two `isLock`s,
`kallocAvail`, `procsAvailAt`, `□ (killCred -∗ Q (-1))`, `actLend`, `wpNext` with `sieArm`); roots `roots.txt:6,19`;
baseline `baseline.json:11-14` (3 axioms + the 3 opaques); `tools/ci/roots-weak.txt`/`tools/audit/baseline-weak.json`
exist ✓.  **(b)** TsoMem: `HEnt.visible` `t ≤ tv ∨ tid = h` (`TsoMem.lean:115-116`), `Hist.read` = latest visible
(`:119-120`), `HRead.cohOk` footprint-wide (`:263-264`), `afterLoad` stamps every footprint byte with `tvn` (`:266-270`),
`afterExcl` keeps `coh` (`:273`), `clearAcq` (`:276`), `bound` (`:279`); `MState.afterExcl` `tv := top iff acq` + resv
(`Lang.lean:134-138`), `MState.store` `tv := top+1 iff excl && acq`, `clearAcq`, `resv := none` (`:147-153`), `fence`
with `itv := max itv (fencePost true false tv rv pub)` iff `fenceIfetch` (`:155-163`), `dmaView` top (`:185`);
`evStep` i-fetch arm `itv ≤ tvn ≤ top` as `ifetchAgent` (`:360-362`), plain-load arm `tv ≤ tvn ≤ top ∧ cohOk ∧
readBytes ∧ afterLoad` (`:363-367`), exclusive-read arm `¬ othersReserve` + `topBytes` (`:368-371`), store arm `¬
othersReserve` ONLY — never `σ.resv cpu` (`:372-375`); `blockedStep :395-403`; `hartStep`'s `.pure` arm `∃ tick, m' =
riscvStep tick ∧ σ' = σ` (`:497-502`) — `.pure` IS the instruction boundary (the whole cycle is one `SailM Unit`, the
Sail events are its `.impure` nodes; `riscvStep = try_step 0 false; tick` `:208-210`), the exact twin of `pnodeStep`'s
`.pure → LInstr` (`WeakEvInst.lean:284-288`) and `instrPost … wRes := none` (`WeakMem.lean:719-721`).  `srvwmoConsistent`
and its residue table (`WeakAxiomatic3.lean:2050-2073`), the litmus divergences LB and reader-fence-only MP
(`WeakSrvwmoLitmus.lean:1663-1695`) ✓.  `cohOk` has ONE use (`Lang.lean:365`) ✓; `coh` is named in exactly 7 MachCSL
files (Lang, TsoMem, Resources, UIcache, WpAtomic, Wp, WpSmodeFenceFloor — the last four only through
`afterLoad`), in NO `Xv6/*.lean`, and in `Weak/` only in `TsoOfPf.lean` ✓; no Iris resource exposes it (`hartViewsAt`
carries `itv`/`rv` only, `Resources.lean:940-941`; `memModelAt :946-951` = top, authors, views, `resvMap`, `mmOk`) ✓.
**(1) G2-Q corrected (a′) = rule 2 + load-value, exactly.**  `gppo2` (`AxGraphCat.lean:151-156`) orders `e1 <gmo e2`
iff a common byte `a` is read from DIFFERENT sources (`t1 ≠ t2`) AND no same-hart write to `a` lies po-between
(`gwritesByte G w a v → gpo e1 w → gpo w e2 → False`; `LRmw`s are writers).  Under (a′) `coh a` at `r` = max of the
FOREIGN-source stamps `t_{w'}` of the hart's loads `r_prev` of `a` po-after its last own store to `a` (the reset).  For
each: same source → `w' <gmo r` by load-value (foreign, so `gvisible` is `gmoLt`); different source → no own write to `a`
po-between (by the reset's bookkeeping), so `gppo2` gives `r_prev <gmo r` and `w' <gmo r_prev` — hence `gwix w' ≤
tvn_sca(r)` in both cases, and the footprint-wide `cohOk` constraint on r's OTHER bytes is harmless because a load has
ONE gmo position.  Conversely nothing cat allows is excluded: a stamp is placed only where rule 2 or load-value already
forces `w' <gmo r`; own-sourced bytes (forwarded or below the view) carry no gmo constraint in cat (`gvisible`'s `gpo`
disjunct) and are unstamped; an own store to PART of a footprint resets exactly its bytes, as `gppo2` exempts exactly
those; DMA sources (`diskAgent`) are foreign and stamped — the disk row's `LStore`s have gmo positions, load-value
applies ✓; image entries stamp `0`, a no-op.  The §B(10) three-case derivation (plan:555-562), the `m0`/`w_c'`
candidate for [R11.1-alt] (plan:562-568; re-checked: ppo on A empty — same source `m0` for byte `a`, no `W;po;R` — and
load-value holds with `w_c' >gmo r`) and rev 14's `r_prev`/`m`/`w_b'` counterexample (plan:1131-1136) are all correct.
**Soundness for the existing proofs**: the new per-byte stamp is pointwise ≤ the old footprint stamp (`t_a ≤ tvn`), and
the reset lowers further, so `cohOk` only WEAKENS — every `tvn` the load rules (`Wp.lean`, `WpAtomic.lean:509-530`,
`WpSmodeFenceFloor`, `UIcache`) choose today stays legal; `mmOk_afterLoad` (`Resources.lean:788-803`) needs `coh a ≤ top`
— `t_a ≤ tvn ≤ top` ✓ and `0 ≤ top` ✓; `mmOk_store :826-850` touches `hr` only through `clearAcq` — the reset adds a
trivial `0 ≤ L` case; TsoMem's CoRR (`relaxed-rr.md`, header `TsoMem.lean:20-24`) survives for foreign-written bytes
(r1 from foreign `w_new` stamps `t_new`; r2's view ≥ `t_new`) and trivially for own-written ones (the own store is the
latest visible entry until a NEWER foreign write becomes visible).  (★) is still discharged by `candScaT` alone
(plan:542-547 ✓).  **(2) W-RSV form (i)**: consistent with AMO atomicity (no `.pure` between the AMO's exclusive read and
its write; the Svadu A/D pair sits inside one translation) and with `Reducible` (`σ.dropResv cpu` is total; both
`blockedStep` arms stay); `TsoMem never reads σ.resv cpu` ✓; the `wpLoop_restart` consumers are exactly the 7 cycle
files (`WpCycle`, `WpSmodeCycleB32/T/Rvc`, `UCycleSwp`, `WpSmodeWait`, `Wp`) ✓; `memModel_dropResv`
(`WpAtomic.lean:49-51`: `memModelAt E σ ∗ resvFragAt E cpu r b ⊢ |==> memModelAt E (σ.dropResv cpu) ∗ resvFragAt E cpu
none b`) is ALREADY the ghost lemma the new boundary rule needs — cite it; `ObsTrace.hartStep_wire/_recvd`
(`ObsTrace.lean:503-540`) and `DiskOf`'s three `hartStep` unfoldings are trivial under `dropResv` (devices untouched).
The COST description is wrong — [R12.1].  **(3) `itvOf`**: `execProgOk'S` (`PfRunShape.lean:242-262`) has the leading
star's labels `ls` existential PER INDEX with `fetchesOk fok (stt E k) s.esAg ls` (`:232-234`; `fok` 5-ary) — a per-row
counter constrained in that conjunct has `ls` in scope ✓; the fence.i/marker disambiguation works because the emission
order within an instruction is boundary `LInstr`, `LIFetch`, announce (`annLabel` = `LInstr`, or the marker at an
`sfence.vma` word, `WeakEvLang.lean:412-419`), body (`ebarLabel .Barrier_RISCV_i = LFence false×4`,
`WeakEvInst.lean:272-275`; `ebarNow … | .Barrier_RISCV_i => none`, `WeakEvLang.lean:745`), as the spike recorded
(`W5dG-spike.md:115-117`): the marker's star ends in `LIFetch`, fence.i's in the announce `LInstr` ✓; both are
REALIZING left-arm steps (`lbAdmin` excludes `LFence`, `WeakAxRealize.lean:130-134`), the intra-pair star is fetch-free
(`lbAdmin false`) ✓; the TsoMem update `max itv (max tv pub)` is computable from the shadow's `tv` and the log's
`ownPub` ✓ (`itvPostMachCSL`, `WeakInterp.lean:378-384`).  **(4) (F-dep)**: `LLoad … []` (`WeakEvInst.lean:323-325`),
`LExLoad … (depsAsrc (depsOfIb ib.ibBits))` (`:329-331`), `LStore`/`LExStore` with `depsAsrc`/`depsVsrc` (`:344-355`),
MMIO arms bare `LDev` (`:300-304,335-338`); `dstepT` inert on `LDev` (`AxDeps.lean:461-463`), `dedgesR` = `DTaddr` +
`DTctx` (`:445-446`), `dedgesW :448-451`, `rowDepsTAddr` (C) (`:702-707`) ✓ — plan:983-1011 is right.

## REQUIRED changes

**[R12.1] W-RSV form (i): the boundary rule cannot be "re-stated over `ctxTok`" — the cycle rules do not hold it; the
fragment must be threaded through the cycle rules' statements and their callers (incl. 8 `Xv6/` files), or moved into
an invariant.  Re-size and re-census; present the two forms in W-RSV-Q.**  Evidence: `wpLoop_restart` (`Wp.lean:385-400`)
is applied bare — `iapply wpLoop_restart; iintro %tick` — inside `wpLoop_m_base`/`wpLoop_m_rvc` (`WpCycle.lean:110,172`),
`wpLoop_wait_wfi`/`wpLoop_s_wfi_cycle` (`WpSmodeWait.lean:98,176`), `wpLoop_ucStep` (`UCycleSwp.lean:367`) and the
S-mode cycles; those rules' premises are `mConf/confCells ∗ clockCells ∗ pcIs ∗ (transTok) ∗ R ∗ P`
(`WpCycle.lean:96-105`, `WpSmodeCycleB32.lean:24-36`) — `WpCycle`, `WpSmodeCycleB32`, `WpSmodeCycleT`,
`WpSmodeCycleRvc` name neither `ctxTok`, `kctx`, `ownCtx` nor `resvFrag` (grep: 0 each; `UCycleSwp.lean:31` only in a
comment).  `ctxTok` rides inside `kctx` as `ctxToken` (`Ctx.lean:29-30`, `KCtx.lean:415,849,939`) and in user mode
inside the walker frames as `uResvTok cpu rv := ∃ r, resvFragAny cpu r` (`URunRW.lean:501-502`; `UCycleSwp.lean:31`) —
both one layer ABOVE the cycle rules.  Under form (i) the `.pure` step changes `σ.resv cpu`, so `memModelAt`'s
`resvName ↪●MAP resvMap σ` (`Resources.lean:949`; `resvMap_get? :611-612` = `(σ.resv c, acq)`) must be updated with the
hart's EXCLUSIVE fragment in hand (`memModel_dropResv`, `WpAtomic.lean:49-51`, is that update) — `resvMap_congr :621`
no longer applies.  Hence either **(i-a)** every cycle rule gains a `resvFragAny cpu r` premise and a `resvFrag cpu none
b` post (the 7 files' ≈ 15 `wpLoop_*` rules: `wpLoop_m_base/_rvc/_instrClk/_instrP/_instr`, `wpLoop_s_base/_rvc`,
`wpLoop_sT_base/_rvc`, `wpLoop_wait_wfi/_s_wfi_cycle`, `wpLoop_ucStep/_uwStep`, `wpLoop_sT_instr`
`WpSmodeSatpU.lean:280`), and EVERY caller supplies it: ≈ 27 MachCSL files (`WpSmodeCycle.lean:49,65`, `WpSmodeRules`,
`WpSmodeIntr`, `WpSmodeKpt`, `WpSmodeProc`, `WpSmodeSret`, `WpSmodeSwtch`, `WpSmodeTime`, `WpSmodeTrapCsr`, `WpStore`,
`WpLockSchema`, `WpMmode*` …) and **8 `Xv6/` files that call cycle rules directly** — `ProofSpin.lean:43`
(`wpLoop_m_instr`), `UserretPt.lean:52,130,177`, `UserretEntryPt.lean:63,113`, `UservecPt.lean:55,129,212`,
`UservecExitPt.lean:90,121,164,198` (`wpLoop_sT_instr`), `UserStepActive.lean:124`, `UkEngine.lean:178`
(`wpLoop_ucStep`), `UserStepWait.lean:34` (`wpLoop_uwStep`) — the fragment IS available at those sites
(`UserretEntryPt.lean:164` frames `∃ r, resvFragAny cpu r`; `kctx_cases` yields `Htok`, `WpSmodeWait.lean:257`), so the
change is mechanical but WIDE: L–XL, an `Xv6`-cone rebuild, and the plan's "`Xv6/` names no reservation except …" is
true of NAMES but not of the files a statement change touches; or **(i-b)** move the per-hart `∃ r, resvFragAny cpu r`
out of `ctxTok`/`uResvTok` into a per-hart invariant opened by the boundary rule and by the three AMO/store rules that
consume the fragment (`swp_sail_mem_write_plain_au :538-544`, `swp_sail_mem_read_excl_au :698-704`,
`swp_sail_mem_write_excl_au :711-717`, which take `resvFragAny`/`resvFrag` explicitly) — the cycle rules stay as
they are, but `Ctx.lean`'s `ctxTokAt` (`:298-299`, 20 sites), `KCtx`'s `ctxToken`, `URunRW`'s `uResvTok` (19 sites) and
every `ctxTok_cases/_intro` user change (M–L, a design change to the context token).  **Change**: in §C W-RSV, replace
"`wpLoop_restart` … is re-stated over `ctxTok` (returning `r := none`); its consumers are the 7 cycle files" by the
two forms above with the measured census, cite `memModel_dropResv` as the ghost lemma, re-size W-RSV to L–XL (i-a) /
L (i-b), and list the 8 `Xv6/` files under (i-a); in §D W-RSV-Q, split option (i) into (i-a)/(i-b) (both FAITHFUL —
the difference is CSL plumbing, no semantics) and re-present; in §0 F1 (ii) and the D26 schedule note that W-RSV is
the larger of the two serial MachCSL items.  Also record that form (ii) (the `inflight` flag) has the SAME ghost
problem unless the flag is kept OUT of `ResvVal` — and then the exclusive-store rule cannot learn "in-flight" from a
resource (`mmOk`'s clause "every reservation agrees with the top", `Resources.lean:779-783`, must weaken to in-flight
reservations, and `memModel_store_excl :221-224` needs that fact) — so (ii) is not the escape hatch.  S in the plan.

**[R12.2] [OWN.21] is missing: every W-COH gate still reads "coordinator to confirm", and the plan never says that the
foreign-only restriction [R11.1-alt] is LOAD-BEARING for route (9d), nor that [OWN.21] confirmed only the reset.**
Evidence: `grep OWN.21 notes/weak-allocproc-plan.md` is empty; the plan's mtime (03:42) precedes [OWN.21] (08:11), whose
text is "owner CONFIRMED corrected (a′) per [R11.1] (reset footprint coh at own store). Rev 15's [R11.1-alt] further
restricts the stamp to FOREIGN-authored sources — reported to the owner" (extra file, last entry).  The plan says
"coordinator to confirm" at plan:7-8, :830-831 ("LAUNCHABLE once the coordinator confirms"), :1074-1075, :1082-1084,
:1100-1103 and D26 :1370-1371.  Why the alt is load-bearing, not cosmetic: without it the §B(10) `m0`/`w_c'` candidate
(plan:562-568) is cat-consistent yet has NO TsoMem schedule — so at Stage 2 `cycleKill`'s realization of a proper hull
as a TsoMem run (§B(9d), `hullRun`, W4) FAILS for that hull and the robustness theorem is unprovable (a hole in (9d),
not merely "W11 (iv) harder"); the only repairs are the alt itself or a W8 census excluding the shape (a (b)-style
transported fact, M, **unverified**).  **Change**: add [OWN.21] to the header/history and §D G2-Q; mark the RESET as
RULED-and-CONFIRMED and the FOREIGN-ONLY stamp as "reported, confirmation pending — REQUIRED for the graph-only
derivation and for (9d)'s hull realization (the `m0`/`w_c'` candidate), the fallback being a W8 transported census";
set W-COH's status to LAUNCHABLE in the corrected form (both components), with the one-line fallback if the owner
declines the alt; replace every "coordinator to confirm" with the [OWN.21] state.  S.

## SUGGESTIONS

- **[R12.s1]** `itvOf` wording (§B(4)(iii)(ii), §C W5d): the update is driven by the index's REALIZING label
  (`s.esLb = LFence false×4` on the left arm), `ls` only disambiguates fence.i from the marker; state the frame
  condition `itvOf (k+1) i = itvOf k i` for every row `i ≠ s.esAg` and for non-fence steps; name `pub` (from the log) as
  an input of `itvStep` beside the shadow's `tv`/`rv`.
- **[R12.s2]** W-RSV's optional widening (standalone `LExLoad` realized as `LLoad`, plan:871-876): a dangling `lr.aq`
  leaves `hr.acq = true` until the hart's next store (`clearAcq`), and an EXCLUSIVE next store would take `tv := top+1`
  (`Lang.lean:150`, guard `excl && acq`) — a floor at the hart's own store position, which cat does not give (no
  `W;po;R` ppo).  Under the widening also clear `hr.acq` at the boundary (same rule, `resvMap` carries the bit), or
  note that `pairAdjacent` already pairs every later `LExStore` with its own `LExLoad`.
- **[R12.s3]** §C W-COH: say that `MState.afterLoad`'s signature is unchanged (it computes the per-byte source
  author/timestamp from `σ.mem` via `Hist.read`'s `find?`), only `HRead.afterLoad` changes — the four `afterLoad`-only
  files (`Wp`, `WpAtomic`, `WpSmodeFenceFloor`, `UIcache`) then need re-proof only where they unfold it; and name
  `hartViewsAt`/`memModelAt` (`Resources.lean:940-951`) as the evidence that no resource exposes `coh`.
- **[R12.s4]** §A(5)/(a): under W-RSV the "two reducible spin arms" are still both present (`blockedStep` now fires only
  against IN-FLIGHT reservations) — say so, so the published caveat is not read as "blocking is gone".
- **[R12.s5]** The W2 acceptance table's `LStore` row should record BOTH new effects on the shadow: the `coh` reset
  [R11.1] and `resv := none` (unchanged) — and the `LInstr` row gains "`resv := none` (W-RSV)", matching `instrPost`.

## Owner questions the plan is missing

- **G2-Q, closing the [OWN.21] loop (OWNER RULE form).**  Spec: riscv.cat rule 2 `([R];po-loc-no-w;[R]) \ rsw`
  (`gppo2`, `AxGraphCat.lean:151-156`); load-value makes an own po-earlier store visible at any gmo position
  (`gvisible`'s `gpo` disjunct) — an own store carries NO gmo constraint for a later same-source read; Sail: `mem_read`
  per access, no coherence state; Zifencei/PMAs: silent.  The ruled (a′) has TWO components: the reset at the own store
  ([R11.1], CONFIRMED [OWN.21]) and the foreign-only stamp ([R11.1-alt], reported).  Options: **(a′) both** — FAITHFUL,
  S–M, the plan's route; **(a′) reset only** — STRONGER (the `m0`/`w_c'` candidate, plan:562-568, is excluded),
  REQUIRES a W8 transported census to keep (9d) sound (M, **unverified**); **(a‴) no floor** — WEAKER, sound, S.  Ask
  for an explicit ruling on the foreign-only component.
- **W-RSV-Q re-presented (engineering; all options FAITHFUL for AMOs).**  Spec: Zalrsc — a reservation may be
  invalidated at any time; the atomicity axiom constrains successful pairs only; Sail in this tree —
  `load_reservation`/`cancel_reservation` are stubs, success is the opaque (`Xv6Extras.lean:65-80`); RVWMO/Zifencei/
  PMAs: nothing on blocking.  Options: **(i-a)** clear at `hartStep .pure` + thread `resvFragAny` through the cycle
  rules and their callers (L–XL, 8 `Xv6/` files, one `Xv6`-cone rebuild); **(i-b)** clear at `.pure` + per-hart
  reservation invariant replacing the fragment inside `ctxTok`/`uResvTok` (L; a context-token redesign); **(ii)**
  `inflight` flag — the same ghost cost (see [R12.1]).  Recommendation: (i-a) if the owner accepts touching the 8
  `Xv6/` call sites; otherwise (i-b).
