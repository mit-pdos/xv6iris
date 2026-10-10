VERDICT: NOT SATISFIED

# Review R11 of `notes/weak-allocproc-plan.md` rev 14 (adversarial, evidence-based; 2026-10-10)

Scope (per the R11 brief): rev 14 = R10's four required changes + [OWN.17]–[OWN.19]; audited hardest: G2-Q's new
options (a′)/(a‴) and "(★) by `candScaT` alone", W5b′'s step-list shadow and re-proved replay, the NEW W-RSV
(D19 (b)), the NEW W13 (F-dep) (D50 (b)), and every RULED mark against `~/dev/weak-orch/allocproc_revise3_extra.txt`.
`file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  NOT as written.  Four REQUIRED changes, all text/spec fixes of size S in the plan, none changing the
published statement: (1) G2-Q option (a′) — the recommended option, about to be re-presented to the owner — is
STRONGER than riscv.cat rule 2, not FAITHFUL (it ignores rule 2's `po-loc-no-w` exemption: the hart's own store
po-between two reads); (2) W-RSV's mechanics are internally inconsistent (the text both keeps and removes the
in-flight blocking that makes the AMO atomic, and the removal would leave a foreign hart STUCK, breaking
`Reducible`); (3) the Exec-trace shadow cannot carry `itv` — `fence.i` and the `sfence.vma` marker are the SAME
`Lbl` event, and `fok` has no `itv` argument — so W5d's M2 cut clause has no carrier as specified; (4) W13 (F-dep)
tells workers to fill the I/O arms "as the RAM arms do", but the RAM plain-load arm carries `asrc = []` (D-8).
G2-Q must NOT go to the owner until [R11.1] lands.  W5b′ may launch with the memory-field shadow only ([R11.3]
is W5d's); W13 (E)/(T), W5d-G G0 and W1b may launch regardless.

## What was verified (holds as cited; not to re-litigate)

**RULED marks**: every RULED tag in §D/§C/§0 matches `allocproc_revise3_extra.txt` — [OWN.17] G1-Q (e), G3-Q (a″),
D46–D49 (a), D50 (b), G2-Q kept OPEN per its NOTE (rev-14 prompt:8); [OWN.18] D51–D52 (a), D42–D43 (a),
`GraphFetchSpike` unrecoverable; [OWN.19] D19 (b), D20 (a), D9 (a), D8 (a); [OWN.16] W1-Q (c), Q-W3a (A), D41 (a),
D45 (a); [OWN.11]–[OWN.15] as before.  Header, §D preamble and history line agree.  **(a)** `Xv6.Allocproc :
ALLOCPROC` (`LinkAllocproc.lean:14-17` → `allocproc_proof`, `ProofAllocproc.lean:3623-3639`, 3,639 lines), in the
audited cone via `LinkSyscall.lean:84` / `LinkMain.lean:53`; `wp_allocproc_body`'s premises as listed
(`SpecAllocproc.lean:204-224`); `allocprocPost :118`; roots `roots.txt:6,19`; baseline axioms + the three opaques
(`baseline.json:11-14`; `adequacy_axioms_baseline.md` §3).  `NCPU = 8` (`TsoMem.lean:54`), `cpus = finRange NCPU`
(`Lang.lean:315`), `xN` (`Capstone.lean:94`).  **(b)** TsoMem: `evStep`'s plain-load arm `tv ≤ tvn ≤ top ∧ cohOk ∧
readBytes` (`Lang.lean:363-367`), `afterExcl` `tv := top` iff aq (`:134-138`), `store` `tv := top+1` iff `excl ∧
acq`, `hr := clearAcq`, `resv := none` (`:147-153`), `fence` (`:155-163`), `blockedStep` (`:395-403`), `dmaView`
(`:185`), DMA `¬ anyReserve` guard (`:539`, `devBlocked :548-553`); `HEnt.visible` `t ≤ tv ∨ tid = h`
(`TsoMem.lean:115-116`), `cohOk :263` footprint-wide, `afterLoad :266-270` stamps the footprint with `tvn`,
`fencePost :345`, `fenceDrains/fenceAcq :356-364` (= `pw ∧ sr` / `pr ∧ sr` on the `LFence` bits, `fence.tso`
included).  `srvwmoConsistent` and its residue table (`WeakAxiomatic3.lean:2050-2073`: rules 1–5, 7, 14; LB and
W→W excluded).  `cohOk` has ONE use (`Lang.lean:365`) ✓.  **G2-Q (a′) vs (★)**: (★) IS discharged by `candScaT`
alone — at `tvn_min := max(F, max_{foreign} t_j)`: `tv ≤ tvn_min`, `cohOk`, `tvn_min ≤ top`, and `Hist.read`
returns `t_j` per byte because `scaByte` at `tvn_sca ≥ tvn_min` (`PfRunShape.lean:61-72`) excludes own later
writes outright and foreign ones in `(t_j, tvn_sca]` ✓ (plan:511-516 correct).  **W5b′**: `pfStepFacts c i l`
reads the pre-configuration (`PfRunShape.lean:265-269`), `pfRunS.snoc` (`:273-277`), `Wpcfg` = img/log/dev/agents
(`WeakPromise.lean:135-139`); the replay `execPrefixPfRunProgShaped :512` builds `st` incrementally, so threading
the shadow is feasible as described; the shadow's `tv/rv/coh/acq` ARE computable from `E.exTr` (`LRmw aq`, the
`LFence` bits, the log for foreign-ness and `ownPub`).  **W-RSV census**: matches my grep exactly per file
(`blockedStep` Wp 8/Lang 4/ObsTrace 2/DecodeBridge 2/DiskOf 1; `othersReserve` WpAtomic 8/Lang 4/WpSmodeDev 3/Wp 3/
Resources 3/WpStoreOrd 2/WpPtWalkOwn 2; `anyReserve` WpDma 3/WpDev 1/Resources 1/WeakLang 1; `dropResv` WpAtomic 9;
`resvMap` Resources 29/WpAtomic 8/Wp 8/Power 3/PowerText 3/WpSmodeFenceFloor 2/WpDma 1; `snapOf` WpAtomic 11/
WpPtWalk 7/WpPtWalkOwn 6/WpSmodeAu 2/WpSmodeAtomic 1); `Xv6/*.lean` names no `othersReserve`/`blockedStep`/
`resvMap`/`snapOf`/`cohOk` ✓.  **W13 (F-dep)**: `dstepT` (`AxDeps.lean:461-481`) and `dstep`
(`WeakRvwmoConf.lean:493-495`) are inert on `LDev`; `dedgesR` = `DTaddr` + `DTctx`, no ctrl (`:445-446`), `dedgesW`
= addr/data/ctrl/trans/r13/ctx (`:448-451`); the `LLoad` arm adds `k :: dtLd` and `dtAcc` (rule 13) — so "`LIo rd`
= the `LLoad` arm shape, `LIo wr` = the `LStore` arm shape" IS faithful to appendix (c1) (addr→I/O load, addr/data/
ctrl(+13)→I/O store, provenance out of an I/O load, no ctrl→I/O load); `pnodeStep`'s MMIO arms emit bare `LDev`
(`WeakEvInst.lean:300-304,335-338`), `elabOk … LDev = True` (`:558`); `lbLdepfree` constrains `LLoad` ONLY
(`WeakPromise.lean:112-115`), so an `LIo rd` with sources does NOT falsify `pstepEvLdepfree`/`wpPfStepInv`/
`pstepEvLatFreeHalf`/`pstepEvTsOblivious` (`WeakEvCapstone.lean:238,714,1048,1058`) ✓; `rowDepsTAddr` (C)
(`AxDeps.lean:702-707`) already admits `DTaddr` edges into pure READ items ✓.

## REQUIRED changes

**[R11.1] G2-Q option (a′) is STRONGER than riscv.cat, not FAITHFUL: rule 2 exempts two reads with a SAME-HART
WRITE to the byte po-between them (`po-loc-no-w`), and TsoMem's `coh` stamp survives the hart's own store.**
Evidence: `gppo2` (`AxGraphCat.lean:151-156`) has the conjunct `∀ w v, gwritesByte G w a v → gpo e1 w → gpo w e2 →
False`; `MState.store` (`Lang.lean:147-153`) changes `hr` only by `clearAcq` — `coh` is never lowered; (a′) as
written (plan:1029-1036, §B(10) plan:523-526) stamps `coh a := max (coh a) t_a` at a global source and nothing
resets it.  **Counterexample** (cat-consistent; TsoMem-under-(a′) cannot realize it; `linCandScaT` FALSE): hart A:
`lb a` = `r_prev` reads `a` from foreign `w` (global at `r_prev`: its minimal view ≥ `gwix w`, so `coh a := gwix
w`); `sb a` = `m` (own); `lh (a,b)` = `r` reads `a` from `m` (forwarded) and `b` from foreign `w_b`.  Hart B writes
`w_b`, then `w_b'` to `b`, then `w` to `a`.  gmo `w_b <gmo r <gmo w_b' <gmo w <gmo r_prev <gmo m`: rule 2 between
`r_prev` and `r` is EXEMPT (`m` po-between, `gppo2`'s conjunct), rule 1 gives only `r_prev <gmo m` ✓, `W;po;R` is not
ppo, load-value ✓ for all three (`w_b'` and `w` are gmo-after `r`, hence invisible to it; `m` visible by po).  Under
(a′) `r` must read at a view ≥ `coh a = gwix w > gwix w_b'`, so TsoMem returns `w_b'` for byte `b` — the candidate's
`(m, w_b)` has NO TsoMem step; at Stage 2 `F(r) ≥ gwix w > tvn_sca(r)` and the plan's case split (same source /
different source ⇒ rule 2) has no case for "different source BECAUSE of an own write between".  **Change**: (a′) :=
per-byte global-source stamp AND `MState.store` resets `coh` on the store's footprint (`coh a := 0` for `a` in the
footprint; a later read re-stamps) — this is exactly `po-loc-no-w` + same-source exemption, FAITHFUL; (a‴) is
unaffected (no `coh`).  §B(10)'s derivation gains the third case (own write po-between ⇒ the stamp was reset ⇒
vacuous).  W5b′'s `stamp` parameter becomes a PAIR (load stamp, store effect) so W2's table stays parametric; W2's
hart-`LStore` row notes the reset (no effect on `R-view` equality — the shadow replays it).  §0 F1 (iii) names the
missing reset as the SECOND component of today's strengthening (today's footprint stamp also survives own stores).
Mark rev 14's (a′) STRONGER (a per-byte CoRR floor that outlives the hart's own store).  Re-present G2-Q only after
this fix.  S.

**[R11.2] W-RSV (D19 (b)) is internally inconsistent and, as written, breaks `Reducible`.**  Evidence: plan:784-785
"`othersReserve`/`anyReserve` range over IN-FLIGHT reservations only, so an AMO's read→write window still excludes
foreign stores" vs plan:791-792 "`blockedStep`'s store arm (`Lang.lean:402`) and the DMA `¬ anyReserve` guard
(`:539, 562`) go" and plan:803-804 "`Wp`'s generic blocked disjunct (its store case becomes vacuous)".  The store
arm of `evStep` requires `¬ othersReserve` (`Lang.lean:372-378`; the exclusive-read arm likewise, `:368-371`) and `hartStep`'s only other arm is `blockedStep`
(`:500-505`): remove the latter's store case while the former still blocks in-flight reservations and a foreign
hart whose store overlaps an in-flight AMO has NO transition — stuck, not self-looping — so `Reducible` (the
published (a)) fails; remove the `evStep` guard instead and the AMO is no longer atomic against foreign stores/DMA
(the lock's `amoswap.w.aq`, `KernelImage.lean:2265-2270`, loses mutual exclusion — `ProofAcquire` unprovable), and
D19's "FAITHFUL for AMOs" mark is false.  **Change** (§C W-RSV, D19): the `evStep` guards, `blockedStep`'s store arm
and the DMA `¬ anyReserve` guard/`devBlocked` arm ALL STAY, restricted to IN-FLIGHT reservations ("its store case
becomes in-flight-only", not vacuous).  State the simplest FAITHFUL form as the recommendation: clear `σ.resv cpu`
at the hart's instruction boundary (`hartStep`'s `.pure` arm, `Lang.lean:500-502`, today `σ' = σ`; the pf twin is
`pnodeStep`'s `LInstr`, `WeakEvInst.lean:284-288`) — then NO reservation is ever dangling, the `inflight` flag and
the "overlapping store INVALIDATES" rule are unnecessary (Zalrsc permits invalidation at any time, so clearing is
FAITHFUL), and the census shrinks to the `.pure` rule in `Wp`, `blockedStep`/`othersReserve` consumers re-proved
against "reservations are in-flight".  Three corrections to the surrounding text: (i) "`LExStore` needs the OWN
reservation still valid" (plan:806-807, 548) — TsoMem never reads `σ.resv cpu` (`MState.store`, `evStep`'s
`memWrite` arm check only `othersReserve`), drop it; (ii) "the exclusive store … becomes a PLAIN store, success by
the opaque — WEAKER than Zalrsc" is TODAY's semantics (same evidence), so W-RSV introduces no new weakening — say
so and move the mark to F1's description of the current model; (iii) the Svadu A/D LR/SC pair (`WpPtWalk.lean:84,
111,135,161` `exclReadAU … snapOf pa 8`) is issued INSIDE one memory instruction's translation, hence IN-FLIGHT for
its whole window — the "needs a reservation-still-valid premise or a retry" risk (plan:800-802) is withdrawn; the
re-proof is mechanical.  Census additions: `SailHooks.lean:5,14,26` (`valid_reservation` hook, unchanged) and the
`MachGS.resvName` ghost name (`Resources.lean:122,433,475`) constructed by `Xv6/AppUnionPre.lean:89`,
`Xv6/AppPreGS.lean:54` — unchanged if `Resv := Mem` (`TsoMem.lean:208`) keeps its type (it does under the
boundary-clearing form; under the `inflight` form `ResvVal` changes and the two Xv6 files are touched — say which).
S in the plan.

**[R11.3] The Exec-trace shadow cannot carry `itv`, and `fok` has no `itv` argument: W5d's M2 cut clause "takes the
SHADOW's `itv`" has no carrier in `execProgOk'S`.**  Evidence: `fence.i` is `ebarLabel .Barrier_RISCV_i = LFence
false false false false` (`WeakEvInst.lean:272-275`, `ebarNow … | .Barrier_RISCV_i => none`,
`WeakEvLang.lean:745`); the Q7 `sfence.vma` marker is the SAME label (`annLabel`, `WeakEvLang.lean:418-419`); `Lbl`
has four constructors (`WeakAxiomatic.lean:87-91`), `projLbl (.LFence …) = some (.LFence …)` (`PromiseBridge.lean:
536`) and `lbAdmin` excludes `LFence` (`WeakAxRealize.lean:129-133`), so BOTH reach `E.exTr` as indistinguishable
`Estep`s (`esAg`, `esLb`; `WeakAxiomatic.lean:98-101`) — `emFenceI`'s criterion needs the admin block, which `E`
does not have and whose `ls` is existential per index inside `execProgOk'S` (`PfRunShape.lean:242-262`).  `fok :
Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop` (`:242`, `fetchesOk :232`).  So plan:737-739 "clause
(iii)′ … over `shadowOf (E.exTr.take k)` … a projection lemma ties it to the step-list shadow" is TRUE for
`tv/rv/coh/acq` and FALSE for `itv`; plan:303-304/821 ("the clause's `itv` is the SHADOW's, supplied by W5d") names
no mechanism.  Over-approximating (every `LFence false×4` raises `itv`) is not derivable at Stage 2 (`gzFetch` uses
the EMISSION's `fence.i` sites); under-approximating (`itv = 0`) breaks W4's `LIFetch` row (TsoMem fetches at `itv ≤
tvn`, `Lang.lean:360-362`).  **Change**: W5b′'s (iii)′ is the MEMORY-field shadow only (say so); W5d adds to
`execProgOk'S` a per-row, per-step `itvOf : Nat → Nat → Nat` CONSTRAINED inside each index's conjunct by that
step's admin block `ls` (`itvOf (k+1) i = itvStep (itvOf k i) (shadow memory fields) ls`, `fence.i` identified in
`ls` by `emFenceI`'s criterion — `ls` IS in scope there), and `fok` takes it as a 6th argument (M2 cut form: `∃ q,
itvOf k i ≤ q ≤ |log| ∧ ifetchOk … ∧ ∀ byte, t ≤ q`); lemma: the step-list `tsoShadow`'s `itv` equals `itvOf`
along the replay.  S inside W5d's L; M1 (`candKfetch`) unaffected.  Update §B(4)(iii)(ii), §C W5b′/W5d, W4's
`LIFetch` M2 row.

**[R11.4] W13 (F-dep) (1) says the I/O payload is filled "as the RAM arms do with `asrc`/`vsrc`" — the RAM
plain-load arm carries `asrc = []` (D-8).**  Evidence: `l = LLoad … (paZ req.pa) tvs []` (`WeakEvInst.lean:
323-325`); only `LExLoad`/`LStore`/`LExStore` carry `depsAsrc/depsVsrc (depsOfIb ib.ibBits)` (`:329-331,344-355`);
`AxDeps.lean:405-406` "the load half is `[]` until D-8 is unmasked"; `WeakAxiomatic3.lean:2065-2067` "rule 9 (LOAD
half) OMITTED BECAUSE OF D-8".  A worker mirroring the `LLoad` arm emits NO addr→I/O-load edge — i.e. D50 (a), not
the RULED (b).  **Change**: (F-dep) (1) reads "`LIo rd`'s `asrc` := `depsAsrc (depsOfIb ib.ibBits)` as the `LExLoad`
arm does (`:329-331`), NOT as the plain `LLoad` arm (D-8 `[]`); `LIo wr`'s `asrc/vsrc` as the `LStore` arm"; add to
(3) that the I/O-load edges are the FIRST load-half `DTaddr` edges the emission produces, that RAM loads stay
D-8-masked (rule 9's RAM load half remains omitted — the I/O edges are a faithful ADDITION, not a D-8 unmasking),
and that `lbLdepfree`/`pstepEvLdepfree` and their four consumers survive because they constrain `LLoad` only
(cites above).  Also record the direction of the pin-bridge re-proof: `pinSegPin` proves "checker `PDep` ⇒
`rowDeps` edge" and `checkerTaintSubProv` "checker taint ⊆ provenance" — both are preserved when `rowDeps`/
provenance GROW, so `gen_weak_pins.py` need not tag MMIO reads unless xv6 pins are to USE MMIO-sourced
dependencies (none expected; the plan's "or the correspondence is stated for RAM items only" is the wrong
dichotomy).  M stands.  S in the plan.

## SUGGESTIONS

- **[R11.s1]** The phrase "the `oib = none` discard" (plan:672-674, 920) is misleading: in `pnodeStep` `oib = none`
  means "`ib` unchanged" (`.pure → some ibNone`, `regRead → some (ibRd ib r)`, every other arm `none`,
  `WeakEvInst.lean:284-296`) — the RAM store arm has it too.  Keep rev 14's gloss, drop the word "discard".
- **[R11.s2]** §0 F1's "(ii) reservation serialisation" should also name what TsoMem's reservation does NOT do:
  it never decides an SC's success (the opaque does, `UWait.lean:21-26`, `UserMemLrsc.lean:9-13`) — so the model's
  LR/SC is ALREADY "WEAKER than Zalrsc" (an SC may succeed over an intervening store) and W-RSV only removes the
  blocking.  Update `TsoMem.lean:27-31`'s header text in W-RSV's acceptance.
- **[R11.s3]** W-RSV census "≈ 18 MachCSL files" → 21 (`DecodeBridge, DiskOf, Lang, ObsTrace, Wp, Resources,
  TsoMem, WpAtomic, WpPtWalkOwn, WpSmodeDev, WpStoreOrd, WpDev, WpDma, Power, PowerText, WpSmodeFenceFloor, WpPtWalk,
  WpSmodeAtomic, WpSmodeAu, UWait, SailHooks`) + `Weak/WeakLang.lean:52` (the pf twin already DROPS the DMA guard —
  cite it as the precedent for the direction).
- **[R11.s4]** G2-Q's Spec line should quote `po-loc-no-w` explicitly ("no write to the byte po-between, by ANY
  instruction of the hart") so the owner sees why the reset is part of faithfulness; and the W2 acceptance column
  [R10.s5] gets a row for the `coh` reset.
- **[R11.s5]** W14's SC run satisfies the corrected (a′) trivially (every load at the top, stamps ≤ top) — say so,
  as plan:939-940 does for `candScaT`/`candDiskLat`.

## Owner questions the plan is missing

- **G2-Q, corrected option set (OWNER RULE form; replaces plan:1017-1054's (a′)).**  Spec: RVWMO rule 2 / riscv.cat
  `([R];po-loc-no-w;[R]) \ rsw` (`gppo2`, `AxGraphCat.lean:151-156`): two same-hart reads of a common byte are
  ordered only if they return DIFFERENT writes AND no same-hart write to that byte lies po-between; rule 1 orders
  a read before a po-later same-byte WRITE (`gppo1 :146-147`); load-value makes a hart's own po-earlier store
  visible at any gmo position (`gvisible`, `Graph.lean:236`); no `W;po-loc;R` ppo; Sail: `mem_read` per access, no
  coherence state; Zifencei/PMAs: silent.  Options: **(a′) per-byte global-source stamp + reset on the hart's own
  store to the byte** — FAITHFUL (exactly rule 2 with both exemptions), S–M, the same 7 MachCSL files + `MState.store`
  (`Lang.lean:147-153`), W11 (iv) graph-only (M); **(a‴) no coherence floor** — WEAKER, SOUND, S; rev 14's (a′)
  without the reset — STRONGER (a CoRR floor outliving the hart's own store), rejected by [R11.1]; (a) as originally
  worded — STRONGER, rejected by [R10.1]; (b) keep TsoMem + W8 (vi) — FAITHFUL as a program fact, TsoMem stays
  STRONGER (both components), W11 (iv) transported; (c)/(d) rejected.  Recommendation: (a′) with the reset, unless
  the owner prefers (a‴).
- **W-RSV form (engineering; both FAITHFUL for AMOs).**  Spec: Zalrsc — a reservation may be invalidated at any
  time (spurious SC failure allowed); the atomicity axiom constrains successful pairs only; Sail in this tree —
  `load_reservation`/`cancel_reservation` are no-op stubs, success by the opaque (`Xv6Extras.lean:65-80`).  Options:
  (i) clear `σ.resv cpu` at the instruction boundary (`hartStep .pure`, `Lang.lean:500-502`) — FAITHFUL, smallest
  (recommended, [R11.2]); (ii) an `inflight` flag + invalidation by overlapping stores — FAITHFUL, +M, touches
  `ResvVal`/`resvName` sites in `Xv6/`.
