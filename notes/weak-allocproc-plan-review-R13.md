VERDICT: NOT SATISFIED

# Review R13 of `notes/weak-allocproc-plan.md` rev 16 (adversarial, evidence-based; 2026-10-10)

Scope (per the R13 brief): rev 16 = R12's two required changes + [OWN.21]–[OWN.23]; audited hardest: (1) the W-RSV
(i-a) MEASURED census — 16 cycle rules / 25 MachCSL / 8 `Xv6/` files — and the claim that the `wpLoop_k_*` wrappers
absorb the fragment so "the rest of the `Xv6` cone stays as it is"; (2) G2-Q (a′) with BOTH components against the
code W-COH must change; (3) that every confirmation gate is gone and no owner question is OPEN; (4) that the Stage-1
launch set (W5b′, W2's rows, W1b, W-COH) is launchable AS WRITTEN with correct dependencies; plus the standing (a)–(e)
checks.  `file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  NOT as written — two REQUIRED changes, both S text fixes that do not touch the published statement:
**[R13.1]** the (i-a) census is right for the S-mode kernel lane but WRONG for the M-mode lane: the 35 `wp_m_*`
wrappers (`MachCSL/WpMmode*.lean`) carry NO context bundle, so THEIR statements change and the three `Xv6/` M-mode
proofs that apply them (`ProofEntry`/`ProofStart`/`ProofTimerinit`, 68 applications) are edited; `SpecSpin`'s
`wp_spin_body`/`SPIN` has no token at all (statement change) — the plan's "the rest of the `Xv6` cone … stay[s] as
[it is]" (plan:905-907, repeated at :1428) is false, and the owner ruled (i-a) "at this cost" [OWN.23]; **[R13.2]**
"W2's WHOLE table launchable NOW" (plan:784-789, :1142) is not: the hart `LLoad` and hart `LStore` rows' LEAN
(`pfStepTso`'s `R-view` EQUALITY) is against the COMPILED `MState.afterLoad`/`MState.store`, which W-COH changes
(and changes `HRead.afterLoad`'s signature), so those two rows depend on W-COH landing; the other rows and the
FlatMem ↔ `histOf` bulk do not.  Also fix W1b's "owner-gated" (plan:777) vs "launchable" (plan:1143).  Everything
else audited holds.  **May launch now without waiting for rev 17**: W5b′, W-COH, W13 (E), W5d-G G0, W1b, and W2's
instance-independent rows.

## What was verified (holds as cited; not to re-litigate)

**RULED marks and gates**: [OWN.21]–[OWN.23] are in the header, §0 F1, §C W-COH/W-RSV and §D exactly as the extra
file rules them (G2-Q (a′) BOTH components; W-RSV-Q (i-a); D19 (b)).  `grep -i "to confirm\|coordinator"` hits only
the header's HISTORY line (plan:8); the only "OPEN" words left are gap statuses (§B(3) graph tier, §B(9) user rows)
and history (plan:22) — "no OPEN owner question" is TRUE ✓.  Both G2-Q and W-RSV-Q open with a "Spec:" line and
mark every option (plan:1176-1188, :1417-1423) ✓ — the OWNER RULE is met.
**(a) `Xv6.Allocproc`**: `LinkAllocproc.lean:14-16` (`allocproc_proof`), `wp_allocproc_body` `SpecAllocproc.lean:
204-224` with exactly the premises listed in §A(1) (`kctx`, `procsInv`, two `isLock`s, `kallocAvail`,
`procsAvailAt`, `□ (killCred -∗ Q (-1))`, `actLend`, `wpNext` with the `sieArm` arm) ✓; roots `roots.txt:6,19`
(`xv6FsAdequacy_closed`, `xv6TextAdequacy_closed`) ✓; `baseline.json:11-14` = 3 axioms + the 3 opaques ✓.
**(b) TsoMem vs sRVWMO**: the residue table (`WeakAxiomatic3.lean:2050-2071`: rules 1–5, 7, 14 IN; 6, 9-load,
12 OMITTED) and the litmus divergences LB + reader-fence-only MP (`WeakSrvwmoLitmus.lean:1663-1695`) ✓; TsoMem's
`HEnt.visible`/`Hist.read` (`TsoMem.lean:115-120`), `HRead` (`:255-280`: `cohOk` footprint-wide `:263`,
`afterLoad` stamps every footprint byte with `tvn` `:268-270`, `afterExcl` keeps `coh` `:273`, `clearAcq` `:276`),
`MState.afterLoad` `{ σ with hr := … }` (`Lang.lean:127-129` — `σ.mem` IS in hand, so per-byte source authors are
computable; signature unchanged as [R12.s3] says), `MState.store` touches `hr` only by `clearAcq` and clears `resv`
(`:147-153`), `dropResv` (`:141`), the plain-load arm with `cohOk` (`:363-367`), the store arm's `¬ othersReserve`
only (`:372-375`), `blockedStep` (`:395-403`), `hartStep`'s `.pure` arm `σ' = σ` (`:499-502`) ✓.  `hartAgent cpu`
is MachCSL's own author id (`Lang.lean:148`), `HEnt.tid : Agent` — the (a′) test `e.tid ≠ hartAgent cpu` is
well-typed as written ✓; DMA entries are `diskAgent`-authored and so foreign ✓.
**(1) The (i-a) census, S-mode lane — CONFIRMED**: the 16 rules exist (`wpLoop_m_base/_rvc/_instrClk/_instrP/_instr`
`WpCycle.lean:96,157,282,321,332`; `wpLoop_s_base` `WpSmodeCycleB32.lean:24`; `wpLoop_s_rvc` `WpSmodeCycleRvc.lean:
22`; `wpLoop_s_instr` `WpSmodeCycle.lean:29`; `wpLoop_s_instr_clk` **`WpSmodeTime.lean:54`** (the plan files it under
`WpSmodeCycle` — 9 defining files, not 8, [R13.s1]); `wpLoop_sT_base/_rvc` `WpSmodeCycleT.lean:72,138`;
`wpLoop_sT_instr` `WpSmodeSatpU.lean:280`; `wpLoop_wait_wfi/_s_wfi_cycle` `WpSmodeWait.lean:87,160`;
`wpLoop_ucStep/_uwStep` `UCycleSwp.lean:362,387`); `wpLoop_restart` (`Wp.lean:385-400`, resource-free, the ONLY rule
discharging the `.pure` step) is applied bare at exactly the 10 sites the plan lists ✓; **exactly 25 MachCSL files**
mention a cycle rule (grep, the plan's list ✓); **exactly the 8 `Xv6/` files** apply one directly at the cited lines
(`ProofSpin.lean:43`, `UserretPt.lean:52,130,177`, `UserretEntryPt.lean:63,113`, `UservecPt.lean:55,129,212`,
`UservecExitPt.lean:90,121,164,198`, `UserStepActive.lean:124`, `UkEngine.lean:178`, `UserStepWait.lean:34`) ✓, and
the fragment IS in scope at the S-mode/user ones: the trampoline files frame `ctxTok cpu curCtx` (`UserretPt.lean:
51-63`, `UservecPt.lean:54-69`, `UservecExitPt.lean:89-101`, `UserretEntryPt.lean:112-164`), `ust_step_active`/
`ust_step_waiting` hold `uFr` ∋ the walker `ctxTok` = `ownCtx ∗ uResvTok` (`UCycleSwp.lean:31-33`, `URunRW.lean:
501-502`), `UkEngine.lean:125` extracts `ctxToken` from `Rut` ✓.  **The `wpLoop_k_*` wrappers DO absorb it**:
`kctxP` contains `ctxToken cpu` for EITHER `lent` (`KCtx.lean:839-850`; `lent` only lends the `intena` cell),
`kctxL := kctxP X ihs` (`:925`), `kctx_cases/_intro` expose it (`:931-952`), `ctxToken = ctxTok cpu curCtx` (`:415`)
= `ownCtxAt ∗ ∃ r, resvFragAnyAt E cpu r` (`Ctx.lean:298-299`); `wpLoop_k_gen` takes `kctxL lent cpu k` and returns
`kctxL lent cpu' …` (`WpSmodeRules.lean:52-60`) ✓ — so `Xv6`'s uses of `wpLoop_k_setReg`/`_keep` (3 sites) are safe ✓.
`memModel_dropResv` (`WpAtomic.lean:49-51`) is the ghost update, `b` the acquire bit (not a fraction) ✓.
**(2) W-COH's target**: `coh`'s 7 files and "no Iris resource exposes `coh`" were verified by R12 and stand.
**(e) Other spot checks**: `NCPU = 8` (`TsoMem.lean:54`), `powerFork` = `cpus.map (Loop gen) ++ DevId.all.map
(DevLoop gen)` (`Lang.lean:315-320`), `xN σ0 = (epsInit σ0).length` (`Capstone.lean:94`), `rvwmoCatConsistentT`
(`AxDeps.lean:208-211`), `gppo2` with the `po-loc-no-w` conjunct (`AxGraphCat.lean:151-156`) ✓.  W5b landmarks
(`PfRunShape.lean:53,72,85,95,232,242,265,512,594`) ✓; `Weak/TsoShadow.lean` does NOT exist yet (W5b′ is genuinely
unstarted) ✓; `Weak/TsoOfPf.lean` names no `evStep`/`hartStep` (the positive rows are argued, as the plan says) ✓.

## REQUIRED changes

**[R13.1] The (i-a) census misses the M-mode lane: the `wp_m_*` wrappers have no context bundle, so their STATEMENTS
change, and with them three more `Xv6/` proof files and `SpecSpin`'s interface.  Correct plan:893-907, :1409-1412 and
:1426-1428, and report the corrected cost to the owner (who ruled (i-a) "at this cost" [OWN.23]).**  Evidence: the
five M-mode cycle rules (`WpCycle.lean:96,157,282,321,332`) are stated over `mConf cpu dq c ∗ clockCells cpu ∗ pcIs
cpu pc ∗ R ∗ P` with NO bundle (`:103-105`), and the 35 `wp_m_*` wrappers that apply them (`WpMmode.lean`,
`WpMmodeAlu.lean`, `WpMmodeCsr.lean`, `WpMmodeCtl.lean`, `WpMmodeMret.lean`; `grep -c "ctxTok\|resvFrag\|kctx"` = 0 in
four of the five, and in `WpMmode.lean` only `wp_m_ld_same` carries `ctxTok cpu curCtx`, `:388-391`) are likewise
bundle-free — e.g. `execSpec_auipc`/`wp_m_auipc` (`WpMmode.lean:28-33`).  Under (i-a) `wpLoop_restart` must consume
the hart's fragment (the `.pure` step now changes `σ.resv cpu`; `memModelAt`'s `resvMap` auth must move with
`memModel_dropResv`, `WpAtomic.lean:49-51` — or at least READ the fragment to learn `σ.resv cpu = none`; either way
the fragment is needed), so `wpLoop_m_*` gain it, and the 34 bundle-free `wp_m_*` wrappers have NOTHING to absorb it
into: their statements gain `resvFragAny cpu r`/`resvFrag cpu none b` (or a new M-mode token).  Their `Xv6/` callers:
`ProofEntry.lean` (8 applications), `ProofStart.lean` (39), `ProofTimerinit.lean` (21) — NOT among the plan's 8.
Their SPEC bodies already carry `ctxTok cpu curCtx` (`SpecEntry.lean:48`, `SpecStart.lean:62`, `SpecTimerinit.lean:
57`), so those three change at the PROOF level only (the fragment is in scope); but `wp_spin_body`/`SPIN`
(`SpecSpin.lean:34-42`) and `ProofSpin`'s `wp_m_j`/`spin_loop` (`:32-55`) have NO token — a STATEMENT change
(isolated: `SPIN.wp_spin` has no caller outside `LinkSpin.lean:14`; `ProofBoot.lean:27`/`SpecBoot.lean:75` use only
the address `KA.«spin»`).  `WpStore.lean:201,223` (`wpLoop_m_instr`) is in the 25 and has `ctxTok` in scope ✓.
**Change**: in §C W-RSV (plan:893-907) after "and EVERY caller supplies it — measured:" add "the S-mode kernel lane's
`wpLoop_k_*` wrappers (`WpSmodeRules.lean:52-60`, `kctxL ∋ ctxToken` for either `lent`) and the user lane's `uFr`
(`uResvTok`) ABSORB the fragment, so their statements and the `Xv6` cone above them stay; the M-MODE lane has no
such bundle: the 35 `wp_m_*` wrappers (`WpMmode*.lean`, 5 of the 25 files) change STATEMENT (34 gain the fragment;
`wp_m_ld_same` already holds `ctxTok`), and their `Xv6/` callers `ProofEntry` (8), `ProofStart` (39), `ProofTimerinit`
(21) are re-threaded at the proof level (their spec bodies already carry `ctxTok cpu curCtx`, `SpecEntry.lean:48`,
`SpecStart.lean:62`, `SpecTimerinit.lean:57`); `SpecSpin.lean:34-42`'s `wp_spin_body`/`SPIN` and `ProofSpin.lean:
32-55` gain the fragment in their STATEMENTS (no chain caller; `LinkSpin.lean:14` only)".  Re-count: **16 rules in
9 files; 25 MachCSL files (35 `wp_m_*` statements among them); 12 `Xv6/` files (8 direct + `ProofEntry`,
`ProofStart`, `ProofTimerinit`, `SpecSpin`; `LinkSpin` rebuilds)**; size class L–XL UNCHANGED.  Replace "so THEIR
statements — and the rest of the `Xv6` cone, which calls them — stay as they are" (plan:906-907) and "the `wpLoop_k_*`
schema wrappers absorb the fragment from `kctx`, so the rest of the cone is untouched" (plan:1428) by the lane split
above; mirror in D19 (plan:1409-1412).  Add one line to the header's history ("R13: (i-a) census + M-mode lane").
S in the plan.  (Form (i-b) is UNAFFECTED by this finding — its boundary rule opens an invariant and the M-mode
wrappers stay as they are — which is a point in its favour the owner has not seen; see the owner question below.)

**[R13.2] "W2's WHOLE table launchable NOW" is wrong for two rows: the hart `LLoad` and hart `LStore` rows' Lean
depends on W-COH landing.  Also W1b's "owner-gated".**  Evidence: W2 proper is `pfStepTso` — "0 or 1 TsoMem steps …
to a related state (`R-view` = EQUALITY through `tsoShadow`)" (plan:781-783).  The TsoMem step for a hart plain
load is `evStep`'s arm with `σ' = σ.afterLoad cpu req.pa n tvn` (`Lang.lean:363-367`) and for a hart store `σ' =
σ.store cpu …` (`:372-375`); both post-states are computed by the COMPILED `HRead.afterLoad` (`TsoMem.lean:268-270`,
footprint-`tvn` today) and `MState.store` (`Lang.lean:147-153`, `clearAcq` only today).  `hr_T = hr_S` therefore holds
only for the shadow INSTANCE equal to the compiled TsoMem — today's `(footprint-tvn × none)`, the (a′) pair only after
W-COH — and W-COH also changes `HRead.afterLoad`'s SIGNATURE (plan:861-863: "gains the per-byte stamp input"), which
breaks any `pfStepTso` arm stated over the old one.  The shadow (W5b′) and the acceptance TABLE are parametric; the
Lean of those two rows is not.  The other rows are instance-independent (`afterExcl` keeps `coh`, `:273`; `fence`
touches `tv/itv` only, `:155-163`; `dmaRead`/`storeDma` move no hart `hr`; `LIFetch` reads only), as is the
FlatMem ↔ `histOf` bulk (`pfLoadRow`'s bytes, `R-hist`).  **Change**: in §C W2 (plan:784-789) replace "the WHOLE
table" by "the acceptance TABLE (parametric) and every instance-INDEPENDENT row's Lean (store-reservation side,
exstore, fence, `fence.i`, fetch-M1, silent/regw/ctrl/dev, `DRead` under `candDiskLat`) plus `pfLoadRow`'s FlatMem ↔
`histOf` bulk; the hart `LLoad` row's `afterLoad` post-state and the hart `LStore` row's `coh` RESET are finished
against the post-W-COH `TsoMem` (S–M once W-COH lands; W-COH is S–M and launches in parallel, so no critical-path
cost)"; in the Status (plan:1142) and D26 (plan:1455-1456) write "W2 (instance-independent rows now; `LLoad`/`LStore`
post-states after W-COH)".  W1b: plan:777 says "owner-gated" while plan:1143 lists it "Now launchable" and the
published (b) says "after W1b, live pids pairwise distinct" (plan:202) — [OWN.16] (c) folds the exports into W1b, so
write "RULED-in by [OWN.16] (c); schedule at the owner's discretion (D10)" at :777.  S.

## SUGGESTIONS

- **[R13.s1]** `wpLoop_s_instr_clk` is defined in `WpSmodeTime.lean:54`, not `WpSmodeCycle` — "16 rules in 8 files" →
  9 files (`WpCycle`, `WpSmodeCycleB32`, `WpSmodeCycleRvc`, `WpSmodeCycle`, `WpSmodeTime`, `WpSmodeCycleT`,
  `WpSmodeSatpU`, `WpSmodeWait`, `UCycleSwp`).
- **[R13.s2]** Under (i-a) the S-mode cycle rules have TWO continuations (`▷ (… -∗ wpLoop cpu) ∧ trapBranch cpu c
  tier root sie pc P`, `WpSmodeCycleB32.lean:33-36`; `trapBranch` `WpSmodeCycleBase.lean:77`): the `resvFrag cpu none
  b` post must be delivered on BOTH arms (the handler re-forms `ctxToken cpu` on the same hart).  Say so, or the
  worker will discover it at `trapBranch`.
- **[R13.s3]** W-COH: `Hist.read` returns the VALUE only (`TsoMem.lean:119-120`); the foreign-only stamp needs the
  entry (`HEnt.tid`, `HEnt.t`) — add a `Hist.readEnt` beside it and have `MState.afterLoad` build the per-byte
  `List (Option (Agent × Nat))` it hands to the new `HRead.afterLoad`.  Name it so W5b′'s `tsoShadow` mirrors the
  same per-byte input from the pf log (`wmTid`, position + 1).
- **[R13.s4]** §C W-RSV: record that `wp_m_ld_same` (`WpMmode.lean:388-391`) is the one M-mode wrapper that already
  threads `ctxTok` — the template for the other 34 if the plan prefers a token to a bare fragment in M-mode.
- **[R13.s5]** Status line: "W-RSV … waits for W-COH (shared files), not for an owner" — add "and for M1 (D26)"; the
  §C W-RSV "Deps" line already says so, the Status line reads as if W-RSV could start right after W-COH.

## Owner questions the plan is missing

- **W-RSV-Q, cost re-presented after [R13.1] (engineering; every option FAITHFUL for AMOs).**  Spec: Zalrsc — a
  reservation MAY be invalidated at any time, the atomicity axiom constrains SUCCESSFUL pairs only; Sail in this
  tree — `load_reservation`/`cancel_reservation` are `pure ()` stubs and SC success is the opaque
  (`LeanRV64D/Xv6Extras.lean:65-80`); RVWMO/Zifencei/PMAs: nothing on blocking — NOT a semantics question, the
  machine change is the same one arm (`Lang.lean:499-502`) under every option.  Options: **(i-a) as RULED** — thread
  the fragment: 16 cycle rules (9 files), 25 MachCSL files INCLUDING the 35 `wp_m_*` wrapper STATEMENTS, 12 `Xv6/`
  files (8 direct + `ProofEntry`/`ProofStart`/`ProofTimerinit` proofs + `SpecSpin` statement), one `Xv6`-cone rebuild —
  L–XL; **(i-b)** — a per-hart reservation INVARIANT opened by the boundary rule and the three `swp_*_au` rules:
  `ctxTokAt`/`uResvTok` redesign (M–L) but the cycle rules, `wp_m_*`, `wpLoop_k_*` and ALL of `Xv6/` untouched — L;
  **(ii)** `inflight` flag — the same ghost cost as (i-a) (R12).  Recommendation: the owner ruled (i-a) at a cost
  that omitted the M-mode lane; confirm (i-a) at the corrected census, or switch to (i-b), whose relative advantage
  grew.
