VERDICT: NOT SATISFIED

# Review R28 of `notes/weak-allocproc-plan.md` (rev 31)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan rev 31, 4,057 lines).  Scope per the R28 brief: rev 31's
record of W4 F9 DONE + M1 PROVED-NOT-CLOSED (verified against `Weak/SrvwmoXv6Adequacy.lean`), the new W5 CLOSE-OUT and
W-SCO items, W8 (f2-ctx) re-sized per R-ctx + [OWN.38]/[OWN.39], [OWN.40], the launch set (W5 CLOSE-OUT, W-SCO, W13 (I),
W5d) and Q-RSV-order — which the owner RULED (b) **[OWN.41]** while this review ran (coordinator notice;
`~/dev/weak-orch/allocproc_revise3_extra.txt`, last line): treated as RULED, with the one requirement that rev 32 records
it, and W-RSV's brief checked for launchability right after W8-β′ merges.  W8-β′ is RUNNING; nothing below touches its
brief (nothing unsound found in it).  Items (a)/(b) of the standing brief (what `Xv6.Allocproc` verifies; TsoMem =
sRVWMO) were settled in R1–R26 and are not re-opened; spot-checks that bear on this round's items are listed under
"What was checked".

**Sign-off.**  NO — five required changes, all S text, none a design change, none a memory-model question (every option
below is proof organisation: the published quantifier, the trusted base and the conclusions do not move — RVWMO, the Sail
model, Zifencei and the PMAs are silent on how a theorem is registered, how a premise is restricted, or in which order two
proof changes land).  Per item: **W13 (I) is LAUNCHABLE as written**; **W5 CLOSE-OUT is launchable once [R28.1] pins the
baseline entry** (as written its first `audit.sh --weak` run FAILS); **W-SCO is launchable once [R28.2] names where the
fetched word's identity comes from** (as written its central per-word lemma has no handle on the word); **W5d is
launchable once [R28.4] pins that `fok`'s arity does not change** (as written §B(4)(iii) and §C W5d contradict each other
and the registered M1); the launch set's "no shared file" claim is false in three files and needs the ordering of
[R28.3]; **W-RSV is launchable right after W8-β′ merges once [R28.5] records [OWN.41] and re-bases its deps/acceptance**.
Do not shrink anything.

## What was checked and holds

- **M1's theorem is exactly as the header says.**  `Weak/SrvwmoXv6Adequacy.lean` (318 lines): `srvwmoXv6M1Core :276-311`
  takes `hP : srvwmoXv6M1Premises σ0 c pst dv`, `g0` with `hg0 : g0.gen = 0`, `hp0 : g0.pow = false`, `hgd : σ0.wgdev =
  g0.m.devs.reset`, `hfs : diskOf g0.m.devs = Xv6.fsImgDisk`, and `hsco : sailCycleOrder` — nothing else ✓; `sailCycleOrder
  :113-124` is the label-list form (`lastCyc :104`, `lbCyc :96`) ✓; `fiArmLastCyc :135`, `fiOfSco :163`, `winOfText :187`,
  `bcRoHiLe :198` (`decide`), `m1Hyps :203-213` (`tso := pfStepTsoProposed _`, `safe` from `xv6FsAdequacy_closed`, `cut :=
  cutOfPristine … winOfText`, `fi := fiOfSco hsco _ σ0`), `bootStateOf :217-222` (builds `g0` from the premises' `ds` —
  the boot facts are never vacuous ✓), `allocprocAns :230`, `xv6Concl :252` ✓; imported at `Weak.lean:634` ✓; the import-
  hygiene fix `ExecSC4.lean:62-70` (imports `MachCSL.UTlb`) ✓ and the protocol rule `weak-port-protocol.md:91-92` ✓.
  `MachOfPf.Hyps :658-680` has exactly `tso`/`safe`/`cut`/`fi` (no `disk`) ✓; `SimRel :342`, `diskSide :331`, `simDisk
  :2603`, `machRunOfPfRun :2854` (no disk hypothesis) ✓; `MachOfPfDisk.devAgree :429`, `cacheWf` is
  **`MachOfPfDisk.lean:105`** (the header `:8` cites it as if in `MachOfPf.lean` — cosmetic, [R28.s6]).
- **"PROVED, NOT CLOSED" is accurate.**  `tools/ci/roots-weak.txt:8-17` lists the ten AxSpin roots only; `tools/audit/
  baseline-weak.json` has 10 entries, none `srvwmo`; `tools/ci/audit.sh:44` `XV6_AUDIT_MODULES` lacks it; the file header
  `:8-9` says "NOT registered as a root here" ✓.  `lint.sh:37-57` checks roots-weak ↔ baseline-weak name agreement ✓.
  `tools/tcb/expected.json` names no `Weak.*` root (grep = 0) — the tcb report does not cover the weak tier, so the
  CLOSE-OUT correctly names no `expected.json` edit ✓.
- **[OWN.40].**  `VirtioProg.outWraps :421` (`decide (2^64 < buf + len)`), used in `dcomplete :424-427` → `DRet DStall` ✓;
  §B(11) (x) `:1155-1163` states Spec first (PMAs; RVWMO/Sail have no DMA model) and marks (a′) FAITHFUL to the PMAs /
  STRONGER than MachCSL / pf ⊆ MachCSL ✓; `MachOfPf.lean`'s header deviation 3 cites [OWN.35] ✓ (`:63-66`);
  `PfStepTsoView.lean:63-66` deviation (4) still says "W4's to supply" — the CLOSE-OUT's item (5) ✓.
- **W8 (f2-ctx) re-size matches `notes/W8-Rctx.md`.**  F0's counterexample (`W8-Rctx.md:59-69`) and the per-author vector
  fix (`:71-80`) are what the plan records (`:27-31`, `:2903-2911`) ✓; the 31-row table totals 18/3/10/0 (`:119-125`) ✓;
  X1–X5 (`:29-38`) ✓; the 4 outside sites — `IputParts.lean:461` (`kctx_floor_of_view`) ✓, `ProofAcquiresleep.lean:809` ✓,
  `StartedInv.lean:198` (`ctxDeposit`) ✓, `:344` (`ctxAbsorbLb`) ✓; the `"log"` lock `ProofInitlog.lean:434` (`kctx_newlockAt
  … "log"`) ✓; `CtxBox.lean:1117-1121` (`boxRows`) ✓, 2,131 lines ✓; `Ctx.lean:179-180` `ctxFloor`, `:187-188` `keyAt`,
  `:298-299` `ctxTokAt` ✓; `Lock.lean:369` `lock_pay_take`, `:386` `lock_pay_intro` ✓; `WpLock.lean:1141-1143` (absorb at
  the AMO's `t`, `T ≤ t` derived) ✓; `KCtxMove.lean:295-303` ✓; `SchedCtx.lean:1199-1200` `procCtxAt` ✓;
  `WpPtWalkOwn.lean:501-515` `swp_update_and_write_pte_own` with `hadue` ✓.  The plan's "12 MachCSL = the 11 +
  `WpPtWalkOwn`" is the correct reading of R-ctx §6's conditional ("`WpPtWalkOwn` only if Q-R2 needs it", `:198-199`)
  under Q-R2 = (a) ✓.
- **[OWN.39]'s Spec line is right.**  The privileged spec's A/D update scheme: updates are ordered as the ASSOCIATED
  access is; A-bit updates may be performed speculatively (D-bit updates exact); the Sail model in this tree performs the
  update as `read_pte_exclusive`/`write_pte_conditional` inside an actual translation (`WpPtWalk.lean:3-7,156-165`,
  `WpPtWalkOwn.lean:501-515`) — never speculatively — so (a) is STRONGER than the model it is proved on and FAITHFUL to
  the spec, as the plan marks it (`:3238-3249`) ✓.  [OWN.38]'s Spec line (`:3227-3229`) ✓.
- **Q-RSV-order's text meets the 2026-10-10 format** (Spec FIRST, plain language, tiny example, definitions, why it
  matters, per-option change/faithful/cost/unblocks/risk, `:3191-3226`) ✓ — now RULED (b) [OWN.41].  Its "(c) NOT
  available" argument is consistent with §C W-RSV's ghost side (`:2345-2349`: `memModel_dropResv` needs the fragment) ✓.
- **W13 (I) brief** (`:2562-2579`): every name resolves at the tip — `gfexecConf` `WeakRvwmoFab.lean:620`, the interim
  clause `:633-634` ("DELETED BY W13 (I)"), `hemitfStatesQ :396`, `hartConffStatesQ :556`, `supplyOfFconf :789`, `hblkQ
  :332`, `hemitf`/`HFone` `:253-259`, `projLbl` `WeakPromiseBridge.lean:530` (the `.LDev .. => none` arm `:538`),
  `wpPfBridge :926`, `mstep` `WeakAxiomatic.lean:142`, `promiseFreeCompleteClean` `WeakAxiomatic3.lean:1445`, `pdevEv`
  `WeakEvInst.lean:604`, `pdiskProg :499` ✓.  The pre-W-DISK `:N` cites in the (I) paragraph (`:522-535`, `:533`,
  `:318-503`, `:689-701`) are superseded by §A's drift line `:658-665` as the plan says; the worker greps names.  No file
  overlap with W5d/W-SCO/the CLOSE-OUT.  **LAUNCHABLE as written** (one hygiene point, [R28.s5]).
- **Spot-checks bearing on (a)/(d).**  `wbootFacts` (`WeakLang.lean:482-490`) pins `g'.wgimg = bootImage` ✓;
  `candKfetch` (`PfRunShape.lean:53-55`) constrains ONLY the fetch footprint to `[lo, hi)` — not the bytes (this is what
  [R28.2] turns on); `bcRoLo = ramBase`, `bcRoHi = _data` (`BootCarve.lean:143-144`) ✓; the pf fetch reads `ifetchOk (imgZ
  σ.wgimg) σ.wglog (σ.wgitv c) base tvs` (`WeakEvInst.lean:631`) — image OR log bytes.
- **The audit's tree-wide check will pass with the new module (by grep, not by run).**  Importing
  `Weak.SrvwmoXv6Adequacy` puts 79 `Weak/` modules into the audited environment; `Audit.lean:356-381` then fails on any
  declared `axiom`, `native_decide` certificate or `sorryAx` in them.  Grep over the 79: `^axiom` 0, `native_decide` 0
  (one prose mention, `WeakDeps.lean:257` "banned"), `sorry` 0 (three prose mentions), `opaque` 0 ✓.

## REQUIRED changes

- **[R28.1] W5 CLOSE-OUT item (2) describes the `baseline-weak.json` entry in a way the audit REJECTS; pin the exact
  entry.**
  *What is wrong (evidence).*  `:2194-2197`: "gains its axiom set — `propext`/`Classical.choice`/`Quot.sound` + the
  `bv_decide` certificate axioms of `xv6FsAdequacy_closed`'s cone + the 4 of the NI/union/text roots … copied from
  `#print axioms Weak.srvwmoXv6M1Core`, NOTHING new allowed".  (1) The baseline's `axioms` field is "the EXACT set of
  axioms allowed OUTSIDE the `<decl>._native.bv_decide.ax_*` certificate family (which is counted, shape-checked, and
  not pinned by name)" (`tools/audit/baseline.json` comment; `Audit.lean:28-34,119-138`); the check `Audit.lean:305-313`
  computes `plain := axs.filter (!isBvCertName ·)` and reports every baseline axiom not in `plain` as "**is no longer
  used (stale baseline; remove it)**" — so an entry that lists the certificate names, as (2) instructs, FAILS the audit.
  (2) `#print axioms` cannot see `opaque`s (`Audit.lean:41-53`), yet the entry needs an exact `opaques` list
  (`Audit.lean:316-321`): `xv6FsAdequacy_closed`'s is `["LeanRV64D.Functions.xv6_resv_is_valid",
  "LeanRV64D.Functions.xv6_resv_matches", "MachCSL.bootImageSealed"]` (`baseline.json`), and **`MachCSL.bootImageSealed`
  appears in NO current `baseline-weak.json` entry** (all ten list the two `resv` opaques only) — so "NOTHING new
  allowed" is literally violated by the only correct entry and a careful worker stalls or files a false deviation.
  (3) `platform_hooks` — identical in both baselines (`realised` 6, `parameters` 2) — needs no change; say so.
  *Exact change (`:2194-2197`).*  Replace item (2) by: "`tools/audit/baseline-weak.json` gains the entry `{ "name":
  "Weak.srvwmoXv6M1Core", "axioms": ["propext", "Classical.choice", "Quot.sound"], "opaques":
  ["LeanRV64D.Functions.xv6_resv_is_valid", "LeanRV64D.Functions.xv6_resv_matches", "MachCSL.bootImageSealed"] }` — i.e.
  EXACTLY `Xv6.xv6FsAdequacy_closed`'s `baseline.json` entry under the new name; the `bv_decide` certificates are NOT
  listed (the audit counts and shape-checks the family and rejects a listed certificate as a stale axiom,
  `Audit.lean:305-313`); `bootImageSealed` is new to THIS file but not to the trusted base (`baseline.json`, §0 F1);
  `platform_hooks` unchanged.  Acceptance adds: `audit.json`'s `bv_decide_certificates` count for the new root is
  reported in the status line (the 4 NI/union/text certificates + the SC cone's)."  Also list the four COMMENT sites the
  worker updates with (3): `audit.sh:13-18` (header), `:51` (the `--build` module list — add the module or it is never
  built on a fresh `--weak --build`), `roots-weak.txt:1-7`, `baseline-weak.json`'s `comment`, `Audit.lean:85-95`.
  S text; FAITHFUL (registration only).

- **[R28.2] W-SCO's per-word lemma has no handle on WHICH word was fetched: `Hyps.fi`'s shape gives the pf run only, and
  on the pf side `candKfetch` does not say the bytes are the image's.  Name the mechanism (the `cutOfPristine` route via a
  widened `Hyps.fi`) and the files it touches.**
  *What is wrong (evidence).*  `:2215-2219`: `sailCycleOrderK` is `sailCycleOrder`'s body "RESTRICTED to runs `pfRunST
  pstepEv pclsEv (candKfetch bcRoLo bcRoHi) cohSrc (wpInit (imgZ σ0.wgimg) …)` with `wbootFacts σ0`", proved by "the
  per-word lemma over EVERY 2-aligned 4-byte word of `[bcRoLo, bcRoHi)`" — i.e. per IMAGE word.  But (1) `candKfetch lo hi
  _img _log _i base tvs := ∀ j < |tvs|, lo ≤ base + j < hi` (`PfRunShape.lean:53-55`) constrains the ADDRESSES only; the
  pf fetch's bytes are `ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs` (`WeakEvInst.lean:631`; `ifetchOk`
  `WeakPromise.lean:225`) — image bytes at `t = 0` OR log bytes of any pf store into the window; "no pf store ever hits
  `[bcRoLo, bcRoHi)`" is exactly the SC tree's `textPristine`, which reaches the pf side only through `SimRel`
  (`MachOfPf.cutOfPristine :2903-2979`: `winPristine` + `hR.mem.2.2.1.1` + `histNoWrite` ⇒ every fetched byte has `t = 0`,
  `:2925-2950`).  (2) `Hyps.fi` (`MachOfPf.lean:672-680`) quantifies `pfRunST … c0 st c` and the node ONLY — unlike
  `Hyps.cut` (`:664-671`), it takes NO `MRun`/`SimRel` premise — so `m1HypsK`'s `fi` field (`:2219`: "exactly the restricted
  form") cannot be discharged by a lemma about image words: the word announced at the node is unconstrained by anything
  the field receives.  (3) The per-word restriction is load-bearing for (a′): the barrier clause needs "`execute (decode
  w)` emits no fetch before its `Barrier_RISCV_i`" for the ACTUAL `w`, and generically over all `w` that is option (a)
  (L–XL, §B(11)), which the plan does not take.  So as briefed the worker reaches the per-word lemma and finds no way to
  connect it to `m1HypsK` — a false start of days in an M–L item.  The fix is small and already modelled by `cut`: at the
  one application site of `fi` (`MachOfPf.lean:1035`) both `hreach : MRun n ([power], g0) κ (t, g)` and `hR0 : SimRel c st
  t g` are in hand (`:1043` passes them to `cut`).
  *Exact change (`:2213-2232`; and `:1324-1328`).*  Add to W-SCO's **Shape**: "(0) **`MachOfPf.Hyps.fi` is WIDENED to the
  `cut` shape** — it gains `∀ t g n κ, MRun n ([Expr.power], g0) κ (t, g) → SimRel c st t g →` before the node quantifier
  (`MachOfPf.lean:672-680`; the single application `:1035` passes `hreach hR0`); `m1Hyps.fi` (`SrvwmoXv6Adequacy.lean:213`)
  becomes `fun st c _ _ _ _ hrun _ _ => fiOfSco hsco _ σ0 st c hrun` — the ONLY edit to that file (replace "UNTOUCHED" by
  "one-line adaptation; statement of `srvwmoXv6M1Core` unchanged").  (i′) `sailCycleOrderK` is stated WITH those premises
  (`g0` as in `m1Hyps`, `winPristine bcRoLo bcRoHi g` from `winOfText`), and the per-word lemma is connected through
  **`cutOfPristine`'s argument** (`:2925-2950`): `SimRel.mem`'s history link + `winPristine` ⇒ every byte of the fetch has
  `t = 0`, hence the announced word is `imgZ σ0.wgimg`'s word at `base` = (by `wbootFacts`, `WeakLang.lean:483`
  `wgimg = bootImage`) the image word — factor that step out of `cutOfPristine` as a lemma `fetchIsImage` (S) both use.
  Files: `Weak/SailCycleOrderK.lean` NEW + `Weak/MachOfPf.lean` (the field, `:1035`, the factored lemma) +
  `Weak/SrvwmoXv6Adequacy.lean:213` (one line).  Land the `Hyps.fi` widening as W-SCO's FIRST commit (it is independent of
  the per-word work) so W5d's `m2Hyps` — which also instantiates `Hyps` — builds on the new shape from the start; W5d's
  `fi` discharge from the general `sailCycleOrder` ignores the extra premises."  Keep the recorded risk line.  S text on an
  M–L item; FAITHFUL (proof organisation; `sailCycleOrder` itself and §A's statement unchanged).

- **[R28.3] The launch set's "four lanes, one worker each, no shared file" is false in three files; sequence the
  overlaps.**
  *What is wrong (evidence).*  `:1327-1328` "no shared file (W-SCO and W5d both consume `SrvwmoXv6Adequacy.lean` and edit it
  NOWHERE …)".  But (1) the W5 CLOSE-OUT edits `tools/ci/roots-weak.txt`, `tools/audit/baseline-weak.json`,
  `tools/ci/audit.sh:44` (`:2191-2198`) and W-SCO edits the SAME three ("registered in `roots-weak.txt`/`baseline-weak.json`
  beside the core", `:2221-2223`; the module list must gain `Weak.SailCycleOrderK` too); (2) BOTH edit
  `Weak/PfStepTsoView.lean`'s header deviation (4) (`:63-66`) — the CLOSE-OUT to "the named premise `sailCycleOrder`
  [OWN.35] … derived for the shadow by `fiOfSco`" (`:2205-2207`), W-SCO to "proved for kernel text" ("Corrects
  `PfStepTsoView.lean`'s header deviation (4)", `:2231-2232`) — the same sentence, two wordings; (3) with [R28.2], W-SCO
  edits `MachOfPf.lean`'s `Hyps`, which W5d's new file instantiates.  None of this is a logic conflict; all of it is a
  merge conflict the plan says cannot happen.
  *Exact change (`:1323-1328`, `:2208-2210`, `:2221-2223`, `:2231-2232`).*  Replace "no shared file" by: "shared files, in
  LANDING ORDER: the W5 CLOSE-OUT lands FIRST (S, hours) and its deviation-(4) wording already anticipates W-SCO ('the named
  premise `sailCycleOrder` [OWN.35]; `sailCycleOrderK_holds` (W-SCO) proves it for kernel text') so W-SCO does NOT touch
  that header; W-SCO's registration (`roots-weak.txt`/`baseline-weak.json`/`audit.sh:44,51`, entry = the core's with the
  per-word lemma's certificates counted) is its CLOSE step, rebased on the merged CLOSE-OUT; W-SCO's `Hyps.fi` widening
  [R28.2] is its first commit, and W5d rebases its `m2Hyps` on it (S) if it has not merged by then."  S text; FAITHFUL.

- **[R28.4] W5d's brief contradicts §B(4)(iii) and the registered M1 on `fok`'s ARITY; pin that `fok`'s type does not
  change, and fix the `rowFetchM2` cite.**
  *What is wrong (evidence).*  §B(4)(iii) `:731-732`: "`fok` takes it [`itvOf k i`] as a 6th argument: the M2 cut form is
  `∃ q, itvOf k i ≤ q ≤ |log| ∧ ifetchOk … ∧ ∀ byte, t ≤ q`", and `:733` "M1's `candKfetch` is unaffected".  Both cannot
  hold: `fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop` is the ONE parameter threaded through
  `execProgOk'S` (`PfRunShape.lean:242`), `execProgOk'ST` (`TsoShadow.lean:555-560`), `pfStepFacts` (`PfRunShape.lean:
  265-269`: `.LIFetch base tvs => fok c.pcImg c.pcLog i base tvs`), `pfStepFactsT`/`pfRunST` (`TsoShadow.lean:576-590`),
  `MachOfPf.Hyps :658`, `sailCycleOrder :114`, `srvwmoXv6M1Premises` (`SrvwmoXv6Witness.lean:599-607`, where `candKfetch` IS
  the `fok`) and `srvwmoXv6M1Core :284`.  A 6th argument changes `candKfetch`'s type and with it M1's REGISTERED statement
  and W-SCO's `sailCycleOrderK` — the opposite of §C W5d's "`SrvwmoXv6Adequacy.lean` untouched" (`:2459-2460`) and of the
  CLOSE-OUT's "no statement changed".  The brief leaves the worker to pick.  Separately, `:2461` cites "`rowFetchM2 :777`"
  as if in `MachOfPf.lean`; it is **`Weak/PfStepTsoView.lean:778`** (table row `:41`) — W2b's view row, consumed by W4
  through `Hyps.cut`, as the sentence says.
  *Exact change (`:2450-2461`; `:731-733`).*  Add to W5d: "**`fok`'s type is UNCHANGED** (5 arguments; `candKfetch`,
  `pfRunST`, `Hyps`, `sailCycleOrder`, M1 text-identical).  The cut form's lower bound `itvOf k i ≤ q` enters through the
  SHADOW-THREADED layer, which has the step list in hand: a new clause beside `pfLoadFactsT` in `pfStepFactsT`
  (`TsoShadow.lean:568-578`) for `.LIFetch`, stating `(tsoShadow cohSrc st i).itv ≤ q` for the `q` of `fok`'s cut form,
  and at the Exec level `itvOf` is a conjunct of the per-index clause of `execProgOk'S` where `ls` is in scope
  (`PfRunShape.lean:232-234`), NOT a `fok` argument; `fok_cut img log i base tvs := ∃ q ≤ |log|, ifetchOk img log q base
  tvs ∧ ∀ byte, t ≤ q` is then an ordinary 5-argument clause and `Hyps.cut` at `fok_cut` is discharged from
  `pfStepFactsT`'s two conjuncts (no MachCSL side needed — the M2 twin of `cutOfPristine`)."  Rewrite `:731-732`
  accordingly ("`fok` takes it as a 6th argument" → "the ST layer supplies it beside `fok`").  Cite fix `:2461`.  S text
  on an L item; FAITHFUL (the M2 clause's content is unchanged; only where it is attached).

- **[R28.5] Record [OWN.41] (Q-RSV-order = (b)) everywhere the lane order is stated, and make W-RSV's brief launchable
  right after W8-β′ merges: its deps, its rebase surface and its acceptance are still written for "after W8 (f2-ctx), M1
  unregistered, pre-F9".**
  *What is wrong (evidence).*  (1) Order text to update: header `:45-48`, §C top `:1328-1331` ("W-RSV for W8 (f2-ctx)
  under D26/[OWN.37]'s order"), `:2233-2235` ("W8-β′ → W8 (f2-ctx) → … → W-RSV"), `:2257-2261`, W8 (f2-ctx)'s deps
  `:3049-3050` ("W8 (f2-ctx) — W8-β′ only"), W-RSV's `:2442-2446`, `:3106-3109`, §D `:3191-3192` (OPEN → RULED (b)
  [OWN.41]), D26 `:4016-4018`.  (2) W-RSV's deps (`:2442-2446`) name "W8 (f2-ctx) by file overlap"; under (b) the item it
  rebases on is **W8-β′**, whose landed edits overlap W-RSV's census in ≈ 8 MachCSL files: `Resources.lean` (β′'s
  `⌜staticIn reg ∧ reservedOk σ reg⌝` conjunct and `rsvName` ghost in `memModelAt :951-956` sit beside W-RSV's `resvMap`
  conjunct `:949`; the era tuple is 15 fields), `Wp.lean`/`WpAtomic.lean`/`WpDma.lean` (β′'s primitive-store `a ∉ reg`
  argument [R27.s1] at the same sites W-RSV re-proves against "reservations are in-flight", `:2412-2426`), `Power.lean`/
  `PowerText.lean` (`resvMap` 3+3 and β′'s mint), `KCtx.lean` (`ctxToken` / `cpuCells` halves), `WpLock.lean` (fraction-
  parametric rules; W-RSV's `WpLock` overlap `:2254`).  (3) Acceptance: M1 will be a REGISTERED root by then (W5
  CLOSE-OUT), and W-RSV changes `MState`'s `.pure` arm (`Lang.lean:535`), so the `Weak/` bridge must be re-proved INSIDE
  W-RSV, not "re-checked after it (S)" (`:2445-2446`, pre-F9 text: "three rows"): the reservation guards now appear in
  `MachOfPf.lean` at 13 sites — `notOthers :746`, the `hno` premises `:757,790`, and **F9's four disk-row `hres : ¬
  anyReserve σ.resv pa n` sites `:1513,1590,1741,1848`** (`simDisk`'s `storeDma` rows, written AFTER the W-RSV brief) —
  plus `PfStepTsoMem.lean` 15, `PfStepTsoView.lean` 6, `PfStepTso.lean` 2 (grep); `pairAdjacent` still supplies them (no
  in-flight reservation straddles a step, `:2427-2429`), so the re-proof is S–M, but it is W-RSV's, and its merge gate is
  `lake build Xv6 MachCSL Weak Vtest` + `audit.sh --weak` with the M1 root GREEN.
  *Exact change.*  At every site in (1): "lane W-COH ✓ → W-DMA0 ✓ → W8-β′ (RUNNING) → **W-RSV** → W8 (f2-ctx) [OWN.41];
  W8 (f2-ctx) waits for W-RSV and rebases on its `resvFragAny` thread (`ctxTok`, `Ctx.lean:298-299`)"; §D Q-RSV-order
  header → "RULED (b) [OWN.41] (11:09 2026-10-12)".  In §C W-RSV add a **Launch (rev 32)** paragraph: "Deps: W8-β′ MERGED
  (rebase surface: the ≈ 8 files above, named), M1 ✓ (D26); W4/W2 re-proof INSIDE this item: the 13 `MachOfPf.lean`
  sites incl. F9's four `hres`, `PfStepTsoMem`/`PfStepTsoView`/`PfStepTso`'s rows, `srvwmoXv6M1Core` (and W-SCO's
  corollary if landed) rebuilt; acceptance `lake build Xv6 MachCSL Weak Vtest`, `audit.sh --weak` green with the
  registered root(s), `tools/ci/vtest.sh check` (the `Vtest` `hartStep` twin, `vtest-lean/Vtest/HartExec.lean`), the
  `TsoMem.lean:27-31` header and §0 F1 (ii) as already written."  S text; FAITHFUL (lane order; W-RSV's semantics
  unchanged, D19 (b)/(i-a) as ruled).

## SUGGESTIONS

- **[R28.s1] (tell the W5 CLOSE-OUT worker) Report the certificate count.**  `audit.json` prints `bv_decide_certificates`
  per theorem (`Audit.lean:393`); the status line "axioms = the SC roots' + 4 certificates" should quote that number for
  `Weak.srvwmoXv6M1Core` (the SC cone's own certificates are in it too, so it is not literally 4).
- **[R28.s2] (W-SCO) Record why the per-word lemma is word-INDEPENDENT except at the barrier clause.**  The sfence.vma
  clause ("latest own cycle label is `LIFetch` at the announce") holds for ANY word (fetch → announce with nothing between,
  `UCycleDefs.lean:11-17`); only the barrier clause needs the decoded instruction.  Saying so lets the worker split the
  SailM residual invariant (the recorded risk) into a generic half and the per-word half, and tells W5d-G/M2 exactly what
  the general `sailCycleOrder` still covers for user text.
- **[R28.s3] (W-SCO) Size the window.**  `[ramBase, _data)` holds `.text`, `.rodata` and `.eh_frame`; the per-word lemma
  is over every 2-aligned 4-byte word, ≈ (`_data − 0x80000000`)/2 instances; the precedent (`AxSpinTextCerts.lean`,
  245 lines) closes 92 conjuncts by `decide +kernel` over the literal image — the whole window is two orders of magnitude
  more and will need a GENERATED table or a per-instruction-CLASS lemma over `decode` (one lemma per opcode family that
  can appear, with the table only proving class membership).  M–L stands; the brief should name which.
- **[R28.s4] Q-RSV-order's "three files" undercounts the W-RSV ∩ W8 (f2-ctx) overlap** (`:3198-3199`, `:3214`): add `Ctx.lean`
  (`ctxTokAt`), `KCtx.lean`, `WpDma.lean`, `WpPtWalkOwn.lean` (W-RSV `:2417`; (f2-ctx) `:2248`) and the load rules — ≈ 7.
  The decision is unaffected (the rework is symmetric); the record should be right.
- **[R28.s5] (W13 (I)) Single-writer hygiene with W5d-G.**  `:2570-2571` has (I) doing "`emFetchImg` → `emZifencei`";
  `emZifencei` is W5d-G G1's deliverable (D26 sequences G1–G5 AFTER (I) "to keep those files single-writer", `:4017-4018`).
  Say whether (I) only renames the slot (G1 fills its content) or leaves `emFetchImg` for G1 to replace.
- **[R28.s6] Cosmetic cites.**  Header `:8` "`cacheWf :105`" is `MachOfPfDisk.lean:105` (not `MachOfPf.lean`);
  `promiseFreeCompleteClean` is `WeakAxiomatic3.lean:1445` (plan `:2578` says 1434); `hemitf`/`HFone` `WeakRvwmoFab.lean:
  253-259` (plan `:2566` says 239-250); W8-Rctx is the plan's name, the note's own header `:5-6` says it was briefed as
  `notes/R-ctx.md` — record the rename once.
- **[R28.s7] Q-R1's §D entry lacks the format's tiny example.**  `:3230-3233` describes F0 in prose; the three-hart
  example (`W8-Rctx.md:61-69`: C stores `y` at 5, A stores `x` at 10 and releases L, B acquires — B's bound ≥ 10 covers C's
  unsynchronised 5) is one sentence and makes the RULED entry self-contained for a reader of §D alone.
- **[R28.s8] `notes/W8-design.md` §4/§5/§8 still state the superseded design** ([R27.s5], not yet applied); the (f2-ctx)
  worker will read it first.  One "superseded by rev 30/31" line per section, or in the (f2-ctx) brief's first paragraph.

## Owner questions the plan is missing

None.  Every required change above is proof organisation or registration (which JSON fields the audit reads, where a
premise's restriction gets the fetched word from, in which order four workers edit three shared files, the arity of an
internal parameter, the recording of a ruling already made): RVWMO, riscv.cat, the Sail model in this tree, Zifencei and
the PMAs are silent on all of them, and every option is FAITHFUL — the published quantifier, the trusted base
(`sailCycleOrder` stays the one named ISA-model premise until W-SCO demotes it for kernel text; `gzFetch`/`ioResidueGmo`
unchanged) and the conclusions do not move.  The plan's existing questions keep their "*Spec (FIRST).*" lines and the
2026-10-10 format (Q-RSV-order `:3191-3226`, Q-R1 `:3227-3237` modulo [R28.s7], Q-R2 `:3238-3249`, W4-F9-wrap `:3250-3258`).
