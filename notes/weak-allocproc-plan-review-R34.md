VERDICT: NOT SATISFIED

# Review R34 of `notes/weak-allocproc-plan.md` (rev 37)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite below was
read at the working-copy tip of `../xv6iris-weak` (plan rev 37, 4,880 lines), `notes/W8-Rctx.md`, `notes/W8-design.md`, and
`../weak-orch/allocproc_WSCO_A_prompt.txt`.  Scope per the R34 brief (narrow): rev 37's records of R33 / [OWN.45] / W13 (I) /
W8-β′ / W-RSV, and whether **W8 (f2-ctx) is launchable as written** against the tip.  W-SCO (A) is running; its brief was read
for verification only and is not changed.  Items (a)/(b)/(d) of the standing brief were settled in R1–R33 and are not re-opened.

**Sign-off.**  NO — THREE required changes, all S text in the §C-top W8 (f2-ctx) launch paragraph (`:1716-1751`), no design or
memory-model change, no owner ruling needed.  Everything rev 37 RECORDS checks out in the tip (below).  The launch paragraph is
right about deps, the rebase surface with W-RSV, the chain-vector deliverables (1)–(4), acceptance and size; it is NOT yet
launchable because (i) deliverable (5) silently drops two of the six conjuncts of the export it claims to complete
(`cpuProcDiscAt`, `utextDiscAt`), unsized and unfed — [R34.1]; (ii) it declares `notes/W8-Rctx.md` §1–§6 BINDING while §4/§6/§7 of
that note still state the user-table verdict the owner REJECTED as unfaithful in [OWN.39] — [R34.2]; (iii) its Files list omits the
ghost-state plumbing the per-author vector necessarily touches (`CtxId`, the functor list, the `MachFixedGS` literals incl. one
`Weak/` file) — [R34.3].  Each is a paragraph edit; W8 (f2-ctx) is launchable the moment the three are in its brief (addendum form
is fine, as [R32.1]/[R33.1] were for W-SCO (A)).

## What was checked and holds

- **R33 applied in the running W-SCO (A) brief.**  `../weak-orch/allocproc_WSCO_A_prompt.txt` (5 lines) names rev 36 §C W-SCO (A),
  [OWN.42], [OWN.45], and an ADDENDUM "[R33.1] `Rboot` must ALSO pin `htif_tohost_base = none` … two places" + [R33.s2] ✓.  The
  plan's §C-top brief carries [R33.1] tagged at `:1578-1579` (`regWrite` arm `r ≠ pma_regions ∧ r ≠ htif_tohost_base`), `:1582`
  (`Rboot` by `match` [R33.s3]), `:1585-1588` (the invariant conjunct, base lemma `bootFin_bootProg`/`resetRegsRun_of_run` [R33.s2]),
  `:1599-1609` ("TWO places … precise about a VALUE"), `:1609-1611` ((iv) text), `:1655-1657` (the third-register risk) ✓; [R33.s4]'s
  cites (`tick_clock` `model/…/Platform.lean:549`, `sail_model_init`, `nodeStep :273`, `good`'s arms) and [R33.s5]'s `barrier_kind_of_num`
  note (`:1620`) present ✓.
- **[OWN.45] recorded.**  §D header `:3911-3912` ("RULED 16:56 … Q-SCO-PMA = (α) [OWN.45] … HTIF window disabled [R33.1]; OPEN: NONE"),
  the item `:3913-3915` with the [R33.1] (iv) wording ("memory map AND HTIF window (`pma_regions`, `htif_tohost_base`, both pinned by
  `bootPost`, `BootInitModel.lean:39,41`)") ✓; the *Spec (FIRST)* paragraph names RVWMO/riscv.cat/Zifencei silent, the PMAs' executability
  attribute, Sail's `pmaCheck`, and the HTIF window as a model (not ISA) notion, marked FAITHFUL ✓ — meets the 2026-10-09 rule; the plain
  language / example / definitions / per-option blocks are rev 36's, unchanged (R33 found them compliant) ✓.  Mirrors at `:582`, `:1402`,
  `:2794`, `:4218`, `:4263` say "RULED [OWN.45]" ✓.
- **W13 (I) bundle half DONE — in the tip.**  `Weak/WeakRvwmoFab.lean:844 def gfexecConfIO` (header `:99-100`: "`gfexecConf` is
  DELETED"), `hemitf :358`/`hartConff :385` take `tq : Nat → Bool`, `hemitfStatesQ :537`, `gfexecConfOfQconf :973`;
  `GraphFabResidue.gfIoDevOfConf :187` (`gfIoDev :176` the graph-visible half); `WeakRvwmoFabInd.gfexecConfRen :334`/`gfexecConfHull
  :377`/`cycleKillOfF :668` (the plan says `:669` — [R34.s1]); the interim `.PDisk` clause survives only as header prose
  (`WeakRvwmoFab.lean:93` "DELETED BY W13 (I)"); `epsInitQuiet` only in `WeakRvwmoCapstone.lean:61`'s "is DELETED"; the spike's def is
  `GraphFetchSpike.emZifencei` (`GraphFetchSpike.lean:85-86`) ✓.
- **W8-β′ DONE — in the tip.**  `Xv6/AccessDiscipline.lean` 197 lines: `inductive Cust :53`, `custAt :89` (ignores `σ`/`t`),
  `xv6LockWord :98`, `lockWordDiscAt :104`, `cpuStaticAt :109`, `xv6AccessDisc :115 := lockWordDiscAt σ ∧ cpuStaticAt σ`,
  `xv6LockWord_registered :153`, `powerInterp_accessDiscβ :186` (takes `MachFixedGS.rsvStatic … = KernelRsv.static`) ✓;
  `SystemAdequacyDisc.lean:35 xv6DiscAdequacy`, `LinkDiscAdequacy.lean:26 xv6DiscAdequacy_closed` ✓; registered `tools/ci/roots.txt:20`,
  `tools/audit/baseline.json:67`, `tools/tcb/expected.json:2323` ✓; `MachCSL/Reserved.lean`, `RsvMint.lean`, `Xv6/KernelRsv.lean`,
  `WpLockInit.lean` (315) exist; `rsvModelAt` (`Resources.lean:1009`) sits in `memModelAt :1022` beside `⌜mmOk σ⌝` ✓; `WpLock.lean:1141`
  is β′'s `by_cases hm : lkRsvIn` split (so β′ shifted the absorb sites — [R34.s1]) ✓.
- **W-RSV DONE — in the tip.**  `MachCSL/Lang.lean:543` `| .pure _ => ∃ tick, m' = riscvStep tick ∧ σ' = σ.dropResv cpu`; `dropResv :144`
  ✓; `Wp.lean`: `hartViews_dropResv :1235`, `memModel_dropResv :1240`, `wpLoop_restartB :2005`/`_restart :2033`/`_restartC :2050`/
  `resvOut :2068`/`_restartO :2108` ✓; `WpSmodeCycleBase.lean:61 wpLoop_restartT` ✓; `Ctx.lean`: `ctxTokAt :299-300 := ownCtxAt … ∗ ∃ r,
  resvFragAnyAt E cpu r`, `resvFragAny :317`, `ctxTok :320`, `ctxTok_cases :406-407` ✓; `Xv6/SpecSpin.lean:17,40` carry `∃ r, resvFragAny
  cpu r` ✓; `TsoMem.lean:33-35` "within the issuing instruction … cleared at the hart's instruction boundary, W-RSV" ✓;
  `Weak/MachOfPf.lean`: 7 `othersReserve`/`anyReserve` lines, 18 `pairAdjacent` ✓; `WeakLang.lean:52` ✓; `vtest-lean/Vtest/XState.lean:262
  dropResv`, `HartExec.lean:454` the `.pure` arm ✓ (the plan writes `Vtest`, `:29`/`:1706` — [R34.s4]).  Census: the tip has 37 `theorem wp_m_*`, all
  `[CurCtx]` (`WpMmode*.lean`, `WpStore.lean`), the plan says "34 gain" (`:27`) — [R34.s2].
- **W8 (f2-ctx) launch paragraph — the parts that hold.**  Deps: W8-β′ and W-RSV merged (above), R-ctx's (f1) list empty
  (`W8-Rctx.md` §6), M1 registered ✓.  Deliverable cites: `ctxFloor` `Ctx.lean:179`, `keyAt :187`, `ctxAt :191`; `CtxLaws.lean`
  `ctx_absorb :480`/`ctx_stamp :520`/`ctx_unstamp :552`/`ctxStamped_raise :577`/`ctx_park :760`/`ctx_resume :788`/`ctx_move :848`;
  `kctx_floor_of_view` `KCtxMove.lean:303`; `CtxBox.lean` 2,131 lines, `boxRows :1117-1121`; `lockHook_llb` `Lock.lean:597`,
  `lock_pay_take :541`, `lock_pay_born :660`, `isLock :861`, `newlock_written :1002`, `lkFresh :1115`, `Lock.lean` 1,239, `WpLock.lean`
  3,531; `ACQUIRE_LLB` `SpecAcquire.lean:123`, `ACQUIRESLEEP_LLB` `SpecAcquiresleep.lean:170`; `wp_s_sd_mint :40`/`wp_s_sw_mint :127`
  (`WpSmodeMint.lean`); `KCtx.cpuCell :545` ✓ — all exact.  The 12 MachCSL files exist; all 21 + 31 `Xv6/` files of `W8-Rctx.md` §2/§5
  exist; the §2 table's `Xv6/` cites are still exact at the tip except `PipeBirth.lean:303 → :307` (the MachCSL-internal ones shifted,
  [R34.s1]).  The `Weak/` files that name contexts (`WeakCtx`, `WeakGhost`, `WeakCtxPt`, `WeakLeafO*`, `WeakCtxLock`, …) are the Weak
  port's OWN context layer (`Weak.ctxAuth`; they import only `MachCSL.MonPredExtra`), not `MachCSL.ctxAt` — (f2-ctx) does not touch
  them ✓.  "NO shared file with W-SCO (A)" is TRUE (w4 edits `Weak/SailCycleOrder*`, `MachOfPf`, `SrvwmoXv6Adequacy`, `PfRunUnpinned`
  only) ✓, with the qualification in [R34.3].  The paragraph's [R28.s8] first line (W8-design §4/§5/§8 superseded) ✓; its (4)/(5)
  say PTE-KEY for both tables [OWN.39] ✓ (which is why [R34.2] is a carve-out, not a redesign).
- **Launch authority.**  [OWN.37] (route (a)), [OWN.38]/[OWN.39] (shape), [OWN.41] (`:3959-3990`: "the serial lane is W8-β′ → W-RSV
  → W8 (f2-ctx) … (f2-ctx) rebases on W-RSV") — the owner has ruled the item, its shape and its slot; no further batch approval is
  implied by the plan's own rule (it asks one only of W5d-G, `:1755`, which [OWN.44] did not cover).  Say so explicitly — [R34.s3].

## REQUIRED changes

- **[R34.1] Deliverable (5) of the W8 (f2-ctx) launch paragraph drops two of the six conjuncts of the export it claims to
  complete; they are neither sized nor fed anywhere in the brief.**
  *What is wrong (evidence).*  §C W8's skeleton (`:3505-3511`) is `xv6AccessDisc := chainOkAt σ ∧ lockWordDiscAt σ ∧ pteDiscAt σ ∧
  cpuStaticAt σ ∧ cpuProcDiscAt σ ∧ utextDiscAt σ`; the tip's header says the same — `Xv6/AccessDiscipline.lean:4-7`: "W8 (f2-ctx) only
  STRENGTHENS it (adds `chainOkAt`, `pteDiscAt`, `cpuProcDiscAt`, `utextDiscAt`, the pipe locks, the rest of the custody map)"; W8-design
  §4 (`W8-design.md:432`) puts `cpuProcDiscAt` and `utextDiscAt` in "W8 proper … fed by (f2-ctx) or (f1)"; §C W8's acceptance
  (`:3710-3716`) says "(f2-ctx) — the FULL `xv6AccessDisc`"; and §C W8 names `utextDiscAt`'s consumer (W5d-G G7, `:3699`) and `cpuProcDiscAt`'s
  role (`kOwnerAt` single-valued, `:3460`).  The launch paragraph's (5) (`:1732-1736`) lists ONLY "σ-readable `custAt`/`xv6LockWord` …,
  `chainOkAt` with the `.pte` exemption for BOTH tables, `pteDiscAt`" and says the root exports "the SAME root … statement strengthened";
  its *Size* (≈ 6.5–9.5k) is R-ctx §6's, which sizes the chain vector + X1–X5 only; neither `cpuProcDiscAt` nor `utextDiscAt` has a feed
  named anywhere in the brief (`cpuProcDiscAt` needs the three `wp_s_sd_proc` sites to carry "holds `p_j->lock`" into the state
  interpretation — a lock-holder fact β′'s cpu-cell rule does not take; `utextDiscAt` needs custody of USER pages, which §C W8's own
  *Unverified points* list as unsettled "`custAt`'s σ-derivability for pipe locks and user pages", `:3723`, plus the `userret` `fence.i`
  image fact, `:241`).  A worker reading (5) + "FULL" + the header must guess; the likely outcomes are a silently narrowed root or an unsized
  bulge in a 3–4-rebuild item.  Not a memory-model question (the export's conjuncts are facts about xv6's code; every option FAITHFUL).
  *Exact change (S, text).*  In (5) enumerate the six conjuncts and decide, in the brief, for each of `cpuProcDiscAt` and `utextDiscAt`:
  EITHER "(5a) IN SCOPE: `cpuProcDiscAt` fed at the three `wp_s_sd_proc` sites (`myproc+0x1e`, `sched+0x2a`, `sched+0x54`, §C W8 (3)) by
  the holder fold of `p_j->lock` — S–M, ≈ +0.2–0.4k, no new rebuild (lands with X1/X3/X4); `utextDiscAt` fed by … (name the user-page custody
  mechanism and the `userret` `fence.i` image fact) — size it" OR "(5b) DEFERRED: the root lands at `chainOkAt ∧ lockWordDiscAt ∧ pteDiscAt ∧
  cpuStaticAt` (four of six); `cpuProcDiscAt` and `utextDiscAt` are a NAMED follow-up item **W8-γ** (serial MachCSL if it edits a rule;
  `Xv6/`-only if the cpu-cell rule already suffices — say which), gating W5d-G G7 (`utextDiscAt`) and W11 (ii)'s `kOwnerAt` uniqueness
  (`cpuProcDiscAt`); the file header and `roots.txt:20`'s comment say 'four of six' so the root's comment never over-claims".  My
  recommendation: (5b) — (f2-ctx) is already the lane's largest item, nothing consumes the two conjuncts before W13 (XL), and
  `utextDiscAt`'s feed is unsettled.  Either way: update §C W8's acceptance sentence ("the FULL `xv6AccessDisc`") and
  `AccessDiscipline.lean:4-7`'s header (the worker's edit) to match the choice.
- **[R34.2] The brief makes `notes/W8-Rctx.md` §1–§6 BINDING but carves out only its lane order; §4, §6 and §7 of that note still
  state the user-table verdict the owner REJECTED as UNFAITHFUL in [OWN.39].**
  *What is wrong (evidence).*  `:1717-1719`: "brief = §C W8 (4)/(6)/Acceptance + `notes/W8-Rctx.md` §1–§6 (BINDING over `notes/W8-design.md`
  §4/§5/§8 …; its 'serial before W-RSV' is superseded by [OWN.41])".  `W8-Rctx.md` §0 item 5 and §4 say "User table: CHAINED as owned
  stores, modulo one spec question (Q-R2)"; §6's file-count line says "`WpPtWalkOwn` only if Q-R2 needs it"; §7 Q-R2 offers "if it is
  ordered … the user arm is CHAINED (FAITHFUL)".  §D Q-R2 (`:4011-4023`) RULED (a) [OWN.39]: user PTE bytes go under the `pte-key` arm;
  option (b) "CHAINED as owned stores — would need the ordering the spec does not give: UNFAITHFUL; rejected" (the A bit may be set
  speculatively; RVWMO orders implicit PT accesses by `SFENCE.VMA`, not `FENCE`).  The launch paragraph's (4)/(5) do say `WpPtWalkOwn`
  under the `pte` arm [OWN.39] — so the paragraph contradicts a document it declares binding, on a point where the binding document's
  reading excludes spec-allowed executions.  A worker who follows the BINDING note at the walker row would prove a chain the spec does
  not provide (or burn time discovering it cannot).  Also stale in the binding note: §7 Q-R1 (RULED [OWN.38] — the vector IS the design,
  not an option) and the "plan :NNNN" cites (rev 29 numbering).
  *Exact change (S, text).*  Replace the parenthesis at `:1717-1719` by: "(BINDING over `notes/W8-design.md` §4/§5/§8, which state the
  superseded scalar design [R28.s8]; **within `W8-Rctx.md` itself three things are SUPERSEDED: §0 item 5 / §4 / §6's user-table verdict
  'CHAINED as owned stores, `WpPtWalkOwn` only if Q-R2' → PTE-KEY for BOTH tables, `WpPtWalkOwn` IN the file list [OWN.39] (option (b)
  there is UNFAITHFUL — rejected); §7 Q-R1 → RULED (a) [OWN.38], the vector is the design; §6's 'serial before W-RSV' → after W-RSV
  [OWN.41]; its `plan :NNNN` cites are rev-29 numbers and its MachCSL cites are at the pre-β′ w3 tip — relocate by name [R34.s1]**)".
  No edit to `W8-Rctx.md` itself is needed (it is a dated record), but a one-line banner at its top pointing at this paragraph would be
  cheap and kind.
- **[R34.3] The Files list omits the ghost-state plumbing the per-author vector necessarily touches — including one `Weak/` file —
  so "12 MachCSL + ≈ 52 `Xv6/`" and the rebase-surface note "rebuild only, no edit, for `Weak/`" are not what the worker will find.**
  *What is wrong (evidence).*  A context's authorities are `ctxAt ξ q B D := MonoNat.auth_own ξ.bound (.own q) (.ofNat B) ∗ (ξ.dirty
  ↪●MAP{.own q} D)` (`MachCSL/Ctx.lean:191-192`) over `structure CtxId where bound : GName; dirty : GName` (`MachCSL/Resources.lean:425-428`).
  Deliverable (1) adds `chain ξ : CPU → Nat` at fraction `q` (it must split with `ctxAt`'s `q`: `ctx_park`/`ctx_move` carry halves).  There
  is no `CPU ↦ Nat` ghost map in the fixed layer: `MachFixedGS` (`Resources.lean:202-262`) has `authG : GhostMapG GF Nat Agent`, `resvG`,
  `dirtyG : GhostMapG GF Nat CPU RegMapF`, `lockSetG`, `kmapG : GhostMapG GF Nat (BitVec 64)`, …, and `xv6GF` (`Xv6/Xv6GF.lean:70-95`,
  slots 4–22 "MachCSL (`MachGpreS` …)") has `MonoNatRF` at slot 8 and `xgfGm Nat CPU RegMapF` at slot 11.  So the worker has exactly two
  routes, BOTH outside the listed files: (A) `CtxId` gains `chain : CPU → GName` (or one `GName` of a new `GhostMapG GF CPU Nat`) with per-CPU
  `MonoNat.auth_own` on slot 8 — edits `Resources.lean:425` and every `CtxId` constructor (`ctx_fresh`-style allocations, `CtxBox`'s
  minted contexts, `ForkretRecord.lean:37`) but no functor change; or (B) a new `MachFixedGS` field (`Resources.lean:202`), `MachGpreS :159`,
  `bootFixedGS` (`MachCSL/Adequacy.lean:160`, a new `GName` argument), `xv6GF` + `xv6GF_machGpreS` (`Xv6/Xv6GF.lean:70,390`), and the
  `MachFixedGS` literal **`Weak/WeakAdequacy.lean:98-99`** (`weakAdeqFixedGS := @bootFixedGS … WeakAdequacy.rsvNone Hinv 0 0 0 0 0 0 …` —
  exactly the file β′ had to touch for `rsvName`/`rsvStatic`, per W-SCO (A)'s own prompt "W8-β′ (w2: MachCSL/, Xv6/, Weak/WeakAdequacy.lean)")
  and `tcb/expected.json` module growth.  `vtest-lean/` has no `MachFixedGS` literal (grep) ✓.  Under (B) the sentence "every MachCSL merge
  rebuilds `Weak/` … (rebuild only, no edit, for W-SCO)" stays true FOR W-SCO's files but "no `Weak/` edit by (f2-ctx)" is false; under (A)
  `Resources.lean` joins the 12 (it is already in β′'s and W-RSV's surfaces, `:1738-1744`).
  *Exact change (S, text).*  In *Files* add: "+ the vector's ghost plumbing: `Resources.lean` (`CtxId :425`; route (A) per-CPU `MonoNat`
  names on slot 8 — RECOMMENDED, no functor change — or route (B) a new `GhostMapG GF CPU Nat` field in `MachFixedGS :202`/`MachGpreS :159`,
  then also `Adequacy.lean:160 bootFixedGS`, `Xv6/Xv6GF.lean:70,390`, **`Weak/WeakAdequacy.lean:98-99`** (β′'s precedent) and `tcb/expected.json`
  growth); say the route in the header".  In *Rebase surface*: "with W-SCO (A): NO shared file in either route (`WeakAdequacy.lean` is not
  W-SCO's); under (B) (f2-ctx) EDITS one `Weak/` file — merge MachCSL-first, W-SCO rebases by rebuild".  13 MachCSL files, not 12.

## SUGGESTIONS

- **[R34.s1] Stale cites in the launch paragraph and the binding note (β′/W-RSV shifted the MachCSL files).**  `:1727` "`WpLock.lean:1141,1345`
  absorb at the stamp `T`" → the `ctx_absorb` sites are `WpLock.lean:1255` and `:1461` (`:1141` is now β′'s `by_cases hm : lkRsvIn`);
  `W8-Rctx.md` §5 "`Lock.lean:375,430`" → `ctx_unstamp :547`, `ctx_stamp :564/:620/:666`; "`KCtxMove.lean:299`" → `:308` (`:299` is the
  docstring); "`CtxBox.lean:104,162,1329,1742,1938`" → `:104, :156 (ctxDeposit), :1329, :1742, :1938` (+ `:1489`, `:1824` `ctxDeposit`
  uses); `PipeBirth.lean:303` → `:307`; `cycleKillOfF :669` → `:668` (`:1667`).  Say once in the brief that `W8-Rctx.md`'s MachCSL cites
  are at the rev-29 w3 tip and the worker relocates by name.
- **[R34.s2] W-RSV census.**  `:27` "34 `wp_m_*` statements gain `[CurCtx]` + `ctxTok`": the tip has 37 `theorem wp_m_*` (all `[CurCtx]`;
  `WpMmode.lean` 20, `WpMmodeCsr.lean` 32, `WpMmodeAlu.lean` 18, `WpStore.lean` 14, `WpMmodeCtl/Mret.lean` 2 each `ctxTok` mentions) —
  write "37 carry (34 gained)" or recount.
- **[R34.s3] Name the launch authority.**  Add to `:1716`'s title line: "launch authority [OWN.37] + [OWN.41] (lane slot after W-RSV);
  no further batch approval — unlike W5d-G, `:1755`".  Removes the asymmetry a coordinator would otherwise have to resolve.
- **[R34.s4] `Vtest` cites.**  The directory is `vtest-lean/Vtest/` (`XState.lean:262 dropResv`, `HartExec.lean:423,454`); `:29`'s
  "1 `Vtest`" and `:1745`'s acceptance "`lake build MachCSL Xv6 Weak Vtest`" are fine as target names; the file cite should carry the path.
- **[R34.s5] Make the 31-file list checkable by grep.**  Only 18 `Xv6/` files name `ACQUIRE_LLB`/`ACQUIRESLEEP_LLB`/`*_llb_*`; R-ctx §5's 31
  include consumers of the `wp_release_hook_body`/`slBody_hook`/`newlockAt_llb` surfaces.  One sentence splitting "LLB-naming (18) +
  hook-surface (13)" lets the worker verify X5's completeness mechanically.
- **[R34.s6] `PROGRESS-W8ctx.md`'s first section.**  Ask for a per-row CLOSED table (the 31 rows of `W8-Rctx.md` §2 + the 4 outside sites +
  the walker row) kept in the progress file from increment 1, so a resisting row is visible at the first stop-green, not at the end.

## Owner questions the plan is missing

None requiring a ruling.  [R34.1]'s include-or-defer is a scope/schedule choice (both options FAITHFUL — the export's conjuncts are facts
about xv6's code; RVWMO, the Sail model, Zifencei and the PMAs are silent on how a proof partitions them); the coordinator may take it and
record it in §C W8 and the root's `roots.txt:20` comment.  [R34.2] restores a ruling already made ([OWN.39]); [R34.3] is proof plumbing.
Q-SCO-PMA (the only question touched by rev 37) meets the 2026-10-09 (spec first, marks) and 2026-10-10 (plain language, example,
definitions, per-option cost/unblocks/risk) standards; rev 37 adds no new question.
