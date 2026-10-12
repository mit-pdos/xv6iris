VERDICT: NOT SATISFIED

# Review R33 of `notes/weak-allocproc-plan.md` (rev 36)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite below was
read at the working-copy tip of `../xv6iris-weak` (plan rev 36, 4,731 lines), in `model/Lean_RV64D/LeanRV64D/` (the Sail model)
and in `../weak-orch/` (`allocproc_WSCO_A_prompt.txt`, `parked/PROGRESS-WSCO.md`).  Scope per the R33 brief (narrow): is the
[R32.1] restatement TRUE, and is §C W-SCO (A) launchable as written.  W8-β′ and W13 (I) are running; their briefs were not read
for change.  Items (a)/(b)/(d) of the standing brief were settled in R1–R32 and are not re-opened.

**Sign-off.**  NO — ONE required change, S.  The rev-36 **premise restatement is TRUE**: under `wbootFacts σ0` every hart's
register file is a landing file of the boot program, `bootPost` pins `pma_regions = bootPMA` AND `htif_tohost_base = none`
(`MachCSL/BootInitModel.lean:39,41`), and neither is written by the cycle.  But **the tree obligation the brief specifies,
`cycleOkBoot` with `Rboot` pinning ONLY `pma_regions`, is still FALSE**: after `pmaCheck` passes, `checked_mem_read` routes the
instruction fetch through `within_mmio_readable` (`Mem.lean:437-446`), whose HTIF branch reads `htif_tohost_base`
(`Platform.lean:243-249`); under an arbitrary `some base` in RAM the fetch is answered by `htif_load` from the `htif_tohost`
REGISTER with NO `.memRead` node, so the cycle announces a word (any word, e.g. `0x12000073`) at phase `.instr` and `good`'s
`.instrAnnounce` arm (`SailCycleOrderK.lean:154-156`) fails.  Same shape as [R32.1], one register further along the same path; the
fix is a second pinned register in `Rboot`, a second `≠` in the `regWrite` arm, one more conjunct in the run invariant, and one
sentence in the brief ("the ONE place … precise about a value" → two).  W-SCO (A) becomes launchable the moment [R33.1] is in its
brief (addendum form, as [R32.1]).  Everything else checked holds; the remaining items are cosmetic ([R33.s1]–[R33.s5]).

## What was checked and holds

- **[R32.1] restatement — the facts it rests on are TRUE in the tree.**  `bootPMA` (`MachCSL/Platform.lean:199-250`): three
  regions — `[0x1000, 0x2000)` IOMemory `executable := false` (`:205`), `[0x0200_0000, 0x1200_0000)` IOMemory `executable :=
  false` (`:225`), `[0x8000_0000, 0x8800_0000)` MainMemory `executable := true` (`:245`) ✓.  `pmaCheck` (`Mem.lean:263-274`):
  `matching_pma_region (← readReg pma_regions) paddr width` — `none ⇒ Err accessFault` (`:265-268`), `.InstructionFetch ⇒
  attributes.executable` (`:274`) after `override_PMA` (`Pma.lean:313-319`: `PBMT_NC`/`PBMT_IO` change `mem_type`/`cacheable`/
  idempotence only — `executable` untouched ✓).  `matching_pma_region` (`Pma.lean:412-423`) = first region with the whole access
  `range_subset` the region ⇒ `some r ∧ r.executable ⇒ 0x8000_0000 ≤ pa` ✓.  `writeReg pma_regions`: `MachCSL/ArchReset.lean:125`
  (boot) and `model/…/LeanRV64D.lean:265` (`sail_model_init`) only — neither reachable from `riscvStep` ✓.  `wbootFacts σ0`
  (`WeakLang.lean:482-490`): `∀ c, ∃ f₀, bootRun (bootProg (bootHid c) bootPMA) f₀ = some ((), g'.wgregs c)` (`:488`) ✓;
  `bootFin_bootProg` (`BootReset.lean:62-70`) says every landing file satisfies `bootPost hid bootPMA`, and `resetRegsRun_of_run`
  (`:107-115`) is exactly the transfer pattern (`bootRun … = some ((), f) → bootPost … f`) commit 1 needs; `bootPost`
  (`BootInitModel.lean:29-45`): `f .htif_tohost_base = none` (`:39`), `f .pma_regions = pma` (`:41`) ✓.  M1 and M2 carry
  `wbootFacts σ0` (`SrvwmoXv6Witness.lean:599`, `PfRunUnpinned.lean:596`) ✓; `sailCycleOrderK :92-93` already assumes it ✓.
- **The refuting run of R32 is real.**  `pnodeStep`'s `.memRead` arm tests `devAddr req.pa` FIRST (`WeakEvInst.lean:314-321`;
  `devAddr pa := pa.toNat < 0x80000000`, `MachCSL/Dev/Fabric.lean:125-126`); `LIFetch` only on the `¬ devAddr` branch (`:322-330`)
  ✓; `epsInit σ0` seats hart `c` at `σ0.wgregs c` (`WeakEvCapstone.lean:1026-1027`) ✓; `sailCycleOrder :126-137` has no boot
  hypothesis ✓.  `good`'s device arm is "any answer, same phase" (`SailCycleOrderK.lean:149-150`), `.regRead` "any answer" (`:156`) ✓.
- **The register file is mutated ONLY where the plan says.**  `pstepEv`'s hart arm: `rs' = ors.getD rs` (`WeakEvInst.lean:594-600`);
  `ors = some _` at exactly two sites — `pnodeStep`'s `.regWrite` (`rs.set r v`, `:313`) and the PLIC wire `pinSet` (`sig_meip`/
  `sig_seip`, `:473,:486`); the boundary `.pure` arm and every other node arm have `ors = none` ✓.  So "every hart's `rs pma_regions
  = bootPMA`" (and, per [R33.1], `rs htif_tohost_base = none`) is preserved by every step once `good`'s `regWrite` arm excludes the
  register ✓.  `inv :264` already quantifies the hart's `rs`, so the extra conjunct has a home ✓; `invInit :414` has no boot
  hypothesis today (the restated one takes `wbootFacts σ0`) ✓; `invRun :430`, `scoOfInv :450`, `sailCycleOrderOfCycle :470` as the
  plan describes ✓.
- **The ifetch path emits its `.memRead` AFTER the PMA check** — `fetch_bytes` (`Fetch.lean:217-226`, both halfwords `:252-280`,
  `Ext_Ziccif` `Extensions.lean:528`) → `translateAddr` → `mem_read (InstructionFetch ())` (`Mem.lean:496`) → `mem_read_priv` →
  `mem_read_priv_meta` → `checked_mem_read :405`: `check_pma_with_pmp_priority :394` (PMA first, PMP on PMA failure) → the split loop
  → `read_ram rk paddr …` (`PhysMemInterface.lean:338`, `rk = Read_ifetch`) = the `.memRead` node with `req.pa = paddr` ✓ — so under
  `pma_regions = bootPMA` the node carries `pa ≥ 0x8000_0000` ✓.  BUT see [R33.1]: between the PMA check and `read_ram` sits
  `within_mmio_readable` (`:437-446`).
- **§C W-SCO (A) brief (`:1521-1599`)**: [R32.4]'s decomposition is right — `riscvStep` (`MachCSL/Lang.lean:241-243`), `try_step`
  (`Step.lean:416-440`: `ext_pre_step_hook`, `minstret_increment`, `run_hart_waiting :230` / `run_hart_active`, the handler arms),
  `run_hart_waiting` fetches and announces nothing (`:230-242`), `ucPrelude :55-59`/`ucBody :61`/`ucAfterFetch :169`/`ucEpilogue
  :123-130`/`uc_tryStep_eq`,`uc_runHartActive_eq` (`UCycleDefs.lean:11-17`), `uxaExecAs` (`UExecAluGpr.lean:281-284`), 46 `ExecuteAs`
  sites, 122 `def execute_*` ✓; `tick_clock` is `model/…/Platform.lean:549` ([R33.s4]).  `instr_announce` is called at exactly two
  model sites (`Step.lean:340,377`, both in `run_hart_active` after the fetch) and `Barrier_RISCV_i` is emitted at exactly one
  (`InstsEnd.lean:18296`, `execute_FENCEI`) ✓ — the census is sound.  Files, rebase surface, acceptance, risks present ✓.
- **[R32.2]** every "merge pending"/"once w5 merges"/"not imported"/"coordinator's step" clause is gone (grep: only the header's
  description of the fix at `:21` remains) ✓; `Weak.lean:635-636` imports both files ✓.  **[R32.3]** at `:1616-1619` and `:3082` ✓;
  `GraphFetchSpike.lean:312` is the 4-ary `emZifencei` ✓.  **[R32.4]** at `:1570-1580` ✓.  **Records**: `:44`, `:48`, `:1507`,
  `:1516-1517`, `:2565-2567`, `:3661-3665` say VACUOUS until commit 1 ✓; §A(6) `:547-551`, §B(11) `:1364-1375`, Q-FIARM `:4112-4114`
  say "TRUE from this platform's reset; FALSE over arbitrary register files; stated under `wbootFacts σ0`" ✓.
- **§D Q-SCO-PMA (`:3771-3812`)** meets the 2026-10-09/10 format: *Spec (FIRST)* (RVWMO/riscv.cat silent, Zifencei silent, PMAs put
  executability in the platform table, Sail's `pmaCheck`), plain language, the concrete example (hart 0, `0x12000073` in a PLIC
  enable word, outcome under each map), definitions of every internal name, why it matters, and (α)/(β)/(γ) each marked
  faithful/weaker with cost, unblocks, risk ✓.  One wording fix folded into [R33.1] (iv).

## REQUIRED changes

- **[R33.1] `cycleOkBoot` as specified is FALSE: `Rboot` must ALSO pin `htif_tohost_base = none`; the brief's "the ONE place where
  the footprint walk must be PRECISE about a VALUE" is wrong (there are two).**
  *What is wrong (evidence).*  (1) `checked_mem_read` (`model/Lean_RV64D/LeanRV64D/Mem.lean:405-460`), after the PMA/PMP check and
  inside the split loop (`:437-446`), does `if (← within_mmio_readable paddr split_width) then mmio_read … else read_ram …`.
  `within_mmio_readable` (`Platform.lean:718-728`) = `within_clint ∨ within_sig ∨ (within_htif_readable ∧ 1 ≤ width)`;
  `within_clint` (`:221-229`) and `within_sig` (`:232-240`) are pure arithmetic on the constants `plat_clint_base = 0x0200_0000`/
  `plat_clint_size = 0xC0000`, `plat_have_sig = false` (`PlatformConfig.lean:4476-4486`) — false for any `pa ≥ 0x8000_0000`; but
  `within_htif_readable` (`:252`) = `within_htif_writable` (`:243-249`) **reads the register `htif_tohost_base`** (`RegisterType =
  Option (BitVec 64)`, `Defs.lean:1561`): `none ⇒ false`, `some base ⇒ addr < base + 8 ∧ base ≤ addr + width`.  (2) Under the brief's
  `Rboot r v := r = pma_regions → v = bootPMA` the `.regRead htif_tohost_base` node is "any answer" (`good`'s `R` is `True` there), so the
  path `some 0x8000_1000` with an ifetch at `pa = 0x8000_1000` is in the tree: `mmio_read` (`:746-757`) → `htif_load` (`:598-620`) returns
  `Ok (extractLsb (← readReg htif_tohost) 31 0)` — **register reads only, NO `.memRead` node, hence no `LIFetch`**; `fetch` returns
  `F_Base w` for whatever `htif_tohost` holds (another "any answer" register; `0x12000073` is one value) → `ucAfterFetch` →
  `instr_announce` at phase `.instr` (the boundary's) → `good`'s `.instrAnnounce` arm demands `sfAnnB 32 w = true → ph = .fetch`
  (`SailCycleOrderK.lean:154-156`): FALSE.  So `cycleOkBoot` (brief `:1543-1544`) is refutable exactly as `cycleOkAll` was, and the
  worker would again be asked to prove a false proposition.  (3) The RUN-level restatement is unaffected — TRUE: `bootPost` pins
  `f .htif_tohost_base = none` (`MachCSL/BootInitModel.lean:39`) for every landing file (`bootFin_bootProg`, `BootReset.lean:62`), and
  the only writer `enable_htif` (`Platform.lean:217-218`) has NO caller in `model/` or `MachCSL/` (grep) — the cycle never writes it.
  (4) The tree already knows this: MachCSL's own RAM-read lemmas carry `htif_tohost_base = none` as a premise —
  `uma_within_mmio_readable_ram` (`MachCSL/UMemPhys.lean:169-171`: `s.file .htif_tohost_base = none → inRam pa n → within_mmio_readable
  … = some (false, …)`), used at `UMemRam.lean:86,113`; the Weak fetch leaves too (`WeakFetch2.lean:323`: `(hpma : … pma_regions =
  bootPMA) (hhtif : … htif_tohost_base = none)`; 120 occurrences of `htif_tohost_base = none` in `Weak/`); and `MachCSL/HwConfig.lean:48-57`
  (`hwVal`) lists BOTH `pma_regions ↦ bootPMA` and `htif_tohost_base ↦ none` among the registers "nothing writes after reset"
  (`hwConfig :93-100`).  The brief named one of the two.
  *Spec (FIRST).*  RVWMO/riscv.cat/Zifencei: silent (as Q-SCO-PMA).  The PMAs decide EXECUTABILITY; the HTIF window is NOT an ISA or
  PMA notion at all — it is the Sail model's host-interface device, located by the configuration register `htif_tohost_base` (a platform
  constant: `none` on this board, `BootBoard.lean:31`, `HwConfig.lean:53`).  Pinning it is a PLATFORM hypothesis of the same kind as
  `bootPMA`, already inside `wbootFacts`; FAITHFUL to the Sail model as booted on this board, and the trusted base gains nothing.
  *Exact change (W-SCO (A) commit 1; §C top `:1525-1558` and §C W-SCO `:2670-2677`; S, ≈ +30–60 lines of proof).*  (i) `Rboot` pins
  BOTH registers: `Rboot r v := (r = pma_regions → v = bootPMA) ∧ (r = htif_tohost_base → v = none)` (or, avoiding dependent equality:
  `Rboot : ∀ r, RegisterType r → Prop | .pma_regions, v => v = bootPMA | .htif_tohost_base, v => v = none | _, _ => True`); the
  `.regWrite r v` arm of `good` requires `r ≠ pma_regions ∧ r ≠ htif_tohost_base` (both provable along the walk: no `writeReg` of either
  is reachable from `riscvStep`; `enable_htif` is uncalled).  (ii) The run invariant gains "every hart's `rs pma_regions = bootPMA ∧ rs
  htif_tohost_base = none`" (base: `wbootFacts σ0` + `bootFin_bootProg`/the `resetRegsRun_of_run :107-115` pattern → `bootPost` →
  `:39,:41`; step: `pnodeStep`'s `regWrite` with the two `≠`, `pinSet` touches `sig_meip`/`sig_seip` only).  (iii) Replace "**The ONE
  place where the footprint walk must be PRECISE about a VALUE (the PMA result)**" (`:1554-1555`) by: "**TWO places where the walk must be
  PRECISE about a VALUE: the PMA lookup (`matching_pma_region bootPMA … = some r ∧ r.executable ⇒ 0x8000_0000 ≤ pa`, so the ifetch
  `.memRead` has `devAddr = false`) and `within_mmio_readable` on that `pa` (`Mem.lean:440-448`; `within_clint`/`within_sig` false by
  constant arithmetic on `plat_clint_base`/`plat_have_sig`, `within_htif_readable` false by `htif_tohost_base = none` — the
  `uma_within_mmio_readable_ram` shape, `UMemPhys.lean:169`), so the fetch reaches `read_ram` and not `htif_load`.**  Everything else in
  the walk is footprint-only."  Add to the risks: "a third configuration register on the ifetch path would be found by the walk as a
  `.regRead` whose answer the proof needs — pin it from `hwVal` (`HwConfig.lean:48-57`) in the same way; do not weaken `good`."
  (iv) Text: §D Q-SCO-PMA's title/plain-language "What may the Sail-cycle fact assume about the platform's MEMORY MAP?" → "… about
  the platform's memory map AND HTIF window (`pma_regions`, `htif_tohost_base`, both pinned by `bootPost`)"; its (α) sentence "`good`
  gains a register filter" → "… a register filter pinning `pma_regions = bootPMA` and `htif_tohost_base = none` [R33.1]"; the
  `SrvwmoXv6Adequacy.lean`/`MachOfPf.lean` header sentence of (iv) `:1556-1558` → "the boot PMA table forbids instruction fetch from
  I/O regions and the HTIF window is disabled"; §A(6) `:548-549` and §B(11) `:1365` gain the same six words.  No change to M1/M2's
  statements, names, or the `baseline-weak.json` entry (both facts are inside `wbootFacts σ0`).  **Launch rule**: as [R32.1] — W-SCO
  (A) launches when this paragraph is in its brief (addendum form is fine); the coordinator's prompt must carry it ([R33.s1]).

## SUGGESTIONS

- **[R33.s1] The coordinator's prompt is still rev 35's** (`../weak-orch/allocproc_WSCO_A_prompt.txt`, 3 lines): "plan rev 35 §C
  W-SCO", "prove `cycleOkAll` for EVERY instruction", "(124 clauses …)", "`sailCycleOrderOfCycle cycleOkAll`" — none of [R32.1],
  [R32.4], [R32.s5] or [R33.1] is in it.  The plan's launch rule (`:1522-1523`: "LAUNCHABLE once this paragraph is in its brief") is
  right; this is the reminder that the artefact it points at has not been regenerated.  Not a plan edit; a launch gate.
- **[R33.s2] Name the right base lemma.**  `:1546` routes the base through "`bootRun_bootLand` `BootReset.lean:118`";
  `bootRun_bootLand` only names the landing file (`bootLand cpu f₀`) and carries no `bootPost`.  The lemma that gives `bootPost` of
  `σ0.wgregs c` is `bootFin_bootProg` (`BootReset.lean:62-70`) through the `resetRegsRun_of_run` pattern (`:107-115`: rewrite the
  `BootFin` witness with `wbootFacts`'s equation).  S; cosmetic for the brief, saves the worker a detour.
- **[R33.s3] `Rboot`'s type.**  `R : ∀ r : Register, RegisterType r → Prop` with `r = pma_regions → v = bootPMA` needs a cast
  (`v : RegisterType r`, `bootPMA : List PMA_Region`); the `match r, v with` form in [R33.1] (i) avoids `HEq`/`cast` and lets `simp`
  close the `_` arms.  `regWrite`'s `r ≠ …` is fine as written (`Register` derives `DecidableEq`, `Defs.lean:1542`).
- **[R33.s4] Cites.**  `:1580` "`tick_clock` (`Platform.lean:549-554`)" — that is `model/Lean_RV64D/LeanRV64D/Platform.lean:549`
  (`MachCSL/Platform.lean` has 284 lines and is `bootPMA`'s file; the sentence cites both files as "Platform.lean"); `:19` and Q-SCO-PMA's *Spec* paragraph
  "`writeReg pma_regions` only at `ArchReset.lean:125`" — also `model/…/LeanRV64D.lean:265` (`sail_model_init`), both outside the
  cycle; `:1547` "`invStep :359`'s `regRead` case (`:335-338`)" — the case is `nodeStep :273`'s (`:335-338`), `invStep :359` calls it;
  `good`'s `.memRead` arm is `:145-150` (device conjunct `:149-150`), `.instrAnnounce :154-156`, `.regRead :157`.  Cosmetic.
- **[R33.s5] One census footnote for the per-clause walk.**  `barrier_kind_of_num` (`PhysMemInterface.lean:262-275`) has the fallback
  `| _ => Barrier_RISCV_i`; if any `execute_FENCE*` clause reaches it with a reserved encoding, a plain `fence` emits a
  `Barrier_RISCV_i` node.  Harmless for `good` (its barrier arm only needs phase `.instr`, which the announce established), but the
  brief's "`FENCEI` proves exactly one `Barrier_RISCV_i`" (`:1567`) should not be read as "no other clause emits one" — the per-clause
  lemma for `FENCE` must case on the kind, not assume `≠ Barrier_RISCV_i`.  S.

## Owner questions the plan is missing

None new.  [R33.1] lives inside Q-SCO-PMA's option (α) (the fact is stated under `wbootFacts σ0`, which pins both registers); it
changes the TREE filter, not the premise, so no ruling is needed — the (iv) wording fix lets the owner see that two platform
constants, not one, are what the proof reads off the board.  Q-SCO-PMA's existing text meets the 2026-10-09 (spec first, marks) and
2026-10-10 (plain language, example, definitions, per-option cost/unblocks/risk) standards.
