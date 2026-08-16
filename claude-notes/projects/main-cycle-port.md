# main-cycle-port — worklist

Design: [`design/main-cycle-port.md`](../design/main-cycle-port.md). **Read
it before touching anything here** — every settled decision lives there, not
in this file: the per-node semantics, batching-as-a-theorem, the span rule
(§5 item 1c), the monadic WP layer and why `mval` stays empty (§5 items 6–8),
the pure-exec bridge (§5 item 7), and §5's GOTCHA, which is the list of
measured ways to make a proof take minutes instead of milliseconds.

## CHECKPOINT

Branch `hart-node-port` (off `main`). The port replaces the whole-instruction
hart step with a per-node one, so a page walk, a TLB fill, a fetch and a data
access of one instruction can interleave with other harts.

**The tree is RED from `MinstretInv.v` up — 971 files — and stays red until
item 3 lands.** This is by design (design doc §6): `wp_exec_step`'s
whole-instruction, one-σ witness is unsound under per-node interleaving and
cannot be re-derived as stated. Iterate with single-file `coqc` or
`make -f CoqMakefile <one>.vo` chains; a full `-j` build only at a milestone.

Everything listed under "What exists" is proven with **no admits** and at
**exactly the 5 rv64d platform axioms** (several files are fully closed).
What is NOT yet done: any leaf with its **old statement byte-identical** —
see item 2 and the honest scope note there.  `iris/HartMFetch.v` and
`iris/HartMLeaf.v` are additionally red on their own account: they still
name apparatus the `swp` decomposition deleted (item 1).

Where a fresh agent should start reading: design doc §§2–5 — §5 items 6 and
7 are the interface and the two ways into it, and §5 item 1 is the list of
measured ways to make a proof take minutes instead of milliseconds.  Then
`iris/HartMCycle.v` (the computed route, end to end and small) and
`iris/HartMDispatch.v` (the peeled route, and the `swp` corollary every
caller uses).

## What exists

The language and the bracket:

- `iris/RiscvLang.v` — `HartE gen cpu m`; `LoopE` a Definition;
  `mnode_step` (hart-local, on `mstate`) + `hart_node_step`
  (focus / step / write-back); the fused-AMO window
  (`silent1`/`silent_run`/`wr_node`, `ak_excl`); per-arm `prim_step`
  inversion; `prim_step_hart_regs_frame` — the batching licence: plic's
  `sig_seip` wire is the only cross-thread register write.
- `iris/HartBlock.v` — the solo-block bracket, sound direction
  (`mblock` ⇒ `run`); closed against `exec` by `RiscvExec.hart_block_exec`.
- `iris/RiscvExec.v` — `wp_dead` and the three device rules re-derived;
  `wp_hart_step` (the per-node framing point) and `wp_hart_restart`
  (the ∀-tick boundary).

The proof interface (design §5 items 1, 1c, 6, 7):

- `iris/HartSwp.v` — **`swp`, in CONTEXT-GENERIC form**, and `mctx` with
  its four context formers (identity, bind, composition, and
  `mctx_cer_liftR` for the early-return region).  Laws: ret, bind, bind0,
  mono, frame, fupd both sides, `swp_use`, `swp_wp`/`swp_wp_loop`.
  Read design §5 item 6 before touching it — the obvious CPS form is not
  merely less convenient, it CANNOT be applied inside
  `catch_early_return`.
- `iris/HartSpan.v` — the span rule (writes gated on `Drw`, reads
  UNGATED, `Dro` read-only frame), the pure `hval` predicate, **the
  `swp_span` bridge** that consumes the landing quantifier once, and
  `hfrun` + its reduction equations.  The pure layer is polymorphic in the
  sub-monad's result type.
- `iris/HartSpanChar.v` — the six peel inversions, **`hfrun_hval`** (the
  computed route, no side conditions), `swp_hfrun`, and the two rules that
  fire constantly: `swp_read_reg_pinned`, `swp_write_reg_owned`.
- `iris/HartEvents.v` — RAM read/write and MMIO read/write, each in a
  context form and a `swp` form.
- `iris/HartRegNode.v` — single-node RegRead/RegWrite (the escape hatch
  for invariant-held cells and the `sig_seip` wire), likewise both forms,
  plus the `hregread_resume_red`/`hregwrite_resume_red` equations.
- `iris/HartAmo.v` — the fused-AMO rule (`∃ w` inside the fupd, window
  data a function of `w`) and the pure window layer.  Still WP-shaped:
  there is no `swp` for the exclusive read alone, by design.
- `iris/HartLift.v` / `iris/HartLift2.v` — the older cursor batch and the
  two-footprint functional batch.  **Superseded by `hfrun`**; `HartLift`'s
  projections (`hread_req_at`, `hread_resume`, `hreg_frame`, …) are still
  the event rules' vocabulary and stay.  Delete the batch rules once
  `HartMFetch`/`HartMLeaf`/`HartPilot` no longer use them.

The M-mode cycle, per MODEL FUNCTION (the unit of reuse — not per
segment):

- `iris/HartMDispatch.v` — `mdispatch_hval` /
  `swp_dispatchInterrupt_M`: the dispatch is a `None` no-op at M-mode,
  its five unownable reads ∀-peeled once.  2.4 s, zero axioms.
- `iris/HartMCycle.v` — `hfrun_should_inc_minstret` /
  `swp_should_inc_minstret`: everything it reads is pinnable, so the
  whole proof is the walker plus a case split on two config bits.  2.7 s.
- `iris/HartMPmp.v` — `mpmp_hval_ifetch4` / `swp_pmpCheck_ifetch4`: the
  ifetch PMP check allows at Machine with entries unlocked; **fuel
  induction** over `foreach_ZM_up'` with the loop body captured by ltac
  `context` match (never transcribed).  4.9 s, zero axioms.
- `iris/HartMFetch.v` — **the fetch, complete**: `swp_fetch_ram` is
  WP-level fetch from the boundary to `F_Base w` with no obligation but
  the memory one (the leaf owns the text bytes).  Under it, one fact per
  model function: `translateAddr`, `mem_read`, `fetch_bytes`,
  `check_pma_with_pmp_priority`, `within_mmio_readable`,
  `checked_mem_read`.  634 lines, 6.0 s, 5 platform axioms.
  **Read its header for the early-return recipe, the which-tool
  judgement, and the `untilMT` note.**  What the 4-aligned M-mode path
  touches is visible in the statements: seven PC reads, mstatus,
  cur_privilege, pma_regions, pmpcfg_n, htif_tohost_base, and nothing else
  (Ext_Zca is never read — with bit 1 clear the `and_boolM` short-circuits
  before it — and Ext_Ziccif is a constant true from the config).

- `iris/HartMDecode.v` — the DECODE, and the compressed store's EXECUTE.
  `swp_decode_hp` is the pilot's word; `swp_execute_C_SW` is per-SHAPE
  (generic in the operands), since `execute (C_SW …)` is one `Ret` node
  handing back the `ExecuteAs (STORE …)` the compressed form expands to.
  2.9 s.  **Read its header**: it also carries `d_tests`, the tactic that
  collapses a decode cascade's closed bit tests by conversion, which is
  what makes the decode an ordinary `hfrun` walk instead of the special
  bridge design §5 item 7 used to call for.

Evidence:

- `iris/HartPilot.v` — the Phase B pilot at parity: one instruction at a
  concrete state, 3.6 s file, 0.2 s instantiation.

## Left, in order

1. **`HartMLeaf.v`, rebuilt on `swp`.**  The last RED file: it names the
   deleted segment apparatus.  It is the composition of the per-function
   facts along `try_step`'s own spine.  **Walked to the decode already, in
   a scratch probe, with every step one of the four standard moves** — so
   what follows is a transcript, not a design:

     `read_reg cur_privilege` → `should_inc_minstret` (HartMCycle) →
     `write_reg minstret_increment` (`swp_write_reg_owned`; the cell is
     OWNED, raw-cell form, since `MinstretInv` is above the red line) →
     `read_reg hart_state` → `run_hart_active 0`, a `cer` region:
     `read_reg cur_privilege` → `dispatchInterrupt` (HartMDispatch) →
     `fetch` (HartMFetch's `swp_fetch_ram`, whose memory obligation the
     leaf discharges from its text bytes via `HartLift2.text_read_bytes`)
     → the `isRVC` branch → `ext_decode_compressed` and `execute (C_SW …)`
     (**both done — `HartMDecode.v`**) → **HERE**: `execute (STORE …)`,
     the base store the compressed form expands to, which is the whole of
     the write side → try_step's tail → `tick_clock` at the tick.

   **THE STORE SIDE, mapped** (it mirrors the read side, so the read
   chain in `HartMFetch` is the template, not just an analogy):
   `execute_STORE imm rs2 rs1 4` = `assert_exp'` (pure) → `rX_bits rs2`
   (a GPR read) → `vmem_write rs1 offset 4 data (Store Data) …` →
   `get_transformed_data_addr` → `vmem_write_addr`, a `cer` region:
   the alignment check, `split_on_page_boundary`, the mstatus /
   cur_privilege reads, `translationMode` (all hfrun — pinned reads, no
   memory event), then `translateAddr` (**HartMFetch's fact already**),
   then the write itself.  Only the last step is new work.

   **THE PEEL DEPTH IS NOT GUESSABLE FROM THE `.sail` SOURCE.**  Read it
   off the goal.  `dispatchInterrupt` and `fetch` inside
   `run_hart_active`, and `translateAddr` inside `fetch_bytes`, are all
   DEPTH 1 — their `match`es sit inside the continuation, not in a
   separate bind.  Depth 3 and 4 come from `or_boolM`/`and_boolM` nests
   and from the `untilMT` body.
   **THE FILE TOWER is the one piece of bookkeeping `swp` does not
   remove** (it is inherent: writes change the file).  Each write adds a
   `register_set` layer, and each later lookup costs one
   `rewrite (irrelevant_register_set r r' rs _ eq_refl)` — the value
   argument is inferred, the disequality is `eq_refl`.

   **THE QED DEBT IS SETTLED** and needs no further experiment: the
   stretch that cost 665 s as one monolithic goal-side chain is 6.0 s
   decomposed per model function, and the decomposition exposes four
   reusable intermediate facts the monolith did not.
2. **The verbatim-statement question.**  `wp_word_main_b0` is per-word and
   raw-cell; the old tree's statement is the shape-generic, bundle-taking
   leaf.  (a) the bundles (`mmode_config`/`pc_is`/`gpr_file`/`instr`/
   `minstret_inv`) are defined at or above the red line, so they cannot be
   named until item 3; (b) ∀-operand shapes need a once-per-INSTRUCTION-
   SHAPE decode characterization over the ENCODING FUNCTION — the seam is
   that `instr` pins `decode w = i`, not `w = encode i`; (c) the two
   remaining fetch shapes (2-aligned base, RVC).
   **The design doc's Phase B/C gate — leaf specs preserved verbatim — is
   still open.  Do not report it as met before a statement diff is empty.**
3. **Phase B′ — reconnect the tree** (the 971 files).  Findings that set
   the plan, surveyed against the real statements:
   - Leaf SPECS are resource-shaped (cells in, cells out — no σ, no
     `exec`, no fupd), so "verbatim" is achievable; the σ-callback
     currency is INTERNAL to `wp_instr` and the mid-stack.
   - `wp_instr`'s exact statement is NOT re-derivable: its callback hands
     back `mstate_interp s_exec` inside one fupd, meaningful only when the
     instruction is one atomic step.  Rebuild the same ALTITUDE with a
     per-event internal currency.
   - The `exec_execute_*` catalogue gets `swp`-form twins in the sweep
     (mechanical, `gen_code.py` style); decode (`kd_`) is consumed via
     `instr` unchanged.
   - Memory-class leaves route their data events through `HartEvents`;
     MMIO leaves keep σ-shaped device reasoning through the MMIO rules.
   - The clock/minstret absorption rebuilds on `HartRegNode`'s single-node
     rules; `sr_absorb`/interrupt engines are item 6.
4. **Phase C — the leaf sweep**, spec-identical; whole-function proofs
   must re-check unedited (a failure is a finding, not a patch).
5. **Phase D — adequacy + capstones.**  `RiscvAdequacy`/`SystemAdequacy`
   mention `LoopE` by name, so statements keep elaborating; proofs that
   invert `prim_step` need the new inversion lemmas.
   `tools/proof_coverage.py` parity; `Print Assumptions` unchanged.
6. **The §4 audit items**, resolved and recorded: (a) invariants opened
   across a whole instruction to LINK two accesses — candidates: the
   page-walker's read-then-A/D-update (`CommonWalk`) and the
   interrupt-absorbing step engines (`sr_absorb`); (b) mid-cycle interrupt
   delivery — the model's check reads `sig_seip`/mip at its own node, and
   `WpIntrCore`/`WpIntrInv` already ∀-quantify those off σ.

Optional, decide with evidence, never speculatively: **native Sail values as
`mval`** (design §5 item 8).  The restart marker is the cheap,
independently-landable half; the payoff is `Atomic`/`iInv` for the
invariant-heavy leaves.  Re-open only if the fupd-style event rules prove
painful once B′ puts those leaves back in scope.

## Traps a fresh agent will otherwise re-discover

All measured.  **The first group now lives in design §5 item 1** (the
reduction discipline, heads (a)–(g)) — read it there, and do not duplicate
it here.  What is left is the rest:

- Walking a stretch at a symbolic file with pins as a `register_set` tower
  fails both ways: `cbn` stalls on the tower lookups (~30 s), `lazy`
  full-normalizes dead branches (>300 s). Peel instead, taking pinned values
  as explicit arguments so no lookup term is ever formed.
- `ext_decode_compressed` is vm-opaque (the Acc-guarded `currentlyEnabled`
  diverges); collapse the extension gates with `reflexivity` equations
  instead — `currentlyEnabled`'s `Zwf_guarded` tower unfolds by pure
  conversion, which is also how `HartMDispatch` avoids the exec side's
  `Acc`-destructing entirely.
- On this Rocq, `destruct … eqn:` substitutes in HYPOTHESES too, so the
  follow-up `rewrite H in Hyp` fails as already-gone.
- Closed `bv` equalities need `apply bv_eq` (or `f_equal` per field) —
  plain `vm_compute; reflexivity` trips on the well-formedness proofs.
- `-time`'s output is block-buffered through a redirect, so the last line
  lags execution by ~4 KB; to localize a stall, `kill -INT` the
  `rocqworker` (`timeout` reaps only its direct child, and `pgrep -x coqc`
  does not find it).
- Background builds must `cd` into `iris/` themselves: `make -f CoqMakefile`
  from the repo root fails with "No rule to make target 'CoqMakefile'", and
  a shell whose cwd drifted between commands is the usual cause.
