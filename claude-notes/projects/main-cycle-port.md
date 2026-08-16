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

**The tree is RED from `InstrBytes.v` up — 993 of 1181 `.vo` targets — and
stays red until item 2 lands.**  (It was `MinstretInv.v`/994; that file is
now green, which freed exactly ONE file — itself.  Turning a root green does
not free the tree, it moves the root up one rung.  Expect the same shape all
the way up.) This is by design (design doc §6):
`wp_exec_step`'s whole-instruction, one-σ witness is unsound under per-node
interleaving, and the rungs that were built on it come off one at a time.
Confirmed by full `make -k` at each step: there is always exactly ONE red
root.  `MinstretInv.v` was the first (`wp_exec_step`); `InstrBytes.v:695` is
the second (`wp_exec_step_decode_execute_inv`, which wants `minstret_inv` and
forwards to `wp_exec_step_hart_active_inv`).  The 994 is the
transitive closure of `MinstretInv.vo` in `.CoqMakefile.d` — recount it
there rather than trusting this number, which has already been stale once.  Iterate with single-file
`coqc` or `make -f CoqMakefile <one>.vo` chains; a full `-j` build only at a
milestone (and `-k`, or it stops at the first red root).

**A `.vo` on disk does NOT mean the file is green.**  Measured: 1110 of the
1173 `.v` have a `.vo`, but only 65 of the 994 red ones are actually
missing — the other ~929 carry PRE-PORT `.vo` artifacts that `make` never
touched, because it does not rebuild dependents of a target that failed.
`coqc` on anything importing one reports *"makes inconsistent assumptions
over library X"*, which is the real signal and is easy to misread as a
fresh breakage.  When that appears, rebuild the named dependency; do not
debug the file.

**The whole-cycle leaf is back.**  `HartMLeaf.wp_word_main_b0` is
`WP Loop ⊢ WP Loop` for one real kernel instruction (`c.sw a4,0(a5)` at
`main+0xb0`), at BOTH ticks, with **no admits** and at **exactly the 5 rv64d
platform axioms** — the same statement altitude the pre-port tree had, now
discharged through the per-node language.  17 s for the file.

Everything listed under "What exists" is proven with no admits and at the
same 5 axioms (several files are fully closed).  What is NOT yet done: any
leaf with its **old statement byte-identical** — see item 1 and the honest
scope note there.

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
  mono, frame, fupd both sides, `swp_use`, `swp_wp`/`swp_wp_loop`, and
  **`swp_loop`** — the boundary rule a leaf actually ends on:
  `▷ (∀ tick, swp (riscv_step tick) (λ _, WP Loop)) ⊢ WP Loop`.
  Read design §5 item 6 before touching it — the obvious CPS form is not
  merely less convenient, it CANNOT be applied inside
  `catch_early_return`.
- `iris/HartSpan.v` — the span rule (writes gated on `Drw`, reads
  UNGATED, `Dro` read-only frame), the pure `hval` predicate, **the
  `swp_span` bridge** that consumes the landing quantifier once, and
  `hfrun` + its reduction equations.  The pure layer is polymorphic in the
  sub-monad's result type.  **`hvalE`/`swp_spanE`** are the weakened form
  for stretches whose result is not worth naming: the walk LANDS and what
  it lands on satisfies a caller-chosen `Q`, typically
  `reg_agree_on (D ∖ touched) rs' rs`.  `hval`/`swp_span` are the
  instance `Q x rs' := x = x0 ∧ rs' = rs0`, so both go through one bridge.
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
  whole proof is the walker plus a case split on two config bits.  Also
  `tick_pc`, and the TICK in two forms: `swp_tick_clock` (named post-file,
  four premises about the machine) and **`swp_tick_clock_any`** (no premise
  at all beyond owning the three clock cells; the post-file is SOME file
  agreeing with the old one off `tk_clock3`).  A whole-cycle leaf needs the
  second, because `riscv_step` takes the tick at the MACHINE's choice and so
  the leaf must survive all eighteen paths — including the one that reaches
  the plic's unownable `sig_seip` wire, which the ∀-peel handles and the
  named form cannot.  **`swp_tick_wrap`** then puts the whole tick axis in
  one generic lemma: a leaf proves its body's `swp (try_step 0 false) …`
  and gets `swp (riscv_step tick) …` with its own characterization intact,
  weakened only off the clock cells.  5 s.
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

- `iris/HartMStore.v` — **the store path, complete**: `swp_execute_STORE`
  down to the `MemWrite` event, and under it one fact per model function
  (`check_pma` at the store's writable grant, `translateAddr` at `Store`,
  `mem_write_ea`, `checked_mem_write`, `mem_write_value`,
  `vmem_write_addr`, `vmem_write`).  698 lines, 5.9 s, 5 platform axioms.
- `iris/HartMDecode.v` — the DECODE, and the compressed store's EXECUTE.
  `swp_decode_hp` is the pilot's word; `swp_execute_C_SW` is per-SHAPE
  (generic in the operands), since `execute (C_SW …)` is one `Ret` node
  handing back the `ExecuteAs (STORE …)` the compressed form expands to.
  2.9 s.  **Read its header**: it also carries `d_tests`, the tactic that
  collapses a decode cascade's closed bit tests by conversion, which is
  what makes the decode an ordinary `hfrun` walk instead of the special
  bridge design §5 item 7 used to call for.

- `iris/HartMLeaf.v` — **the leaf**.  `swp_run_hart_active_hp` (the whole
  instruction), `swp_try_step_hp` (the whole cycle body, with the named
  post-state `hp_post` and minstret's VALUE quantified), and
  **`wp_word_main_b0`**: `WP Loop ⊢ WP Loop`, both ticks.  Under them the
  anchor tower `ml_rs` and its 23 lookup lemmas, the footprint split
  (`ml_Drw`/`ml_Dro`/`ml_Df` + `ml_rw_split`/`ml_ro_split`, the frame ↔
  points-to bridge), the three leaf-local `hfrun` equations (landing pad,
  `rX_bits`, `get_transformed_data_addr`), the concrete address facts, and
  the two memory obligations discharged from persistent text bytes
  (`ml_fetch_obl`) and owned data bytes (`ml_store_obl`).  1400 lines,
  17 s, 5 platform axioms.

  What the statement SAYS: the machine ends one instruction on — PC/nextPC
  at `pc+2`, the flag cell holding 1, every pin returned at the value it
  came in with — and the four cells the wrapper and the tick own (minstret
  and the three clock cells) hold SOME value.  That value-agnosticism is
  the raw-cell shadow of `MinstretInv`/`clock_inv`, which is where those
  cells go in B′.

Evidence:

- `iris/HartPilot.v` — the Phase B pilot at parity: one instruction at a
  concrete state, 3.6 s file, 0.2 s instantiation.

## Left, in order

1. **The verbatim-statement question.**  `swp_try_step_hp` is per-word and
   raw-cell; the old tree's statement for this instruction is the
   shape-generic, bundle-taking leaf.  (a) FOUR of the five bundles are
   above the red line — `minstret_inv` (`MinstretInv.v`, the root itself)
   and `pc_is`/`instr`/`mmode_config` (`InstrBytes.v`, above it) — so they
   cannot be named until item 2.  **`gpr_file` (`WpGpr.v`) is GREEN and
   usable today**; do not assume the whole bundle vocabulary is blocked.
   (b) ∀-operand shapes
   need a once-per-INSTRUCTION-SHAPE decode characterization over the
   ENCODING FUNCTION — the seam is that `instr` pins `decode w = i`, not
   `w = encode i`; (c) `swp_execute_C_SW` is already per-shape, which is
   the pattern (b) wants.
   **The design doc's Phase B/C gate — leaf specs preserved verbatim — is
   still open.  Do not report it as met before a statement diff is empty.**
2. **Phase B′ — reconnect the tree** (the 971 files).  Findings that set
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
3. **Phase C — the leaf sweep**, spec-identical; whole-function proofs
   must re-check unedited (a failure is a finding, not a patch).
4. **Phase D — adequacy + capstones.**  `RiscvAdequacy`/`SystemAdequacy`
   mention `LoopE` by name, so statements keep elaborating; proofs that
   invert `prim_step` need the new inversion lemmas.
   `tools/proof_coverage.py` parity; `Print Assumptions` unchanged.
5. **The §4 audit items**, resolved and recorded: (a) invariants opened
   across a whole instruction to LINK two accesses — candidates: the
   page-walker's read-then-A/D-update (`CommonWalk`) and the
   interrupt-absorbing step engines (`sr_absorb`); (b) mid-cycle interrupt
   delivery — the model's check reads `sig_seip`/mip at its own node, and
   `WpIntrCore`/`WpIntrInv` already ∀-quantify those off σ.  **(b) has
   already bitten twice, benignly: `swp_tick_clock` needs a premise that the
   CLINT does not change mip, precisely because the other branch reads
   `sig_seip` — and that premise is exactly what a whole-cycle leaf cannot
   pay, which is why `swp_tick_clock_any` exists.  The ∀-peel is the general
   answer; the named form is the convenience.**

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
- **A `Definition` for an intermediate register file is a conversion bomb.**
  A premise stated at `Definition mlb_rs2 := register_set … mlb_rs1` is one
  delta step from the caller's expected type; the conversion checker answers
  that by unfolding `register_set` instead, and never comes back (>2 min,
  killed).  Use `Local Notation` so the premise's type is SYNTACTICALLY what
  the consumer spells.  The anchor file itself may stay a `Definition` — it
  is what gets PASSED, not what gets matched under.
- **Never `rewrite` between two register-file towers.**  In a goal
  `register_lookup r towerA = register_lookup r towerB`, a conditional
  `rewrite` whose keyed match fails on one side unfolds `register_set` and
  compares two record-update towers (the 3^N bomb).  `etransitivity` +
  `apply` only ever unifies against ONE side, so each cell is constant-time.
  One tower is fine: `rewrite /the_definition` there reduces the lookup all
  the way by iota, which is both cheap and complete.
- `set_solver` in a clean top-level goal is 7 ms; the SAME goal inside a
  leaf proof, with the towers in scope, is unbounded.  Precompute
  memberships as standalone lemmas (`ml_in_*`, `ml_ind_*`) and pass them.
- Background builds must `cd` into `iris/` themselves: `make -f CoqMakefile`
  from the repo root fails with "No rule to make target 'CoqMakefile'", and
  a shell whose cwd drifted between commands is the usual cause.
