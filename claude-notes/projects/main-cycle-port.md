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
item 4 lands.** This is by design (design doc §6): `wp_exec_step`'s
whole-instruction, one-σ witness is unsound under per-node interleaving and
cannot be re-derived as stated. Iterate with single-file `coqc` or
`make -f CoqMakefile <one>.vo` chains; a full `-j` build only at a milestone.

Everything listed under "What exists" is proven with **no admits** and at
**exactly the 5 rv64d platform axioms** (several files are fully closed).
What is NOT yet done: any leaf with its **old statement byte-identical** —
see item 3 and the honest scope note there.  `iris/HartMFetch.v` and
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
- `iris/HartMFetch.v` — `swp_fetch`: the WHOLE fetch, 2.7 s, ~40 lines of
  script, **taking the `fetch_bytes` fact as a premise**.  It is also the
  worked example of the early-return walk; read its header for the recipe.
  What the 4-aligned M-mode path touches is now visible in the statement:
  seven PC reads and nothing else (Ext_Zca is never read — with bit 1
  clear the `and_boolM` short-circuits before it — and Ext_Ziccif is a
  constant true from the config).

Evidence:

- `iris/HartPilot.v` — the Phase B pilot at parity: one instruction at a
  concrete state, 3.6 s file, 0.2 s instantiation.

## Left, in order

1. **`swp_fetch_bytes`, the premise `swp_fetch` is stated against.**
   `fetch_bytes` is `translateAddr` then `mem_read`; `mem_read` is a
   PLAIN-`M` bind spine (`swp_bind` applies directly, no context needed)
   down to `mem_read_priv` → `checked_mem_read`, which is a `cer` region
   containing `check_pma_with_pmp_priority`, an `untilMT` misalignment
   loop, `pmpCheck` (HartMPmp's fact) and the memory event.
   **Which tool where** — this is the one judgement the walk needs:
   `hfrun` for any maximal stretch whose reads are all pinned and which
   contains NO memory event (`translateAddr` at Bare, `effectivePrivilege`,
   `check_pma_with_pmp_priority`); `swp_bind` at plain-`M` spines;
   `swp_use_cer{,2,3}` inside `cer` regions; the ∀-peel only where reads
   leave `D` (`pmpCheck`, already done).
   **This is also the Qed-debt experiment.**  The old 665 s / 671 s `Qed`s
   covered exactly this stretch — the walk from the minstret chop down to
   the fetch's `MemRead` — as ONE monolithic goal-side chain.  The fetch
   layer above it already went from 912 lines / 665 s to 136 lines /
   2.7 s; whether the rest follows is the real test.  If it does not, that
   is a finding that changes the plan for item 3.
2. **`HartMLeaf.v`, rebuilt on `swp`.**  Still RED: it names the deleted
   segment apparatus.  It becomes the composition of the per-function
   facts along `try_step`'s own spine, with the invariant-cell writes
   (`minstret_increment`, the clock) taking `HartRegNode`'s single-node
   rules.
3. **The verbatim-statement question.**  `wp_word_main_b0` is per-word and
   raw-cell; the old tree's statement is the shape-generic, bundle-taking
   leaf.  (a) the bundles (`mmode_config`/`pc_is`/`gpr_file`/`instr`/
   `minstret_inv`) are defined at or above the red line, so they cannot be
   named until item 3; (b) ∀-operand shapes need a once-per-INSTRUCTION-
   SHAPE decode characterization over the ENCODING FUNCTION — the seam is
   that `instr` pins `decode w = i`, not `w = encode i`; (c) the two
   remaining fetch shapes (2-aligned base, RVC).
   **The design doc's Phase B/C gate — leaf specs preserved verbatim — is
   still open.  Do not report it as met before a statement diff is empty.**
4. **Phase B′ — reconnect the tree** (the 971 files).  Findings that set
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
     rules; `sr_absorb`/interrupt engines are item 7.
5. **Phase C — the leaf sweep**, spec-identical; whole-function proofs
   must re-check unedited (a failure is a finding, not a patch).
6. **Phase D — adequacy + capstones.**  `RiscvAdequacy`/`SystemAdequacy`
   mention `LoopE` by name, so statements keep elaborating; proofs that
   invert `prim_step` need the new inversion lemmas.
   `tools/proof_coverage.py` parity; `Print Assumptions` unchanged.
7. **The §4 audit items**, resolved and recorded: (a) invariants opened
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
