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
see item 3 and the honest scope note there.

Where a fresh agent should start reading: design doc §§2–5, then
`iris/HartPilot.v` §6's header (the rule/instance discipline), then
`iris/HartMCycle.v`'s `mseg1_char` (the worked peel template and the
spine-reduction incantation), then `iris/HartMLeaf.v` (the full assembly).

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

The proof kit:

- `iris/HartLift.v` — the reflective silent stepper (`hsil_node`,
  `hrun_silent`, cursor `hcur`, projections + inversions), `hreg_frame`,
  and `wp_hart_batch` (equation-free, F8 form).
- `iris/HartLift2.v` — the TWO-footprint functional batch (`Drw` writable +
  `Dro` dfrac-generic read-only) and `text_read_bytes`, the F7 byte bridge
  (`read_bytes` from persistent kernel-text cells).
- `iris/HartEvents.v` — the per-event rules: RAM read/write, MMIO
  read/write, fupd σ-callback currency.
- `iris/HartAmo.v` — the fused-AMO rule (`∃ w` inside the fupd, window data
  a function of `w`) and the pure window layer.
- `iris/HartRegNode.v` — single-node RegRead/RegWrite rules (the escape
  hatch for invariant-held cells and the `sig_seip` wire) and the
  `hregread_resume_red`/`hregwrite_resume_red` reduction equations.
- `iris/HartSpan.v` — **the B′ keystone.** Writes gated on `Drw`, reads
  UNGATED, `Dro` read-only frame, continuation over the relational landing
  set; proven by structural induction on the monad (`mchild`/`macc`).
- `iris/HartSpanChar.v` — the six chain-peeling inversion lemmas (fully
  closed, zero axioms).

The M-mode cycle characterizations (all tail-generic over `KT`, so one proof
serves both ticks; the `riscv_step false` instances are kept byte-identical):

- `iris/HartMCycle.v` — `mwrap`/`mseg2_startK`; `mseg1_charK`: the wrapper
  prelude lands at the `minstret_increment` write. **The peel template.**
- `iris/HartMDispatch.v` — the dispatch is a `None` no-op at M-mode; the five
  unownable reads ∀-peeled once. Zero axioms.
- `iris/HartMPmp.v` — the ifetch PMP check allows at Machine with entries
  unlocked; **fuel induction** over `foreach_ZM_up'` with the loop body
  captured by ltac `context` match (never transcribed). Zero axioms.
- `iris/HartMFetch.v` — segment 2 assembled: post-chop → the fetch `MemRead`,
  with the mixed-file walker landing that leaves attach to.

Evidence:

- `iris/HartPilot.v` — the Phase B pilot at parity: one instruction at a
  concrete state, 3.6 s file, 0.2 s instantiation. **Its §6 header carries
  the rule/instance discipline** — read before writing any new rule.
- `iris/HartMLeaf.v` — `wp_word_main_b0`: the first per-word leaf,
  `WP Loop ⊢ WP Loop` through the honest wrapper at both ticks (dispatch,
  the PMP walks, fetch from text, decode+execute, the store, the tail
  including `tick_clock`). 2259 lines, 5 platform axioms.

## Left, in order

1. **`swp_of_pure_exec`** (design §5 item 7) — the `goodb` bridge ported.
   Highest value on the list: it collapses the decode cascade that a leaf
   currently peels by hand, which is where most of the per-leaf `Qed` cost
   sits. Needed whichever WP shape wins, so it is not blocked on item 2.
   Prove `mem_free` once for the decoder from its source structure.
2. **`swp`, the derived monadic WP** (design §5 item 6) — ~200 lines,
   additive, invalidates nothing. Prove `iMon` associativity + right unit
   (induction, funext at `Next`), then re-export the existing
   characterizations through bridge lemmas. **Land before item 4**: B′
   freezes the tree-wide interface shape, and `swp` is a better thing to
   freeze than landing-threading.
3. **The next leaf, and the verbatim-statement question.** `wp_word_main_b0`
   is per-word and raw-cell; the old tree's statement for this instruction
   is the shape-generic, bundle-taking leaf. Three deltas to close, in
   dependency order: (a) the bundles (`mmode_config`/`pc_is`/`gpr_file`/
   `instr`/`minstret_inv`) are all defined at or above the red line, so
   they cannot even be named until item 4 — that closes the raw-cell delta
   and folds the extra premises back in; (b) ∀-operand shapes need the
   once-per-INSTRUCTION-SHAPE decode characterization over the ENCODING
   FUNCTION (at `ext_decode (encode_itype imm rs1 rd)` the branch bits are
   the shape's, concrete, and the operand bits ride into the constructor);
   the seam to design there is that `instr` pins `decode w = i`, not
   `w = encode i` (non-canonical encodings), so either the per-shape lemma
   takes the encoding form as a premise — the `kd_` catalogue words are
   canonical and can supply it — or the `instr` premise is consumed
   per-word downstream; (c) the two remaining fetch shapes (2-aligned base,
   RVC) for leaves quantifying over `is_rvc`/alignment.
   **The design doc's Phase B/C gate — leaf specs preserved verbatim — is
   still open. Do not report it as met before a statement diff is empty.**
4. **Phase B′ — reconnect the tree** (the 971 files). Findings that set the
   plan, surveyed against the real statements:
   - Leaf SPECS are resource-shaped (cells in, cells out — no σ, no `exec`,
     no fupd), so "verbatim" is achievable; the σ-callback currency is
     INTERNAL to `wp_instr` and the mid-stack.
   - `wp_instr`'s exact statement is NOT re-derivable: its callback hands
     back `mstate_interp s_exec` inside one fupd, meaningful only when the
     instruction is one atomic step. Rebuild the same ALTITUDE with a
     per-event internal currency.
   - The `exec_execute_*` catalogue gets `swp`-form twins in the sweep
     (mechanical, `gen_code.py` style); decode (`kd_`) is consumed via
     `instr` unchanged.
   - Memory-class leaves route their data events through `HartEvents`;
     MMIO leaves keep σ-shaped device reasoning through the MMIO rules.
   - The clock/minstret absorption rebuilds on `HartRegNode`'s single-node
     rules; `sr_absorb`/interrupt engines are item 7.
5. **Phase C — the leaf sweep**, spec-identical; whole-function proofs must
   re-check unedited (a failure is a finding, not a patch).
   **Blocked on the Qed debt below** — do not start the sweep before it.
6. **Phase D — adequacy + capstones.** `RiscvAdequacy`/`SystemAdequacy`
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
`mval`** (design §5 item 8). The restart marker is the cheap,
independently-landable half; the payoff is `Atomic`/`iInv` for the
invariant-heavy leaves. Re-open only if the fupd-style event rules prove
painful once B′ puts those leaves back in scope.

## The Qed debt (blocks item 5)

`HartMFetch.mfetch_char`'s `Qed` is ~665 s and `HartMLeaf`'s exec
characterization's is ~671 s — 84 % of that leaf's 13 min. **Bisected**: the
cost is the kernel re-checking the GOAL-SIDE walk chain; the entire chain
side (~110 hypothesis rewrites plus the loop induction) rechecks in 5.6 s.
Statement-shape tricks are measured dead ends (`etransitivity` with an evar
RHS: 668.7 s; `remember`/`exact`: 664–680 s; both within noise of baseline).
The fix is to batch the walk's own reduction into once-stated per-stretch
helper equations — fewer, bigger conversion steps. Item 1 removes the decode
portion of it; the rest is the PMP/walk portion.

Per-leaf cost model for planning the sweep: ~2 minutes per leaf for
everything except that `Qed`, which does not scale and must be fixed first.

## Traps a fresh agent will otherwise re-discover

All measured; the first group is also in design §5's GOTCHA.

- Never `iApply` a kit rule at a composition-spelled cursor from a concrete
  call site; never state a cursor equation between two different spellings;
  never leave one in the context across `set_solver` (its `simplify_eq`
  whnf-evaluates both sides — 57 s); never write a bare `eq_refl` in
  argument position. Use the rule-at-abstract-cursors + instance-with-
  `reflexivity`-equations split (`HartPilot.wp_hart_rw_seq`).
- **vm is unusable past a resume application**, even at a concrete value:
  the resume's register-`decide` carries the Qed-opaque
  `register_encode_inj`, the `eq_rect` sticks, and readback then normalizes
  the whole dead instruction executor (>200 s). vm only for closed facts
  whose value is never consumed.
- The spine-reduction incantation for symbolic residuals is at
  `HartMCycle.mseg1_read3_at_local`: whitelisted
  `cbn beta iota zeta delta [bind/returnm spine]` rounds (the dead executor
  stays folded), then `rewrite !hregread_resume_red` — rewrite's unification
  beta-reduces `K v`, so one `!` steps every exposed read level — then
  bit-fact rewrites.
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
