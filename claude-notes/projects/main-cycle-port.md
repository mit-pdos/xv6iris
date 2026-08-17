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

## THE LEAF SWEEP: state, and the rule that makes it cheap

Nine leaf files plus `ProofSpin` are converted to the `swp` obligation, **14
statements verified byte-identical** (mechanically, against the pre-sweep
commit).  Green: `WpMmodeRtype`, `WpMmodeItype`, `WpMmodeShiftiop`,
`WpMmodeAddiw`, `WpMmodeMul`, `WpMmodeUtype`, `WpMmodeJal`, `WpMmodeJalr`,
`ProofSpin`.  Red roots: `WpMmodeLoad`, `WpMmodeStore`, `WpMmodeMret`,
`WpGprCsrrCommon`, `WpGprCsrwA` (2 of 4 leaves done), `WpGprCsrwB`,
`SmodeCore`.

**THE RULE, and it decides every case: ask whether the stretch WRITES.**

- **READ-ONLY, however deep its recursion → `HartGoodb.hval_of_goodb`.**
  `goodb` is `vm_compute`d at `dstateM` and the `exec` fact is the one the
  exec-based stack already proved.  This is what makes
  `currentlyEnabled Ext_Zicfilp` (four levels of guarded recursion) and
  `check_CSR_result` (ditto) free instead of a reduction project.  Their read
  sets are both inside `WpDecodeBridge.D_m` = {cur_privilege, mseccfg, misa},
  which is why `cw_Dro` is exactly those three.
- **WRITES → hand-walk with `hfrun`.**  `goodb` rejects writes outright.
  `jump_to` and `write_CSR` went this way; both are a handful of nodes at
  CONCRETE registers once the spine is reduced with a whitelisted `cbn`.
  `try_catch` is a Fixpoint over the term, not a node, so it pushes THROUGH
  reads and writes and vanishes — `catch_early_return` costs nothing.
- **A SYMBOLIC register index is the only thing no walker takes.**
  `rX_bits`/`wX_bits` at a quantified operand is where every leaf peels:
  `HartMFrame.swp_rX_file` / `swp_wX_file` (at `gpr_file`, so operand
  aliasing is free), or `WpMmodeJump.swp_wX_zero` when the destination is x0.

**WHEN A LEMMA'S PREMISE IS AN `hfrun` FACT, IT ONLY WORKS AT CONCRETE
OPERANDS.**  Twice now the fix was the same: make it a `swp` OBLIGATION and
keep the `hfrun` form as a corollary for the pilot.  `swp_vmem_write_gen`
(address computation) and `swp_doCSR_csrw` (the CSR write) both did this, and
`swp_execute_STORE` still wants it.  An abstract rider `Q` carries `gpr_file`
through such an obligation; the GPRs stay OUT of every footprint.

**A REAL LIMIT OF THE `goodb` CERTIFICATE, isolated and measured.**
`HartGoodb.hval_of_goodb`'s second premise is *pointwise* agreement between the
caller's file and the reference on every register the stretch READS:

    (forall r, Db r = true -> register_lookup r rs = register_lookup r dst.(sregs))

so the route only works when every read register's value is **pinned by the
reference state**.  True for the decode and for `check_CSR_result` (they read
only cur_privilege / mseccfg / misa, all fixed by `hw_config`).  FALSE for
`write_CSR csr_menvcfg`, which reads `menvcfg` — the leaf's own variable.  No
generalization of the certificate fixes this: adding write-tracking (a
`goodbw`) would not touch that premise.  I proposed exactly that and it was
wrong; the read-agreement requirement is the binding constraint.

And a second, independent limit: **`goodb` is not COMPUTABLE when the certified
stretch carries symbolic data.**  `goodb D_m (legalize_menvcfg o v) dstateM`
with `o`/`v` free does not finish under `vm_compute`, `cbv` or `lazy` (measured:
>100 s each, and >15 GB inside a proof).  goodb's ANSWER does not depend on that
data — only on guards driven by misa at `dstateM` — but the evaluators normalise
the symbolic bitvector expressions anyway.  Every other `goodb` use in the port
is at concrete arguments, which is why this had not shown up.

Consequence for the CSR family, counted rather than guessed:
- **7 of 10 are on the proven cheap path** — the write is shallow register
  traffic and `hfrun` walks it (`medeleg`, `mcounteren`, `mepc` done or
  written; `stimecmp`, `sie`, `pmpaddr0`, and `WpGprCsrrCommon`'s).
- **3 hit the wall** — `menvcfg`, `mideleg`, `satp`, whose writes wrap a
  MONADIC legalization parameterized by the old value and `v`
  (`legalize_menvcfg` / `legalize_mideleg` / `legalize_satp_rv64`).
- Those 3 are on the CRITICAL PATH, not optional: a file is green only when all
  its leaves are, so `WpGprCsrwA` needs menvcfg and `WpGprCsrwB` needs mideleg
  and satp.

The route for the 3: peel the legalization at the swp layer.  Each reads misa
ONLY (~4-5 reads, via `currentlyEnabled`), and misa is pinned in `cw_Dro`, so
every read is one `swp_read_reg_pinned` and the rest is pure data — roughly ten
`swp_bind_use` steps per legalization, written once each.

**AND A HARD-WON TACTIC RULE, both directions measured:**
- NEVER prune `write_CSR`'s ~90-way dispatch inside a `swp` goal.  The exec
  stack's `skip_csr_false_clauses` is `exec`-shaped so it matches nothing there,
  and the expansion meets the whole `envs_entails`: 23 GB, OOM at 8 minutes.
  In a PURE term-equation goal the same peel is **2.5 s**.
- When a reduction has to be NAMED, PRINT IT — do not write it from the model
  source.  `write_CSR csr_menvcfg`'s surviving clause associates as
  `bind (bind0 write read) k`, not `bind0 write (bind read k)`.  Guessing wrong
  makes the closing `reflexivity` grind on two ISA-sized terms, and it looks
  exactly like the blowup above.

**THE REMAINING LEAVES, MAPPED BY WHAT THEY OWN — this is the map to work from.**
Surveyed by extracting each leaf's own `↦ᵣ` premises and comparing against what
its `execute` writes.  Three groups, and only ONE of them touches the wrapper:

1. **Leaves that OWN every cell they write — no wrapper change needed.**
   `WpGprCsrwB`'s `mideleg`, `satp` (the menvcfg three-step recipe: assemble the
   `goodb` certificate, prune the dispatch in a pure goal, read off the clause),
   `sie` (writes `mie`, and owns `mie` + `mideleg`), `pmpaddr0` (writes
   `pmpaddr_n`, owns it).  `WpGprCsrrCommon` owns nothing and only writes rd.

2. **ONE genuine obligation gap: `wp_csrw_stimecmp_gpr` writes `mip`.**
   `mip` is a CLOCK cell — it arrives via `pc_is` → `clock_res` and is therefore
   in `mm_Drw`, held by the wrapper for the whole obligation.  The leaf's
   statement does not mention it, so it cannot write it.  Fix: lend `mip` in the
   obligation exactly as `PC` is lent (writable, returned at whatever the
   instruction left).  Cost: one more lent cell plus a two-token edit in each of
   the 13 converted leaves' obligation proofs.  Nothing else in the leaf set
   writes `mcycle`/`mtime`/`minstret`, so this is the LAST obligation change.

3. **`wp_instr_config` must be rebuilt — MRET and the two `_raw` CSR leaves do
   not take `mmode_config` at all.**  `wp_mret_gpr`, `wp_csrw_mstatus_raw` and
   `wp_csrw_pmpcfg0_raw` take `hw_config` plus `hart_state` / `cur_privilege` /
   `mstatus` at FULL ownership.  That is not an accident and `wp_instr` cannot
   serve them: MRET *changes* cur_privilege (Machine -> Supervisor) and mstatus,
   so the bundle is NOT invariant across the instruction and `mmode_config`
   cannot be handed in and taken back.  The old stack had `wp_instr_config` for
   exactly this (3 call sites); it was deleted in this port and has to come
   back, as a raw-cell wrapper whose config cells are exclusive and may change.

**AND A FORCED STATEMENT CHANGE, the first in the sweep.**  Those same three
leaves take `minstret_inv` as a premise, and `minstret_inv` no longer exists —
the counter facts moved into `pc_is`'s `minstret_res` when invariants became
owned resources.  The premise must be DELETED from their statements.  That is a
weakening (the lemma gets stronger), so it is benign for the theorem, but it IS
a statement diff and callers stop supplying it.  It is the only statement change
the sweep has needed so far; the other 17 leaves are byte-identical.

**WHAT REMAINS, per family:**
- `WpGprCsrwA/B`, `WpGprCsrrCommon` (8 leaves): substitution, plus one write
  peel each.  Same-shaped CSRs (read old / write legalized / read back) are
  PURE SUBSTITUTION — `mcounteren` was `medeleg` with the name changed.
  `menvcfg`/`mepc` wrap a read-only legalization (`legalize_menvcfg`,
  `legalize_xepc`) around their store: goodb the legalization, cell-write the
  store.  There is NO per-CSR legality lemma — `check_CSR_result` at
  `dstateM` is `vm_compute; reflexivity` for every csr.
- `WpMmodeLoad`/`WpMmodeStore` (6 leaves): every one is **width 8** and
  `HartMStore`'s chain is hardcoded to 4 (37 sites: `mem_write_ea`,
  `split_on_page_boundary .. 4 = (4,0)`, `subrange_vec_dec d 31 0`, the
  4-alignment side conditions).  A width sweep of the same kind the 2-byte
  fetch needed.
- `WpMmodeMret`: the only leaf that pushes on the obligation.  It WRITES
  mstatus and cur_privilege, so the `mmode_config_split` trick that carried
  JALR/JAL/CSR does not apply — it needs those cells exclusively.
- `SmodeCore`: reuses `HartMCycle.swp_exec_step_decode_execute` verbatim (that
  rule is mode-agnostic on purpose); needs its own ~30-line `s_cycle` and its
  own fetch.

**THE DOWNSTREAM CLAIM IS UNVERIFIED.**  770 of 1179 files sit behind the red
roots, so no whole-function proof has been re-checked.  Leaf statements being
identical is necessary, not sufficient.  Known exposure: 6 files DESTRUCTURE
`pc_is` (`WpIntrInv`, `WpSmodeIntr`, `WpSmodeWfi`, `UserKernelBridge`, …) and
each needs the one-line fix `ProofSpin` needed, because `pc_is` now carries
`minstret_res ∗ clock_res`.

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
2. **Phase B′ — reconnect the tree** (the 971 files).

   **THE LADDER, MEASURED.**  Between the 135 leaf-instruction call sites
   and what this port has already rebuilt there are exactly four rungs:

   | rung | what | count |
   |---|---|---|
   | leaves | `wp_or_gpr`, `wp_jalr_gpr`, … | 135 sites / 38 files |
   | wrappers | `wp_instr` (33), `wp_instr_s_sconf` (68), `wp_instr_s_config_regime` (14), `wp_instr_config` (3), `wp_instr_s_regime` (2), `wp_instr_s_intr` (1) | 6 |
   | decode+execute | `InstrBytes.wp_exec_step_decode_execute_inv`, `SmodeCore.wp_exec_step_decode_execute_inv_priv` | 2 |
   | cycle | `wp_exec_step_hart_active_inv` → … → `wp_exec_step` | DONE (deleted; `HartMCycle.swp_try_step_gen` / `wp_loop_cycle`) |

   **THE LEAF STATEMENTS SURVIVE VERBATIM, and that is the thing to
   protect.**  They are resource-shaped -- `mmode_config dq`, `pmpcfg_n ↦ᵣ`,
   `pc_is`, `gpr_file m`, `instr pc is_rvc i`, continuation, `WP Loop` -- with
   no σ, no `exec`, no fupd anywhere.  `mmode_config` is one of their premises,
   which is exactly where the counter/clock cells are going, so even that stays
   byte-identical.

   **WHAT CANNOT SURVIVE is the wrapper's OBLIGATION**, and it is the port's
   real semantic content rather than an artefact:

       (∀ σ, register_lookup PC σ.(sregs) = pc ->
          mstate_interp σ ={⊤ ∖ ↑minstretN}=∗
          ∃ s_exec, ⌜exec (execute i) (set_reg σ nextPC …)
                      = Some (RETIRE_SUCCESS, s_exec)⌝ ∗
                    mstate_interp s_exec ∗ (… -∗ ▷ WP Loop))

   It hands the caller ALL of σ and asks for the successor in ONE fupd.  Under
   per-node stepping other harts run between the instruction's nodes, so a
   successor computed from the σ you saw is stale unless you can argue nothing
   you depend on changed -- and THAT argument is exactly a declared footprint,
   i.e. a frame.  (`prim_step_hart_regs_frame` would rescue the register-only
   families, since `sig_seip` is the only cross-hart register write; it does
   not rescue memory, and the SAME wrapper carries loads and stores --
   `WpMmodeLoad`/`WpMmodeStore` both go through `wp_instr`.)

   **THE REPLACEMENT** is one uniform obligation, `swp (execute i) Φ`:
   register-only instructions discharge it with `swp_hfrun` off `hfrun` twins
   of the `exec_execute_*` catalogue; memory instructions with the event rules
   plus the `R`-threaded memory obligation, which is the shape
   `HartMStore.swp_execute_STORE` already has.  Uniformity is preserved --
   the old obligation was uniform too.

   **COST, and why it may be cheaper than it looks:** the 135 proof SCRIPTS
   change, the statements do not.  A typical leaf (`WpMmodeRtype.wp_or_gpr`)
   is ~50 lines of which ~40 are σ plumbing -- `reg_update`, `gpr_pt_value`
   off `Hreg`, naming `s_exec` as a `set_reg` tower -- that a frame-shaped
   obligation deletes outright.  `gpr_file m` IS already a frame: the leaves
   already declare their footprint and merely convert it into σ-reasoning.

   **THE DECODE'S CURRENCY: DECIDED, and the generated corpus is untouched.**
   `swp_run_hart_active_base`/`_rvc` want the decode as a FOOTPRINTED fact;
   the `instr` bundle supplies it as `exec (decode_fetch r) σ = Some (i, σ)`.
   The fix is NOT to re-prove the decode catalogue (3752 `kd_` lemmas across
   33 `KernelDecode*.v`) -- it is one bridge lemma, because the missing
   ingredient already exists:

   `WpDecodeBridge.goodb D m s` is a COMPUTABLE certificate that `m` run from
   `s` reads only `D`-registers and hits nothing else (memory, Choose,
   failures all give `false`), and every generated proof already establishes
   it by `vm_compute` -- that is what `decode_state_bridge` consumes.  The
   decoder's read set is pinned and tiny: `D_m = {cur_privilege, mseccfg,
   misa}`, `D_s = {cur_privilege, menvcfg, misa}`.

   `goodb` is exactly the "reads only `D`, touches no memory" hypothesis that
   made a general `exec` → footprint bridge look circular.  With it:

     hval_of_goodb :
       (forall r, Db r = true -> r ∈ D) ->
       reg_agree_on <Db> rs dst.(sregs) ->
       goodb Db m dst = true ->
       exec m dst = Some (x, dst) ->
       hval D Drw rs m x rs

   Target `hval`, NOT `hfrun`: `hval` is fuel-free, so no fuel enters the
   interface.  `swp_span` takes `hval` directly, and existing `hfrun` callers
   (the pilot) still reach it through `hfrun_hval`.

   **A GAP THE PILOT HID: THERE IS NO 2-BYTE FETCH PATH.**  Every rule in
   `HartMFetch` (`swp_fetch_bytes_M`, `swp_fetch`, `swp_fetch_M`,
   `swp_fetch_ram`) assumes `neq_vec (access_vec_dec pc 0) zerobit = false`
   AND `... pc 1 ... = false` -- i.e. 4-ALIGNMENT -- and is hardcoded to
   `fetch_bytes pc pc 4`.  The model's `fetch` branches on bit 1 of the PC:
   at a 2-mod-4 address it reads a HALFWORD, sees `isRVC`, and stops.
   `instr_bytes` already knows this -- its `F_RVC` arm carries four bytes
   when `is_aligned_vaddr … 4` and only TWO otherwise.

   The pilot never exercised it (`main+0xb0` is 4-aligned, which is why its
   fetch is one 4-byte read), so the gap was invisible until `wp_instr` --
   which must work at ANY 2-aligned pc, and roughly half the kernel's
   compressed instructions sit at 2-mod-4 addresses.  `swp_fetch_bytes_2`
   and the `F_RVC`-at-2-mod-4 fetch rule are REAL WORK and belong before
   `wp_instr`, not inside it.

   THE PLAN, in order:
     1. prove `hval_of_goodb` (induction on the monad; `goodb` and `hfrun`
        are near-identical structural walkers, so the arms line up);
     2. change `swp_run_hart_active_*`'s decode premise from `hfrun nd …` to
        `hval …`;
     3. change `instr`'s decode component to the `hval` form;
     4. re-prove `instr_intro_base`/`instr_intro_rvc` via `hval_of_goodb`,
        from the SAME `goodb` + `exec` evidence they already take.

   `mk_rvc` / `mk_base`, all 3752 `kd_` lemmas and every `Code*.v` are
   UNCHANGED -- the two Ltacs are the only interface the generated corpus
   has, and their arguments do not move.

   **DO NOT GRIND.**  Rebuild the 2 decode+execute rules and the 6 wrappers,
   then convert ONE leaf of each family by hand -- an ALU one, a JALR, a load,
   a store -- before touching the other 131.  If those four diffs are not
   mechanical, the wrapper shape is wrong and wants redesigning, not grinding.
  Findings that set
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
- **A footprint (`hfrun`/`swp_hfrun`) CANNOT run an instruction with
  SYMBOLIC operands**, and every leaf in the tree has symbolic operands
  (`wp_or_gpr` quantifies `rs2 rs1 rd : mword 5`).  `hfrun` answers a
  register read by `bool_decide (r ∈ D)`, which does not compute at a
  symbolic index.  This kills the whole "convert `gpr_file` into
  `hreg_frame` so the leaf can use `swp_hfrun`" plan -- the GPRs do not
  belong in the wrapper's footprint at all.  What a leaf needs is per-NODE
  access at a symbolic index, which is `HartRegNode`'s σ-shaped
  `swp_hart_regread`/`swp_hart_regwrite`, needing no frame; see
  `HartMFrame.swp_rX_bits`/`swp_wX_bits`, proved once by the same 32-way
  `lia` case split `WpGpr.exec_rX_bits_gpr` already uses.
- **`vm_compute` does NOT normalise a `regidx`'s WIDTH INDEX, so computed
  register keys never syntactically match hand-written `k%bv` literals.**
  Measured with `Set Printing All`: the literal is
  `@BV 5 5 I`, while a key read out of `map_to_list (rf_to_gmap m)` is
  `@BV (MachineWord.Z_idx (match false return Z with true => 4 | false => 5
  end)) …` -- the width stays a stuck `match` on the xlen config bool.  The
  two are CONVERTIBLE but not syntactically equal, so `reflexivity` succeeds
  while `exact`, `iFrame` and every intro-pattern match FAIL, with an error
  that prints the two types identically ("has type X while it is expected to
  have type X").  Consequence for register-file bridges: build them with
  `big_sepM_delete` at keys you WRITE, never by computing the key list.
- Background builds must `cd` into `iris/` themselves: `make -f CoqMakefile`
  from the repo root fails with "No rule to make target 'CoqMakefile'", and
  a shell whose cwd drifted between commands is the usual cause.
