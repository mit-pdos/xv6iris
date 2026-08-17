# main-cycle-port — worklist

Design: [`design/main-cycle-port.md`](../design/main-cycle-port.md). **Read
it before touching anything here** — every settled decision lives there, not
in this file: the per-node semantics, batching-as-a-theorem, the span rule
(§5 item 1c), the monadic WP layer and why `mval` stays empty (§5 items 6–8),
the pure-exec bridge (§5 item 7), and §5's GOTCHA, which is the list of
measured ways to make a proof take minutes instead of milliseconds.

## CHECKPOINT

Branch `hart-node-port` (off `main`).  The port replaces the whole-instruction
hart step with a per-node one, so a page walk, a TLB fill, a fetch and a data
access of one instruction can interleave with other harts.

**BOTH WRAPPERS ARE DONE AND THE CSR FAMILIES ARE GREEN.**  No admits anywhere;
`wp_instr` closes at exactly the 5 rv64d platform axioms.  The sweep has needed
**zero leaf statement changes** (18 verified byte-identical against the
pre-sweep commit `0bac621b`).

Last counted: **450 of 1183 `.vo`, seven red roots.**  Do not trust that —
rerun `make -f CoqMakefile -jN -k` and recount; the numbers here have gone
stale before.

GREEN: `WpMmodeRtype`, `WpMmodeItype`, `WpMmodeShiftiop`, `WpMmodeAddiw`,
`WpMmodeMul`, `WpMmodeUtype`, `WpMmodeJal`, `WpMmodeJalr`, `WpGprCsrwA` (4
leaves), `WpGprCsrrCommon`, `WpGprCsrrA` (3), `WpGprCsrrB` (3),
`WpGprCsrwB` (4), `WpGprCsrwC` (2), `WpInstrRun`, `WpInstr`, `WpInstrConfig`,
and `ProofSpin` (a whole-function proof, by Löb — the wrapper survives Löb,
which was worth knowing).  **Sixteen CSR leaves in all**, which is every CSR
instruction this kernel executes except `csrw stimecmp`.

RED ROOTS, with what each needs and what it GATES (dependent counts off
`.CoqMakefile.d`; rerun the count, do not trust it):

| file | dependents | needs |
|---|---|---|
| `WpIntrCore` | 711 | THE INTERRUPT-ENTRY ENGINE.  Its cycle rule now EXISTS (`HartMIntr.swp_exec_step_any`); what is left is the S-mode `run_hart_active` with a DISJUNCTIVE conclusion — see §"the arm nobody can pick".  Also blocks `WpSmodeWfi` (needs the `Enter_Wait` arm too) and `UserStepFull` |
| `SmodeCorePt` | 464 | the S-MODE FETCH (Sv39 + TLB), then `wp_instr_s` / `s_cycle` on it.  `TrampStepPt` (19) is the same story |
| `WpMmodeLoad` | 8 | width-8 sweep of `HartMStore` |
| `WpMmodeStore` | 7 | ditto |
| `WpGprCsrwStimecmp` | 7 | the cycle rule's post-file as a PREDICATE, so a leaf may write mip — see §"the two cells a leaf cannot have" |
| `WpMmodeMret` | 6 | the MRET walk plus a value-preserving write rule for elp — same § |
| `RiscvAdequacy` | 2 | one `discriminate` over the language's step relation ("No primitive equality found" at line 907) |

**TWO ENGINES GATE THE TREE; THE LEAVES DO NOT.**  The four M-mode leaf roots
are worth 6–8 files each.  `WpIntrCore` is worth 711 and `SmodeCorePt` 464.
**Do not judge the remaining work by the number of red roots** — it is three
ENGINES (fetch/execute, done; interrupt entry; the S-mode fetch) and then
everything else follows.

`SmodeCore.v` itself is green now: its blocker was the dead engine
`wp_exec_step_decode_execute_inv_priv`, deleted for the reason the M-mode one
was — it hands the caller the whole machine state and asks for a successor in
one fupd.  Deleting it turned 22 more files green and revealed the two real
gates above.

**IMMEDIATE NEXT STEPS, in the order I would do them:**
0. **THE S-MODE `run_hart_active`, DISJUNCTIVE** — see §"the arm nobody can
   pick".  Its cycle rule is done; this is what feeds it, and it is also the
   entry to the fetch.  The two engines turn out to be ONE piece of work, not
   two: the interrupt arm cannot be reached without going through the same
   rule the fetch does.
1. **The S-MODE FETCH itself** — `swp_fetch_ram`'s twin through Sv39 and the TLB.
   Everything else on that side reuses M-mode machinery: the cycle rule
   (`swp_exec_step_decode_execute`) is already privilege-agnostic, the four
   fetch SHAPES are `WpInstrRun.swp_run_hart_active_instr`'s business, and
   `instr` itself is privilege-generic by construction.  What is genuinely new
   is one fetch that WALKS, and it is the reason the port exists — a page walk
   interleaving with other harts is the thing whole-instruction stepping could
   not express.
2. **`wp_instr_s` + `s_cycle`** on top of it (the `mm_cycle` / `wp_instr` pair,
   with the S-mode bundle), then the three call sites.
3. **Load/Store** — volume, no new machinery: every leaf is a width-8 access
   and `HartMStore`'s chain is hardcoded to 4 (`mem_write_ea`, the
   `split_on_page_boundary .. 4 = (4,0)` premise, `subrange_vec_dec d 31 0`,
   the 4-alignment side conditions).  Generalize over the width with the
   arithmetic facts as PREMISES — width 4 is still live (it is the
   `HartMLeaf` pilot's `c.sw`), so this is a generalization and not a
   conversion.  `swp_vmem_write_gen` already takes the address stretch as an
   obligation, which was the part blocked on the wrapper's shape.
4. **The cycle-rule generalization**, then `stimecmp`.
5. **MRET**, independent of (4), needs only the elp rule.

### The two cells a leaf cannot have

Both remaining M-mode leaves fail for the same reason and in opposite
directions, and the analysis is done in both cases:

**mip, for `csrw stimecmp`.**  `write_CSR csr_stimecmp` calls
`clint_dispatch`, which refreshes mip from the CLINT: it reads mtime /
mtimecmp / stimecmp / the plic wires (∀-peels, nothing owns them) and then
WRITES mip.  mip is in `mm_Drw` — the cycle wrapper owns it, exclusively,
because the tick writes it.  Lending it to a leaf is sound, and the reason is
already in the cycle rule: `mm_tick_agree` constrains the post-file only OFF
`tk_clock3`, and mip ∈ `tk_clock3`.  What blocks it is that
`swp_exec_step_decode_execute` takes the post-file `rsB` as a PARAMETER, so
the body cannot choose it.  The fix is to take a PREDICATE instead (which is
what `wp_loop_cycle`/`swp_try_step_gen` already do one level down — the
specialization to `rsx = wrap_post rsB mi` happens in
`swp_exec_step_decode_execute` itself), thread it through `mm_cycle` and
`wp_instr_ex`, and hand the leaf the mip cell in and an arbitrary one back.

**elp, for MRET** (and the recipe, since the walk is scoped now).    MRET writes elp with the value it already holds
(`NO_LP_EXPECTED`, forced by `hw_config`'s pin), so the write is a no-op —
but `hw_config` holds elp at `DfracDiscarded`, so no leaf can own it, and
**the span semantics genuinely forbid the step**: `hspan_node` gates a write
on `r ∈ Drw` with no value-preserving exception, and adding one is not
possible without making `hspan_stops` file-dependent (it is a bool on the
term, and a term that both may step and is a stopping point makes `hval`
unprovable).  So the walk must SPLIT at that node and use a `swp`-level rule, and
**`HartRegNode.swp_write_reg_same` is that rule and is proved** (the trap
handler's `reset_elp` needs it too, which is why it lives there and not in a
leaf file).  The
surrounding walk is ~25 nodes; its exact order is known (print the reduced
term -- see the traps section -- which gives the whole chain: 4 cur_privilege
reads, ~8 mstatus reads, 5 mstatus writes producing `cms1`..`cms5`, the
cur_privilege write, the elp reset, and the tail through
`prepare_xret_target` / `set_next_pc`).

WHAT MAKES IT MORE THAN A WALK, measured while scoping it: the sub-calls need a
FRAME, not cells, so the leaf wants a 6-cell footprint of its own —
Drw = {mstatus, cur_privilege, nextPC}, Dro = {misa, menvcfg, mepc} — with the
three writables as tower parameters plus the usual agreement lemma, in the
`cw2_*` style.  Which sub-call needs which:

- `currentlyEnabled Ext_U` and `Ext_Zca` read ONLY misa (checked:
  `ExecCommon.exec_currentlyEnabled_U` has just the misa.U premise), and misa
  IS reference-pinned, so both can go through `hval_of_goodb` at
  `D0 := D_misa` rather than at `D_m` — which matters, because by then
  cur_privilege is no longer Machine and `agree_m` would not hold.
  `HartMRun.hfrun_cE_Zca` already exists for the Zca one.
- `hartSupports Ext_Zicfilp` and `long_csr_write_callback` are pure: term
  equations by `vm_compute`.
- `get_xLPE Supervisor` reads menvcfg and its RESULT depends on the value, so
  it CANNOT be transported from the reference state (the leaf knows only that
  menvcfg's LPE bit is clear, not the whole value).  It needs an `hfrun` at the
  leaf's own frame — which is the reason menvcfg is in Dro above.
- `prepare_xret_target Machine` reads mepc, then `align_pc` (the Zca call).

So: the footprint family first, then the walk is uniform.

### The arm nobody can pick

`dispatchInterrupt` reads the PLIC WIRES: `read_mip IncludePlatformInterrupts`
ORs `sig_meip` / `sig_seip` into mip, and those cells live in
`WireInv.wire_inv`, not in any frame.  Under per-node stepping another hart may
move them BETWEEN the dispatch's nodes, so **whether a cycle retires an
instruction or takes a trap is the machine's choice, and no caller can promise
it.**  A one-armed interrupt rule is therefore unusable — I proved one and
deleted it.

M-mode is exempt and that is not luck: at Machine privilege with mstatus.MIE
clear the dispatch short-circuits BEFORE the wires
(`HartMDispatch.swp_dispatchInterrupt_M`), so `wp_instr`'s one-armed rule is
both sound and complete for this kernel.  The S-mode side has no such
shortcut.

`HartMIntr.swp_exec_step_any` is the rule this forces, and it is proved.  What
feeds it is the piece to write next:

**an S-mode `run_hart_active` rule with a DISJUNCTIVE conclusion** —

    swp (run_hart_active 0)
      (fun st => (∃ w, ⌜st = Step_Execute (RETIRE_SUCCESS, w)⌝ ∗ <execute post>)
                 ∨ (∃ i p, ⌜st = Step_Pending_Interrupt (i, p)⌝ ∗ <frames, unchanged>))

i.e. peel the privilege read and the dispatch, and on `Some` land in the second
disjunct with the state untouched (the dispatch only reads), on `None` continue
into the fetch exactly as `WpInstrRun.swp_run_hart_active_instr` does.  It has
to be ONE rule rather than a caller-side case split, because the region is
inside `catch_early_return` and the continuation after the dispatch is not a
nameable model function — the four `swp_run_hart_active_*` rules are where the
dispatch is peeled, so that is where the disjunction belongs.

That rule is also the entry point to the S-MODE FETCH, which is the other big
piece: `SmodeCorePt.s_regime_fetch` is the exec-side version (a bupd over the
`s_regime` abstraction: `sr_inv` / `sr_absorb`, producing `exec (fetch tt) σ =
Some (r, σf)` plus σf's frame properties), and its `swp` twin is the work.  It
WRITES (the TLB fill), so it is not a `goodb` transport; it is a walk with
memory events, the shape `HartMFetch.swp_fetch_ram` has in M-mode.

**`minstret_inv := emp`, PERSISTENT, ON PURPOSE (MinstretInv.v).**  The Iris
invariant is gone — counter facts are owned resources in `pc_is`'s
`minstret_res` — but three leaves still take it as a premise and deleting it
would have been the sweep's only statement change.  It carries no information.
**Delete it once the tree is green**, as a standalone premise-removal commit.

**THE DOWNSTREAM CLAIM IS STILL UNVERIFIED.**  Most of the tree sits behind the
red roots, so no whole-function proof but `ProofSpin` has been re-checked.
Identical leaf statements are necessary, not sufficient.  Known exposure: 6
files DESTRUCTURE `pc_is` (`WpIntrInv`, `WpSmodeIntr`, `WpSmodeWfi`,
`UserKernelBridge`, …) and each needs the one-line fix `ProofSpin` needed,
because `pc_is` now carries `minstret_res ∗ clock_res`.

Where to read next: the "THE LEAF SWEEP" section below (the rule that decides
every remaining case, and the per-family costs), then `iris/WpInstr.v`
(`wp_instr_ex` + `wp_instr` + `mm_cycle`), `iris/WpInstrRun.v` (the fetch
dispatch both wrappers share), `iris/WpInstrConfig.v` (the raw-cell wrapper),
`iris/HartMCycle.v` (`swp_exec_step_decode_execute`, mode-agnostic on
purpose), and `iris/WpMmodeCsrSwp.v` (both CSR engines and the three
footprints).

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

## MACHINERY INVENTORY (what this port added, and where)

| where | what | why it exists |
|---|---|---|
| `HartMCycle.swp_exec_step_decode_execute` | the cycle rule: resources in, ONE obligation, resources back with PC at the new value | replaces `wp_exec_step_decode_execute_inv`.  **MODE-AGNOSTIC ON PURPOSE** — no privilege, misa or mstatus.  S-mode reuses it verbatim; baking M-mode in here was a bug I had to undo |
| `HartMIntr.swp_try_step_any` / `swp_exec_step_any` | the cycle rule that does NOT pick the arm: the body's postcondition MATCHES on the step reached, and the post-file is a PREDICATE | `dispatchInterrupt` reads the PLIC wires, which live in `WireInv.wire_inv` and can move BETWEEN the dispatch's nodes, so no caller can promise whether a cycle retires or traps.  The predicate post-file is independently what `csrw stimecmp` needs.  `swp_try_step_gen` / `swp_exec_step_decode_execute` are the singleton-`Q`, retire-only instances and should become instances at the fold-back |
| `HartMCycle.swp_step_ex` | introduces the fetched word's existential | the word must be existential in the obligation, or a caller that dispatches on fetch SHAPE cannot instantiate it per branch |
| `HartMCycle.reg_agree_l/_r` | footprint weakening | |
| `HartMCycle.wrap_pre_*` / `wrap_post_*` | cell-by-cell reads of the tick's pre/post files | |
| `WpInstrRun.swp_run_hart_active_instr` | the FETCH-SHAPE DISPATCH: takes the `instr` resource, dispatches on the fetch result inside it and on pc's 4-alignment | the fifth member of `HartMRun`'s family and the only one a wrapper calls; the other four each take a concrete shape.  Both wrappers share it, so adding a wrapper costs its own bundle bookkeeping and nothing else |
| `WpInstr.wp_instr_ex` | the engine: post-GPR-file EXISTENTIAL | `csrr rd, time` reads mtime, which the tick writes, so no leaf can pin the value before the step and none can NAME its post-file.  `wp_instr` is the instance that names it |
| `WpInstr.wp_instr` | THE leaf wrapper, all four fetch shapes | takes `npc` explicitly (the old one recovered it from `s_exec`); lends PC read-only for AUIPC/JAL |
| `WpInstr.mm_cycle` | the M-mode instance of the cycle rule | adds only the two bundle↔frame bridges |
| `HartMFrame.swp_rX_file` / `swp_wX_file` | GPR access at `gpr_file`, not at three cells | operand ALIASING is free this way; an instruction may name the same register twice |
| `HartRegNode.swp_write_reg_same` | the WRITE THAT CHANGES NOTHING: write a register you do not own, with the value already there | the span CANNOT express this (its write case is gated on `r ∈ Drw`, and `hspan_stops` is a bool on the TERM, so a node that both steps and is a stopping point makes `hval` unprovable) -- so a walk that meets one SPLITS at it and takes this rule.  Both clients are the elp reset: MRET's, and the trap handler's.  Rests on `RiscvPtsto.reg_interp_set_same` |
| `HartMFrame.swp_read_reg_cell` / `swp_write_reg_cell` | register nodes at ONE owned cell | `HartSpanChar`'s pair is frame-shaped, right for the wrapper, wrong for a leaf |
| `HartMFrame.mm_rw_ext` / `mm_ro_ext` / `mm_rw_open` / `mm_rw_close` | DIRECTED frame bridges | a `⊣⊢` rewrite in a proofmode goal cost ~110 s at one site; these are free |
| `HartMFrame.mm_rs_agree`, `mm_rs_ro_agree`, `mm_npc_agree`, `mm_ro_nPC` | tower transports | see the two-tower trap in `optimization.md` |
| `WpMmodeSwpBase` | the NODE SHAPES: `swp_execute_rw`/`rw2`/`rrw`/`rrw2`/`w`/`pure_w`/`pcw` | every register-only instruction is one of these; each takes the model's reduction as a hypothesis discharged by `eq_refl`, so an instruction family is one-line corollaries |
| `WpMmodeJump` | `hfrun_jump_to_zca`, `hval_update_elp_state`, `swp_jump_to_zca`, `swp_execute_JALR_ret`, `swp_execute_JAL`, `swp_execute_JAL_zreg`, `swp_wX_zero`, the `cw_Drw`/`cw_Dro` footprint | the first family needing both routes |
| `WpMmodeCsrSwp` | `swp_doCSR_csrw`, `swp_execute_CSRReg_csrw`, `cw_rs`/`cw_fresh`/`cw_frames`/`cw_set_agree` | one lemma for all ten CSR writes; the write is an OBLIGATION, not an `hfrun` fact |
| `WpInstrConfig` | `wp_instr_config` + `mc_cycle` + `mc_rs` (cur_privilege PARAMETRIC) + `mc_ro_acc` | the wrapper for the three instructions that WRITE the cells `mmode_config` bundles, where "hand the bundle in, get the same bundle back" is the wrong contract.  THE FOOTPRINT IS UNCHANGED: a cell is in `Drw` so the WALKER may write it; these are written by the LEAF, which holds them as points-to during the instruction |
| `WpMmodeCsrSwp.swp_doCSR_csrr` / `swp_execute_CSRReg_csrr(_gen)` | the READ engine, mirror of the write one | the CSR read is an obligation for the reason the write is: `read_CSR` is read-only, so `goodb` certifies its SHAPE, but its VALUE is the caller's register content.  `_gen` carries an abstract `Q` on the read value, for the CSR nobody owns |
| `WpMmodeCsrSwp.cr_*` / `cr0_*` / `cw2_*` | three footprints: read with one owned cell, read with none, write with one EXTRA read cell | a csrr writes nothing (rd is in `gpr_file`, outside every frame), so its writable half is EMPTY; `cw2` covers sie/satp/pmpaddr0, whose written value comes from a second cell |
| `WpMmodeCsrSwp.hval_read_any` / `hval_ret` | ∀-peel a read of a register NOBODY owns | `hfrun` answers reads from the pinned file, so it needs them owned; the span's read case is ungated, so a stretch whose RESULT ignores the value needs neither.  `HartMCycle.tick_clock_hvalE`'s `tk_peel_any` move, as a lemma.  **Belongs in `HartSpanChar` once a second family wants it** |
| `WpMmodeCsrSwp.swp_read_reg_any` | the same at the `swp` layer | `csrr rd, time` |
| `WpGprCsrrCommon.drive_csr_term` | `drive_csr` at the TERM instead of inside `exec` | the guards are in the term, not in the interpreter, so ONE walk serves `exec` and `hfrun` both.  Every per-CSR `_red` lemma is one call |
| `WpDecodeBridge.goodb_bind` / `goodb_bind0` | **goodb COMPOSES along a bind** | the key to certifying a stretch that carries SYMBOLIC data — assemble the certificate instead of computing it |
| `HartMStore.swp_vmem_write_gen` | `vmem_write` with the address computation as an obligation + an abstract rider `Q` | an `hfrun` premise only discharges at CONCRETE operands; `Q` carries `gpr_file` through |
| `InstrBytes.mmode_config_cert` | `gen_cert` out of the bundle without consuming it | every leaf's obligation needs it and the bundle is gone by then |
| `MinstretInv.minstret_inv := emp` | a persistent no-op | so three upstream leaves keep their statements; **delete when green** |

**THE RULE THAT DECIDES EVERY REMAINING CASE — ask whether the stretch WRITES:**
- **read-only, any depth → `goodb`** at `dstateM`, transported by agreement.
  Free.  Made `currentlyEnabled Ext_Zicfilp` and `check_CSR_result` (both four
  levels of guarded recursion) cost nothing.
- **writes → hand-walk with `hfrun`.**  `goodb` rejects writes.  A few nodes at
  concrete registers once the spine is `cbn`'d with a whitelist.
- **a SYMBOLIC register index is the only thing no walker takes** — that is where
  every leaf peels (`swp_rX_file` / `swp_wX_file` / `swp_wX_zero`).

**TWO LIMITS OF `goodb`, both isolated the hard way:**
1. It transports only stretches whose reads have REFERENCE-PINNED values (its
   premise is pointwise agreement with `dstateM`).  So `write_CSR csr_menvcfg`,
   which reads `menvcfg` — the leaf's variable — can never go that route.  A
   `goodbw` that tracked writes would NOT have helped; I proposed it and was
   wrong.
2. It is not COMPUTABLE when the certified term's CONTROL FLOW depends on
   symbolic data (`vm_compute`/`cbv`/`lazy` all diverge).  Hit three times now
   — `write_CSR csr_menvcfg`'s legalization, satp's (it branches on the MODE, a
   field of the written value), mstatus's (it branches on MPP, via
   `have_nominal_privLevel`, which branches on the privilege bits).  Two fixes,
   and which one applies is visible in the term: `goodb_bind` when the
   dependence is on a CALLEE's result (assemble the certificate from data-free
   pieces), a plain `destruct` of the scrutinee when it is a branch (then each
   arm is closed).  Measured on mstatus: naive `vm_compute` does not finish in
   5 minutes, the assembled proof takes 7 seconds.

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
   in `mm_Drw`, held by the wrapper for the whole obligation, so the leaf cannot
   write it.

   **And the value cannot be named.**  `exec_write_CSR_stimecmp` concludes
   `exists mp, exec .. = Some (.., set_reg (set_reg s stimecmp ..) mip mp)` —
   `mp` comes out of `clint_dispatch`, i.e. from DEVICE state, so neither the
   leaf nor a `mip' = f ip` parameter can name it.  Lending the cell is
   therefore not enough: the wrapper must absorb an EXISTENTIAL post-file.

   The shape is already there to absorb it, which is what makes this tractable:
   the cycle rule's continuation constrains the post-file only OFF `tk_clock3`,
   and `mip ∈ tk_clock3`.  So the generalization is to let the instruction's
   obligation return frames at any `rs2'` agreeing with `rsB` off `tk_clock3`,
   and compose that with the tick's own agreement by transitivity (`wrap_post`
   touches only minstret and PC, both outside `tk_clock3`, so it commutes).
   Keep the strict form as a corollary and the other 13 leaves are untouched.

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

- **PRINTING A MODEL TERM IS HOW YOU GET A `_red` LEMMA — do not guess the
  bind structure.**  A pruned model function is a term equation both
  interpreters can use, but hand-writing its RHS gets the ASSOCIATION wrong
  and `reflexivity` then grinds (measured: 15 GB, killed).  Instead prune in a
  throwaway goal and print:

      Goal forall v, write_CSR (mword_of_int 0x303) v = returnM (Ok v).
      Proof. intros v. unfold write_CSR. drive_csr_term.
        match goal with |- ?g => idtac g end. Abort.

  All five `write_CSR` shapes this port needed came out of ONE 13-second run
  that way.  The same trick with `Eval vm_compute in` gives a whole
  read-only stretch outright — `check_CSR_result csr_time Machine CSRRead`
  printed as two reads and a `Ret`, which is what showed that leaf needs no
  premises at all.
- **A MIS-ORDERED EXPLICIT ARGUMENT LIST IS A HANG, NOT AN ERROR.**  A
  `rewrite (hfrun_bind n k D Drw rs …)` with the three file arguments in the
  wrong positions did not fail — elaboration ran for 10 minutes and was
  killed.  The same call in a small scratch file failed in 5 seconds with a
  clear type error.  So when a file that compiled in 20 s suddenly does not
  finish, suspect the newest positional application first, and re-check it in
  a scratch file rather than waiting.

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
