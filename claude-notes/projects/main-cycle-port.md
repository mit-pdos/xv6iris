# main-cycle-port — worklist

Design: [`design/main-cycle-port.md`](../design/main-cycle-port.md) — read it
first; the settled decisions (per-node semantics, batching as a theorem, the
self-enforcing batch boundaries, the tick-family shape) live there, not here.

## What exists (pointers, not status)

- `iris/RiscvLang.v` — `HartE gen cpu m`; `LoopE` a Definition; `mnode_step`
  (hart-local, on `mstate`) + `hart_node_step` (focus/step/write-back);
  the fused-AMO window (`silent1`/`silent_run`/`wr_node`, `ak_excl`); per-arm
  `prim_step` inversion; `prim_step_hart_regs_frame` (the batching licence:
  plic's `sig_seip` wire is the only cross-thread register write).
- `iris/HartBlock.v` — the solo-block bracket, sound direction
  (`mblock` ⇒ `run`); closed against `exec` by `RiscvExec.hart_block_exec`.
- `iris/RiscvExec.v` — `wp_dead` + device rules re-derived; `wp_hart_step`
  (the per-node framing point) + `wp_hart_restart` (the ∀-tick boundary).
- `iris/HartLift.v` — the reflective silent stepper (`hsil_node` /
  `hrun_silent` / cursor `hcur` / projections + inversions), `hreg_frame`,
  and the batched rule `wp_hart_batch` (equation-free, F8 form).
- `iris/HartEvents.v` — per-memory-event rules (RAM read/write, MMIO
  read/write), fupd σ-callback currency.
- `iris/HartAmo.v` — the fused-AMO rule `wp_hart_amo` (∃-`w` inside the
  fupd; window data a function of `w`) + the pure window layer.
- `iris/HartRegNode.v` — single-node RegRead/RegWrite fupd rules (the escape
  hatch for invariant-held cells and the wire).
- `iris/HartPilot.v` — the Phase B pilot, DELIVERED at parity: `sw a4,0(a5)`
  at `main+0xb0` on the cold-boot file (292 nodes, 2 memory events), through
  `wp_hart_rw_seq` (the generic sequence rule at abstract cursors) — whole
  file 3.6 s of sentence time, the instantiation itself 0.2 s.  **Read its
  §6 header before writing any adapter rule**: it records the four measured
  lazy-evaluation traps and the rule/instance split that makes them
  impossible (also in the design doc §5's GOTCHA).

## Left

0. **The span rule** (`iris/HartSpan.v`, statements pinned, proof in
   flight) — the B′ keystone, design in the doc's §5 item 1c.  Charted
   from the pilot's per-node register trace: a real M-mode cycle reads
   ~54 unownable value-irrelevant registers (pmpaddr×48, mie/mideleg/mip/
   sig_meip/sig_seip), so batching cannot cover the prelude and per-node
   ∀-rules would not be at parity.  Span = writes gated on `Drw` (frame),
   reads ungated, `Dro` ro-frame (dfrac-generic) for the value-sensitive
   config, relational landing killed by a once-per-class pure
   characterization.  Chop points: invariant-cell writes only
   (minstret_increment, minstret, tick's clock cells).
0b. **The prelude characterization** (once for ALL M-mode leaves): the
   pure lemma computing every span landing of the M-mode cycle prelude
   with the config pinned — then the M-mode cycle rule
   (span / chop(minstret_increment) / span-to-fetch / F7-fetch-event /
   decode+execute batches / tail chops / boundary, in the
   `wp_hart_rw_seq` rule/instance discipline).
   **Implementation, measured (do not re-litigate): CHAIN-PEELING, not
   tactic normalization.**  Walking the prelude at a symbolic base file
   with pins as a `register_set` tower fails both ways: `cbn` stalls on
   the tower lookups (heuristic refusal at ~30 s), `lazy` full-normalizes
   dead branches under stuck scrutinees (>300 s).  Instead: per-node
   INVERSION lemmas on `hspan` itself — a D-read peel taking the pinned
   value as an EXPLICIT argument (no lookup term ever formed), an
   off-D-read peel introducing a ∀-binder, a silent peel, a `Drw`-write
   peel — chained ~106 times in the once-per-class lemma; the between-peel
   monad reduction is pure spine β/ι, which the symbolic probe measured
   at ~6 ms per 30 nodes.
0c. **The landing-naming resolution (settled; use it for every remaining
   characterization): NESTED-IMPLICATION STATEMENTS.**  A segment's landing
   monad must never be spelled as a Definition (the composition would be a
   ~200-application literal; a functional walk at a witness file either
   re-enters the tower-lookup stall or loses the parameters).  Instead the
   characterization is ONE lemma whose conclusion conjoins, per stage,
   projection facts about the current landing AND a ∀-quantified
   implication about chains from that landing's resume — the landing rides
   through as a BOUND VARIABLE, and the cycle rule consumes the conjuncts
   in step order, instantiating each at the landing its previous stage
   produced.  Post-fetch (decode+execute at the leaf's known word) is NOT
   characterized — it is the leaf's own functional-cursor batch, pilot
   style; the generic machinery covers boundary→fetch and the tail (whose
   start monad is one closed term, spellable from try_step's own source).
0d. **The leaf-attachment seam — RESOLVED by the mixed-file walker**
   (`HartMFetch.mfetch_char`, proven, 5-axiom-clean): the fetch landing is
   pinned to `(hrun_any_f 200 (register_set pmpcfg_n pmpcfg_boot rs)
   mseg2_start).2` — the caller's own pin file with pmpcfg alone forced
   concrete-OFF (a merely-unlocked symbolic pcfg leaves the walk's
   per-entry branches stuck; the chain side still runs at the real pcfg,
   and the equality holds because the post-fetch continuation retains
   nothing the PMP loop read).  Leaves' functional cursors start at
   `hread_resume w <that application>`.
   **Known debt: `mfetch_char`'s Qed is 665 s** (92% of the file; tactic
   side ~55 s) — kernel rechecking of rewrite motives carrying the giant
   residuals.  Once-per-tree-build, tolerated; MUST be fixed before Phase
   C replays the pattern for the S-mode fetch (walk events multiply the
   residuals).  BISECTED (0e): the cost is the
   goal-side walk chain itself (the chain side — ~110 hypothesis rewrites
   + the loop induction — rechecks in 5.6 s); statement-shape tricks
   (etransitivity evars, remember/exact) are measured dead ends.  The fix
   is batching the walk's own reduction into once-stated per-stretch
   helper equations — fewer, bigger conversion steps for the kernel.
0e. **[DONE — `mseg1_charK`/`mfetch_charK` land tail-generic over `KT`,
   originals kept byte-identical as instances, 5-axiom-clean.]**
   Original entry: **The tick generalization pass** (mechanical, after `mfetch_char`
   lands): `mseg1_char`/`mseg2_start`/`mfetch_char` are pinned at
   `riscv_step false`, but the tick's `if` node sits BEYOND every
   characterized stretch (in the tail), so the statements and proofs
   generalize to a `tick : bool` parameter by substitution — the peel
   proofs never reach the tick node.  Needed before the cycle rule
   (`wp_hart_restart` hands out both ticks); the tick=true tail's extra
   `tick_clock` stretch is leaf-side (three clock_inv chops + ∀-reads),
   like the rest of the tail.
0f′. **The decode gap, bottomed out (supersedes 0f's first cut).**  A
   monad that branches on a symbolic encoding `w` has no constructor
   head, so NO WP rule can step it per-node — the exec-span idea fails
   at the meta level (the rule's own induction cannot case an open
   term), not on soundness.  Consequences, in order of delivery:
   (a) **The pilot leaf is PER-WORD** (concrete encoding, like the
   existing CodeXxx catalogue's `mni_*` altitude, and like the pilot):
   everything computes, the existing kit suffices end to end.  Ship it
   first — it is the honest heir of the catalogue's per-word facts and
   is what whole-function proofs actually consume at concrete sites.
   (b) **∀-operand leaf shapes** (wp_addi_gpr's ∀ imm/rs1/rd with `w`
   existential) need a once-per-INSTRUCTION-SHAPE decode
   characterization over the ENCODING FUNCTION: at
   `ext_decode (encode_itype imm rs1 rd)` the branch bits are the
   SHAPE's (opcode/funct, concrete) and the operand bits ride as values
   into the constructor — so the span/batch reduces at symbolic
   operands.  The seam to design: `instr` pins only `decode w = i`, not
   `w = encode i` (non-canonical encodings), so either the per-shape
   char takes the encoding form as its premise (and the leaf's caller —
   the catalogue — supplies it, which it can: the kd_ words are
   canonical), or the leaf statement's `instr` premise is consumed
   per-word downstream.  Decide when building leaf #2; do not block the
   per-word pilot on it.
0f-old (first cut, kept for the analysis trail): **The decode gap.**
   A leaf's encoding word `w` is EXISTENTIAL inside `instr`, and decode
   branches on `w`'s bits — so the functional batch (hsil2) is a STUCK
   TERM through decode at symbolic `w`, and no cursor fact computes.  The
   old route used `instr`'s ∀σ-conditional exec fact
   (`∀ σ, conforming σ → exec (decode_fetch r) σ = Some (i, σ)`) — a
   relational fact, exactly the right currency.  Resolution: a new derived
   rule `wp_hart_exec_span` consuming that fact directly: for a
   WRITE-FREE, state-preserving sub-monad, WP (bind mm K) reduces to
   WP (K i) with frames intact — proven by mchild-induction where each
   read node re-applies the ∀σ fact at the machine's own σ (the values
   cannot matter: the result is σ-independent), and conformance (the Dro
   pins) survives interference because it is framed.  The write-freeness
   side condition is genuinely needed (an unowned register write cannot
   re-establish the reg auth) and is NOT derivable from the ∀σ fact; it
   goes in the same epistemic slot as the weak branch's `sail_live_st`
   (per-instruction, decoder-checkable, declared where needed): prove
   `decode_fetch` write-freeness once if the decoder's structure permits
   (conversion-collapse of the encdec towers, as HartMDispatch found for
   currentlyEnabled), else per-class instances in the Phase C catalogue.
   The execute phase needs NO such fact — its registers are all framed,
   hsil2 covers it (symprobe-verified for the ALU class).
1. **The pinned-text fetch rule** (spike F7): derive from
   `wp_hart_ram_read` + `↦ₓ□` facts (`text_valid` per byte → `read_bytes`
   via `read_bytes_ne`/`read_bytes_spec`/`bv_eq_of_bytes`).  Shape it
   against the pilot's real fetch plumbing (`instr`/`fetch_from_pts_*`),
   not speculatively.
1a. **[DONE — `HartMLeaf.wp_word_main_b0`: the first per-word leaf,
   boundary to boundary at both ticks, 5-axiom-clean.]**  What it
   settled: (i) the leaf-side stretches are SPANS + pure characterizations
   wherever PMP walks (symbolic pcfg) or `tick_clock` branches appear —
   the two-footprint batch serves only pure ALU register stretches;
   tick=true's tail reads mcyclecfg/menvcfg/sig_meip/sig_seip, unownable,
   span-absorbed.  (ii) Two premises the draft missed and the old
   hw_config always carried: misa.C (the Zca decode gate reads it) and
   elp ≠ LP_EXPECTED (the landing-pad check).  (iii) THE PER-LEAF COST
   MODEL: 13m16s, of which the exec characterization's Qed is 671 s (84%)
   — the same goal-side walk-chain kernel cost as the mfetch debt, now
   per leaf.  **The walk-batching fix is MANDATORY before the Phase C
   sweep**; the rest (~2 min/leaf) scales.  (iv) `ext_decode_compressed`
   is vm-opaque (Acc diverges under vm) — gate equations by reflexivity.
2. **The next leaf** (was: the first converted leaf) — `wp_addi_gpr` re-derived spec-verbatim
   on 0b's cycle rule, timed against the original (the design doc's real
   Phase B gate), then:
   - ONE small whole-function proof re-established at parity (the pilot was
     one instruction; a whole function exercises the boundary chaining and
     the tick family).
   - The tick is a certification FAMILY uniform in `(w, tick)` — design doc
     §5's 5b; only reach for `hsil`-commutes-with-`bind` if measurement says.
   - Every adapter rule follows the `wp_hart_rw_seq` shape: generic rule at
     abstract cursors + equations-as-premises, instance with reflexivity
     equations in the definitions' own spelling.
3. **Phase B′ — reconnect the tree** (971 files behind `MinstretInv.v`).
   Surveyed against the real statements; the findings that set the plan:
   - **Leaf SPECS are resource-shaped** (`wp_addi_gpr`: cells in, cells out —
     no σ, no `exec`, no fupd), so "leaf specs verbatim" is achievable.  The
     σ-callback currency (`∀ σ, mstate_interp σ ={..}=∗ ∃ σ', ⌜exec … = Some
     …⌝ ∗ mstate_interp σ' ∗ …`) is INTERNAL to `wp_instr` and the mid-stack.
   - **`wp_instr`'s exact statement is NOT re-derivable**: its callback hands
     back `mstate_interp s_exec` inside one fupd — meaningful only when the
     whole instruction is one atomic step.  Rebuild the same ALTITUDE with a
     per-event internal currency; the leaf proofs above it are the Phase C
     sweep (their statements stay).
   - **The execute phase of the ALU/CSR class is all silent nodes**, and
     branch-free in the data values (branches split into taken/not-taken
     leaves already), so it batches at a SYMBOLIC register file — `hsil`
     reduces by `cbn` when the node path is value-independent; `vm_compute`
     is only for concrete instantiation.  The `exec_execute_*` catalogue
     gets cursor-form twins in the sweep (mechanical, gen_code-style
     tooling); decode (`kd_`) is consumed via `instr` unchanged.
   - Memory-class leaves route their one/two data events through
     `HartEvents`; MMIO leaves (uart/plic/virtio access paths) keep their
     σ-shaped device reasoning via the MMIO event rules — enumerable, small.
   - The clock/minstret absorption rebuilds on `HartRegNode`'s single-node
     rules; `sr_absorb`/interrupt engines are audit item 6.
4. **Phase C — the leaf sweep**, spec-identical; whole-function proofs must
   re-check unedited (a failure is a finding, not a patch).
5. **Phase D — adequacy + capstones** (`RiscvAdequacy`/`SystemAdequacy`
   mention `LoopE` by name — the Definition keeps statements elaborating;
   proofs that invert `prim_step` need the new inversion lemmas);
   `proof_coverage.py` parity; `Print Assumptions` unchanged.
6. **The §4 audit items**, resolved and recorded: (a) invariants opened
   across a whole instruction to LINK two accesses — candidates: the
   page-walker's read-then-A/D-update (`CommonWalk`) and the
   interrupt-absorbing step engines (`sr_absorb` family); (b) mid-cycle
   interrupt delivery — the model's check reads `sig_seip`/mip at its own
   node, `WpIntrCore`/`WpIntrInv` already ∀-quantify those off σ.

The tree is RED from `MinstretInv.v` up (971 files) until item 3 lands —
this is by design (design doc §6); iterate with single-file `coqc` /
`make -f CoqMakefile <one>.vo` chains, not full builds.
