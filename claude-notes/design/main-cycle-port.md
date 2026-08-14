# Porting the monadic Cycle expression to main — execution design

**Audience: an agent working on the MAIN branch.**  This document is
self-contained; it references weak-memory-branch files only as OPTIONAL
pattern sources.  Scope: restructure main's language so a hart's
expression carries the in-flight Sail monad and steps it node by node —
NO weak-memory content (no log, no views, no promising machinery).  The
purpose is to land the expression/WP superstructure on main now, so the
later weak-memory port swaps the memory semantics *under* an unchanged
superstructure.  Everything below was validated by a completed spike on
the weak-memory branch (measured time parity ≈1.03–1.19× vs the
instruction-atomic originals); the mandatory lessons from that spike are
folded in as constraints, marked **(MANDATORY)**.

NOTE ON SOURCES: line references below are from the weak-memory branch's
copy of `iris/RiscvLang.v`, which should be near-identical on main —
VERIFY each anchor before editing.

## 1. What main has today (verify)

`iris/RiscvLang.v`: `gstate = GState (gregs : CPU → regstate) (gmem)
(gdev : dev_state) (ggen) (gpow)`;
`mexpr = LoopE gen cpu | UartLoopE gen | DiskLoopE gen | PlicLoopE gen |
PowerLoopE` (no values); `prim_step`'s hart arm executes ONE WHOLE
INSTRUCTION:
`run (riscv_step tick) (MState (gregs cpu) gmem gdev) tt s'` and writes
back registers/memory/device; the device arms are single relational
steps (`uart_step`/`disk_step`/`plic_step`, each with an Idle arm;
`plic_step` writes a hart's registers cross-thread); the power arm
bumps/forks generations with corpse arms gated on `thread_live`.

## 2. The change, in one paragraph

Add ONE constructor `HartE (gen : nat) (cpu : CPU) (m : M unit)` and
make `LoopE gen cpu` a **Definition** (not a constructor):
`Definition LoopE gen cpu := HartE gen cpu (Interface.Ret tt).`
The hart arm of `prim_step` is REPLACED by per-monad-node reduction
rules on `HartE`, plus the restart rule: from `HartE gen cpu (Ret tt)`
(the boundary — the result type is `unit`, so `Ret tt` is the unique
end-of-cycle value), step to `HartE gen cpu (riscv_step tick)` for an
existentially chosen `tick`.  The infinite CPU loop thus lives in the
STEP RELATION (unfolding at the boundary), which is the only place it
can live: the monad is an inductive type, so an in-monad loop value is
impossible (the immediate-subterm relation is well-founded — provable by
a structural `Fixpoint` returning `Acc`; the weak branch has this as
`WeakSailComplete.mchild_wf`).  Because `LoopE` is a Definition, every
existing statement mentioning `LoopE gen cpu` (whole-function WPs, the
`Notation Loop`, `power_fork`, adequacy plumbing) keeps elaborating
UNCHANGED — only proofs that unfold the hart step break, and those are
exactly the leaves (§6).

## 3. The step rules (the semantics)

One arm per `Interface.outcome` node, transcribing what `run`'s
interpreter does per node (read the SC interpreter — `RiscvExec`/the
`run`/`exec` stack — and mirror its per-outcome handling exactly; do NOT
invent semantics):

- **restart** (boundary): `HartE gen cpu (Ret tt)` → `HartE gen cpu
  (riscv_step tick)`, `∃ tick`, gated on `thread_live g gen`; the CORPSE
  arm (dead generation ⇒ pure self-loop) covers `HartE` uniformly —
  one arm, since `LoopE` is now a `HartE`.
- **register nodes** (`RegRead`/`RegWrite`): against `gregs cpu`.
- **RAM `MemRead`/`MemWrite`**: against `gmem`, exactly as `run` answers
  them (value at the address; writes update the map).  Alignment/PMA
  logic stays inside the monad where the model put it.
- **device `MemRead`/`MemWrite`** (`dev_addr`): against `gdev` via
  `dev_read`/`dev_write`, as `run` does.
- **the AMO window (MANDATORY: keep it FUSED).**  An exclusive
  (`ak_latest = true`) RAM read steps together with its in-window silent
  nodes and the paired conditional write as ONE step (transcribe the
  window-walking: a `silent_run`-style rtc over register/choice nodes to
  the conditional-write node).  This is what keeps a lock acquire a
  single invariant access in the logic; the weak branch's
  `WeakSailLTS.silent1`/`wr_node` and `WeakEvLang`'s fused arm are the
  pattern.  Guard the plain-read arm with `ak_latest = false`, or the
  two arms overlap and no atomic acquire rule is statable (spike finding
  F6).  VERIFIED ON MAIN'S MODEL AND IMAGE, so the guard costs nothing:
  the kernel ELF contains exactly ONE atomic (`acquire`'s `amoswap.w.aq`)
  and NO `lr`/`sc` at all, so no bare exclusive read is ever executed; the
  model's `read_ram`/`write_ram` give BOTH halves of an AMO
  `AV_exclusive` (`Read_RISCV_reserved{,_acquire}` /
  `Write_RISCV_conditional{,_release}`), so one `ak_excl` predicate keys
  both; and `execute_AMO`'s window between the read and the write is
  register reads plus pure arithmetic — no `cancel_reservation` (that is
  in `execute_SC` and `reset_sys` only), so the silent walker needs no
  opaque-effect arm.
- **`Barrier`/announce/`Choose`/`GetCycleCount`/…**: silent, as `run`
  treats them (at SC, fences are semantically inert; if `run` models
  fence.tso in two phases, carry the parked half as an extra `HartE`
  argument — VERIFY; expected NOT needed on main).
- **stuck-is-fine**: `GenericFail`/`Discard`/etc. have no arm.  Do NOT
  add shape/liveness predicates about the monad — a shape predicate is a
  promise about an instruction's future, and no rule here mentions the
  future.  (On the weak branch, hand-written ∀-statements of that kind
  were refuted six times; the event design deletes the entire category.)
- Devices/power arms: UNCHANGED in this port.  (Optional later phase:
  move device operation state into the device expressions — e.g. split
  the disk's atomic DMA into burst+emit steps — matching the weak
  design; not needed now.)

THE PLACEMENT RULE (why the monad goes in the expression, recorded so
the choice survives review): put control state in the expression exactly
where control flow is MODEL-DEFINED, in σ where it is MEMORY-DEFINED.
Inter-instruction control flow is memory-defined (the next instruction
is fetched through a page table from mutable memory — must be proven),
hence the boring boundary token and σ-resident registers/PC.
INTRA-instruction control flow is model-defined: the continuation IS the
Sail monad value, syntactically known and monotonically consumed —
expressions are for exactly this, and WP-of-an-instruction becomes proof
by syntactic descent.

## 4. The semantic delta — state it honestly in the PR

Mid-instruction interleaving becomes REAL: another hart's (or device's)
step can land between one instruction's events.  At SC this admits more
interleavings than the old machine (the old machine's runs embed as the
contiguous-block special case).  This is deliberate — it is the honest
concurrency of the eventual weak model, minus weak memory — and the
spike's evidence is that the Iris resource layer absorbs it: exclusive
ownership and invariants are interference-stable by construction, and
re-establishing the state interpretation per EVENT is weaker per step
than per instruction.  Two audit items where instruction-atomicity might
be load-bearing today (spike fail-criterion 2; neither fired on the weak
branch):
1. any proof that opens an invariant across a whole instruction to LINK
   two accesses (candidates: the page-walker's read-then-A/D-update —
   the `CommonWalk` technique — and the interrupt-absorbing step
   engines).  The fused-AMO arm keeps lock acquires safe; anything else
   must move to a ghost protocol.  Enumerate and report before the leaf
   sweep.
1b. the two VALUE-AGNOSTIC register invariants are safe, and that is not an
   accident worth losing: `MinstretInv.clock_inv` (mcycle/mtime/mip) and
   `minstret_inv` (minstret, minstret_increment) pin no value, so they can be
   opened and closed around each INDIVIDUAL node that touches them — no
   invariant has to stay open across an instruction, which Iris would not
   allow.  The one thing to watch is `minstret_increment`, written near the
   TOP of `try_step` and read at the BOTTOM: a reopen at the bottom yields an
   arbitrary `mi`, so the adapter must carry the written value in the CURSOR
   (registers are per-hart and no other thread writes that cell — see §5's
   ownership boundary) rather than expect to read it back out of the
   invariant.
2. interrupt delivery timing: `plic_step` already writes hart registers
   cross-thread, which is the right design (keep delivery OUT of the
   hart's own arms — on the weak branch a hart-side delivery arm would
   have forced Löb into every rule; finding F1).  Mid-cycle deliveries
   become possible; the model's interrupt CHECK reads the register at
   its own node, so proofs see the value at that node.  Audit the
   absorbing-engine lemmas (`sr_absorb` family) for hidden reliance on
   between-instruction-only delivery.

## 5. The proof interface (MANDATORY — this is where ports die or live)

**SETTLED: the SEMANTICS stays per-node; batching is a THEOREM.**  A
coarser "chunk" semantics (one step = silent run + one shared access) was
considered and rejected: the definition of the machine should stay minimal
and obviously faithful, and proof performance is recovered by derived rules,
not by complicating `prim_step`.  Do not re-litigate.  Two consequences that
fall out of the theorem-level batching, recorded so they are designed in
rather than discovered:
- **the `sig_seip` batch boundary is SELF-ENFORCING**: the batch rule's
  premise is ownership of the cells for every register the stretch touches,
  and `sig_seip` sits at `DfracOwn 1` inside `WireInv.wire_inv` — an
  invariant cannot stay open across a multi-step derived rule, so no caller
  can supply that cell and a stretch reading `sig_seip` makes the rule
  inapplicable, structurally.  (Prove once that `plic_step` writes ONLY
  `sig_seip`: it is the licence for batching every other register.)
- **the invariant-held cells get SINGLE-NODE rules**: nodes touching
  minstret / minstret_increment / mcycle / mtime / mip each take a one-step
  rule that opens `minstret_inv`/`clock_inv` around exactly that node.  The
  bottom-of-cycle `minstret_increment` read needs NO value-carrying: its
  value only decides whether `minstret` bumps and both branches are
  value-agnostic, so one generic lemma ∀-quantifies the flag and absorbs the
  whole tail — the per-node analogue of `wp_exec_step_clock`'s tick
  absorption.

**The language's step granularity must NOT become the proof's step
granularity.**  Measured on the weak branch: naive per-node proofmode
stepping costs ~1 ms/node (~50× on a real 293-node instruction).  The
proof interface is:

1. **A reflective silent-stepper** in equation-free form (spike finding
   F8, MANDATORY): a cursor `(regstate * M unit)` with TOTAL stepper
   functions (`esil n D : cursor → cursor`, plus `ecur_read v`,
   `ecur_write`, …), where a certification is a CHAIN OF APPLICATIONS —
   the residual monad is NEVER named at a call site (VM readback of a
   monad closure did not finish in 110 s; the same run projected to a
   number takes 0.1 s).  Rules match the residual's head via
   value-output projections (`enode_tag` a number, request-record
   projections) with once-proven inversion lemmas.  The batched WP rule
   takes NO equation:
   `ereg_frame … D -∗ (ereg_frame … (esil n D x).1 D -∗ WP (HartE …
   (esil n D x).2)) -∗ WP (HartE … x.2)`.
   GOTCHA (measured): discharge any cursor equation with
   `have H : … by reflexivity` and pass `H`; a bare `eq_refl` inside an
   application hands the goal to the elaborator's unifier, which lazily
   evaluates the stretch (5 s → unbounded).
   **BATCH BREAKS (main-specific; the mechanics are the two bullets at the
   top of this section).**  A batch is sound only while the cursor's
   `regstate` is provably this hart's file, i.e. while the caller owns the
   touched cells.  So a batch breaks at: memory/device events, `sig_seip`
   accesses (cross-thread-written; self-enforcing per above), and the
   minstret/clock invariant cells (single-node rules per above).
   `dispatchInterrupt` reads mip and `sig_seip` at the TOP of every
   instruction, so every cycle has breaks early; the existing
   `WpIntrCore`/`WpIntrInv` layer already ∀-quantifies those reads off σ,
   so the adapter reuses it rather than inventing anything.
5b. **The tick, settled by the spike's own pilot** (`WeakEvStarted` §4, the
   two-instruction composition): the boundary rule quantifies the
   continuation over `tick`, and the next instruction's certification is
   supplied as a FAMILY of unevaluated cursor compositions uniform in the
   tick (and in any value the previous instruction read) — `∀ w tick, y1 w
   tick = hsil k1 D (hcur_loop tick (x3 w))` — with the per-site projection
   facts ∀-quantified likewise.  No bind-commutation lemma; the measured
   1.03–1.19× parity INCLUDES this cost.  A `hsil`-commutes-with-`bind`
   equation remains available as an optimization if the adapter's
   measurements show the per-tick duplication biting on main (main's tail
   is bigger than the weak branch's: `tick_clock` is register-only, so its
   nodes are batched silent stretches broken only at the clock_inv cells,
   each taking a single-node rule that opens `clock_inv` around exactly
   that node — the per-node heir of `wp_exec_step_clock`'s absorption).
2. **Per-memory-event rules**: one WP rule each for RAM read, RAM write,
   the fused AMO, device read/write — these are where the real reasoning
   (points-to, invariants) happens, exactly as in today's leaves.
3. **A pinned-text fetch rule** (spike finding F7, MANDATORY): the fetch
   is an ordinary RAM read node, so without a special rule every
   instruction pays one general memory-event rule for its own fetch.
   Derive `wp_cycle_fetch` from main's persistent kernel-text facts
   (`instr`/text points-to): it concludes the fetch returns exactly the
   certified word, no caller obligation.  This was the largest single
   parity cost until specialized.
4. **The certification adapter**: from today's per-instruction
   certification data (the decode `kd_` catalogue + the interpreter-run
   facts the existing leaves are certified with), produce the
   whole-instruction WP by chaining 1–3, with obligations ONLY at memory
   events.  **Leaf SPEC statements are preserved verbatim** — the
   adapter's whole point is that `wp_<leaf>` lemmas keep their exact
   statements, so every whole-function proof above re-checks UNCHANGED.
   Decode is imported, not re-solved: all existing decode
   proof-engineering is consumed inside the reflective stepper's
   computation.
5. **Proof-term discipline** per durable-notes: `vm_cast_no_check` for
   reflective equations; compute-once-into-a-`Definition` for VALUES
   (never for monad residuals — that is F8 again); watch the async-`Qed`
   traps.

Optional pattern sources on the weak-memory branch (read for shape, not
for content — they carry weak-memory semantics you must NOT port):
`iris/WeakEvLang.v` (the HartE arms), `iris/WeakEvLift.v` (§3b the
equation-free cursor interface; §5-§7 the event rules and adapter),
`iris/WeakEvStarted.v` (a whole leaf + the measured instantiation at a
real kernel instruction).

## 6. Migration phasing

**THE TREE CANNOT STAY GREEN ACROSS THIS PORT, AND THE RED WINDOW IS THE
WHOLE TREE.**  This corrects the earlier claim that "everything except leaf
proofs still compiles" in Phase A.  The reason is not `LoopE` (that trick
works exactly as advertised — every statement mentioning `LoopE gen cpu`
re-elaborates untouched): it is `RiscvExec.wp_exec_step`, whose statement is
UNSOUND under the new semantics and therefore cannot be re-derived.  It hands
the caller `mstate_interp σ` and asks for `exec (riscv_step false) σ = Some
(tt, σ')` — ONE whole-instruction certification against ONE σ — and under
per-node stepping σ can move between the instruction's events, so no such
witness can predict the successor.  A sound whole-instruction rule needs a
FOOTPRINT side condition ("this run reads only what the caller owns"), which
is new machinery and is not the same statement.

Measured on the tree: the breakage funnels through a SINGLE chokepoint.
`MinstretInv.v` is the only direct consumer of `wp_exec_step` below the rest
of the development, and **971 files sit behind it** (`RiscvExec` 1054,
`RiscvLang` 1067 — i.e. the tree). So the red window is all-or-nothing, and
"file-by-file, keep it green" is not available. Plan for it:

- **Phase A — the language + the bracket.**  `HartE` + `mnode_step` +
  `hart_node_step`; `LoopE` as a Definition; per-arm `prim_step` inversion;
  the SOLO-BLOCK BRACKET (`HartBlock.v`).  `RiscvExec.v` re-derives
  `wp_dead` and the three device rules unchanged and replaces
  `wp_exec_step` with the per-node framing point `wp_hart_step` (+ the
  derived boundary rule `wp_hart_restart`).  Ends with the tree red at
  `MinstretInv.v`.
  The bracket is proven in the SOUND direction only (block ⇒ run), which is
  the unconditional one and the one the adapter consumes.  The converse is
  NOT unconditionally true — the language fuses the AMO and guards the plain
  read with `ak_excl = false`, so a `run` containing a bare exclusive read
  has no block — and its honest witness is the reflective stepper's own
  functional interpreter (Phase B), where "the fused window was found" is a
  computation rather than a hypothesis.  Do not try to state it with a
  shape predicate.
- **Phase B — the proof-interface kit** (§5 items 1–5b), and it is on the
  CRITICAL PATH, not an optimization: nothing above `MinstretInv.v` compiles
  until the adapter exists.  Land it against ONE pilot leaf and ONE small
  whole-function proof at parity, measuring `coqc -time` per lemma
  (weak-branch benchmark: ≈1.03–1.19× time; ~1.7× lines, the residue in
  statements).
- **Phase B′ — reconnect the tree.**  The five whole-instruction rules
  (`wp_exec_step`, `_clock`, `_minstret`, `_hart_active(_inv)`,
  `_decode_execute_inv`) and `InstrBytes.wp_instr` are the adapter's real
  surface; the footprint argument that makes a whole-instruction rule sound
  is available AT `wp_instr` and not below it, because that is the first
  layer where the caller's ownership of the instruction's read set is known.
  Getting `wp_instr` back with its statement intact is what turns 971 red
  files green in one step, and it is the milestone to drive at — not the
  leaf sweep.
- **Phase C — the leaf sweep**, file by file, spec-identical (tooling in the
  `gen_code.py` style where mechanical).  Whole-function proofs must
  re-check without edits; any that does not is a finding to report, not to
  patch silently.
- **Phase D — adequacy + capstones** re-derived over the new language;
  `tools/proof_coverage.py` parity with pre-port; `Print Assumptions` on the
  capstones must be UNCHANGED.  The audit items of §4 resolved and recorded.

Because the tree is red for the whole of A–B′, do the work on a dedicated
branch and keep `main` off it until B′ lands; and expect the near-total
recompile at every A/B iteration, so iterate with `make -f CoqMakefile
<one>.vo` chains (durable-notes' "build the CHAIN, not the cone") and pay the
full `-j` build only at the milestone.

## 7. Success criteria / honesty protocol

Green tree per phase; leaf specs byte-identical (diff the statements);
whole-function layer untouched; measured parity within ~1.2× time on
comparable lemmas; no new axioms; every place instruction-atomicity was
load-bearing enumerated with its resolution.  If something fundamental
resists (an invariant that cannot become a ghost protocol, a leaf that
cannot keep its spec), STOP and record the finding — on the weak branch
every such surprise was a design input, and two of them (F7, F8) were
found only by measuring.
