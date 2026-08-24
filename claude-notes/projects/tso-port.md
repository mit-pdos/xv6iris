# TSO port — plan of record (PROPOSED, awaiting owner ratification)

Goal: move main's memory semantics from SC to operational **Ztso**, keeping
the proof tree. The port is **interface-first**: a context-indexed ownership
surface Σ is installed on main in independently-landable sweeps while the
semantics stays SC (every Σ statement has a degenerate SC instance, so main
stays green throughout), the same Σ is proven satisfiable by the Ztso machine
on the `tso` branch (the standing cutover certificate), and the final cutover
swaps only the below-Σ kit. Nothing above Σ is reproven at cutover — it
recompiles.

The load-bearing invariant of the whole plan: **every statement above the
seam must be provable in BOTH instantiations at all times.** The `tso` branch
is the standing check for the TSO side; main's CI is the check for the SC
side.

## 0. What is inherited from the `weak-memory` branch

Read via `git show weak-memory:<path>`. The branch is a long RVWMO effort;
this port takes its *validated* pieces and drops its RVWMO-only towers.

Take:
- **The machine**: `iris/WeakMem.v` (promise-free view machine: era image +
  global append-only write log + per-hart view record `wstate`) and
  `iris/WeakInterp.v` (the Sail seam: `MemRead`/`MemWrite`/`Barrier` arms,
  `classify : accessKind → akinfo`, read oracle). Ztso is an *instantiation*,
  not a new machine: TSO ⊊ promise-free ⊊ RVWMO, and
  `design/weak-memory.md` (Rejected alternatives) records "TSO = the same
  machine with implicit RCpc annotations" — every load acquire, every store
  release, at the `classify` seam. The forward bank `w_fwd` is the
  store-buffer-forwarding (W→R) exception, already built.
- **The language pattern**: `iris/WeakEvLang.v` (event-granular: one language
  step = one Sail monad node) and `iris/WeakEvAdequacy.v`. Main's `HartE`
  per-node language was built precisely so this swap happens "under an
  unchanged superstructure" (`design/main-cycle-port.md`).
- **The context surface** (the crown jewel; substantially implemented and
  green on the branch): `iris/WeakCtx.v` (CtxId, `ctx_auth` over the
  floors-only view, persistent `ctx_view_lb`, the `cobj` modality,
  `wrunning`/park/resume with the two causality premises),
  `iris/WeakCtxPt.v` (`wptsto`/`wptsto_cl` — iProp points-to with SC-shaped
  rules; `ctx_dom` ledger domination; `CtxMorph`), `iris/WeakCtxLock.v`
  (every lock owns a context ξ_L, internal only; release/acquire re-index
  points-to via `CtxMorph` "inside these lemmas and nowhere else").
  Acceptance tests to port as-is: `WkYieldFrame.v` (same access lemma
  verbatim on both sides of a cross-hart yield), `WkCtxSurface.v`
  (machine-checked: the exported statements are free of
  monPred/⊒/view_*/⊑), `WkMemmoveLoop.v` (interruptible loop at exact
  SC proof-length parity).
- **SC-parity as the organizing goal**: `design/weak-memory-sc-parity.md` —
  "for lock-disciplined code, the proof above the leaves should be the SC
  proof". Measured on the branch: converted M-mode chains at ~1.4× (residue
  attributed to a non-memory interface), memmove at parity, zero fences in
  client proofs.
- The vProp base (`WeakView.v`/`WeakVProp.v`), `WeakGhost.v` (state
  interp), `WeakFence.v`, `WeakLock.v`, `WeakBridge.v` (the ~1220-lemma SC
  decode/leaf transfer), `WeakCert.v`, and the litmus mold
  (`WeakSrvwmoLitmus.v`).

Do NOT take (RVWMO-only; the big prize of choosing Ztso):
- the full promising machine and both robustness towers (`WeakPromise*`,
  `WeakRobust*`, `WeakRvwmo*`, Route A/B, the pin checker, taint/witness
  machinery) — Ztso is interleaving-representable (no LB), so none of it is
  needed;
- the abandoned instruction-atomic lift tower (`WeakSailLTS*`, `WeakShape*`,
  `WeakRetag`, the premises ledger) — superseded on the branch itself by the
  event language.

## 1. Leg T — the `tso` branch (experiments; nothing lands on main from here)

**T1 — the Ztso machine: `iris/TsoMem.v` (BUILT, compiles clean).**
RULING (owner): the semantics is written fresh and PRECISELY TSO — not a
port of the branch's `WeakMem.v`, whose per-hart state (per-byte coherence
map, five scalar views, forward bank, dependency views) is RVWMO
apparatus. What the minimal machine keeps from the branch is only the
memory-as-a-message-log shape. The whole machine:

- global: era image + `glog : list wmsg`, each message author-tagged
  (timestamp 0 = image, `S i` = slot `i`; log order IS the total store
  order);
- per hart: **one monotone log index** `tv` — the entire per-hart state;
- visibility: `t ≤ tv` or own message (own-always-visible IS store
  forwarding; a store must NOT advance the author's view or SB dies);
- load: advance `tv` nondeterministically (≤ log top), read
  LATEST-visible per byte (latest-only is what kills stale-after-fresh);
- store: append, view unchanged; W→R fence (`pw ∧ sr`): view :=
  max(tv, own last message) — drains are in log order, so passing one's
  own top message passes everything below; all other fences no-ops;
- exclusive/AMO: read at the log top, write appends and takes the view
  past the append; atomicity stays the LANGUAGE's reservation self-loops.

In-file theorems: `read_down_le`/`read_down_latest` (the latest-visible
characterization the forbidden litmus arms consume), `tso_read_own_top`
(forwarding is mandatory), `tso_read_top_flat` (**the SC collapse**: a
hart pinned to the top view is an SC hart — leg C's compatibility story
in miniature). `iris/TsoLitmus.v` (WeakLitmus.v mold, no annotations in
the instruction language) is LANDED and clean: SB and n6 exhibited
(forwarding is load-bearing in both); fenced-SB, MP-with-no-fences (the
headline), CoRR (two verdicts), LB, IRIW, and AMO-strength proven
forbidden, each with a reachability witness so no forbidden verdict is
vacuous.

Rulings still open at this layer:
- **MMIO stays strongly ordered** (recommended): device/`dev_addr` accesses
  drain/sequence as today — matches hardware I/O regions, keeps the whole
  device-proof tier and `device-conformance` untouched. The Sail
  FENCE-I/O-bits boundary clause from the branch carries over.
- **Crash drops unpublished writes**: the era/generation split already wipes
  RAM at a power edge, so the honest "buffer lost at crash" semantics is
  free; the disk's durability story is device-side (M5 disk-as-agent
  pattern) and unaffected. Verify against `design/crash.md`'s
  crash-spanning disk invariant.
- **FIFO-buffer presentation is a theorem, not the model** (recommended): if
  the literal per-hart-buffer rendering is wanted for trust, prove it
  equivalent to the annotated view machine later (small, because stores are
  never early and drain in order — the log tail above all floors *is* the
  union of buffers). Everything else consumes the view machine.

**T2 — freeze Σ, the cutover contract.** The SC-degenerate side of Σ is
begun: `iris/TsoCtx.v` (`CtxId`, ambient `CurCtx` with deliberately NO
default instance, `own_context`, `ctx_pointsto` + its law surface
mirroring `mem_pointsto`'s, `ctx_dom`/`CtxMorph` + structural instances
with the composition acid test) — its header carries the three
owner-ratified rulings. The TSO twin (same statement list over
`TsoMem.v`, the context ledger in place of the token; the branch's
`WeakCtxPt.v` is the design source, with per-byte floors collapsing to
MaxNat ledgers over single-nat views) is what validates the freeze. Σ as
adopted by main is the statement list of `TsoCtx.v`:
- `CtxId` (explicit record) + `Class CurCtx` (ambient, invariant across
  migration — the one property `CpuId` lacks);
- `mem_pointsto` with a context index, notation-compatible with today's
  `↦ₘ{dq}`/`↦ₘ□`/`↦₈`/`↦₄`/`↦ₛ` tower, ktier axis preserved;
- the leaf AU rules of `WpSconfMem.v` shape, statement-identical above the
  seam;
- lock specs: exported handle unchanged (`locked γ i` stays), payload
  obligation `CtxMorph`, ξ_L internal;
- `wrunning ξ` and the park/resume laws; `wp_next`'s continuation re-anchors
  `CpuId` but ξ is unchanged — framing across a yield is "not a lemma at
  all";
- fence/publication leaves with their TSO-shaped postconditions.

Σ must NOT contain context-irrelevance (`wptsto ξ a v ⊣⊢ wptsto ξ' a v`) —
that is SC-only and would die at cutover. The one-time SC compat shim (§3)
is quarantined and burned.

**T2b — the TSO twin (`iris/TsoCtxTwin.v`), the leg-C gate.** A
self-contained Iris ghost theory over `TsoMem.v` (gmap-image variant), no
WP/language — ghost updates only — that satisfies `TsoCtx.v`'s exported
statement list against the real TSO rules. The design:

- interp `tso_interp img log tvs run parked` owns: the per-byte latest
  auth (`a ↪ (t, v)` — timestamp and value of a's latest write), the
  per-hart view auth, the per-context LEDGER auth (`a ↪[ctx_name ξ] t`
  frags ride inside `ctx_pointsto`, NOT persistent — re-minted at
  transport, which is why migration needs no per-fact bookkeeping above
  the seam), the running pairing (`h ↪ ξ`, whose frag is `own_context`),
  and the parked map (`ξ ↪ T`);
- the SEES invariant, pure, in the interp: for every running pair
  (h, ξ), every ledger entry (a, t) of ξ has `t ≤ tvs h` OR the log's
  message at `t` is authored by h (forwarding covers a thread's own
  unpassed stores); for every parked ξ at T: every entry ≤ T;
- the four gate lemmas: LOAD (interp ∗ own_context ∗ ctx_pointsto ⊢ the
  machine's `load_ok` at this hart returns the fact's value, for EVERY
  admissible view advance — latest-cell agreement kills later writes,
  SEES gives visibility); STORE (append re-registers the fact at the new
  top, own-author arm); TRANSPORT (`ctx_dom ξ ξ' := ∃ T, ⌜ξ's entries ≤
  T⌝-evidence ∗ ξ''s hart's view ≥ T` — minted from release/acquire,
  consumed by re-registering the fact's ledger entry under the prefix
  arm); PARK/RESUME (park publishes at T := log top; resume on any hart
  whose view passed T re-founds SEES in pure-prefix form — no relation
  between the two harts' states needed, the branch's key finding, now at
  a single nat).

THE GATE PASSED (`TsoCtxTwin.v` landed, clean, no axioms): all four
lemmas proven, load even stronger than sketched (no upper bound needed
on the view advance), `twin_init` shows the interp inhabited, and
park/resume confirmed to need NO relation between the two harts'
states. The M sweeps are safe to spend on. What the gate ADDED to the
design (the real Σ instantiation must plan for these):

- three invariant clauses beyond the sketch are load-bearing:
  RUN-INJECTIVITY (a context runs on at most one hart — the real system
  gets it from `own_context`'s exclusivity inside one `sie_cap_gpr` per
  hart), PARKED-NOT-RUNNING, and PER-BYTE LEDGER UNIQUENESS;
- `twin_transport` must run with the state interp open (re-registration
  needs the ledger auth) — fine, the real lock lemmas do;
- under TSO, `ctx_dom`'s SOURCE-side evidence is subsumed by the ledger
  bound plus acquirer-at-top — domination is strictly simpler than the
  weak-memory branch's two-sided form;
- fractional dq is the one deferred refinement: the twin's facts are
  fraction-1 (cross-context agree became exclusivity), and splitting
  registrations across contexts needs per-(byte, holder) uniqueness.

**T3 — close the branch's flagged open items, on the spike, where TSO makes
them cheap.** These are the design risks; resolve before any main sweep
depends on their shape:
- **The real `wp_next` migration** (the branch's "Stage 2", never done).
  Under Ztso every store is a release, so "publish-before-park" is expected
  to be a *theorem* about the scheduler's `p->lock` handoff rather than an
  interim rule; if so, the heavier `WDirty ξ` redesign dies here. Validate
  on the real swtch/scheduler/interrupt cone: `wrunning ξ` threaded into
  the migration, the reschedule path obliged to return it.
- **`CtxFlip`** (general owned payloads across contexts; only clean ptsto
  morphs today).
- **The boundary seam** (sc-parity §6.3, acquire hands out the right floor)
  — declare it closed or fix it.
- The per-footprint vs all-address release floor weakening — accept or
  repair.

**T4 — the standing mirror.** Script: rebase main's swept surface onto the
T-branch kit and recompile the ↦ₘ-using surface (162 files today). Run it
per main sweep (§3). This is the mechanical meaning of "the specs are true
under TSO".

## 2. The SC-degenerate instance (lands on main first)

One new file pair on main, semantics untouched:
- Σ's statements with instances where the view lattice is trivial:
  `wptsto ξ a v` unfolds (sealed) to today's `mem_pointsto a v`;
  `ctx_view_lb`/`ctx_auth` over the unit view; `wrunning ξ` an exclusive
  per-thread token; park/resume causality premises trivially dischargeable.
  All Σ laws proven. `Typeclasses Opaque` everywhere; no unfolding lemma
  exported.
- The compat shim: `↦ₘ`(old) ⊣⊢ `wptsto cur_ctx`(new), in ONE file, used
  only at sweep boundaries, deleted at cutover.

## 2b. The mixed tree — one converted proof among unconverted ones (PROTOTYPED)

`iris/TsoCtxShim.v` + `iris/TsoMemsetCtx.v` are the worked answer, on the
real `memset`. The mechanics:

- A CONVERTED spec differs from its original by exactly three deltas: the
  ambient `` `{XI : CurCtx}`` binder; `own_context cur_ctx` threaded
  beside `sie_cap_gpr` (a stopgap conjunct — M2 folds it into the bundle
  and it disappears from spec text again); the memory footprint stated
  with `ctx_pointsto … cur_ctx`. Registers, premises, ktier axis,
  `wp_next` — character-identical. At the spec's `wp_next`, `CID` rebinds
  and `cur_ctx` does not: the migration-survival property is now VISIBLE
  in the statement.
- The converted spec is PROVED FROM the sealed original (`MS : MEMSET`)
  through the shim: ~10 lines of wand plumbing, memset's own proof
  untouched. Symmetrically the ORIGINAL spec is re-derived from the
  converted one — an unconverted caller mints a context on the spot
  (`own_context_alloc`, free at SC) and loses nothing. And the round
  trip closes as a MODULE (`MemsetRoundTrip <: MEMSET`), so every
  existing linker instantiation can take a converted function unchanged:
  the sweep converts one function at a time, in any order.
- `TsoCtxShim.v` is the ONLY file allowed to state
  `ctx_pointsto ξ ⊣⊢ mem_pointsto` (both wand directions + the
  `[∗ list]` window forms). Its import list IS the tree's live seam
  inventory (`grep -l TsoCtxShim`), and at cutover the file is deleted:
  every leftover unconverted boundary and every SC-only context mint
  becomes a compile error — the remaining worklist, not a soundness
  hole.

## 3. Leg M — the main sweeps (each independently landable, main green after each)

Precedents that say this scale of sweep is routine for this tree:
`completed/explicit-cpuid.md` + its porting guide (an interface axis added
to every WP statement), `projects/instr-subgoal-sweep.md` (214-file
scoreboard), `xv6-bump-playbook.md`. Use the same scoreboard discipline;
spawn subagents for the mechanical files per the orchestration note.

- **M1 — ambient context.** `Context {XI : CurCtx}` into every WP-statement
  file; rebind the `↦ₘ` notation tower to the context-indexed sealed
  definition. Statement-identical above the seam; the explicit-cpuid guide
  is the recipe. Guard the branch's measured `CurCtx` hazard (two instances
  in scope resolve silently to the last).
- **M2 — `wrunning` through the spec spine.** Fold `wrunning cur_ctx` into
  `cpu_own` (recommended: `cpu_own` already appears in every whole-function
  spec and already transports across `wp_next` via `cpu_own_transport`, and
  with M1's ambient ξ its visible arity does not change). Restate
  `wp_next`, swtch (`valid_context`/`SpecSwtch`), the scheduler protocol,
  and the interrupt/reschedule path to carry and RETURN it — proven at SC
  where it is trivial, so the plumbing exists before it matters.
- **M3 — lock payload morphability.** Restate `SpecAcquire`/`SpecRelease`/
  `WpLock` client obligations with the `CtxMorph` premise; derive instances
  structurally (ptsto, pure, persistent — note plain ghost state is
  objective, so ghost-heavy FS payloads morph for free; `∗`/`∃`/big-ops).
  `completed/lock-set.md`'s audit bounds the client list. **Any payload
  that fails `CtxMorph` here is a real TSO bug found early** — that is the
  incremental validation paying off.
- **M4 — the deliberately racy sites.** The only places whose specs
  genuinely change meaning: the lock word itself, `started`, the virtio
  ring/DMA handoff (`design/virtio-driver.md`'s protocol), and any
  flag read outside a lock. Convert to the subjective interface (the
  branch: these "MUST stay subjective — stale reads there are the theorem,
  not a gap"). Give the fence leaves (`WpSconfCtl.v`) and release-store
  leaves their TSO-shaped postconditions, trivially provable at SC, so call
  sites consume the final shape.
- **M5 — audits.** Re-run `main-cycle-port.md` §4's two audit classes
  (invariants opened across an instruction; interrupt-delivery timing) for
  the store-buffer delta; audit `state_interp`-adjacent pure clauses
  (`resv_ok`, DMA's `all_resv` guard) for gmem-vs-log meaning; check
  `design/fs-state.md`'s predicates are built only from Σ-morphable parts.

After every M-sweep: run T4's mirror recompile on the `tso` branch. A sweep
is DONE only when the mirror is green too.

## 4. Leg C — cutover

Only after M1–M5 are everywhere and T4 is green: swap the below-Σ kit for
the T-branch one. The kit (the bounded reproof set, ~20–40 files, from the
seam survey): `RiscvLang.v` (mnode_step memory/Barrier arms, gstate),
`RiscvExec.v` (`wp_hart_step`), `RiscvPtsto.v` (`mem_pointsto`,
`mstate_interp`/`era_interp`/`power_interp`, `resv_*`), `HartSwp.v`,
`HartSMem.v`/`HartMLoad.v`/`HartMStore.v` (the `Mobl/Wobl` obligation
shapes), `WpSconfMem.v`/`WpSconfCtl.v` leaves, `WpLock.v`/`SpecAcquire.v`/
`SpecRelease.v` internals, `WpIntrInv.v`'s engine, `RiscvAdequacy.v`/
`SystemAdequacy.v` (WeakEvAdequacy is the pattern; adequacy's φ export and
the 5-axiom budget must survive `Print Assumptions`). Burn the compat shim.
The 1000+ files above Σ recompile. Flip main.

## 5. Optional aftermath

- A Ztso axiomatic characterization (machine ≡ Ztso ppo) in the branch's
  `WeakAxiomatic` vocabulary — expected far smaller than sRVWMO's T1/T2
  since Ztso is interleaving-representable; the litmus suite stays as the
  definition's regression harness.
- The RVWMO door stays open: same surface Σ, weaker instance, reader-side
  obligations added — the `weak-memory` branch's tier-2 work continues to
  apply.

## 6. Decisions

RATIFIED (owner):
- The semantics is precisely-TSO, written fresh (§1 T1) — minimal per-hart
  view state (one log index), message-log model inherited, no RVWMO
  apparatus. Extend toward RVWMO later, not now.
- The context rides in `sie_cap_gpr`: the bundle exposes the context name
  and internally owns `own_context` (the tie to the current CPU's view
  state), so no proof threads a new SL resource — the bundle already moves
  everywhere the context is needed. `CurCtx` is ambient wherever `CpuId`
  is. (Encoded in `TsoCtx.v`'s header rulings; the M2 sweep edits
  `IntrDefs.v` in place.)
- Staffing: Fable defines the TSO semantics and the context machinery;
  once the leg-M porting recipe is well-defined, Opus/Sonnet agents crank
  the mechanical transformations.
- Leg C is PROTOTYPED EARLY: after the leg-M machinery exists, merge it
  onto leg T and instantiate the context machinery with TSO for real, so
  a wrong-shaped context definition is caught before the M sweeps spend
  effort. (This is the T2 twin + T4 mirror, promoted to a gate.)

OPEN:
1. Lock payload signature: `R : iProp` + `CtxMorph` premise (recommended —
   no arity change at ~every `is_lock` mention) vs the branch's
   `R : CtxId → iProp` with internal ξ_L.
2. MMIO ordering ruling (§1 T1; recommended: strongly ordered).
3. Sequencing against in-flight projects: the M-sweeps touch the same spec
   spine as durable-disk 2c and the sp-migration/instr sweeps — freeze Σ
   first (T2), start M1 only after 2c-body lands or with 2c's predicates
   audited as Σ-morphable (M5 item), and fold the M1 axis into the standing
   sweep scoreboards rather than running competing sweeps.
