# φ and the residues — the pre-port framework surgery (design)

**Status (2026-08-12): DESIGN, nothing landed.**  The M6 robustness
theorem ([`completed/weak-memory-m6.md`](../completed/weak-memory-m6.md),
`WeakCompose.xv6_weak_robust`) carries a declared residue
(`WeakCompose.v` §6).  This file is the design for discharging it —
worked out with the coordinator against the recorded blocking analysis —
and the list of framework changes that must land BEFORE the mass SC→weak
port, because they change the leaf interfaces the port replicates.

## 1. `pf_violation_free`: the three-state points-to (C/D/S)

The MODEL needs no change: `wm_ak`/`w_pub`/`w_relp` are landed, and
`load_post_at`'s coh-absorbs-post-view choice is LOAD-BEARING (it makes
`readable` block stale-reads-under-a-high-floor, concentrating φ's whole
preservation proof into the fragment-load-of-a-hazarded-byte arm — do
not "simplify" it away).  The blocker was that an auth ghost cannot see
outstanding-fraction distribution.  Fix: the hazard state lives IN the
element fragments agree on.  Per byte, a three-state protocol in the
wlat auth, mirrored by the points-to:

- **C (clean)** — every WCplain message on the byte is published.
  `↦[C]{q}` splits/joins as usual.
- **D (dirty)** — latest message is an unpublished WCplain store by the
  holder.  EXCLUSIVE, no fractions.  A WCplain store takes
  `∃s, ↦[s]{1}` and produces `↦[D]`; CS re-stores stay at D (this is
  exactly what killed the escrow variants — here it is free).
- **S (sync, absorbing)** — permanently racy-readable (started, lock
  words); entered once by discarding at init; yields a PERSISTENT
  witness.  S-stores require `⌜w_relp ∨ rl ∨ ak_latest⌝` (WCrel/WCexcl
  only) — the kernel's racy-publish and AMO sites satisfy it.

D→C flips at publication: the flag/rl store raises the author's `w_pub`
to the fresh top (covering all prior own stores), and the release leaf's
ghost section flips the author's dirty bytes clean BEFORE the deposit
egresses; transfer lemmas require C (automatic).  Closure argument:
fragment-loads present C, agreement + the invariant "C ⟹ all WCplain
messages on the byte published" (per-byte history stays clean below a
clean top: cross-author overwrites need the exclusive D; same-author
publication is `w_pub`-monotone) refute the violation; racy loads use S
(S-bytes never carry WCplain); stores/fences free (`ws_bounded`).
Freebie: any store immediately after a release fence is WCrel and
produces C — sound, it is born-published.

**SC-parity survives**: `a ↦w v := ∃ s, a ↦[s]{1} v` for owned memory;
proofs holding `{1}` never mention the state; it surfaces ONLY at
fraction splits (require C — shared bytes are published by
construction), the release/deposit lemmas (do the flip), and the racy
rules (use S).  The φ conjunct + the three-line adequacy export then
land per the D-M6-6 wiring plan unchanged (`WeakGhost.v` interp,
`WeakAdequacy.v` continuation).

## 1b. THE SURGERY LANDED (2026-08-12) — deltas and flags

Landed green (31 files, lemma_diff clean, all Print Assumptions
preserved).  Deltas from §1's sketch, all improvements: TWO ghost maps
(`weak_lat_name` untouched + `weak_cds_name : gmap Z wcds`,
`wcds := WClean | WDirty CPU | WSync`) so `wlat_pointsto` keeps its
meaning verbatim and the window machinery is untouched; PUBLICATION IS A
LOG PREDICATE (`wpublished log tid p` — a later WCrel message by the
same tid — implying real `w_pub` coverage, so `wlat_interp` keeps its
arity; the `w_pub` bridge is a one-line machine fact owed to the φ
export); the S state is entered by DISCARDING THE STATE ELEMENT
(persistent `sync_byte`, byte stays writable, plain stores excluded by
dfrac algebra, no premise threading); owned store prims need NO side
condition (`WCexcl ↦ WDirty` is a sound weakening); and the RELEASE
CLASS IS NOW LOAD-BEARING (`wQ_store_w` gains
`w_relp → k ≠ WCplain`, `wQ_fence` gains the `pw∧sw → w_relp` arm,
`wrelease_core`/`wstarted_set` take `w_relp = true` — the D→C flip at a
release IS the release store's own class transition).  Lock words left
CLEAN, not SYNC (nothing racy-reads them — the spin is `ak_latest`);
mint S for them only if a racy lock read ever appears.

**TWO OPEN FLAGS from the landing:**
- **`↦wo` is CpuId-indexed and does NOT cross `wp_next`** (exactly
  `WeakSmodeFrame` §5's control).  The migrating/`cobj` (S-mode
  context) world needs a CONTEXT-indexed dirty author — a real design
  item for the port; the interim rule (stated in `wpt_own`'s header):
  a migrating context PUBLISHES before it moves.  `WkMemmoveLoop`'s
  `wssb1_spec` hypothesis is now unrealisable as stated (it compiles —
  the leaves there are Prop hypotheses) — fix when that file is next
  touched.
- **DMA messages (tid None) are exempted** from the clean/dirty
  invariants and can never be published; Layer 1's `bad` predicate must
  therefore carry "the message's tid is a hart" — closed by the
  DMA-tid unification item below (seam 1c/d).

## 1b'. φ STAGE 1 LANDED (2026-08-12): WeakViolation.v + sync threading + the sweep map

Landed green: `WeakViolation.v` (`no_violation` aligned term-for-term
with `WeakRobust.violation`; the `nv_byte`/`nv_hart` induction algebra;
the three discharge arms `nv_byte_of_{pointsto,own_st,sync}`; the
`w_pub` bridge `wpublished_w_pub` under the honest `wpub_covers`
machine-invariant premise), the `sync_win` premise threaded into the
racy/started rules, the started escrow made SYNC (minted inside
`wstarted_alloc`, which already proves the empty-history fact — so
adequacy's statement is untouched), and the machine-level reduction
`nv_hart_weffs` (`WeakEff` §5b): a leaf's φ obligation = one `nv_byte`
per byte of its own effect trace, framed elsewhere by
`weffs_coh_frame`.

THREE DURABLE FINDINGS: (1) **every leaf raises `coh`, because every
instruction FETCHES** (rv64d fetch = Read_plain), so the interp
conjunct cannot ride only the memory leaves — all ~50
`wmstate_norg`-reassembly sites pay, with the fetch arm vacuous via
`winstr_flat`'s `latest_ts = 0`; (2) the two shortcut candidates are
REFUTED — a pinned read of a hazarded byte ALWAYS violates (pinned
reads are exactly the dangerous ones), and no view-bound invariant can
substitute for ownership (own-store + `fence rw,rw` floods `vrNew`
above a foreign hazard); (3) a **zero-width release-class write breaks
the `w_pub` bridge** (`store_post_run` folds per byte, so a width-0
WCrel message raises nothing) — `wpub_covers_write` carries the
nz-width premise explicitly, dovetailing with `WeakInterpProj`'s
`nz_writes` and `sail_shaped`.

**THE SWEEP IS COMPLETE (2026-08-12): φ IS EXPORTED.**
`weak_system_adequacy_phi` delivers
`no_violation (wglog g2) (wgws g2)` at every reachable state on exactly
the 5 rv64d baseline axioms; `weak_system_adequacy` is its three-line
projection (statement byte-identical; the vestigial unused `sieG`
binder dropped from `_phi` only).  Landing shape worth knowing:
`nv_hart` sits after `ws_bounded` in all four interpretations (device
rules untouched); the certificate layer was upgraded GENERICALLY
(`wQ_eff`/`wQ_fr`/`wstep_cert_fr` + `wstep_cert_pair`/`_fr_pin` for the
AMO's `wP_eff_pin`) so no `wcert_*` was re-proved; the AMO path uses
the option-2 callback interface (`wacq_cb`/`wrel_cb` return
`wmstate_rest_nonv` + the leaf-minted fetch fact; `wwp_acquire_swap`
pays the lock word from the retargeted clean bundle in `wlock_inv`);
the fetch arm everywhere is `WeakFunnel.winstr_nv` (any-log form —
store leaves must pay at the POST-store log); `nv_ok` (hart-indexed
per-byte form) is the owned-byte arm — the clean/`nv_free` vs `nv_ok`
gap IS the WDirty arm; `WeakKpt`'s walk leaf-slot mints `nv_free` at
the pre-state before `Hclose` (consumer-free today — feeds the walk
option-(a) work).  Gotcha: `iApply` SHELVES an unfilled Prop argument
("No such goal") — `assert` footprint premises before the `iApply`.
CONSEQUENCE FOR THE M6 RESIDUE: seam (2) (`pf_violation_free`) is now
DISCHARGED at the WeakLang level — it remains a premise of
`WeakCompose.xv6_weak_robust` only through seam (1) (the
WeakLang ↔ wp-machine lift), which is where the export gets consumed
when `WeakComposeLang.v` lands.

## 1c. The migration test: the ownership ping-pong (Stage 1 now, Stage 2 at the port)

**Stage 1 — `WkOwnPingPong.v` (buildable on the C/D/S + φ base; the
protocol's acid test).**  Two harts, one flag word (lock, stays CLEAN —
`ak_latest` AMO acquires, WCrel releases), one TRANSFERRED byte x, one
deliberately PRIVATE byte y:
A: `x := 1` (dirty-A), `y := 1` (dirty-A, never transferred);
`fence rw,w`; flag store (WCrel — the flip bundle carries x, NOT y);
deposit `↦w{1} x`.  B: spin-acquire; `load x = 1` (clean arm);
`x := 2` (dirty-B — author alternation); fence; release back.
A: re-acquire; `load x = 2`; still uses its dirty y freely (the flip is
per-byte selective; the frame is real).  Tests in one proof: the
release-site `wlat_flip` at a REAL site (its "my WCrel message is the
log's last" premise holds because the flip is atomic with the append),
`wpt_own_of_wpt` on the receiving side, the
`WDirty A → WClean → WDirty B` cycle, the `⊒view_byte` transfer through
the payload, and — with φ landed — all three arms of the
`no_violation` preservation trichotomy exercised in one run.

**STAGE 1 LANDED (`WkOwnPingPong.v`, 798 lines, 2026-08-12; σ-altitude
theorems closed, WP-altitude ones on the 5 baseline axioms).  THE FLIP
RECIPE THAT PROVED OUT — the port-recipe answer:** a release that
EGRESSES owned memory is a DIFFERENT CORE from `wrelease_core` (which
consumes the payload at the PRE-state, while `wlat_flip` needs the
post-state authority where the WCrel message is the log's last).
`wrelease_flip_core`: lock element update → flip → reassemble `↦w{1}`
at the element's own timestamp → `wwp_release_deposit`.  The missing
class fact (`wm_ak = WCrel` on the nose, which `wQ_store_w`'s
existential deliberately withholds) is read off the φ-upgrade's OWN
trace fact with no new certificate: `wQ_eff_store_rel`
(`ak_latest = false` + `w_relp = true` pin the appended message's
class).  A ported release keeps its leaf interface + one pure lemma
application; the RECEIVING side needs NO new rule
(`wwp_acquire_loop_cert` verbatim).  `pp_return_leg` exhibits the
private byte surviving BOTH handoffs dirty; `pp_receive_and_dirty`
closes the `WDirty A → WClean → WDirty B` cycle; `pp_phi_three_arms`
pays the trichotomy at one state.  TWO PRE-PORT GAPS RECORDED:
(1) **`wpt_load_rule_own` is missing** — a hart cannot yet read its own
DIRTY byte through the collapse rule (`wpt_load_rule` goes through
`wlat_lookup`, which wants the clean half; the ingredients
(`wlat_lookup_elem`, `readable_latest_pin`) are owned-ready — a
~10-line copy).  A real blocker for ported proofs that re-read what
they just wrote; land it with the site-predicate pre-port batch.
(2) `wpt_store_rule_dirty`/`_post_dirty` exist only in the example for
the exhibit — ported store sites keep the absorbing `↦wo` form.

**STAGE 1.5 — THE FRAMING PATTERN (the user's intended shape,
2026-08-12; supersedes the interim publish-before-park rule and
DISSOLVES the context-indexed-WDirty redesign).**  The required
pattern: ONE thread owns several locations, accesses them, calls
`yield`, resumes on another CPU — and the ownership facts FRAME AROUND
the yield call (they appear in neither its pre- nor postcondition).
Yield internally: `fence rw,w` on the old CPU before migrating, a
fence/acquire on the new CPU before returning.  How it lands on C/D/S:

- MACHINE SIDE, inside yield, zero ghost ops: the old-CPU fence arms
  `w_relp`, so the migration handoff store (the scheduler-flag
  release) is WCrel — BORN-PUBLISHED, covering every pre-yield store
  of the old hart including all the thread's dirty bytes.  The
  new-CPU fence installs the floor.  φ/`no_violation` needs no change:
  the new hart touches only published messages.
- GHOST SIDE: clean `↦w` facts frame FREE (vProp view-monotonicity;
  yield only raises the thread's view).  DIRTY facts frame AS-IS
  (`WDirty A` survives the crossing) and are LAZILY UPGRADED at first
  use on the new CPU: extend the own-load/own-store leaves to accept a
  foreign-dirty element WHEN PUBLISHED — evidence = a persistent
  `w_pub` lower bound (the WeakViewMono sixth mono_nat, now
  load-bearing) linking the element's timestamp under the floor; the
  leaf's interp-open section retargets the `wcds` state (flip to
  WClean on load; to `WDirty cpu_id` on store) via `wlat_flip`'s
  published premise.  Yield's whole memory-visible postcondition is
  that ONE persistent floor token.  Publication-at-migration + lazy
  retarget ≡ context indexing, with no `wcds` redesign and no leaf
  statement changes beyond the acceptance arm.
- SPEC REFINEMENT (2026-08-12, from design review): in the PORTED
  whole-function `yield()` spec, the resume-side facts travel as ONE
  persistent bundle `yield_lb ξ V := ctx_view_lb ξ V ∗
  ⌜pub_covers_view c_old V⌝` — the sc-parity `ctx_view_lb` (which is
  what crosses `wp_next`; the example's raw `⊒V` is its
  altitude-lowered stand-in, used only because the example's thread is
  not a registered WeakCtx context) plus the publication half stated
  OVER THE VIEW, not over a position: the framed dirty fact's
  `⊒view_byte a t` gives `t ≤ V(a)` by construction, so the `t ≤ n`
  side condition disappears, and the release store can mint coverage
  of V without naming any position (its watermark is the fresh top).
  The two halves are independent and both needed: `ctx_view_lb` is
  about what the context OBSERVED (frames clean facts; implies nothing
  about `w_pub`, which is deliberately inert and not a view
  component); the pub half is about what the world may READ of the old
  hart's writes (the lazy-upgrade evidence + the φ payment).
  Certificates (`wstep_cert`/`wQ_fr`) appear only in the
  example-altitude lemmas because the example has no Code file; in the
  ported spec they are proof-internal (CodeYield facts), exactly as in
  the SC tree.
- **STAGE 1.5 LANDED (2026-08-12; `WkYieldFrame.v` 652 lines +
  WeakGhost/WeakVProp additions; all green, adequacy unchanged).**
  TWO FINDINGS: (1) the `w_pub` mono_nat is a DEAD GHOST (its authority
  field was deleted with WeakCtx) — and re-threading it would have been
  wrong anyway (the arm needs the converse of `wpublished_w_pub`, not a
  machine invariant); the token rides the LOG's mono-list instead:
  `pub_floor c n := ∃ l, wlog_lb l ∗ ⌜wpub_upto l (Some c) n⌝` and the
  view-indexed `pub_covers_view c V` — ZERO new ghost state, minted at
  the release append.  (2) THE ACCEPTANCE ARM COLLAPSED TO ONE LEMMA:
  `wpt_own_upgrade` retargets WDirty c → WClean and returns an ORDINARY
  clean `↦w{1}` — no "load/store with evidence" variants, no leaf
  statement changes; `wpt_load_rule`/`wpt_own_of_wpt`/
  `wpt_store_rule_own` then apply verbatim.  The view-indexed token
  killed the timestamp side condition as predicted.  Yield spec shape
  as designed: `wyield_park_core` consumes/returns only the handoff
  lock + `pub_covers_view i V`; `wyield_resume_core` returns the holder
  token + `⌜V ⊑ ws_view⌝`; no points-to anywhere.  `wpt_load_rule_own`
  (ping-pong gap 1) landed.  Word-level `↦wo` wrappers unneeded (byte
  altitude covers via wpt4/8_own decompositions).
- THE EXAMPLE `WkYieldFrame.v` (as specced): thread T on hart A: `x := 1`
  (dirty-A), holds a clean fact `z`; yield (fence rw,w; handoff-flag
  release; [migration]; new-CPU acquire/fence; return); resumed on B:
  `load x = 1` (the lazy upgrade), `x := 2` (re-dirty at B), use `z`
  (framed clean) — with x and z appearing ONLY in T's own pre/post
  and in NO yield spec component.  Stage 1's transfer example remains
  valid as the lock-payload test; this is the FRAMING test.

**STAGE 1.6 — THE UPGRADE MUST BE INVISIBLE (user directive,
2026-08-12; CORRECTS Stage 1.5's ergonomics — `wpt_own_upgrade` as a
caller-applied lemma is NOT acceptable; the first touch after
migration must cost zero script lines).**  The fix: CONTEXT-index the
owned points-to and move the upgrade INSIDE the leaf rules:

- `wpt_own ξ a v := ∃ t b, elem (t,v,b) ∗ ⊒view_byte a t ∗
  (⌜b = None⌝ ∨ ∃ c, ⌜b = Some c⌝ ∗ ctx_wrote ξ c (view_byte a t))`
  — indexed by the WeakCtx context ξ, NOT CpuId, so it frames across
  yield/`wp_next` unchanged.  `ctx_wrote ξ c V` is a persistent "ξ
  wrote via hart c at-or-below V" breadcrumb minted by the own-store
  leaf.
- THE CTX MIGRATION INVARIANT (scheduler-protocol-internal, invisible
  to callers): for every hart c that ξ is NOT currently running on,
  `ctx_wrote ξ c V ⊢ pub_covers_view c V` — maintained by yield
  (park publishes, so the old hart's breadcrumbs gain coverage; the
  invariant rides the `wrunning ξ` bundle / WeakCtx machinery, where
  ctx_view_lb already lives).
- THE OWN LEAVES take `wrunning ξ ∗ wpt_own ξ …` (the sc-parity
  conversion threads the ctx token through every function ANYWAY, so
  this is not new per-caller plumbing) and case-split INTERNALLY:
  b = Some (current hart) → the own-dirty path; b = Some (other hart)
  → the migration invariant supplies the pub evidence and the leaf's
  ghost section retargets (the Stage-1.5 `wpt_own_upgrade` BECOMES
  leaf-internal machinery, not caller API).  Caller scripts are
  IDENTICAL before and after yield — true SC parity.
- The wcds ghost stays HART-indexed (machine truth); only the logical
  layer is context-indexed.  Yield's spec: pre/post carry `wrunning ξ`
  (a scheduler resource like cur_proc, NOT part of the memory frame)
  and no memory facts; park's mint feeds the invariant instead of
  returning a caller-visible token (pub_covers_view remains as
  internal machinery).
- **STAGE 1.6 LANDED (2026-08-12, 12 files, green; adequacy unchanged;
  the upgrade lemmas are DELETED from the API).**  Acid test passed
  verbatim: `WkYieldFrame.wyf_touch` (load x; x := 2; load z) is ONE
  lemma instantiated argument-for-argument on hart A before the yield
  and on hart B after migration, at a byte still `WDirty A` in the
  ghost map — zero upgrade applications.  As-landed shapes:
  `CtxId := CtxNames {ctx_vn; ctx_wn}` (moved to WeakGhost; opaque);
  breadcrumbs = auth (gmap nat max_nat) per context (`ctx_wrote_pos`
  core-persistent for free); `ctx_migr ξ c` rides `ctx_run`/`wrunning`
  with the live hart's entry carrying a position BOUND instead of
  coverage; park converts to `ctx_migr_all` (all-covered, hart-free) —
  which is why resume needs no memory evidence and yield's park
  returns a scheduler resource naming no byte/view/hart-publication.
  FINDING: own LOADS need no migration machinery at all (a load moves
  no wcds state — foreign-dirty reads through `wpt_load_rule_own`
  verbatim); only the STORE retargets, and the post-log offset is
  absorbed by `pub_transfer_snoc` (own append can't be a foreign
  release).  Sanctioned alias: `wpt_own_h` (hart-indexed) survives as
  the carrier of the wpt4/8 towers and M-mode batch-2 leaves that
  never cross wp_next — documented as not-the-API, converts only
  through clean `↦w{1}`.

**STAGE 1.7 — THE AMBIENT CONTEXT CLASS (user directive, 2026-08-12):**
`Class CurCtx := cur_ctx : CtxId.` + notation making the bare owned
points-to (`↦wo` and its width towers) elaborate to
`wpt_own cur_ctx …` by typeclass search, so existing/ported proofs
write access sites UNCHANGED and take `` `{CurCtx} `` once per
lemma/section (arriving with `wrunning cur_ctx`, like `cur_proc`).
SOUNDNESS OF THE AMBIENT TRICK: ξ is invariant across the whole
function INCLUDING migration — the exact property `cpu_id` lacked
(which is why explicit-cpuid had to go the other way).  ξ stays
EXPLICIT at: lock invariants (mostly moot — payloads carry the
context-free clean `↦w{1}` via the release flip), the
scheduler/WeakCtx machinery (multiple contexts in scope), and any
context-quantifying spec (yield's own).  DISCIPLINE (from the
explicit-cpuid scar tissue): `Typeclasses Opaque` + single-instance
hygiene so two `CurCtx` instances never silently coexist; two-context
lemmas use the explicit spelling only.  Acceptance: the examples'
access scripts written with bare `↦wo`, zero explicit ξ outside the
yield/scheduler lemmas.
**LANDED (2026-08-12, 3 files, green, adequacy unchanged).**  As-built:
class + notation + convention block in WeakVProp §3''; CpuId's
conventions mirrored exactly (bare singleton class, ZERO instances —
every supplier a local binder; notation over the primitive), PLUS
`Typeclasses Opaque cur_ctx` and the load-bearing NAMED-binder rule:
`` `{XI : CurCtx} `` not anonymous — Coq auto-names an anonymous
instance `H`, colliding with `iIntros "%H"` ("H is already used").
Acceptance passed: `wyf_touch` takes NO context argument and its two
instantiations (hart A pre-yield, hart B post-migration) differ only
in the hart; `cur_ctx` resolves to the one section instance on both
sides — the same ξ, the property CpuId lacks.  MEASURED HAZARD
(documented next to the class, not papered over): with two `CurCtx`
hypotheses in scope, `cur_ctx` silently resolves to the LAST-declared
one (no warning) — so transfer-joining lemmas (both sides' contexts in
scope) MUST spell ξ explicitly; explicit terms print unsugared, so the
spellings stay visually distinct.  `_cur` one-line corollaries wrap
the own rules; ξ-explicit originals remain the primitives;
`wpt_dirty` deliberately stays explicit (the sharp exhibit form).
Process note: use DISTINCT build-log sentinel names per run (a dead
build's `echo EXIT` can append into a same-named live log).

**Stage 2 — the REAL migration test (a PORT TARGET, gated on the S-mode
scheduler cone): the same program with the handoff replaced by
`wp_next`/`p_sched`** — the parked-continuation crossing where the
proof context teleports instead of passing through an explicit payload.
The parked closure may contain only migration-stable resources
(`cobj ξ`, clean `↦w`, `ctx_view_lb`); the park site inherits "flip
everything dirty in the closure at the parking release".  Stage 2
decides empirically between the INTERIM RULE (publish-before-park —
matches what xv6's scheduler crossing physically does: the `p->lock`
release is fence-then-store; prior: this survives, and the
context-indexed dirty author is never needed) and the heavier
`WDirty ξ` redesign.  Keep Stage 1's program shape so Stage 2 is a
drop-in replacement of the handoff.

## 2. Per-residue framework changes

- **WeakLang ⇐ lift (seam 1)**: (a) fold INTERRUPT DELIVERY into the
  oracle stream — `plic_step` writes other harts' registers, which the
  log-only wp machine cannot express; the hart's mip-visible bits become
  per-hart oracle events in `psail`, consistent with the MMIO seam.
  (b) The fused-RMW ⇐ direction needs the AMO's silent prefix
  choose-free — check rv64d, restrict `silent_run` if so.  (c) Unify
  the DMA tid (WeakLang stamps `Some n_disk`, not `None`) — erases
  seam (1d).  Then `WeakComposeLang.v` is one induction.
- **Static side conditions (seam 3) + `sail_shaped` (seam 6), one
  shared investment**: SITE PREDICATES in the leaf rules — the
  racy-load leaf takes `⌜decode(pc+4) = fence r,rw⌝`, the release leaf
  `⌜decode(pc−4) = fence rw,w⌝`, vm_compute-discharged per site — plus
  a GENERATED whole-image enumeration lemma (gen_code.py-family tool)
  proving every text site satisfies its predicate; `sail_shaped` rides
  the same sweep (fetch reads fixed text, Decision 4).  `byte_ok`
  becomes structural from C/D/S (S-bytes are the sync bytes).  What
  remains of D-M6-8(c) is the pc-in-text/message-supported bridging,
  largely closed by C/D/S ownership of function-pointer bytes.
- **MMIO (seam 4)**: keep — M5's device views; the oracle-stream design
  is already positioned for it.
- **PARM (seam 5)**: keep — the Rocq-9 port is the optional upgrade.
- **`bad_wf` STAYS DECLARED even with φ proven**: a bad SCC
  (mutually-justifying owned-read LB) admits no exhibit — its events'
  pf-realization is circular and its messages never enter the pf log —
  and a certified full machine does not help (certification is vacuous
  over completed behaviors; LB completes).  It is the minimized kernel
  of the old blanket axiom ("no owned thin-air").  If ever attacked:
  a value-flow argument (the SCC's reads' values must be produced by
  its own writes), research not plumbing.

## 3. Sequencing (why this precedes the port)

Land BEFORE the mass port, in order: (1) the C/D/S points-to surgery +
release-flip lemmas (rewrites the leaf interfaces the port replicates);
(2) the site-predicate premises on racy/release leaves (same reason);
(3) the DMA-tid and mip-oracle unification (trivial; simplifies
`WeakCompose`).  Additive afterwards: φ's conjunct + export, the
whole-image sweep tool, `WeakComposeLang.v`, the PARM port.
