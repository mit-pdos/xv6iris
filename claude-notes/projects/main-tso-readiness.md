# Main TSO-readiness: the incremental landing project

**Status**: owner-authorized handoff spec (2026-08-28).  This document is the
complete brief for the agent executing the incremental restructuring of
`main` toward TSO-readiness.  It was written by the coordinator of the TSO
port (branches `tso` and `tso-flip`) at the point where the real-TSO tree
stood at 1100/1296 green with every remaining red characterized, and it
encodes everything that effort learned about how to do this conversion
without repeating its mistakes.

**Mission**: transform `main` — in SLICES, each leaving main FULLY GREEN —
into "TSO-ready SC": a tree whose *statements* (specs, resource shapes,
channels, obligation premises) are converged with the TSO proof's, over
*sealed SC bodies*.  The final TSO cutover ("leg C") then becomes a
below-interface swap of the sealed bodies plus the machine, with the
statements already right.  Nothing in this project introduces weak-memory
semantics; every slice is SC-provable.

**Non-negotiable ground rules**
- `main` ends every slice FULLY GREEN: full build + `make audit` at its
  baseline, zero `Admitted`, zero new `Axiom`.  A slice that cannot close
  green gets reverted and re-characterized, never left half-open.
- Numbers are citable only when sentinel-backed (see Build discipline).
- Design questions get characterized and surfaced to the owner, not
  guessed.  Refutations of this document get recorded in place.
- Verify EVERY claim this document makes about main against main's
  actual HEAD before editing (see Slice 0 and "The two no-ops").
- **THE SPELLING RULE (added after an owner audit caught this document
  carrying superseded intermediate designs — the §0.27′ `U` parameter,
  a floor-parametric `initlock`, era-image floor-0 locks, a stale
  `kpt_creds` formula):** this document is authoritative for
  PRINCIPLES, ORDER, and PROCESS ONLY.  For any concrete definition,
  statement, or lemma shape, the AUTHORITATIVE SOURCE IS THE TREE — the
  current `tso-flip` tip (plus the kpttree files named in
  tso-handoff-current.md) for T-leg shapes, `tso` for M-leg statements
  — read at execution time.  Where this document writes a formula, it
  is illustration; if it disagrees with the tree, the tree wins and the
  discrepancy is recorded.  The port's history is a graveyard of
  ruling-era sketches reshaped by the build (four shapes for one lock
  word); do not land a sketch.

---

## 0. The reading list (in order — do this before any editing)

All paths are on the `tso` branch unless stated.

1. `claude-notes/durable-notes.md` — guiding principle, build
   instructions, cross-cutting gotchas.  Then
   `claude-notes/remote-build-gcp.md` — ALL builds run on the GCP VM,
   serialized under `flock /tmp/claude-gcp.lock`.
2. `claude-notes/projects/tso-port.md` — the OWNER RULINGS, §0.11′–§0.39′.
   These are the design law of the port.  The ones this project lands the
   shapes of: §0.27′ (p->lock resume tie), §0.28′+addendum (trap caps come
   from the trapping site), §0.32′ (visibility-free page ownership;
   byte_any/page_own bodies), §0.33′ (channel inventory; the two no-ops),
   §0.35′+§0.38′ (is_lock context-relative; the lk_floor disjunction),
   §0.36′ (kernel-page-table fact context-relative), §0.37′ (U-mode
   deferred — DO NOT TOUCH), §0.39′ (handler contract context-dependent).
3. `claude-notes/projects/tso-flip-replay.md` — THE REPLAY RUNBOOK: the
   M-leg statement flip as a *procedure* rather than a diff, written
   specifically to re-run on a moved main.  This project's Slice 2 is that
   procedure, corrected by the findings below.
4. `claude-notes/projects/tso-machine-flip.md` — the A6 amendment series:
   the measured findings of the real-TSO leg.  You do not need the
   below-seal content; you DO need the lessons cited throughout this
   document by A6-number.
5. The decision memos (design rationale, worth skimming):
   `tso-transport-memo.md`, `tso-park-protocol-memo.md`,
   `tso-absorb-memo.md`, `tso-pin-memo.md`, `tso-m4-memo.md`.
6. Lane notes with measurements you will reuse:
   `tso-kpt-lane.md` (K-series), `tso-intr-lane.md` (the λ-payload
   identity measurement — the single most important cost-avoidance
   finding, see §4.1 below).
7. The cautionary record: `/shared/tmp/main-channel-refactor-design.md` —
   the two withdrawn refactorings, each refuted by measuring main.  Read
   it to internalize WHY measurement precedes design here.

**The two reference trees**
- Branch `tso` (the "M-leg"): main's proof restructured with the full
  context vocabulary over SC semantics, FULLY GREEN (~1331 files).  This
  is your primary reference implementation — the statements you are
  landing exist there, proven.
- Branch `tso-flip` (the "T-leg"): the real-Ztso tree.  Reference ONLY for
  the corrected shapes listed in §4 (the T-leg refuted several M-leg first
  drafts).  Never port its below-seal tiers (see §2).

---

## 1. Why the plan is shaped this way: the two no-ops

The first design doc for main proposed two refactorings; both were
withdrawn when measurement showed main already had the right structure
(§0.32′, §0.33′): devsw travels the park chain (console_ready →
park_world → ParkCap → p->lock → ut_caps → syscall_env), and
`main_deposit` (SpecMainSecondary.v:105 on main) already carries the
correct nine started-deposit rows.  The diagnosis: main's CHANNEL
architecture was already right — what main lacks is VOCABULARY (contexts,
floors, the context axis on persistent handles).  Vocabulary cannot be a
no-op.  That is what this project lands, and it is why Slice 0 is
mandatory: every "main needs X" claim must be re-verified against main's
HEAD, because main's architecture keeps turning out better than remembered.

---

## 2. The seal principle (what lands vs what never lands)

The port's architecture is a SEAL: a sealed module of context-indexed
resources (`TsoCtx.v` on the M-leg) whose *statements* all proofs are
written against, and whose *bodies* differ per leg.

- **Above the seal — LANDS ON MAIN**: every spec statement, resource
  bundle shape, distribution channel, obligation premise, handle
  definition, and typeclass discipline.  On SC these are provable with
  trivial bodies (visibility is universal; every bound is vacuously
  satisfied) but the statements are real and identical to the TSO ones.
- **Below the seal — NEVER LANDS ON MAIN**: the ledger/timestamp tiers,
  racy-window kits, visibility algebra (`ledger_vis`, `visibleb`,
  windows, pins, drains), `TsoMemPa`/`TsoGhost`, and the Ztso machine.
  These are the T-leg's private content and swap in at leg C.

Test for any piece you're unsure about: "does an SC proof of the
statement exist with a trivial body?"  Yes → above seal, land it.
No → below seal, leave it.

---

## 3. Slice 0 — MEASURE (read-only, produces this project's real numbers)

Before any edit, produce an inventory report:
1. Diff main's HEAD against the `tso` branch's merge-base: which
   subsystems' spec files diverge, how many spec signatures each, where
   the M-leg rehearsal's seams (named in `tso-flip-replay.md` and the
   "CUTOVER REHEARSAL" commits `8f675587b`, `d3db2b27`) fall on TODAY'S
   main — main has moved since the M-leg branched, and the runbook was
   written expecting that.
2. For every §4 shape below: verify main's current form (the way §0.33′
   was verified — grep the actual definitions, don't trust this doc).
3. Size each Slice-2 subsystem tranche (file count, spec-signature
   count) so the landing order can be committed to with real numbers.
Record the inventory as the project's first notes entry.

---

## 4. Slice 1 — the context core (additive; green by construction)

Land the sealed context module with SC bodies.  Reference: `iris/TsoCtx.v`
on the M-leg (statements), with these MANDATORY inclusions the M-leg's
first draft lacked (the T-leg had to retrofit them — A6.96/A6.97):

- `ctx_floor ξ lo` — persistent lower-bound witness on a context's bound.
- `ctx_bound_raise` — buy a floor with a receipt (`own_context ξ -∗
  hart_view_lb K ==∗ own_context ξ ∗ ctx_floor ξ K`).
- `own_context_floor_view` — cash a floor into the receipt pair
  (`∃K, view_lb K ∗ ⌜lo ≤ K⌝`).
- `ctx_floor_le` (monotone weakening) and `ctx_floor_dom` (a floor the
  sender can discharge is one the receiver can discharge — free
  transport across crossings; ten lines on the T-leg, A6.117).
On SC all three have trivial bodies (define `hart_view_lb`/`view_lb` as
`True`-like sealed props or vacuous bounds), but they must EXIST with
these exact interfaces: the T-leg measured that every tier of the proof
eventually consumes the buy/carry/cash triple (locks, KPT, park, trap).

Also from day one: `CtxMorph` (transport class), `ctx_parked`/deposit/
absorb statements (the park channel), and the ambient-context typeclass
(`CurCtx`) with `Typeclasses Transparent` declared — see §6 gotcha (g).

This slice is purely additive: no existing file changes; main is green by
construction.  Land it alone, certify, then start Slice 2.

---

## 5. Slice 2 — the statement conversion (the wide churn, by subsystem)

Follow `tso-flip-replay.md`'s procedure: leaves first, then the function
tier; the migration equivalence (ctx fact ⊣⊢ plain fact, SC-only) stays
EXPOSED while subsystems convert, so converted and unconverted files
coexist green; it is deleted at Slice 4's seal.  Each subsystem tranche
is one green landing with the close-or-revert rule.

### 5.1 THE CORRECTED SHAPES — with their VALIDATION STATUS

This is the heart of the handoff.  The T-leg refuted several M-leg first
drafts; main should land the corrected forms so it never repeats the
retrofits.  **But entries below differ in how validated they are, and
the difference is load-bearing** (an owner audit caught this document
presenting a ruled-but-unbuilt sketch as a finished shape).  Each entry
is tagged:
- **[LANDED]** — built and certified green on the T-leg: land the shape
  as the T-leg spells it (diff against the CURRENT tso-flip tip, not
  this document — the doc can lag the leg).
- **[MEASURED]** — the necessity is measured and/or one instance exists,
  but the full conversion is unlanded: land the *principle*, take the
  spelling from the existing instance, and expect the T-leg to refine.
- **[RULED-ONLY]** — an owner ruling names the mechanism but the T-leg
  has NOT built it: do NOT land any concrete spelling from this
  document.  Either wait for the T-leg's landing, or land only the
  weakest statement-level placeholder the ruling forces, marked for
  revision.  History says ruled-only sketches get reshaped by the
  build (three times for the lock word alone).

**(a) [MEASURED] λ-payloads for every context-mentioning lock payload —
NEVER the constant embedding.**  The single biggest avoidable cost.  The intr lane
measured (tso-intr-lane.md) that `<{ P }>`/const_pay embeds the payload
AT the handle's context, so the same lock at two contexts names two
DIFFERENT Iris invariants — no freshness premise can ever bridge them —
and retrofitting costs a 457-site surface across 163 files (the four
trap-path payloads alone: proc_lock_res 44 sites/19 files, disk_res 175,
ticks_res 16, cons_res 10).  The correct form: `is_lock … (λ ξ,
payload (XI:=ξ) …)` — one invariant serving all contexts, with a real
`CtxMorph` obligation per payload.  The target shape exists proven:
`main_deposit`'s disk lock row on the M-leg (SpecMainSecondary.v).
When converting a lock's clients on main, convert its payload to λ-form
IN THE SAME TRANCHE.

**(b) [LANDED] `is_lock` is context-relative, with the internal floor
and the lk_floor disjunction.**  Rulings §0.35′ + §0.38′; implementation
A6.105/A6.109 (T-leg `WpLock.v`).  The handle bundles, inside, per
context: `lk_floor ξ lo := ctx_floor ξ lo ∨ (install-receipt at lo)` —
"you received this handle, or you wrote this lock".  On SC both arms are
trivial; land the SHAPE: floor existential INSIDE the handle (never in
`is_lock`'s exported arity), hoisted so that open and close witness ONE
`lo` (the A6.109 bug: `∃lo` inside a `□∀` accessor hands unrelated
witnesses to two opens — three iExact failures each one lo apart).
**AUDIT CORRECTION (verified against the T-leg tree):** two earlier
sub-claims here were intermediate designs the T-leg later superseded —
`initlock` is NOT floor-parametric (that plan, A6.101/A6.103, was
replaced: `initlock` keeps its store-then-mint order, the floor is the
store's own position for EVERY lock, and the certificate is `lk_floor`'s
right arm — SpecInitlock.v's header on the T-leg states this
explicitly), and there are NO era-image floor-0 locks (A6.113:
`ctx_floor_0` is a correct lemma with no client; the boot-static vs
dynamic distinction is about DISTRIBUTION CHANNELS, not floors).  The
creator bootstrap (`holding()` runs BEFORE acquire's AMO) is answered by
the disjunction plus the crossing/AMO conversion.  Take the whole story
from the T-leg's WpLock.v + SpecInitlock.v as they stand at execution
time.

**(c) [LANDED for is_lock/is_pipe/KPT; RULED-ONLY for the handler
contract] The context-relative treatment for ALL persistent memory-fact
families.**  The uniform rule (§0.35′/§0.36′/§0.39′, and the paper form
in §0.36′): "persistent" means never invalidated, NOT free to whoever
finds it — every persistent fact about memory carries a context axis and
is distributed only through channels (crossings that raise the
receiver's bound).  The four families with rulings: `is_lock` (b above),
`is_pipe` (second handle, same treatment — A6.105), the kernel-page-table
fact (§0.36′ — but the LANDED form is NOT the ruling-era `∃B,
kpt_bound B ∗ ctx_floor` sketch: K12 built it as the table at the
per-hart SEEN tier — "the credential stopped being a receipt about a
bound and became the table, at the tier this hart can see it" — still
persistent, still arity-free, NOT ξ-indexed; take the spelling from the
kpttree's `KptShare.v`/`PhysSeen.v`/`KptCtxTravel.v` and the K10–K15
notes, never from a formula written here), and the trap-handler contract
(§0.39′: proven once at boot, persistent, but USE requires a
sufficiently fresh context; the arity-preserving spelling — freshness
bundled inside `intr_handler_spec`, stamp under the existing `▷`, zero
consumers move — is designed and recorded in tso-intr-lane.md; it
depends on (a) being done for the trap-path payloads).  On SC every
freshness premise is trivially discharged; land the statements.

**(d) [MEASURED; export in flight on the T-leg] Acquire's
postcondition exports the USABLE receipt.**  The
M2-era post `(∃K, hart_view_lb K)` exists on both legs but K is
existential and tied to nothing — half a transport (K11 correction,
tso-kpt-lane.md).  The T-leg's agreed export form (coordinated across its lanes) is the
**ctx_floor form** — the AMO leaf hands back `ctx_floor cur_ctx T` for
each install receipt presented, with consumers deriving the
`view_lb ∗ ⌜T ≤ K⌝` pair via `own_context_floor_view` when they want
that spelling; nobody exports the bare pair.  On SC: trivial.  Take the
final spelling from the T-leg when its lock file closes.

**(e) [LANDED] The no-migration premise family on instruction
obligations.**
A6.89/A6.109/A6.112: load-datum, store, and value-unknown obligations
each carry `(b = false ∨ p = zero_reg → CID = CID0)` — the wp_next
same-CPU promise threaded down, discharged at `holding()`-class sites by
`or_introl eq_refl` because those specs are stated at literal
interrupts-off.  Existing callers ignore the premise.  SC-trivial;
land wherever main's obligation statements are converted.  DO NOT land
the refuted alternative (§0.34′'s carrier: the strengthened `locked`
token — refutation written beside `locked` in T-leg WpLock.v; the token
crosses wp_next continuations at fresh CpuIds and cannot carry hart
identity).

**(f) [RULED-ONLY — DO NOT LAND A SPELLING] §0.27′'s resume tie.**
The ruling: the p->lock invariant ties the parked context's stamp T to
the release write's position, and acquire exports the resume-ready
bundle.  The T-leg has NOT built it (ProofSwtch red; queued behind the
lock-file close and the λ-conversion), and the ruling-era sketch (a
relational parameter `U` on the payload type) is EXPECTED TO BE WRONG
IN FORM: the T-leg's arity law has twice taken exactly this kind of
~160-site parameter estimate to zero by bundling the fact inside the
existing shape, and every bound-relation actually landed since
(lk_floor, the floor hoist, the KPT credential) went the bundled route.
Land NOTHING for this on main until the T-leg's §0.27′ lands; then take
its spelling verbatim.  Depends on (a) for the p->lock payload's
λ-form regardless.

**(g) [LANDED] Page-currency statement discipline.**  §0.32′/A6.88: `byte_any`/
`page_own` keep their names with the visibility-free meaning (on SC the
bodies coincide with today's — the SEALING is what lands); `kalloc`'s
success post is the VALUED run of the allocator's own memset
(`page_filled … kalloc_junk`), downgradable to `page_own`; a borrowed
page is `page_named` (pointwise ∃ — lives in ProcPtOwn.v on the T-leg,
not KallocInv.v).  Kernel stacks travel FILLED through
the boot chain (A6.90 §"kstack"; five files on the T-leg).  The
read-before-write audit rides along: no kalloc client may read a byte it
has not written (§0.32′; audit was completed once on `tso` — re-run on
main, it is the soundness condition for the sealed meaning).

**(h) [MEASURED on main] What is already right on main — do not
churn.**  §0.33′: the
started-deposit membership (all nine rows), devsw's park-chain
distribution, `StartedInv.v` itself (parameter P — never changed on any
leg), the virtio ring pointers' lock-payload placement.  Touch these
only as (a)'s λ-conversion requires payload re-spelling.

### 5.2 Suggested tranche order

Slice-0's measurement decides finally, but the dependency logic is:
core module (Slice 1) → the memory-leaf statement layer (the wide
mechanical tier, per the runbook) → the lock kit with (a),(b),(d),(e)
together → subsystem functions (fs, console, proc) → the boot chain +
started producer statements with (g) → trap/interrupt statements with
(c)'s handler contract → scheduler/park with (f).  U-mode: SKIP
ENTIRELY (§0.37′ — main's own user-mode WP rework lands first; the
context-ownership home for that tier is deliberately undecided, with the
deciding measurement preserved in A6.107 §3(f)–(g)).

---

## 6. Process law (the mistakes, so you don't repeat them)

(a) **Measure before designing; verify before editing.**  Two design-doc
refactorings died at "verify against main" (§1).  Three more T-leg
plans inverted on measurement (A6.98 ordering, A6.101 bootstrap, A6.112
queue inversion).  The cheapest pass you will ever run is the grep that
kills a wrong plan.

(b) **Before building any law, grep for it.**  Nine separate times the
T-leg found the needed lemma/gate/combinator already existed unused
(A6.104 §"nothing new underneath", A6.111 §"already exported", A6.115,
K10 "eighth instance"…).  The port's motto: *the expensive step has not
once been building the law — it is noticing the law is already built.*
Search `TsoCtx`/the M-leg first; the answer is usually there.

(c) **When a proof cannot pay a premise, look for the fact the type is
hiding.**  A6.98 (`lo` existential inside the cell), A6.100 (timestamp
sealed inside the ctx word), A6.102 (the exposing-vs-sealing combinator
pair, built 18 amendments early).  Prefer exposing an existing fact over
inventing machinery; when two combinators differ by sealing, route the
cells that need the fact through the exposing one.

(d) **Arity rule.**  A6.97/A6.105: bundle new per-context facts INSIDE
existing shapes; before pricing an interface change, ask which consumers
actually NAME the new parameter.  This turned a 160-site estimate into
zero, twice.  Corollary: a fact ambient at every site (the context)
belongs in a typeclass, not an argument.

(e) **Tranche discipline.**  One tranche at a time; close to green or
revert byte-identical (verify with `diff`) — never leave a tranche open
"to continue tomorrow".  Land laws ADDITIVELY first (standalone green
boundary), then convert consumers.  When a long dependent chain is
fully measured, run it uninterrupted rather than measure-per-pass
(A6.103's process note); when it is NOT fully measured, measure first
(A6.93: "two errors quoting the same type constructors were three
different problems").

(f) **Record everything.**  Notes file per effort, amendment-numbered;
measured facts with file:line; refutations recorded in place (never
deleted); rulings cited in source comments at the load-bearing
definitions (see T-leg WpLock.v's `locked` refutation note — write those
so nobody re-tries a refuted design).

(g) **Typeclass gotchas.**  Declare `Typeclasses Transparent` for every
`Class X := x : T` alias the context machinery introduces (the CurKtier
bug, A6.91: instances stated at the class silently fail to fire on
T-typed goals — cost a mystery "not persistent" failure).  Instance
searches over unfolded fixpoint bodies can hang >90s — name the instance
(T-leg IntrDefs persistence comment).  A Coq premise that cannot be
focused must be NAMED (a `_` for a non-goal premise is shelved, not
opened — A6.87's proof-mode note).

(h) **Build discipline** (durable-notes + remote-build-gcp are
authoritative): GCP VM only, under the flock; per-subtree coq_makefile
for non-main trees; numbers only from MAKEEXIT/DONE-sentinelled rounds,
never mid-round polls; clean-round certification at milestones (an
incremental round over a changed deep file is "effectively clean" but
say so); check free disk before trusting a red list (ENOSPC/Error 143
mimics proof failures); never detached local makes; beware pgrep
self-matching; NEVER broad `pkill` (a lane once killed another's build).
**The stale-.vo trap**: `.vo` in a copied tree can be stale w.r.t. `.v`
and Rocq does not check — a local `About`/`coqc` probe silently answers
about a different tree; probe only against artifacts pulled after a
sentinelled green build.

(i) **Parallel lanes** (if used): separate full tree copies, strict
disjoint file-ownership contracts declared up front, separate notes
files, separate remote build dirs under the shared flock; cross-lane
needs are routed through the coordinator, never by editing a foreign
file; merges happen at green boundaries as clean applies of disjoint
diffs.

---

## 7. Slice 3 — audits and artifacts

- The read-before-write kalloc audit (§5.1(g)) as its own certified pass.
- The per-fact channel table: every persistent fact → the channel that
  distributes it → the ordering fact that justifies it.  §0.33′'s
  inventory is the seed (devsw → park chain; console_caps/kpt word/
  kstack+trampoline kmaps/disk lock handle → started deposit; ring
  pointers → vdisk_lock payload; fsinit's publications → fs_ready/first).
  Land it in main's notes; it is also a paper artifact.

## 8. Slice 4 — seal

Delete the migration equivalences; `Typeclasses Opaque` (or the tree's
sealing idiom) on every context-module interface; certify.  After this,
no client can exploit SC-only equivalences — which is the point: those
equivalences are exactly what leg C deletes, and a client that peeked
would break then.  Main is now TSO-ready: leg C = swap the sealed bodies
for the T-leg tiers + the machine, statements untouched.

## 9. Completion criteria

Per slice: main fully green (sentinelled), audit clean, notes entry with
measured numbers, and — for Slice 2 tranches — a statement-level diff
against the corresponding M-leg/T-leg files showing convergence modulo
the seal.  Overall: the project is done when the remaining main↔T-leg
statement diff is entirely below-seal, plus the two §0.37′ U-mode files
and anything main's own concurrent development added (report those to
the owner rather than converting unilaterally).

## 10. Escalation

Anything that contradicts a ruling (§0.x′) or this document by
measurement: record the refutation in place, stop that item, surface to
the owner with the exact failing statement and the measured facts —
the standing protocol that produced every good design in this port.

## Amendment 9 (2026-08-29, from the T-leg): §0.42′'s vocabulary -- the park box

Landed on `tso-flip` at r51 (`2cec2c862`), A6.127 §5–§7 in
tso-machine-flip.md; the ruling is §0.42′ in tso-port.md.  For main this is
SHAPE, to be materialized in syntax/vocabulary first (SC-provable, as §0.30′
prescribes); the tree is the authority for every statement below.

- **`TsoCtxPark.v`** (new, off `TsoCtx`'s public unseals):
  `ctx_parked_raise : llb loglen_name T' -∗ ctx_parked ξ T ==∗ ctx_parked ξ (max T T') ∗ ctx_floor ξ T'`;
  `ctx_park_box : own_context ξ -∗ ctx_parked ξb Tb ==∗ ∃ T Tb', ⌜Tb ≤ Tb'⌝ ∗ ctx_parked ξb Tb' ∗ ctx_parked ξ T ∗ ctx_floor ξb T`;
  `ctx_resume_floor : own_context ξr -∗ ctx_parked ξ T -∗ ctx_floor ξr T ==∗ own_context ξr ∗ own_context ξ`;
  `ctx_morph_floor : CtxMorph (λ ξ, ctx_floor ξ lo)`;
  `ctx_box_over : ctx_parked ξ T ==∗ ctx_parked ξ T ∗ ∃ ξb, ctx_parked ξb T ∗ ctx_floor ξb T`.
  On main at SC these are the same statements with vacuous floors.
- **`WpLockIn.v`** (new, off `WpLock`): `lock_finisher_in γ lk s R D Out E :=
  ∃ Pay, (own_context cur_ctx ==∗ own_context cur_ctx ∗ Pay) ∗ lock_finisher_body … Pay`;
  `lock_finisher_to_in`, `lock_finisher_close_body`, `lock_finisher_close_in`,
  `lock_finisher_close_pay : lock_pay R -∗ lock_finisher_in … emp E`.
- **`SpecRelease`**: `wp_release_gen_in_sconf_body` (generic, prelude takes
  only the token) is the proof; `wp_release_gen_sconf` its corollary;
  `wp_release_in_sconf_body` = the plain tier with
  `(own_context cur_ctx ==∗ own_context cur_ctx ∗ lock_pay R)` for `R cur_ctx`;
  `Module Type RELEASE_IN`, functor `ReleaseInOfGen`, `LinkRelease.ReleaseIn`.
- **`SwtchCtx`**: `valid_context P A c p XIp` (identity a parameter, token
  OUT of the record, the parked stack at `XIp`);
  `park_tok None XIo := ∃ ξb Tb Tp, ctx_parked ξb Tb ∗ ctx_parked XIo Tp ∗ ctx_floor ξb Tp`,
  `park_tok (Some h) XIo := own_context (CID := h) XIo`;
  `resume_tok None XIt := ∃ T, ctx_parked XIt T ∗ ctx_floor cur_ctx T`,
  `resume_tok (Some h) XIt := own_context (CID := h) XIt`; `stack_own_morph`.
- **`SpecSwtch`**: premises `adm An cpu_id -> adm Ao cpu_id ->`; the target
  `(∃ XIt, resume_tok An XIt ∗ ▷ valid_context P An newc p XIt)`; the hand-back
  `(if back' then ∃ XIo, park_tok A' XIo ∗ ▷ valid_context P A' cret p XIo else own_ctx cret)`.
- **`SchedCtx`**: `proc_ctx_at ξl pa := ∃ XIp Tp, ctx_parked XIp Tp ∗ ctx_floor ξl Tp ∗ ▷ valid_context p_sched None (p_context pa) pa XIp`;
  `proc_slots_at ξl pa st`, `proc_lock_res_at ξl γl pa`, ambient forms
  `proc_ctx pa := proc_ctx_at cur_ctx pa` (etc.) keep every consumer lemma;
  `proc_lock_pay γl pa := λ ξ, proc_lock_res_at ξ γl pa` with
  `CtxMorph (proc_lock_pay γl pa)` by instance search; `procs_inv` over it;
  `sched_vc_at h c p := ∃ XIs, own_context (CID := h) XIs ∗ valid_context p_sched (Some h) c p XIs`;
  `sched_vc_at_intro`/`_tok`, `proc_ctx_resume_tok`, `proc_ctx_at_of_tok`,
  `proc_ctx_boxed pa := ∃ ξb Tb, ctx_parked ξb Tb ∗ proc_ctx_at ξb pa`,
  `proc_slots_park_at`, `proc_slots_park_box`, `proc_lock_res_at_intro`,
  `proc_lock_pay_of_box`.  The 40 `<{ proc_lock_res … }>` sites are
  `(proc_lock_pay …)`.
- **Consumers**: `ProofSwtch` (the exchange: `ctx_park_box`/the running token
  in; `ctx_resume_floor`/the running token out; the block engine's
  `own_context` threaded); `ProofScheduler` (`sc_tail_body` takes the
  pre-parked payload; `ReleaseIn` in the functor; reclaim via
  `proc_slots_park_box`); `ProofSched` (`sched_vc_at_tok` before both swtch
  calls, `sched_vc_at_intro` after); `SpecForkretPark(Paid)`/`ParkCap`
  conclude `proc_ctx_boxed`; `ProofForkretPark` deposits the child's stack
  into its context (`ctx_deposit` + `stack_own_morph`) and boxes; `ProofUserinit`
  / `ProofKforkB5` build the slot at the box and release through `RLI :
  RELEASE_IN` (functor params threaded through `KforkProof`, `UserinitProof`,
  `LinkUserinit`, `LinkKfork`).
- **Deferred, named**: the per-hart cells' hand-off across swtch (`cpu_own`,
  `p_sched`) stays at the ambient -- a hart-tier unit (A6.127 §6);
  `ProofForkretPark`'s remaining root is the M3 debt on its rows.

## Amendment 10 (2026-08-29, from the T-leg): §0.43′'s vocabulary -- the same-hart hand-off

Landed on `tso-flip` at r53 (`5779cf1b1`), A6.128 in tso-machine-flip.md; the
ruling is §0.43′ in tso-port.md.  Same terms as Amendment 9: shape and
vocabulary for main, SC-provable; the tree is the authority.

- **`TsoGhost`**: the per-context dirty registry is a MONOTONE SET
  authority, `inG Σ (authR (gsetUR (nat * Arch.pa)))`; `dset_auth γ q S`,
  `dset_in γ k` (persistent, timeless), `dset_alloc`, `dset_halves`,
  `dset_agree`, `dset_lookup`, `dset_get`, `dset_insert`.  On main at SC
  the registry is vacuous; the API is what consumers spell.
- **`TsoCtx`**: `ctx_at ξ q B D` with `D : gset (nat * Arch.pa)`; a cell's
  dirty arm is `dset_in (ctx_dirty_name ξ) (t, a)` at every fraction;
  `ctx_wrote ξ t a := dset_in …`.
- **`TsoCtxMove.v`** (new): `ctx_move_floor`, `ctx_move_pointsto`,
  `ctx_move_phys_pointsto`; `Class CtxMove R := ctx_move : ∀ ξ0 ξ1,
  own_context ξ0 -∗ own_context ξ1 -∗ R ξ0 ==∗ own_context ξ0 ∗ own_context ξ1 ∗ R ξ1`;
  structural instances (const/sep/exist/or/if/big_sepL/big_sepM/big_sepS)
  and the points-to leaves; the tactic `ctx_move_solve` (SYNTACTIC head
  dispatch + `apply _` -- do not port an `apply`-based leaf, A6.128 §3).
  On main every instance is trivial at SC (`R ξ0 ⊢ R ξ1` when nothing is
  ξ-indexed) but the CLASS and the call shape are the vocabulary.
- **`PtTreeMove.v`**, **`CpuOwnMove.v`** (new): the instance files for the
  page-table tree at `UTier ξ` and for `cpu_own`'s tower.
- **`SwtchCtx`**: `valid_context_pre` fully at `XIp` -- `ctx_cells (XI :=
  XIp) c vs`, the wand's `cpu_own (CID := h) (XI := XIp) …`, `ctx_cells (XI
  := XIp) c vs`, `P h A' c cret … back XIp`, zombie `own_ctx (XI := XIp)
  cret`; `valid_context` is a closed term (this IS main's §0.15′ shape, so
  main may already be there); the `SwtchCells`/`SwtchCtx` section split.
- **`SpecSwtch`**: `P : CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d> mword
  64 -d> mword 64 -d> bool -d> CtxId -d> iPropO Σ`; premise `(forall h A c
  c' tp p' b, CtxMove (λ ξ, P h A c c' tp p' b ξ))` after the register
  equalities; `P … back cur_ctx` in, `P … back' cur_ctx` out.
- **`SchedCtx`**: `p_sched … back ξ` (its `proc_held`/`park_pay` at ξ), the
  `SchedCtx`/`SchedCtxPay` split, one `CtxMove` instance per named piece
  (list in A6.128 §2), `p_sched_move`; `proc_ctx_cells`/`proc_ctx_own_ctx`
  deleted.  `ProofScheduler`/`ProofSched` pass `ltac:(intros; apply _)`.
- **`ParkCap`**: `proc_ctx_boxed γs pa` unannotated.
- **`ProofForkretPark`**: the child's cells and kstack row deposited into
  the child's context beside the stack; the wand body at `(XI := XIc)`;
  the three λ-conversion rows bracketed (`{ iExact "Hpinv". }` …) so the
  red root fails fast.  On main those rows are already λ-converted, so
  main's port of this file should go GREEN.

