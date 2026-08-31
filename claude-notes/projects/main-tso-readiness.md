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

## Amendment 11 (2026-08-29, from the T-leg): §0.44′ -- fork's mint is a twin; the p->lock payload honest at the lock's context; wait/nextpid λ-converted

Landed on `tso-flip` at r54 (`6b62156`) and r55 (`3df4de899`), A6.129 in
tso-machine-flip.md; the ruling is §0.44′ in tso-port.md.  Same terms as
Amendments 9–10.

- **`TsoCtxMove`**: `own_context_twin : own_context ξ ==∗ own_context ξ ∗ ∃ ξc,
  own_context ξc` (fork's mint; stamp-0 `ctx_parked_alloc` is boot's and the
  lock boxes'); `ctx_move_wrote` (the dirty witness's move).
- **`SchedCtx`**: `lk_floor_move`, `is_lock_move`, `procs_inv_move`;
  `run_slot_at ξl pa` (`run_slot := run_slot_at cur_ctx`), `proc_slots_at ξl`
  with `run_slot_at ξl` and `proc_dormant (XI := ξl)`, `proc_lock_res_at ξl`
  with its words and `proc_pub` at `ξl`; `proc_lock_res_at_intro` honest
  (cells at `ξl`), `proc_lock_res_deposit` (cells at the ambient deposited
  into a parked box), `proc_slots_park_box` a BASIC update taking and
  returning the running token; one `CtxMorph` per named piece (A6.129 §2's
  list).  `ProofKforkB5`/`ProofUserinit`/`ProofScheduler` deposit inside
  `ReleaseIn`'s token wand.
- **`CtxMorphTac`**: the syntactic `ctx_morph_step` (do not port an
  `apply`-based solver), `ctx_morph_or`, `ctx_morph_big_sepS`,
  `ctx_morph_phys_pointsto`, `ctx_morph_phys_word`.
- **`WaitInv`**: `parents_own_at ξ`, `wait_res_at ξ` (+ morph);
  **`SpecAllocpid`**: `nextpid_res_at ξ` (+ morph); every `<{ wait_res }>` /
  `<{ nextpid_res }>` is `wait_res_at` / `nextpid_res_at` (55 sites, 21
  files); `park_globals`'s two lock rows accordingly.
- **`ProofForkretPark`**: twin → `ctx_move` (cells, stack, kstack,
  `procs_inv`) → `ctx_park_box`; wand body at `XIc`; red at row 2
  (`park_globals`, blocked on `is_ftable` -- A6.129 §4).
- **Not landed, for the owner's ruling**: the invariant class (A6.129 §4).

## Amendment 12 (2026-08-30, from the T-leg): §0.45′ -- the started barrier at the ledger tier; the era's image as a name; the pipe λ-converted

Landed on `tso-flip` at r56 (`80e2e1da7`, A6.130–A6.131) and r57 (`3d998dbbb`, A6.132); the ruling is §0.45′ in
tso-port.md.  Same terms as Amendments 9–11.

- **`riscvEraGS.era_img`** (A6.131): the era's image is a constant of the
  era record; `tso_interp_at`/`tso_interp_of` state `gimg = era_img`
  (`tso_interp_at_img`, `tso_interp_of_img`); `power_boot_res` and
  `power_boot_res_unpack` export `⌜era_img riscv_eraGS = g.(gimg)⌝` as the
  TRAILING conjunct (`BootShared`'s unpack pattern ends `… & #Hcert &
  %Hera`).  main's port must add the conjunct wherever it constructs
  `power_boot_res` (`iSplitR; [iExact "HRelem" | iPureIntro; reflexivity]`).
- **`PipeInvDefs.pipe_data_at ξ`, `pipe_res_at γp pi ξ`** (context last),
  `pipe_res := pipe_res_at γp pi cur_ctx`; `is_pipe … (pipe_res_at γp pi)`
  -- parenthesised partial application, NOT `<{ pipe_res }>`.
- **`StartedInv`** (A6.132 §2–§3): `started_inv γi ξd P`, `started_prim γi`,
  `started_alloc`, `started_inv_claim`, `started_claim`(+`_intro`),
  `started_read_open`/`started_read_obl`/`started_W`/`started_res`,
  `started_absorb`, `started_store_open`/`started_store_obl`/
  `started_right`, `started_win_plain`/`started_win_rel`, `started_img`.
  The old `started_inv P`, `started_inv_alloc`, `started_inv_load_au`,
  `started_inv_store_au` are GONE.
- **The read leaf** `WpSconfMem.wp_load_s_sconf_au_relr` (+ `HartSMem`'s
  `_exvvr` nodes): resource-post, `W : mword → nat → iProp`, continuation
  gets `∃ V0, hart_view_lb V0 ∗ W v V0`.
- **Specs**: `SpecMain.wp_main_boot_sconf_body … tlbvec0 γi ξd P` with
  `{!∀ ξ, Persistent (P ξ)} {!CtxMorph P}` and rows `started_inv γi ξd P
  -∗ started_prim γi -∗ □(… -∗ P cur_ctx)`; `SpecMainSecondary`'s body
  takes `γi ξd` and `started_inv γi ξd (main_dep γd γv)`; `main_dep γd γv
  := λ ξ, main_deposit (XI := ξ)` with its `Persistent`/`CtxMorph`
  instances (`is_txlock_morph`, `is_conslock_morph`, `console_caps_morph`,
  `printk_env_morph`, `disk_geom_morph`).
- **Boot**: `BootCarve.boot_cran_ledger_at0_bss4`; `BootShared.boot_bss_carve`
  row `started_claim ∗ started_win_plain`; `boot_shared_alloc` ∃-binds
  `γi ξd` and exports `started_inv γi ξd (main_dep γd γv) ∗ started_prim
  γi`; `BootChain.boot_hart_primary/secondary` take `γi ξd`
  (`started_prim γi` on the primary); `SystemAdequacy` routes `Hprim`.
- **Consumers**: `ProofMain.mn_grp_started` (`cid_word = zero_reg`
  premise, `Hprim`, `wp_store_s_sconf_au_dat` + `started_store_open` +
  `started_store_obl`, `Require Import TsoGhost`);
  `ProofMainSecondary.ms_spin` (`γi ξd P`, `cid_word ≠ zero_reg`,
  `wp_load_s_sconf_au_relr` + `started_read_open/obl` + `started_absorb`
  via `SieCapCtx.sie_cap_gpr_own_ctx_acc`; `Require Import SieCapCtx`).
- **Verification status main should know** (A6.132 §4): `BootChain`,
  `BootShared`, `SystemAdequacy` and `ProofMain`'s release site are NOT
  certified on this tree -- they are under all seven red roots.
  `ProofMain` has a second standing red at `mn_grp_fs` (`iApply fupd_wp`,
  ~`:1495`) behind K15d's `:996`, and `ProofForkretPark` a module-signature
  mismatch (`usertrap_res_bare_park`, `:373`) behind its `:318`.
- **Not landed, for the owner**: the barrier ABSTRACTION (§0.45′ NEXT),
  the invariant class (A6.129 §4), the bcache escrow recycler ruling.


## Amendment 13 (2026-08-31, from the U-mode lane, LANDED ON MAIN): the U-mode cone's context threading -- generic tier mirrored from tso-flip r60, binary tier threaded, tree GREEN

This one is different from Amendments 9-12: it is not a vocabulary
request, it is a REPORT of a slice that already landed on main
(branch umode-main-work -> origin/main, iris/ only; merged with the
concurrent fd-view seam -- uvis carries the descriptor states, Rfd/fdv
through uvb/ukc/urun, first-generation sh proofs retired -- and GREEN
after the merge: 1468/1468 targets, MAKEEXIT=0 clean rebuild, zero
admits).  What main now has, so the T-leg can consume it rather than
re-derive it:

**Mirrored verbatim from tso-flip r60 (statements identical, SC
bodies where the flip's are ledger-real):**
- `TsoCtx.ctx_phys_pointsto`/`ctx_phys_word_pointsto` (sealed, SC body
  = the raw phys facts) + morph/move instances and solver rows
  (`CtxMorphTac`, `TsoCtxMove`).
- `PtTree` transplanted (ptier = `KTier B | UTier ξ`; `kpt_slot_pin`
  SC-trivial), `PtAdBits`, `UptTree`, `UserPtTree` (flip base + main's
  five addition hunks), `PtBuild`, `PtFree`, `UserBytes`, `HartMemAsm`,
  `Pt4kWalk`, `KptPt`, `UmodeMem`, `HartStepFull`, `UserTrap`,
  `UserActiveClass`, `TfPage36`; the four SC-era interp files deleted.
- The payer-threaded walk (`KptTree.ptree_translateAddr_own`), the
  A6.61 trampoline threading end to end (`TrampStepPt`, `UptWalkPt`
  with `utf_translate` GREEN in place, `Pt2WalkPt`), `HartMemRun`'s
  token-in/token-out `swp_hmrun_of_exec` (+ `_reg` minting form).
- `ProcDefs.tf_words/tf_tail` and the whole trapframe tier at
  `ctx_phys_word_pointsto` (A6.58), with `tf_page` morph/move rows.
- **kpt_body at the CONTEXT-FREE KTier** (A6.20/A6.21: an invariant
  body may not name a context): `kpt_body = ∃ t M B, kptree_own B 2 1 t
  ∗ …`, arity-stable, WITHOUT the T-leg pin receipt (`kpt_bound`/`llb`
  have no SC content).  Openers (KptShare walk, HartSKpt, TransPt)
  walk at `(KTier B)`.  The PUBLICATION seam is
  `PtTreeShim.ptree_own_retier_sc` at ProofMain's `kpt_inv_alloc` call
  -- the T-leg replaces exactly that rewrite with `KptPublish`.

**The design rule the binary tier now follows (hart-AND-context
quantification, §0.43'/0.44'):** every migration-surviving shape that
already quantified `∀ CID` now quantifies `∀ (CID) (XI)`:
`UmodeCap.uv_intr_wp/uv_sys_wp`, `UexecWp.uexec_F`,
`UexecRet.uslot/ukc/uvb/ukb` (+ `UexecRetFs` twins), `UkRun.urun`
(xi EXISTENTIAL inside, arity unchanged -- the program never names
it), `WpUmodeStep.uv_step_obl/uv_ih/uv_resume` and the retire
continuations (`∀ CID0 XI0, uv_cap_gpr (CID:=CID0) (XI:=XI0) …`),
`UkStep.uk_step_obl/uk_ih`, `UmodeIo`/`UmodeSyscall` protocol rows
(the PROTOCOL itself is xi-free -- rows quantify internally; do NOT
re-add an XI parameter to `xv6_io_protocol`/`xv6_sys_protocol`, it
makes Ψ vary under the continuation binder and nothing unifies).
(The first-generation sh proof
tier -- UProofSh*/USpecSh* -- was retired by the owner in the
concurrent fd-view seam, so its threading died with it; the
new-generation sh files take the plain tier's xi binders at their
`urun` destructs.)

**The residue-token contract (M2), as landed:**
- `SpecUser.wp_user_exec_closed_body` takes the `Rut_ctx` borrow
  accessor as a premise (`forall pt', ⊢ Rut pt' -∗ own_context cur_ctx
  ∗ (own_context cur_ctx -∗ Rut pt')`); `ProofUser` threads it to
  `wp_user_exec_full`; a CONCRETE caller supplies it from
  `ut_trap_parked`'s conjunct.
- The A6.61 trampoline-consumer blocks are statement-threaded for
  real: `UserretPt.wp_uld_pt/wp_ualu_pt/wp_usret_pt`,
  `UservecPt.wp_usd_pt/wp_ucsrw(r)_sscratch_pt`,
  `UservecExitPt.wp_uservec_exit_pt`,
  `UserretEntryPt.wp_userret_entry_pt`, `SpecUserret`'s body (tf cells
  at the ctx tier), `UserretUser`, `ProofUserret`, `ProofUservec`.

**SC-only seams added (the cutover worklist is the import/grep list):**
- `TsoCtxShim.own_context_sc` (the M-leg body is `True ∨ …`, so the
  token is FREE on main) and `rut_ctx_sc` (minted accessor for a
  ∀-bound residue).  Mint sites: `WpUmodeStep.uv_swp_fetch/execute/
  uv_swp_exec` + the ecall nodes (UkStep/UkStore/WpUmodeStore twins),
  `ProofUexecWp` (accessor for the iProp-∀ Rut), `ProofUservec`,
  `UserretUser`, `ProofUservec`'s resumed-hart userret call.  Each is
  where the T-leg substitutes the residue borrow.
- `PtTreeShim.pt_slot_payer_sc` (generic payer), `pt_slot_raw_sc`,
  `ptree_own_retier_sc` (SC re-tier; real publication at cutover).

**Two Coq facts that cost rounds, recorded as rules:**
- A definitional-class implicit (`CurCtx`) in a lemma STATEMENT
  resolves to the NEWEST instance in scope at statement elaboration --
  a per-lemma `{XIp}` binder therefore wins over the section ambient,
  which is what makes the sh-tier helper pattern work; but an
  `iPoseProof`-minted token lands in the INTUITIONISTIC context and
  survives its first use, so never re-bind the same name at the next
  continuation intro (rename or clear).
- Implicit binders inside a `forall`-stated lemma auto-insert at
  CONSTANT applications but are POSITIONAL in an `induction`-generated
  IH -- `intros` lists and `IH _` applications need the slot, direct
  lemma applications must not pass it.

**Deferred, for the owner / the T-leg:**
- The retire/park quantification stops at the uv/uk tier;
  `wp_next` (the usertrap park) still re-binds the hart only -- the
  context exchange at swtch is the kernel lane's (A6.127/A6.129).
- `uk_step_obl`'s XIo and the `$! CIDo XIo` retire applies assume the
  resumed context is the obligation's own; when the T-leg makes parks
  real, those sites are the frontier (grep `XIo`).
- The fs enrichment (`UexecRetFs`/`UkRunSysFs`/`UkRunFsLeaf`, the
  fd-view seam's own tier) stays uniformly at its section-ambient XI;
  its two bridges to the honestly-∀-quantified plain tier are
  instantiated at the ambient (`uslot_uslot_fs`, `urun_fs_urun`).
  Making the enrichment migration-honest is the fs lane's, when it
  cares.

## Amendment 14 (2026-08-31, LANDED ON MAIN): the ready-now flip tranches -- A6.129 remainder + A6.139 family, with real is_lock transports

Two commits on main (`A6.129 remainder ported`, `A6.139 ported from
tso-flip r63`), both green 1454/1454.  What landed, what was
substituted at the SC seam, and what was measured and deferred.

**A6.129 remainder (the M3 λ-payload completion):**
- `WaitInv.parents_own_at/wait_res_at` (ctx cells at explicit ξ, real
  `CtxMorph`), `SpecAllocpid.nextpid_res_at`, 51 handle-spelling sites
  (`<{ X }>` -> `X_at`), `SchedCtx.run_slot_at` + morphs +
  `lk_floor_move`, `TsoCtxMove.ctx_move_wrote/own_context_twin`.
- Consumers of `parents_own` hand ctx cells END TO END now, so the
  `ctx_word_of_mem/to_mem` seam conversions DROPPED at the p_parent
  sites (ProofKexit/ProofKwait/ProofReparent/ProofKforkB5) and
  `BootShared` mints the parent cells at the carve like `p_chan`.
- The hunks the first pass missed, surfaced by instance search (a
  CtxMove leaf fails EXACTLY where a definition still reads the
  ambient context -- the leftover-goal probe is the diagnostic):
  `proc_lock_res_at` pins its cells at ξl (flip's honest spelling),
  `proc_slots_at` pins `proc_dormant (XI := ξl)`, `procs_inv` gains
  its move/morph section, `proc_pub_morph`/`proc_lock_res_at_morph`.

**is_lock_move/is_lock_morph are ON MAIN, and the M4 blocker note is
retired**: main's `lock_inv` is ξ-INDEPENDENT under SC because
`TsoCtxShim.ctx_word_shim/_word4_shim` are `⊣⊢` against the raw cell,
so the handle re-homes by `inv` properness (`setoid_rewrite` -- plain
ssreflect `rewrite` cannot reach under the ∃-binders).  STATEMENTS are
flip's verbatim (`SchedCtx.v`, at the site); only the proof bodies are
the seam and become flip's one-line `ctx_move_solve` at the M4 lock-kit
reshape.  This unblocked the whole `devintr_caps_move` chain.

**A6.139 (flip r63, the kernelvec handler-environment family):**
- `IntrDefs`: `ihs_fam`/`ires_pack_of`/`env_move`, `ihs_trap_of` takes
  the env family E with a `□ E XI` premise at the trap-time context,
  `ihs_body_of` quantifies ∀XIb (the M2 context-generic contract,
  which main had never taken), `intr_res` ∃-packs the env + its
  swtch-crossing witness, `intr_res_at`/`ihs_env` (arity-stable
  carrier row), the `sie_*_pack` lemmas, seals on the new faces.
- `SpecKernelvec.kernelvec_env` is the REAL ξ-relative credentials
  family (not a const-family stub) and `kernelvec_env_move` is the
  real transport, funded by `SpecDevintr`'s CtxMove pile ->
  `is_lock_move`.
- `SchedCtx`: `p_sched` pins `trap_csrs (XI := ξ)`; `intr_res_move`
  (uses the packed witness), `trap_csrs_move`, `p_sched_move` fixed.
- Engine/leaves/producer/installers/usertrap rows: r63's hunks applied
  (7 of 11 files verbatim by `git apply`, the rest 3-way with main's
  fd-tier spellings kept -- `ud_hold` keeps `(U : ustate)(sts)`, the
  devintr caps spell `fsc_uart/fsc_disk/fsc_dlock`).

**SC seams ADDED (cutover worklist, grep these):**
- `SchedCtx.lock_inv_reindex_sc/is_lock_reindex_sc` (Local; the
  is_lock transport proof bodies).
- (The producer-site seams this amendment first shipped --
  `proc_cells_reindex_sc`, `ctx_word_reindex`, the `ctx_dom_sc` retier
  in `proc_slots_park_box` -- are GONE: `TsoCtx.ctx_deposit` was on
  main all along, so the three sites and the ZOMBIE park now run
  tso-flip's deposit shape verbatim (`SchedCtx.proc_lock_res_deposit`,
  the token-threaded `proc_slots_park_box`).  RULE for the next port:
  when a flip proof leans on a TsoCtx gate, grep TsoCtx.v itself, not
  just the Move/Park satellites.)

**Measured and deferred (unchanged from the survey, now with reasons
verified in-tree):**
- A6.126 §4 view-carrying read leaf: its premise names
  `tso_interp_of/tso_read_bytes` (interp tier); main's `ms_spin`
  already stands on the quarantined `hart_view_lb_any` idiom.
- A6.135 §5 ghost-hooked write engines + kvminithart establishment
  hook: the hook's statement names `tso_interp_at riscv_eraGS g`;
  main has `gstate` but no interp tier, and a hook minus the tso
  conjunct would be a guessed narrowing.  Wait for the owner's call.
- A6.138 position-indexed started payload: depends on kpt_creds
  decisions; measure separately.
- `ctx_deposit` itself (and the deposit-shaped park/release sites):
  T-leg vocabulary main does not have yet; the SC seams above are its
  stand-ins.
