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

### 5.1 THE CORRECTED SHAPES — land these directly, not the M-leg's drafts

This is the heart of the handoff.  The T-leg refuted several M-leg first
drafts; main must land the corrected forms so it never repeats the
retrofits.  Each entry: the shape, the ruling/finding, the reference.

**(a) λ-payloads for every context-mentioning lock payload — NEVER the
constant embedding.**  The single biggest avoidable cost.  The intr lane
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

**(b) `is_lock` is context-relative, with the internal floor and the
lk_floor disjunction.**  Rulings §0.35′ + §0.38′; implementation
A6.105/A6.109 (T-leg `WpLock.v`).  The handle bundles, inside, per
context: `lk_floor ξ lo := ctx_floor ξ lo ∨ (install-receipt at lo)` —
"you received this handle, or you wrote this lock".  On SC both arms are
trivial; land the SHAPE: floor existential INSIDE the handle (never in
`is_lock`'s exported arity), hoisted so that open and close witness ONE
`lo` (the A6.109 bug: `∃lo` inside a `□∀` accessor hands unrelated
witnesses to two opens — three iExact failures each one lo apart).
`initlock`'s spec is floor-parametric (the mint is the caller's side;
the store frames the floor) — A6.101/A6.103: the creator bootstrap is
structural (`holding()` runs BEFORE acquire's AMO), so the two floor
sources (era-image 0 for .bss locks; the install store's position for
dynamic ones) are two different FLOORS, not two distributions (A6.100).

**(c) The context-relative treatment for ALL persistent memory-fact
families.**  The uniform rule (§0.35′/§0.36′/§0.39′, and the paper form
in §0.36′): "persistent" means never invalidated, NOT free to whoever
finds it — every persistent fact about memory carries a context axis and
is distributed only through channels (crossings that raise the
receiver's bound).  The four families with rulings: `is_lock` (b above),
`is_pipe` (second handle, same treatment — A6.105), the kernel-page-table
fact (§0.36′: `kpt_creds := ∃B, kpt_bound B ∗ ctx_floor cur_ctx B`; the
walker gate two-armed via the context tower's own clean/own-write
disjunction; reference implementation in tso-kpt-lane.md K10–K11 and the
kpttree's `PhysSeen.v`/`KptCtxTravel.v`), and the trap-handler contract
(§0.39′: proven once at boot, persistent, but USE requires a
sufficiently fresh context; the arity-preserving spelling — freshness
bundled inside `intr_handler_spec`, stamp under the existing `▷`, zero
consumers move — is designed and recorded in tso-intr-lane.md; it
depends on (a) being done for the trap-path payloads).  On SC every
freshness premise is trivially discharged; land the statements.

**(d) Acquire's postcondition exports the USABLE receipt pair.**  The
M2-era post `(∃K, hart_view_lb K)` exists on both legs but K is
existential and tied to nothing — half a transport (K11 correction,
tso-kpt-lane.md).  Land the corrected post: the pair
`hart_view_lb K ∗ ⌜U ≤ K⌝` against the lock's bound (see (f)), or
equivalently the already-upgraded floor for handles crossing in the
payload.  On SC: trivial.  Shape matters.

**(e) The no-migration premise family on instruction obligations.**
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

**(f) §0.27′'s relational bound in the p->lock payload.**  The lock
invariant ties the parked context's stamp T to the release write
(`⌜T ≤ U⌝`, U instantiated by the free arm at the lock element's
timestamp); acquire exports the resume-ready bundle.  On SC: vacuous
content, real shape.  This is what makes swtch/scheduler statements
converge.  Depends on (a) for the p->lock payload's λ-form.

**(g) Page-currency statement discipline.**  §0.32′/A6.88: `byte_any`/
`page_own` keep their names with the visibility-free meaning (on SC the
bodies coincide with today's — the SEALING is what lands); `kalloc`'s
success post is the VALUED run of the allocator's own memset
(`page_filled … kalloc_junk`), downgradable to `page_own`; a borrowed
page is `page_named` (pointwise ∃).  Kernel stacks travel FILLED through
the boot chain (A6.90 §"kstack"; five files on the T-leg).  The
read-before-write audit rides along: no kalloc client may read a byte it
has not written (§0.32′; audit was completed once on `tso` — re-run on
main, it is the soundness condition for the sealed meaning).

**(h) What is already right on main — do not churn.**  §0.33′: the
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

---

# AMENDMENT 1 (2026-08-28) — SLICE 0's INVENTORY

Measured against `main` at `7f66e9dee`, the commit at which this project
opened.  Every number below is a grep over `iris/*.v` at that commit;
where it contradicts the brief above, the brief is corrected IN PLACE by
this amendment (§6(a)/§10 — refutations are recorded, never deleted).

## 1.1 The two reference trees are further away than the brief assumes

`main` is **489 commits** past the `tso` merge-base
(`e1292b3821de241732a1e1475aac64463cdc6e8d`, 2026-08-24); `tso` is 139.
File-level:

| | count |
|---|---|
| `.v` common to both | 1296 |
| on `main` only | 56 |
| on `tso` only | 36 |
| `main` total | 1352 |

The 56 main-only files are main's own development (the `Fs*Era`/`FsAbs*`
/`FsCollect*` cluster, the `Uexec*`/`USyncKernel`/`VSlot` user-WP slot
tier, `SbPark`, `TxPin`).  The 36 tso-only files are NOT M-leg additions:
**25 of them are files `main` has since DELETED** (`FsEff*`, `FsOp*`,
`DirLinks`, `FsWf`, `IregDirBit`, `FsDurWire/Obj/Refute/Defer` — killed by
the durable-disk lane at `8f54e5326`, `589f9181e`, `4a418d1e2`,
`542222367`).  Only **11** are the context machinery: `CtxRecord`,
`SieCapCtx`, `TsoCtx`, `TsoCtxRehearsal`, `TsoCtxShim`, `TsoCtxTwin`,
`TsoCtxTwin2`, `TsoGhost`, `TsoLitmus`, `TsoMem`, `TsoMemPa` — and by §2's
seal test only the first five are above-seal candidates.

**CONSEQUENCE, and it modifies §5.2's tranche order:** the M-leg is stale
on main's most active subsystem.  For the fs tier there is NO reference
implementation to converge against — those statements get written from the
pattern, not ported, and §9's "statement-level diff against the
corresponding M-leg/T-leg files" is not available there.  Sequence the fs
tranche LATE and expect it to cost more than its file count suggests.

## 1.2 Slice 1 must be taken from `tso-flip`, not from `tso`

The brief's §4 says the M-leg's `TsoCtx.v` is the statement reference and
that its first draft lacked the buy/carry/cash triple.  Measured: the
triple is **absent from `origin/tso` entirely** — `ctx_floor`,
`ctx_bound_raise` and `own_context_floor_view` appear on `origin/tso-flip`
only, in `TsoCtx.v`, `WpLock.v`, `SpecInitlock.v`, `WpSconfMem.v`,
`SmodeCorePt.v`, `TsoGhost.v`.  So Slice 1 takes the M-leg's `TsoCtx.v`
(1334 lines) as the skeleton and the triple's interface from the T-leg's.

## 1.3 §5.1(a) — the λ-payload price on main, measured

The brief quotes the intr lane's T-leg figures.  Main's are larger, and
the payload family is wider than the four trap-path ones:

| payload | file | sites | files | brief's T-leg figure |
|---|---|---|---|---|
| `disk_res` | `DiskInv.v:365` | 255 | 107 | 175 |
| `proc_lock_res` | `SchedCtx.v:433` | 117 | 32 | 44 / 19 files |
| `log_res` | `LogInv.v:1182` | 111 | 15 | — |
| `wait_res` | `WaitInv.v` | 63 | 20 | — |
| `pipe_res` | `PipeInvDefs.v:510` | 56 | 5 | — |
| `cons_res` | `ConsoleInv.v:203` | 46 | 10 | 10 |
| `kmem_res` | `KallocInv.v:292` | 41 | 20 | — |
| `bcache_res` | `BioInv.v:941` | 37 | 9 | — |
| `ftable_res` | `FileInv.v:40` | 35 | 12 | — |
| `ticks_res` | `TicksInv.v:41` | 31 | 9 | 16 |
| `nextpid_res` | `SpecAllocpid.v:59` | 29 | 12 | — |
| `sl_res` | `SleepLock.v:422` | 20 | 5 | — |
| `pr_res` | `SpecPrintk.v:209` | 16 | 7 | — |

**Union of files touched: 207.**  The four trap-path payloads alone are
449 sites against the brief's 457 — so the brief's total is right by
accident and its per-payload split is not.

Ten distinct locks: `virtio_disk` (178 `is_lock` mentions), `wait_lock`
(27), `nextpid` (14), `pr` (11), `uart` (5), `kmem` (5), `time` (2),
`itable` (2), `ftable` (1), `cons` (1); plus `"proc"` (p->lock) reached
through `proc_lock_res`.  `is_lock` itself: 397 mentions / 163 files.

**MITIGATION FOUND (§6(b)/(d) — the law is already built).**  Main's
`is_lock` is already `Global Typeclasses Opaque` (`WpLock.v:339`, sealed
for a measured 5.1 s persistence-resolution win), and its whole consumer
interface is the three lemmas `is_lock_name`/`is_lock_inv`/`is_lock_intro`
— **162 of the 163 files never unfold it**.  Changing `R : iProp Σ` to
`R : CtxId → iProp Σ` therefore prices at the definition plus the sites
that NAME a payload, not at 397.  This is the §6(d) arity rule paying out
a third time; confirm it against the build before committing to a tranche
size.

## 1.4 The §4/§5.1 shapes, verified against main's HEAD

| shape | on main | status |
|---|---|---|
| (a) λ-payloads | no `const_pay`, no `<{ }>`; every payload const-embedded | **all work** |
| (b) `is_lock` ctx-relative | `WpLock.v:321`, `R : iProp Σ`, context-free, sealed | **all work**, cheaper than feared (§1.3) |
| (c) `is_pipe` | `PipeInvDefs.v:599`, context-free; 25 sites / 10 files | all work, small |
| (c) KPT fact | `KptShare.v:78` `kpt_inv`; `SRegime.v:1303` `kpt_res_at` | all work |
| (c) handler contract | `IntrDefs.v:441` `intr_handler_spec`, persistent `□` | all work |
| (d) acquire's receipt pair | no `hart_view_lb` anywhere on main | **all work**, but see below |
| (e) no-migration premises | obligations inlined per statement | all work |
| (f) §0.27′'s U in p->lock | `proc_lock_res` has no stamp/bound parameter | all work |
| (g) `byte_any`/`page_own` bodies | `KallocInv.v:112`/`:121` — **already the visibility-free bodies, and already `Typeclasses Opaque` (`:128`)** | **NO-OP** |
| (g) `page_filled`/`page_named` | absent; but `ByteBuf.bb_page_named` (`:662`) is already the pointwise-∃ law | partial — the law exists, the currency does not |
| (h) `main_deposit`'s nine rows | `SpecMainSecondary.v:105` — verified, all nine present verbatim | **NO-OP, do not churn** |

Two entries turn out to be no-ops on today's main, both in the brief's
favour: §5.1(g)'s sealing ("the SEALING is what lands") is already there,
and §5.1(h)'s deposit membership is exactly as §0.33′ recorded it.

**A second arity mitigation, for (d).**  Main's acquire contract is
already factored through body definitions — `wp_acquire_pre_body`,
`wp_acquire_gen_pre_body`, `wp_acquire_{fresh_,}sconf_body`
(`SpecAcquire.v:105–221`).  Adding the receipt pair to the post edits
those bodies, not the call sites.

## 1.5 §0.20′'s three back-ports never reached main — SLICE 0.5

Ruling §0.20′ is titled "THREE FLIP-WORKSPACE SHAPES LAND ON MAIN" and
they did not: `wobl_prem`, `robl_prem`, `dma_acc`, `phys_map_store`,
`virtio_lease_acc` are all present on `origin/tso` and all absent from
main.  They carry no context vocabulary, are SC-provable as they stand,
and exist to shrink the leg-C edit.  The owner authorized landing them
**ahead of Slice 1**, as Slice 0.5.  Target files — `HartMStore.v`,
`HartMLoad.v`, `WpVirtio.v`, `VirtioProto.v`, `WpUart.v` — verified
untouched by the user-wp-slot landing (last moved 2026-08-19…27).

## 1.6 The flip surface (Slice 2's first tranche), measured

| notation | sites | files | stage |
|---|---|---|---|
| `↦₈` | 2674 | 237 | **1** |
| `↦ₘ` | 1277 | 170 | **1** |
| `↦₄` | 1964 | 217 | 2 |
| `↦₂` | 131 | 29 | 2 |
| `↦ₛ` | 112 | 33 | 3 (§0.21′/§0.22′) |
| `↦ₚ` | 470 | 47 | never — below seal |
| `↦ᵣ` | 2639 | 117 | never |
| `↦ₓ` | 83 | 15 | never |

Stage 1 is **3951 sites across ~280 files**.  Definitions to flip:
`RiscvPtsto.v:1149` (`mem_pointsto`) and `:1427` (`word_pointsto`), with
their four notation spellings each at `:1157–1177` and `:1431–1445`.

Where the flip sites LIVE, by family — this is the tranche map:

| family | files w/ flip sites | files total | flip sites |
|---|---|---|---|
| `Proof*` | 146 | 260 | 2845 |
| `Spec*` | 80 | 214 | 332 |
| `Proc*` | 5 | 7 | 133 |
| `Riscv*` | 3 | 8 | 113 |
| `Wp*` | 11 | 99 | 81 |
| `Boot*` | 4 | 7 | 49 |
| `Disk*` / `Console*` / `Virtio*` | 5 | 10 | 111 |
| **`Link*`** | **0** | 212 | **0** |
| **`Code*`** | **0** | 183 | **0** |
| **`HartM*`** | **0** | 11 | **0** |

**395 of main's 1352 files (`Link*`, `Code*`, `HartM*`) contain not one
flip site.**  `HartM*`'s zero independently confirms §0.20′'s reason for
the back-port: those files own no points-to, which is exactly why their
obligations are pass-throughs.

## 1.7 Two hazards in the working tree

- **Stale `.vo` (§6(h)), live here.**  `iris/` carried **256 orphaned
  artifact sets** — `.vo`/`.vok`/`.vos`/`.glob` with no `.v` — left by the
  `weak-memory` branch (the whole `Weak*`/`Wk*` family) and by the fs
  deletions of §1.1.  A local `About`/`coqc` probe against those answers
  about a different tree.  **Purged** at Slice 0; 1310 `.vo` remain
  against 1352 `.v`.  Re-check after any branch switch.
- **No build lock.**  The brief's §0 reading list says builds serialize
  under `flock /tmp/claude-gcp.lock`.  **The owner refuted this
  (2026-08-28): there is no global lock** — the VM is 192-core and many
  agents build on it concurrently, each in its own remote subdir.  The
  surviving rule is one build per *tree*, never two in the same remote
  directory.  This tree maps to `/mnt/rocq/trees/_shared_xv6iris-2`.

## 1.8 THE BASELINE, CERTIFIED

`main` at `7f66e9dee`, built on the GCP VM at
`/mnt/rocq/trees/_shared_xv6iris-2` through the per-subtree `CoqMakefile`
recipe (never a dump rule):

| gate | result |
|---|---|
| build sentinel | `MAKEEXIT=0` |
| plain `Error` in the log | 0 |
| `Admitted` / `admit.` / `Axiom` in `iris/*.v` | 0 (the ten grep hits are all inside COMMENTS *about* not having any) |
| `md5sum kernel-rocq/*.v user-rocq/*.v` | unchanged across the run |
| `make audit-only` | `AUDITEXIT=0`, **13** assumptions — the sanctioned set (10 `PrimInt63`/`PrimString`, `functional_extensionality_dep`, `resv_is_valid`, `resv_matches`) |

This is the number every later slice is measured against.  The audit
reports whatever was last BUILT, not what is at HEAD, so re-run it only
after a green build of the tree in question.

---

# AMENDMENT 2 (2026-08-28) — SLICE 1 LANDED

Two new files, `iris/TsoCtx.v` (1446 lines) and `iris/TsoCtxShim.v` (222),
inserted in `iris/_CoqProject` after `RiscvPtsto.v`.  **No existing file
changed** — §4's "purely additive, green by construction" held literally.

## 2.1 What landed

The M-leg's `TsoCtx.v` as the skeleton — `CtxId`/`CurCtx`, the
`own_context`/`ctx_parked`/`hart_view_lb` tokens with their lifecycle
(`ctx_park`/`ctx_resume`/`ctx_exchange`/`own_context_boot`), the
`ctx_pointsto` tower and its word/word2/word4/string levels with the four
notation spellings each, `ctx_dom`, `CtxMorph` with its instance set, and
`ctx_deposit`/`ctx_absorb` — plus §4's MANDATORY additions taken from the
T-leg (Amendment 1 §1.2: they are on `tso-flip`, not on `tso`):

| law | statement |
|---|---|
| `ctx_floor ξ lo` | persistent, timeless; `ctx_floor_0`, `ctx_floor_le` |
| `ctx_bound_raise` | `own_context ξ -∗ hart_view_lb K' ==∗ own_context ξ ∗ ctx_floor ξ K'` |
| `own_context_floor_view` | `own_context ξ -∗ ctx_floor ξ lo -∗ own_context ξ ∗ ∃K, hart_view_lb K ∗ ⌜lo ≤ K⌝` |
| `ctx_floor_dom` | `ctx_dom ξ ξ' -∗ ctx_floor ξ lo -∗ ctx_dom ξ ξ' ∗ ctx_floor ξ' lo` |

All four have trivial SC bodies and real statements.  `ctx_floor_dom` is
A6.116/A6.117's ten-line law — a floor the sender can discharge is one the
receiver can discharge — which is why payload transport needs no
`CtxMorph` strengthening.  The token is THREADED, not consumed, by
`own_context_floor_view`: a read gate discharges its floor mid-proof and
keeps running as ξ.

## 2.2 Two drift findings against the M-leg

- **`ghost_varG Σ CPU` is already in main's Σ** (`riscvF_parkGS`,
  `RiscvPtsto.v:375`), which is exactly what `own_context_def` needs.  No
  Σ change, no new `inG`, no functor row.
- **`word2_pointsto_unfold` does not exist on main.**  The M-leg's shim
  names it; main's `word2_pointsto` (`RiscvPtsto.v:1527`) is a plain
  transparent definition and only the word4 tier ever needed a named
  unfolding.  Resolved by delta in the shim (`rewrite /word2_pointsto`)
  rather than by adding the lemma upstream — adding it would have edited an
  existing file and cost Slice 1 its additive property for nothing.

## 2.3 THE SEAL DELIVERS LESS THAN §8 CLAIMS — say what it does deliver

Recorded per §6(f) and §10.  §8 says that after the seal "no client CAN
exploit SC-only equivalences".  That is stronger than any of the seals
available here.  The M-leg's idiom — `Definition f := proj1_sig f_aux`
with `Lemma f_aux : {g | g = f_def}` closed by `Qed` — does block
CONVERSION (the match on the opaque witness is stuck, so `reflexivity`
alone fails).  But `f_aux` and `f_def` are both public global constants,
so any file may write `rewrite (proj2_sig f_aux)` and recover the body in
one line, with no import of `TsoCtxShim` and nothing reliable to grep for.
Sealing or deleting the `_unseal` lemmas does not change this.  The same
holds a fortiori for `Global Opaque`, which `unfold` walks straight
through — that weaker seal is what let the port grow the silent crossings
`8f675587b` was written to find.

Only module-signature ascription makes the body equation NOT EXIST as a
term rather than merely inconvenient to reach.  **The owner considered and
declined it (2026-08-28)**, so the sig-projection idiom stands.  The
consequence to carry, and the reason this is written down: at Slice 4,
"main is TSO-ready" is a property maintained BY DISCIPLINE, not enforced by
the typechecker.  State it that way in the completion criteria, and treat
`grep -l TsoCtxShim` plus a scan for `proj2_sig .*_aux` outside `TsoCtx.v`
as the audit that stands in for the guarantee.  Measured for calibration:
across the M-leg's 1332 files the hatch is touched in exactly TWO —
`TsoCtx.v` (30 uses, its own law proofs) and `TsoCtxShim.v` (5).  The
discipline has held; it is just not enforced.

## 2.4 Gate

`MAKEEXIT=0`, 0 `Error`, dumps unchanged, `audit-only` = the same 13
assumptions as the baseline (`Print Assumptions` emits them in an unstable
ORDER, so compare the sorted set, not the bytes).  Confirmation round over
the committed tree recompiled 0 files.

---

# AMENDMENT 3 (2026-08-28) — SLICE 2, CHUNK 1: THE MEMORY-LEAF TWIN TIER

35 ctx twins, each spliced BESIDE its original in the same kit file
(§2c's rule), across five files.  **1304 insertions, ZERO deletions** —
every original is byte-identical and every consumer of them is untouched.

| file | twins | tier |
|---|---|---|
| `WpSconfMem.v` | 16 | the S-mode `sconf` load/store leaves + `ctx_pointsto_claim` |
| `WpSmodePtMem.v` | 8 | the PT-translating loads/stores |
| `WpSmodePtLeaves.v` | 4 | `cld`/`csd` |
| `WpSmodePtMemWrap.v` | 4 | `cldsp`/`csdsp` |
| `WpSmodeHalf.v` | 3 | the halfword tier (`↦₂`) |

## 3.1 The import-order gate, PROBED not assumed

`TsoCtx.v` re-declares all four spellings of `↦ₘ` and `↦₈`, so a file that
imports it LAST flips (tso-flip-replay.md pass 1).  A file that needs the
ctx vocabulary but must NOT flip yet re-imports `RiscvPtsto` after it.
Verified rather than reasoned about, with the runbook's own probe
(`Set Printing All`): under `Require Import TsoCtx TsoCtxShim.` followed by
`Require Import RiscvPtsto.`, `a ↦ₘ v` elaborates to `mem_pointsto` and
`a ↦₈ w` to `word_pointsto` — RAW.  That one probe is what makes the whole
tier additive: twins get the context vocabulary, originals keep their
meaning, and the flip stays a separate, later, deliberate act.

## 3.2 TWO TWIN IDIOMS, and which to use when

- **Continuation intercept** — for `wp_next`-shaped leaves (`WpSconfMem`,
  `WpSmodeHalf`; 19 of the 35).  `ctx_*_to_mem` in, apply the original,
  `rewrite /wp_next`, re-introduce, `ctx_*_of_mem` back.  `wp_next b p K`
  is a plain `∀ CID, ⌜…⌝ -∗ K CID`, so it introduces like any wand.
- **Goal rewrite** — for the PT tier (16 of the 35), whose continuation is
  a flat wand chain of ten-odd hypotheses.  `rewrite !(ctx_word_shim _
  cur_ctx)` turns BOTH occurrences of the window raw, at which point the
  goal is LITERALLY the original statement and `exact` discharges it.  No
  hypothesis names, indifferent to the continuation's shape.  Strictly the
  nicer idiom; it is not used for the `wp_next` tier only because the
  window there sits under the continuation's `fun CID => …` binder, which
  a plain `rewrite` will not enter.

Both die at cutover — the shim's `⊣⊢` is exactly what stops being true —
so each twin then gets its direct TSO proof with its STATEMENT unchanged.
That is the whole point of the tier.

## 3.3 What the statement buys, and it is visible in the type

The twin's window comes back at the SAME `cur_ctx` it went in at, ACROSS
the `wp_next`, where `CID` rebinds and the context does not.  That is
migration survival, stated.  It is why the fact is indexed by the thread
of control and not by the hart — the axis A6.89/A6.92's two refuted
spellings (the strengthened `locked` token, the lock word's author
receipt) were both on the wrong side of.

## 3.4 Deferred, with the reason

- **`WpAu4`'s two AMO leaves** (`wp_lw_au_s_sconf`, `wp_sw_au_s_sconf`).
  Their window sits inside an atomic update (`∃ v, … ↦₄ v ∗ (… ={Em,⊤}=∗ Ψ v)`),
  so neither idiom applies mechanically — and they should not be twinned
  mechanically: the AMO is exactly where §0.35′(iii)'s log-top receipt and
  bound-absorb enter, so their ctx statement is lock-tranche content, not
  leaf-tier content.
- **`WpLock`'s nine** (`lk_cpu_res_*`, `newlock*`, `lock_inv_alloc`, …).
  Not per-instruction leaves at all — lock-kit lemmas, which §5.2 wants
  converted together with (a) λ-payloads, (b) `lk_floor`, (d) the receipt
  pair and (e) the no-migration premises.
- **`WpSwtchVc.seg_cells_ctx`, `WpLockAt.newlock_at`,
  `WpSconfLock.wp_sd_lkcpu_lockopen_gen`** — same reason, lock/swtch tier.

## 3.5 Gate

`MAKEEXIT=0`, 0 `Error`, 470 files recompiled, dumps unchanged,
`audit-only` = the sanctioned 13.

---

# AMENDMENT 4 (2026-08-28) — SLICE 2, CHUNK 2: THE LOCK KIT'S CONTEXT LAWS

Additive only (142 insertions, 0 deletions): `TsoCtx.log_lb`, and in
`WpLock.v` the `lk_floor` family and the parked-record payload.  Nothing
existing changed; `lock_inv`/`is_lock`/acquire/release convert in chunk 3,
per §6(e) (land laws at a standalone green boundary, convert consumers
after).

## 4.1 PROVENANCE — every statement copied, none derived here

The owner's instruction, and it caught a real error: *"be sure to confirm
how the tso and tso-flip branches are defining the lock payload; it's done
a lot of engineering to get it right, and it's really subtle… DO NOT
INVENT ANYTHING HERE."*

| landed | source | note |
|---|---|---|
| `lock_pay R := ∃ ξ T, ctx_parked ξ T ∗ R ξ` | `tso` WpLock.v:388 **and** `tso-flip` WpLock.v:1002 | both branches character-identical |
| `lock_pay_intro` | `tso-flip` WpLock.v:1022 | the HONEST form; see §4.3 |
| `lk_floor ξ lo := ctx_floor ξ lo ∨ ⟨install receipt⟩` | `tso-flip` WpLock.v:869 | absent from the M-leg entirely (pre-§0.38′) |
| `lk_floor_0` / `_of_ctx` / `_of_log` / persistence | `tso-flip` WpLock.v:872–881 | `_of_log` is the T-leg's `_of_llb` |

## 4.2 TWO INVENTIONS CAUGHT AND REMOVED — recorded so they stay removed

A first draft of this chunk added two things to `lock_pay` that looked
natural and are **refuted by both branches**.  Both are now written into
the source beside the definition.

- **A bound parameter `U`.**  §0.27′'s relational bound belongs to the
  PROCESS RECORD, not to the generic lock payload; neither branch's
  `lock_pay` carries one.  The absorb's `T ≤ K` premise is discharged at
  the ACQUIRE SITE from the AMO's own receipt — and at SC by the trivially
  valid pair (`K := T`, reflexivity; `tso` ProofAcquire.v).  Carrying `U`
  in the payload gives a fact that already has a home a second, wrong one.
- **An elim lemma.**  Neither branch has one, and that is *by design*:
  the token does not survive the held phase.  A record is minted per
  PUBLICATION, at release, and abandoned by the winner that claims it,
  because `ctx_absorb` hands the token back — so keeping it would force
  release's `ctx_deposit` inside the word-clear store's ATOMIC UPDATE,
  where no `own_context` is in scope (§0.17′'s measured rule), or make it
  ride inside `locked`, a resource change under every lock client.  The
  elimination is `ctx_absorb` applied where the receipt is.

The general lesson, and it is the §6(b) motto turned around: the expensive
step is not building the law, it is noticing the law is already built —
**and noticing when the thing you are about to add was already considered
and rejected.**  Both of these compiled green.  A wrong statement that
compiles is the defect class `durable-notes.md` calls out as the worst.

## 4.3 TWO JUDGMENT CALLS, FLAGGED FOR RATIFICATION

Neither is an invention, but both are choices this file made:

1. **`TsoCtx.log_lb` is a NAME this tree coined.**  The T-leg's right arm
   is `TsoGhost.llb loglen_name lo`, which is BELOW the seal, so it cannot
   land.  §5.1(b) sanctions the concept ("`ctx_floor ξ lo ∨ (install-receipt
   at lo)`… on SC both arms are trivial; land the SHAPE"), and §2's test
   passes (the statement has an SC proof with a trivial body).  The ARM is
   the ruling's; the NAME is ours, and at leg C it is what `llb
   loglen_name` swaps into.
2. **`lock_pay_intro` is the T-leg's form, not the M-leg's, and that
   imports a cascade.**  `tso`'s is weaker (`R cur_ctx ==∗ lock_pay R`)
   and buys the weakness with a shim quarantine at `ctx_dom_sc`, because
   at SC it had no way to move a payload onto a fresh parked record.  Main
   HAS the real `ctx_deposit` (slice 1), so the T-leg proof goes through
   verbatim and no quarantine is needed anywhere on the lock's transport
   path.  What it costs is named on the M-leg and is real: `ctx_deposit`
   wants the creator's running token, so every `newlock` wrapper gains one
   — the **19-call-site creator cascade** (12 in the newlock family, 7 at
   `WpLockAt.newlock_at`) that §0.18′ priced and DEFERRED.  Chunk 3 pays
   it.  §5.1 says land the corrected shapes directly, which is why it was
   taken; it is flagged because the M-leg's deferral was deliberate.

## 4.4 Gate

`MAKEEXIT=0`, 0 `Error`, 780 files recompiled, dumps unchanged,
`audit-only` = the sanctioned 13.

# AMENDMENT 5 (2026-08-29) — SLICE 2 CLOSED GREEN: the wave, and what was deferred

The tree is green at this checkpoint: full `-k` build `MAKEEXIT=0`,
`audit-only` = the sanctioned 13, `kernel-rocq/`/`user-rocq/` byte-identical
to `a4fe91a78`.  63 local commits over `a4fe91a78` (the `wip: hNN fixes`
series is the build-round log; squash at the push if wanted).  Nothing has
been pushed.

## 5.1 What landed — the propagation, by method

1. **Tree-wide 3-way merge of the M-leg** (`origin/tso`) with base
   `e1292b382`, ours `a4fe91a78`: 1119 files merged clean and were
   installed wholesale (385 differed from the checkpoint); ~165 conflicted
   (main moved in the same hunk) and kept the script-converted checkpoint
   version, then got the M-leg's edits back by line-pick where the line
   still existed (the acquire continuation's receipt `_`, binders).  71
   main-only files (`FsAbs*`, `FsCollect*`, `*AU`, `Uexec*`, …) have no
   M-leg twin and were converted by hand as they surfaced.
2. **T-leg shapes for the propagated APIs**, per the rule "T-leg for
   API/spec shapes, M-leg for SC shortcuts": `SpecAcquire` exports the
   `(∃ K, hart_view_lb K)` receipt (minted by `hart_view_lb_any`); the
   swtch cluster (`SwtchCtx`/`SpecSwtch`/`ProofSwtch`/`ProofSched`/
   `ProofScheduler`/`SchedCtx`) is the T-leg's — `P` takes NO `CtxId`, no
   `CtxMorph` premise on swtch, the record's resume wand is at `XIp` for
   the bundle only; the trap tier (`SpecKernelvec`/`SpecKerneltrap`/
   `SpecConsoleintr`/`SpecUartintr`/`SpecDevintr`/`SpecClockintr` and
   their proofs) is the T-leg's (no `caps_fam`); `FsReady`/`FirstTok`/
   `TicksInv`/`SpecPanic`/`SpecPrintk`/`SpecUserinit`/`SyscParkEnv` are
   the T-leg's.  **Lock payload spelling follows the T-leg:** const
   embedding `<{ R }>` for `proc_lock_res`, `pipe_res`, `bcache_res`,
   `disk_res`, `log_res`, `itable_res2`, `ticks_res`, `nextpid_res`,
   `ftable_res`, `cons_res`, `sl_res(_gen)`, `wait_res`, `pr_res`,
   `tx_res`; the λ form `(λ ξ, kmem_res (XIk := ξ) …)` ONLY for `kmem_res`
   (T-leg: 27 λ uses, 0 const).  The M-leg's `CtxMorph` instance sections
   that exist only to serve λ payloads were dropped where the T-leg has
   none (`ConsoleInv.console_inv_morph`, `ProcInv`'s section, `FileInv`'s
   `ftable_res_morph`, `SchedCtx`'s, `SpecAllocpid`'s, `FsReady`'s).
3. **`lock_name` is the closed term both legs have** (raw discarded word
   + `ctx_string_all`); `lock_name_intro` takes `ctx_string_all`, and the
   boot string minter is `KernelDataInv.kernel_data_string_all`.
4. **Binders.**  Section-level `Context `{XI : CurCtx}` in the
   Spec/Inv files (a section variable attaches only where used); inline
   `` `{GEN} `{CID} `{XI} `` in the Proof-tier files whose lemmas
   implement Module Type fields (the order must match the signature —
   XI last, after CID; `Parameter`s carry it INSIDE the `forall`).  Files
   that do not `Import TsoCtx` spell the class `TsoCtx.CurCtx`
   (unqualified `CurCtx` there silently generalises a `CurCtx : Type` —
   the trap §1.7 recorded; it bit four more times).

## 5.2 DEFERRED — the M2 threading, exactly (each with its SC stand-in)

The user's ruling (2026-08-28): "if that complicates things, defer it for
now, we'll thread it through later. it would be good to land this giant
change first."  Every deferral is an SC-only stand-in that dies at the
shim burn; each is marked `main-tso-readiness` in the source.

| deferred | where the M/T-legs have it | the stand-in on main |
|---|---|---|
| `own_context cur_ctx` in `sie_cap` (+`SieCapCtx`) | both legs | absent; `sie_cap` patterns are 5-conjunct everywhere |
| acquire-side `ctx_absorb` | `ProofAcquire` | `ctx_dom_sc` + `ctx_morph` (the T-leg's own SC form) |
| release-side `ctx_deposit` | `ProofRelease` | `WpLock.lock_pay_intro` (M-leg SC form) |
| swtch `ctx_park`/`ctx_resume`/`ctx_deposit`; `ctx_parked XIp Tp` in `valid_context_pre` | `ProofSwtch`, `SwtchCtx` | conjunct dropped (binders kept for arity); `ctx_dom_sc` + `stack_own_reindex` / `ctx_cells_reindex` |
| `cpu_ctx_free`'s parked record + receipt | T-leg `SchedCtx` | bare `∃ vs ξ` cell run; `ProofScheduler` claims via `ctx_dom_sc` |
| bcache escrow as a parked record (`buf_escrow_rec`, `escrow_absorb/deposit`) | M-leg `BioInv`/`ProofBrelse`/`ProofBread(Parts)` | main's `buf_escrow`; the LRU link words stay RAW and cross at the accessor (`ctx_word_of_mem`/`to_mem` pairs, the M-leg's own idiom) |
| the boot deposit's named context (`xid`, `CtxRecord.ctx_parked_inv`, `own_context_boot` per hart) | M-leg `BootShared`/`SpecMainSecondary`/`SystemAdequacy` | `main_deposit γd γv` (2 args); `SystemAdequacy` pins ONE dummy `ξ0 := MkCtxId inhabitant inhabitant` for all eight harts |
| `boot_hart_res` rows at `∀ ξ` | M-leg `BootChain` | ambient rows; `BootShared` crosses `proc`/`noff`/`intena` at `cur_ctx` |
| the `caps_fam`/`caps_morph` credential family in `intr_res` | M-leg only | absent (T-leg shape) |
| `KptShare.kpt_creds`, `TsoCtxAbsorbLb` | T-leg only | absent |

## 5.3 SC-ONLY LEMMAS ADDED ON MAIN — flagged, because §4.2 says "do not invent"

These are shim-class (each is FALSE at TSO and says so in its comment),
introduced because a main-only consumer needed them.  Review candidates:

- `WpLock.is_lock_reindex` / `lock_inv_reindex` (the floor is re-minted
  from `log_lb_any`; `inv_iff` re-indexes the invariant) — used by
  `ConsoleInv`'s and `SchedCtx`'s (now removed) morphs; may be dead.
- `WpLock.lock_openable_parts` (T-leg projection; not SC-only).
- `WpSconfMem.ctx_word_claim` (8-byte twin of `ctx_word4_claim`),
  `ctx_word_pointsto_split4` / `_join4` (the 8↔4 carve at the flipped
  spelling, through the shim).
- `StackOwn.stack_own_reindex` (T-leg statement, `ctx_morph` proof).
- `SwtchCtx.ctx_cells_morph` / `own_ctx_morph` (M-leg), `DiskInv.
  disk_geom_morph` (M-leg), `InodeInv`'s `InodeResMorph` section (M-leg),
  `FileInvDefs.off_mark_acc` (M-leg name; definitional on main).
- `TsoCtx.ctx_word_pointsto_timeless'` / `_discarded_persistent'` (the
  ktier-explicit twins the 2/4/string towers already had; neither leg has
  them for 8 bytes).

## 5.4 Process notes for the successor

- Round-trip: `./gcp-rocq/run-on-gcp … make -f CoqMakefile -j180 -k` from
  the REPO ROOT (a backgrounded Bash chain loses `cd`; three rounds were
  wasted on `run-on-gcp: No such file`).  ~5 min per incremental round,
  ~10 min when `TsoCtx.v` changes (whole tree).
- The classifier/fixers live in the session scratchpad only
  (`autofix.py` = error triage + `bind2.py` binder insertion,
  `secbind_all.py`, `inlinebind_all.py`, `linepick.py`, `m3.sh`); they are
  one-offs, not tools — the reusable ones are `tools/ctx_convert.py` and
  `tools/lock_ctx_sweep.py` from `tso`.
- A stale `.vo` can mask a red file until its deps change: `BootShared`
  was red for ~40 rounds behind an up-to-date `.vo`.  Before calling a
  tree green, a full rebuild (touch `TsoCtx.v`) is the honest gate.


# AMENDMENT 6 (2026-08-29) — THE M2 THREADING LANDED ON THE SC STUB: the running token, parked records, and the two sites the stub carries

Slice 2 shipped with the M2 threading deferred (§5.2).  This amendment
ports it from the M-leg (`origin/tso`) with the T-leg spec shapes kept
(owner ruling: "we don't want to back out the real spec shapes from
T-leg … they're the real deal").  Gate, met twice: on the base `c1227faec`
(full `-k` build `MAKEEXIT=0`, 1302 files) and again after the rebase onto
`origin/main` `6285fd1ad` (48 commits of the syscall-tier sweep; `MAKEEXIT=0`,
1331 files) -- `audit-only` = the sanctioned 13 both times,
`kernel-rocq/`/`user-rocq/` unchanged, zero `Admitted`/`Axiom` in `iris/`.
Landed as ONE commit on `main` (the ~40 `wip(M2)` build-round commits are
squashed; the pre-rebase branch is tag `m2-port-pre-rebase`, local only).

## 6.1 What landed — each §5.2 row, resolved

| §5.2 row | now on main | from |
|---|---|---|
| `own_context cur_ctx` in `sie_cap` | the conjunct after `sie_arm`; `SieCapCtx.sie_cap_gpr_own_ctx_acc` borrows it; every `sie_cap` destruct/rebuild carries `Hctx` (the M-leg's "Hctx line twins", applied by line-pick in ~25 files) | M-leg `IntrDefs`/`SieCapCtx`, token hunks only (no `caps_fam`) |
| acquire-side `ctx_absorb` | `ProofAcquire`: `lock_pay R` opens to `ctx_parked ξ0 T0 ∗ R ξ0`, receipt `hart_view_lb_any T0`, `ctx_absorb R ξ0 cur_ctx`; the `(∃ K, hart_view_lb K)` receipt `SpecAcquire` exports is minted from the same receipt | M-leg |
| release-side `ctx_deposit` | `ProofRelease`: `ctx_parked_alloc` + `ctx_deposit R cur_ctx ξc 0` rebuild `lock_pay R` (the M-leg's per-publication record) | M-leg |
| swtch `ctx_park`/`ctx_resume`; `ctx_parked XIp Tp` in `valid_context_pre` | `SwtchCtx`/`ProofSwtch` = the T-leg's files WITH the token; `ProofSwtch` exchanges tokens (`ctx_park` into the record it builds, `ctx_resume` out of the one it consumes, receipt `hart_view_lb_any`) | T-leg shape, M-leg mechanism |
| `cpu_ctx_free`'s parked record | still the bare `∃ vs ξ` run; `ProofScheduler` claims via `ctx_cells_morph` + `ctx_dom_sc` (the T-leg's `ctx_cells_reindex` is modal on main) | deferred, as before |
| bcache escrow as a parked record | `BioInv.buf_escrow_rec`, `escrow_absorb`/`escrow_deposit`/`escrow_alloc_seq`; `bio_init_at` takes `own_context cur_ctx`; `ProofBrelse`/`ProofBread(Parts)` absorb/deposit at the escrow | M-leg |
| the boot deposit's named context | `SpecMainSecondary.main_deposit xid γd γv := ctx_parked_inv xid ∗ main_deposit_rows xid γd γv` (`CtxRecord`); `SpecMain`'s boot body takes `xid` and `ctx_parked_inv xid`; `BootShared` mints `xid`; `own_context_boot` for the boot hart in `SystemAdequacy`; `ProofMain.mn_grp_started` deposits, `ProofMainSecondary` absorbs | M-leg |
| `boot_hart_res` rows at `∀ ξ` | M-leg `BootChain`; `BootShared` crosses `proc`/`noff`/`intena` under the ∀ | M-leg |
| forkret's park | the record carries `ctx_parked` (6.3); `UsertrapRes.park_globals` + `ConsoleInv.console_inv_morph`/`console_ready_morph` are on main for the day the child gets its own context, unused by the park today | see 6.3 |
| `caps_fam`/`caps_morph` | ABSENT (T-leg trap tier) — the reason for 6.3 | — |

## 6.2 Method notes

- Whole-tree `git merge origin/tso` = 263 conflicts; abandoned.  Per-file
  3-way merges (base `e1292b382`) + a keyword resolver (token hunks from
  the M-leg, the rest from main, payloads re-normalised to `<{ R }>`);
  for `IntrDefs`/`WpIntrInv` a hunk applier keyed on `own_context|Hctx`
  that excludes the `caps_fam` hunks.  Where main and the M-leg had BOTH
  moved since the base (the usertrap/forkret park cluster: `UsertrapRes`,
  `ParkCap`, `SpecForkretParkPaid`, `ProofForkretPark`, `ProofKforkB5`,
  `ProofUserinit`), main's design wins (its consumers — `UtResFits`,
  `ProofUsertrap*`, `ProofSyscall` — are main-only) and only the token
  hunk is added.
- **The const-payload `CtxMorph` hang (§0.15′ again).**
  `ctx_morph_const_pay` was priority 99: `apply _` on
  `CtxMorph <{ bcache_res bn V }>` (escrow-bearing now) descends the
  payload and leaves a term the next tactic never finishes.  Priority 0
  fixes the `$!`-on-a-hypothesis sites (`[ apply ctx_morph_const_pay | | ]`)
  but NOT the lemma-argument sites (`newlock_at`, `wp_acquire_sconf`,
  `wp_release_sconf` with `<{ bcache_res bn V }>`); those take a local
  instance ahead of the sentence,
  `pose proof (TsoCtx.ctx_morph_const_pay (bcache_res bn V)) as Hcm_bcN.`
  Only the `bcache_res` family needs it.  Why priority 0 is not honoured
  there is recorded, not understood.
- Diagnosing a hang: kill the worker (filter `ps` by `/proc/<pid>/cwd`),
  then `timeout 300 rocq compile … -time File.v`; the last printed sentence
  is the one BEFORE the hang (owner's bound: 5 min is plenty).

## 6.3 THE TWO SITES THE SC STUB CARRIES, and why (owner ruling: "use the shim")

The M-leg models `own_context ξ`/`ctx_parked ξ T` as ONE exclusive ghost
per context.  On main that is unsatisfiable at exactly two sites, for one
structural reason:

- a forked child's record (`ProofForkretPark`) must be stated at its
  PARKER's context (main's `wp_forkret` takes `procs_inv` and the
  `sie_cap` at one context), and
- the seven secondary harts must run at the boot carve's context
  (`SystemAdequacy`; `main_deposit xid γd γv` is not a closed term on main —
  its `procs_inv`/`console_caps`/disk-lock rows are ambient),

because `procs_inv` cannot be restated at a fresh context: its per-proc
lock rows reach `valid_context → p_sched → trap_csrs → intr_handler_spec`,
and only the M-leg's caps channel (`IntrDefs` binding the credential
family `C` inside `intr_res`) makes that contract a closed term.  Both
legs' own comments say so (`tso-port.md` §0.11′/§0.12′; the T-leg's
`ProofForkretPark`).

What the stub does about it (`TsoCtx`, `TsoCtxShim`): the two token
bodies are TRIVIAL on main, exactly as `hart_view_lb_def` already was
(`True ∨ ∃ c, ghost_var …` — the dead disjunct only keeps the constants'
implicit signature), so the shim exports `own_context_any ξ` and
`ctx_parked_any ξ T` beside `hart_view_lb_any`; the fork record takes its
token from `ctx_parked_any cur_ctx 0`, the secondaries their running
token from `own_context_any ξ0`.  Every law statement is unchanged; the
three exclusivity lemmas the M-leg states (`own_context_excl`,
`ctx_parked_excl`, `own_context_parked_excl`) are not, because they are
false for the trivial bodies and no file used them.  At cutover these two
sites are the fork/boot items of the M2 worklist, beside the five
`hart_view_lb_any` sites the M-leg itself carries.

The ambient-row corner that goes with it: `procs_inv` stays at the
ambient context in `main_deposit_rows`, `park_globals`, `ProofMain`'s
deposit and `ProofForkretPark`'s record (as a `ctx_morph_const` row),
`proc_priv` likewise; rows with real morphs (`is_kstack`, `ctx_cells`,
`stack_own`, `disk_geom`, `ctx_word_pointsto`, `console_ready`) are
indexed.  Un-deferring needs the caps channel or the M-leg's
`XIp`-pinned `valid_context_pre` — a decision, not a merge.

## 6.4 SC-only lemmas added (§5.3 class, flagged)

`TsoCtxShim.own_context_any` / `ctx_parked_any`; `WpLock.is_lock_pay_iff`
(an `inv_iff`, not SC-only); `ConsoleInv.console_inv_morph` /
`console_ready_morph` (via `is_lock_reindex` + `is_lock_pay_iff` +
`cons_res_morph` along `ctx_dom_sc`); `WpLock.newlock`-side
`lock_pay_intro` kept (M-leg SC form).

## 6.5 Deferred

| deferred | stand-in |
|---|---|
| a fork child's own context; per-hart contexts at boot | the stub tokens (6.3) |
| `procs_inv`/`proc_priv` rows at the record's context | ambient rows, `ctx_morph_const` |
| `cpu_ctx_free`'s parked record + receipt | bare `∃ vs ξ`; `ctx_dom_sc` |
| `caps_fam`/`caps_morph`; `KptShare.kpt_creds`; `TsoCtxAbsorbLb` | absent |
| the M-leg's own M2 debt (five `hart_view_lb_any` sites, `ctx_dom_sc` at `lock_pay_intro`/create/destroy) | as on the M-leg |
