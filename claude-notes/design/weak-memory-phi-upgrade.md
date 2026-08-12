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

The remaining C/D sweep (in flight): carry the effect trace through the
certificate Q's (`wQ_pure` → `wQ_pure_fr es` family, ~30+30 sites), the
`nv_hart` conjunct into the interp defs paid at ~50 sites, the
non-funnel paths (racy/started/acquire/walk/Tor/Amo4) with their
per-path evidence, then `weak_system_adequacy_phi`.

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
