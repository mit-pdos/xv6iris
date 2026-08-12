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
