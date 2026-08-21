# Route B — the exchange-normalization plan of record (IN PROGRESS)

Status: ADOPTED by the user 2026-08-21 (over route A, on the D-iii probe
evidence — see the certification worklist's D-iii entry for the probe
verdicts and the two routes' bills).  This document is the route's design
pass, being written as the design settles; sections marked OPEN are not
yet decided and nothing should be built against them.

## 0. The goal, unchanged

The tier-2 capstone: every RVWMO⁻(+deps, §2)-consistent execution of the
xv6 image satisfies the safety property the EWPs establish.  `Print
Assumptions` target: the five rv64d reservation axioms + the recorded
hardware-fidelity boundary clauses.  Zero kernel premises, nothing
undischarged — the same standard as everything landed.

## 1. The chain

```
G : gexec, rvwmo_minus_deps_consistent, xv6 image
  │  (the exchange normalization — THIS ROUTE'S NEW CONTENT, §3)
  ▼
G' : same observables, grule14
  │  (T2-1c, LANDED: rule14_linearization — Closed, no axioms)
  ▼
c : cand, srvwmo_consistent, same log
  │  (T1, LANDED: promise_free_complete_clean / srvwmo_realizable)
  ▼
a promise-free machine execution
  │  (tier-1 adequacy + φ, LANDED)
  ▼
safety
```

The machine NEVER realizes a weak (rule-14-violating) execution — only
normalized prefixes.  That is why none of route A's quarantine retrofit
(D-8 drop, fetch/CSR/trap guards, the restriction simulation) is needed,
and why the instance reset-point fix (W2b-c1) is about model honesty,
not about this chain.

## 2. The declared model gains the store-dep fragment (`gx_deps`)

Re-reading S6 §3's edge inventory against this route: the
dependency-based kills — #2/#3 (control/data into later stores), #6
(branched-on reads), #7/#8 (W-TV: translation reads before the
translated access's store) — are MACHINE facts in route A's telling, and
bare RVWMO⁻ (ppo rules 9–13 dropped) cannot see them.  Route B needs
them as GRAPH constraints: `gx_deps` — dependency edges INTO STORES as
graph data, with the consistency axiom `gx_deps ⊆ gmo` — exactly D-v's
deferred item, promoted to this route's core.  Scope of the edges
(matching what the machine enforces and RVWMO's ppo licenses):
syntactic address/data deps into stores (rules 9/10's store halves),
control deps into stores (rule 11), and the W-TV translation edge into
stores (the adopted boundary sentence's transposition of Arm `dob`;
rule 13's rationale).  Loads gain nothing (D-8 stays; matches both Arm
models per the W3 audit).

Direction check: adding constraints SHRINKS the declared model toward
RVWMO; since every added edge class is ⊆ RVWMO's own ppo, the final
theorem still covers RVWMO-conformant hardware.  The F2 caveat already
recorded this as the intended eventual shape.

Representation decision: ADDITIVE — a wrapper record
`gdexec := { gd_g : gexec; gd_deps : list (geid * geid) }` with
`deps_wf` (source a READ — control/addr/data/translation dep sources
are all reads, since branch events are not in the fused alphabet —
same hart, po-before a write target) and `deps_gmo : ∀ (r,w) ∈ deps,
gmo_lt r w`.  Nothing landed moves.

A SIMPLIFICATION this buys (2026-08-21 finding): with `gx_deps` in the
model, the dependency kills AND the fence/acquire kills of S6 §3 become
PURE GRAPH ARITHMETIC (`deps_gmo`, and ppo⁻ rules 4/5 which RVWMO⁻
kept) — the pf-realized-prefix machinery of §3a is needed ONLY for the
two export kills, #4 (φ) and #5 (lock protocol).

**§2a — WHY THE DEP FRAGMENT IS NECESSARY IN THE HYPOTHESIS, and the
OPEN conformance question (the route's hardest design item).**  Bare
RVWMO⁻ admits genuine THIN-AIR executions (dropping rules 9–13 is what
admits them; RVWMO forbids them exactly there, and sRVWMO forbids them
by its `ax_no_thin_air` axiom).  A thin-air graph of the xv6 image can
fabricate values into protected bytes, so the bare-RVWMO⁻ capstone is
most likely FALSE — the hypothesis must carry the dep fragment.  But
`gx_deps` as free data does not help by itself: the capstone
quantifies over graphs, and a graph may simply OMIT its dep edges
(fewer constraints admits it again).  So the hypothesis needs a
CONFORMANCE clause — "`gx_deps` contains the program's actual
syntactic/translation deps" — and the fused label alphabet cannot
express "the program's deps" (no operand lists; this is F1's alphabet
issue resurfacing at the model level).  Candidate resolutions, to be
weighed in the B0 design pass:
  (α) state conformance through `WeakDeps.deps_of_bits` (a PURE decoder
  on instruction words): per hart, an instruction-word stream from the
  image decodes to the row's label shapes with `gx_deps ⊇` the decoded
  deps.  Static per-instruction correspondence, no machine runs — but
  it is the fetch/decode-to-labels front-end, a real new piece (which
  route A's `axiomatic_to_promising` port would ALSO have needed, so
  not a route-B regression);
  (β) restate the capstone over machine-run graph ABSTRACTIONS instead
  of free graphs — rejected on sight (that is route A's containment
  again);
  (γ) an `ax_no_thin_air`-style po∪rf acyclicity axiom instead of deps
  — rejected: it forbids LB and collapses the model toward sRVWMO.
  (α) is the working favorite.  Note the same question decides what #9
  (the walker-exit case) needs from the model.

## 3. The exchange normalization (the new content)

### 3a. The induction object — DECIDED: trace-world frontier

The mechanized C-tree kills (`fcov_of_dep_chain`,
`covered_of_release_chain`, `cs_read_covered_window`,
`scc_no_bad_of_phi`, `S1_of_aq`-genre) are all stated over RECORDED
per-agent traces (`ptraces` / `at_ags`), not over `gexec`.  So the
induction maintains a **pf-realized prefix with real traces**: an
invariant of the shape

> the gmo-prefix of `G` up to the current frontier, restricted per
> agent to its po-prefix, is realized by a promise-free machine run
> whose per-agent traces are exactly those label prefixes and whose log
> is the prefix's writes in gmo order (the T2-1c prefix construction +
> T1 realization, both landed),

so at the frontier every export (φ via `weak_ev_pf_violation_free`, the
lock-word protocol via `weak_ev_adequacy_lockproto`, and the machine
facts) applies to the realized configuration, and the kill lemmas apply
VERBATIM with `T` = the realized trace of the acting agent.  No
re-derivation of the C-tree in `gexec` vocabulary.

### 3b. The induction and the exchange lemma — OPEN, first sketch

Measure: the number of rule-14 inversions of `G` (pairs `(e, w)` with
`e` po-before the write `w` but `w` gmo-before `e`), or the
displacement sum.  Step: take a gmo-minimal violating write `w`;
everything gmo-before `w`'s target position is a rule-14-respecting
prefix (realize it, §3a); attempt to EXCHANGE `w` one gmo position
later.  The obstruction cases (what a swap can break):

  1. the gmo-successor is a READER of `w` (rf edge) — the classic
     early-observation shape; the read is at a pf-realized frontier,
     and the S6 §3 kill table names its refutation (aq/M, ctrl/M via
     `gx_deps`, fence/M, φ/X, lock-protocol/X);
  2. the gmo-successor is a SAME-BYTE write — co order flips; killable
     or absorbable (coherence-facing; poloc cases are already gmo-fixed
     by ppo rules 1–3, so the swap candidates are cross-hart same-byte
     writes — OPEN: the absorption argument);
  3. the gmo-successor is same-hart — po/ppo⁻/`gx_deps` edges pin it —
     these swaps are refused and the violation is instead killed at its
     OBSERVER (case 1) or vacuous (OPEN: prove the trichotomy).

Termination: each successful exchange strictly reduces the measure;
each refused exchange comes with a kill (contradiction with
consistency + the exports) — so a consistent xv6-image execution
normalizes fully.

**STRESS-TEST FINDINGS (2026-08-21, orchestrator; they reshape §3b's
detailed design):**

- **Read-down-moves are nearly free.**  A violation `(e, w)` with `e`
  a READ resolves by moving `e` gmo-EARLIER (below `w`), not `w`
  later: swapping a read past adjacent events breaks nothing (no
  write positions move, visibility sets only grow) — EXCEPT past the
  read's own rf-SOURCE.  So the read-violation residue is exactly:
  `e` reads some `w0` sitting gmo-BETWEEN `w` and `e`.  That is S6's
  segment-entry shape, and the kill split is: rule 5 (`e` acquire) /
  `gx_deps` (`e` feeds `w`) / rule 4 (fence between) make the
  violation INCONSISTENT outright — pure graph arithmetic; otherwise
  `e` is a genuinely unordered racy read and the φ/lock-protocol
  kills must refute `w0`'s readability at the realized prefix.
- **The LB sanity check.**  On the LB graph the induction gets STUCK
  (both harts' reads are pinned against their sources, both writes
  against their readers) — CORRECTLY: LB is a genuine RVWMO⁻ behavior
  outside sRVWMO, and if the induction succeeded unconditionally the
  models would collapse against our own non-collapse witness.  The
  induction's success for the xv6 image IS the kernel-level
  exhaustiveness claim (S6 §3's classes a–e): classes (a)–(c) give
  graph edges making the LB shape inconsistent; (d)/(e) fire the
  export kills.  This is the honest restatement of "route B = the
  same C1–C5 tree".
- **The prefix-closure subtlety.**  The gmo-prefix below the minimal
  violating write is po-closed at WRITES (by minimality) but NOT at
  reads — a prefix read may have po-predecessor reads still above the
  frontier — so the realized set must be the largest doubly-closed
  subset, and the induction likely wants to eliminate READ-violations
  first (the free moves) so the frontier's po-closure holds when the
  export kills need realization.  Organizing the induction around
  this (which violation to attack, closure maintenance) is B2's
  detailed design, together with the write-class inventory.

### 3c. What is reused, by name

- T2-1c's construction and the six-obligation bootstrap (the worklist's
  "standard route") for the prefix realization — likely as a PREFIX
  variant of `rule14_linearization` (OPEN: statement).
- The kill lemmas as listed in S6 §3, unchanged.
- The exports: T2-0's `weak_ev_adequacy_lockproto` (F3, landed), φ's
  `weak_ev_pf_violation_free`, D-ii's TOP fact for the walker cases.
- The E1-genre glue (extending a realized prefix by one event and
  re-establishing the invariant) — the cone-replay machinery
  (`head_prestate_pf_real`, L2-M2 §8.3) is the closest banked piece;
  OPEN: how much transfers.

### 3d. What is retired

D8-2/D8-3 (never built), the quarantine retrofit (never built),
`WeakCertify`/D8-1 (built; becomes archive — keep compiling, mark the
header), E1/L2′ in their route-A statements (their CONTENT — the case
analysis and the exports — survives as §3b's kills; their carrier
changes from "extended pf runs of the full machine" to "the frontier of
the normalization").

## 4. Staging

- **B0a — LANDED (2026-08-21, orchestrator-built, definitional):**
  `WeakRvwmoGraph.v` §7 — `gdexec` (the additive wrapper), `gdeps_wf`
  (read → po-later same-hart write), `gdeps_gmo` (the ppo 9–13 store
  fragment as the ordering axiom), `rvwmo_minus_deps_consistent`, and
  the re-checked non-collapse witness `lb_graph_deps_consistent`
  (`lbgd := GDExec lbg []` — LB's pairs are syntactically independent,
  so the empty dep set is the honest one; Closed under the global
  context).  Nothing landed moved; `WeakRvwmoLin` recompiles untouched.
- **B0b — the conformance interface (design SETTLED 2026-08-21; build
  owed):** the capstone-level clause is stated through TIER-1'S OWN
  conformance vocabulary, not a new bits-level statement.
  `WeakAxRealize.exec_prog_ok` is trace-order-indexed with the fabric
  threaded through, so the tier-2 form factors it: (i) PER-HART ROW
  EMITTABILITY — the hart's event program emits its label row in po
  order, via `lbl_realizes` with timestamps abstracted
  (`ts_oblivious` is exactly the insensitivity this needs) and the
  fabric threaded only at dev-touching events (the M5 fence discipline
  pins those, so the exchange never reorders them — §3b case note);
  (ii) `row_deps` — a PURE register-dataflow relation over the emitted
  INSTANCE label sequence (`LRegW rd [DLdRes]` after loads, `asrc`/
  `vsrc`/`deps_ctrl` at stores, last-writer chains), with the
  conformance clause `gd_deps ⊇ row_deps(emission)`;
  `WeakDeps.deps_of_bits` enters only through the emission's own
  announce nodes — machinery that exists.  (iii) the FINAL realization
  (of the normalized cand) is discharged by showing normalization
  preserves per-hart emittability — the rows are unchanged, only the
  interleaving moves, and per-hart emission is row-determined modulo
  ts and the fabric order (which is preserved).
- **B1**: the prefix-realization statement (§3a/§3c) — T2-1c's prefix
  variant + T1, packaged as the induction invariant.
- **B2a — LANDED (2026-08-21): the exchange kit's first lemma,
  `iris/WeakRvwmoXchg.v`** — `gswap` (adjacent gmo swap via the `sidx`
  involution: ONE lookup equation, the "except the swapped pair"
  clause lives in `sidx_mono`/`sidx_mono_inv` once),
  `gswap_read_down` (consistency preserved when the UPPER event is a
  non-write, the lower is not its rf-source, and `¬ gppo lower upper`
  — with `gppo_same_hart` making that free cross-hart), the `gdexec`
  corollary (the no-dep side condition DERIVED from `gdeps_wf`, not
  hypothesized), `gviol`/`gviol_grule14`, `gswap_viol_mono`
  (violations only shrink under a read-down move) and
  `gswap_resolves` (the swapped pair's violation dies — the measure
  step).  All Closed, no axioms, ZERO hypotheses beyond the spec (one
  spec hypothesis removed as derivable).  KEY SCOPE FACT: the lemma's
  only label hypothesis is "the upper event is not a write", so it
  covers BOTH `(W,R)` and `(R,R)` adjacencies — and `(W,R)` IS
  write-moves-up-past-a-read viewed from the other end.  B2b's new
  work is only `(R,W)` (write down past a read: the read's visible
  set GROWS, so co-maximality needs a `ts ≥ gwix w`-or-byte-disjoint
  side condition) and `(W,W)` (the real work: `gwrites` itself swaps,
  readers' `ts` entries renumber; the §1 `lswap` kit self-applies at
  the `gwrites` level).  The RMW-read case (upper event a fused
  RMW) is deliberately out of B2a's scope.
  POST-LANDING SCOPING — CORRECTED (orchestrator, 2026-08-21, second
  pass; the first version of this note claimed "(R,W) likely never
  needed", which a deeper pass refuted).  Resolving a WRITE-WRITE
  violation `(e, d)` (write `e` po-before `d`, `d` gmo-early) cannot
  move `d` up past its own READERS — but a write's readers never
  block its DOWNWARD moves (the source only gets earlier), so the
  induction moves `e` DOWN below `d` instead.  The descent needs:
  `(R,W)` — a write descending past a read, side condition per shared
  byte `gwix e ≤ t` (the read already reads at-or-after `e`; a
  same-hart forwarded read of `e` satisfies it with equality) — and
  `(W,W)` byte-disjoint with the ts-transposition label rewrite (the
  two writes' `gwix` values exchange, so every reader's `ts` entry
  naming either renumbers; values unchanged.  Same-byte same-hart is
  poloc-inconsistent; same-byte cross-hart stays excluded until the
  inventory shows a need).  THE MOVE STRATEGY that keeps rule-14
  bookkeeping monotone: sweep the reads sitting gmo-between `d` and
  `e` down below `d` FIRST (B2a; each is itself a read-violation
  witness or free), so when `e` descends no same-hart-po-earlier read
  remains between — the viol-mono lemmas hypothesize
  `¬ gpo lower upper` accordingly, discharged by the sweep order; in
  the RESOLVING orientation (lower = `d`, upper = `e`, `e po< d`) it
  is automatic.  A dep edge `(x, e)` into a descending write blocks
  the descent — correctly: the violation is then dep-killed
  (`gdeps_gmo` contradiction).  The full kit is THREE lemmas: B2a
  (landed), B2c `(R,W)`, B2b `(W,W)`-byte-disjoint.
- **B2bc — LANDED (2026-08-21): THE EXCHANGE KIT IS COMPLETE.**
  `gswap_write_down` (+deps corollary, viol-mono) and `gswapw_ww`
  (+deps corollary, viol-mono, `gswapw_resolves`, `gwix_adjacent`),
  all Closed, no axioms; the LB witness smoke-tests the (W,W) move
  (both loads' `ts` entries renumber).  `tswap` IS `sidx` at another
  argument — the arithmetic re-exports, and
  `gx_gmo (gswapw …) ≡ gx_gmo (gswap …)` definitionally, so B2a's §2
  position kit applied verbatim.  THE DESIGN FINDING (a spec claim
  REFUTED by counterexample): the fused alphabet means "dep sources
  are reads" NEVER excludes a write — an `LRmw` is both — so EVERY
  exchange lemma whose moved-up event may be an RMW carries a
  `(x, e) ∉ gd_deps` side condition (B2a's free derivation was free
  only because its moved event was a non-write).  The induction
  discharges these by the dep-kill (edge present ⇒ `gdeps_gmo`
  contradiction ⇒ the violation is dead anyway).  Induction side
  conditions to discharge, now enumerated: `¬ gppo lower upper`
  (cross-hart free via `gppo_same_hart`), `¬ gpo lower upper` (the
  sweep order), the `(R,W)` co-max condition (`gwix e ≤ t` on shared
  bytes), byte-disjointness for (W,W), and the `∉ gd_deps` pair.
  Two unused hypotheses (`gis_w e` in `gswap_write_down` and
  `gswapw_resolves`) kept for statement fidelity, droppable.
- **B2**: the exchange lemma's case trichotomy (§3b) with the kills
  wired per S6 §3; the induction + measure.  NOTE from the B0 pass
  (2026-08-21): several S6 kills flip from reader-refutation to
  WRITE-SIDE PINNING on graphs — e.g. `s:=1` (#2) is fence-pinned
  (rule 4) and can never be rule-14-early, so its "harmless early
  read" case never obstructs; a same-hart same-byte future-read is
  killed by poloc (rules 1–3) with no deps; the CS store `x:=v` is
  acquire-pinned (rule 5) below and release-fence-pinned above, and
  its cross-hart reader is window-ordered by `win_excl`.  The
  systematic write-class inventory (the "B-S6" table) is B2's design
  gate.
- **B3**: the capstone assembly (§1) + audits; retirement notes (§3d).

## 5. Honest residual risks — OPEN

To be priced during B1/B2 design: (i) the prefix variant of T2-1c (the
full theorem assumes grule14 of the WHOLE graph; the prefix form needs
"grule14 below the frontier" only — expected clean, the construction is
per-segment); (ii) case 2's absorption argument (cross-hart same-byte
co swaps); (iii) the exhaustiveness of the kernel-level read classes
(S6 §3's kernel claim) when expressed at the frontier — this is L2′'s
old obligation in new clothes and remains the route's largest single
item.
