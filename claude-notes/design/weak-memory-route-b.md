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
  │  (T2-LIN: no violation on an R-cycle — §4d; then the DIRECT
  │   LINEARIZATION `WeakRvwmoTopo.topo_linearizes`, which superseded
  │   §3's exchange normalization on 2026-08-22)
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

### 3b′. The induction's obstruction landscape (2026-08-21, mapped
### against the completed kit — B2d's design input)

The uniform move: to resolve `(e, w)`, DESCEND `e` (read or write) to
just below `w`, one adjacent swap at a time.  A swap of `e` past `z`
(sitting below `e`) can be refused three ways, and each refusal has a
disposition:

1. **`gppo z e`** — by `gppo_same_hart`, `z` is same-hart and
   po-before `e`, hence po-before `w`, hence ITSELF a violation
   witness `(z, w)` sitting gmo-in `(w, e)`.  Disposition: descend the
   witnesses of `w` in PO ORDER (earliest first); then no
   gppo-blocker remains when `e` descends.  This is the sweep order,
   now with its precise justification.
2. **`e` a read blocked at its rf-SOURCE `w0`** gmo-in `(w, e)` — THE
   KILL POINT: aq (rule 5), deps (`gdeps_gmo`), and fence (rule 4)
   refute the configuration outright (consistency contradictions);
   the residual — a genuinely unordered racy read of a
   mid-window-sourced value — is where the φ/lock-protocol kills fire
   at the realized prefix (§3a).
3. **`e` a write blocked at an OLD-BYTE READER `z`** (the B2c co-max
   side condition fails: `z` reads a byte of `e` at `t < gwix e`) — a
   case the S6 inventory did not name (it is the co/fr-side twin of
   case 2).  Disposition: descend `z` first (it is a read — B2a), and
   ITS blockers recurse into cases 1/2.  No new kill class arises:
   case 3's stuck forms reduce to case 2's.

TERMINATION — RESOLVED (2026-08-21, the B2d design session; this
SUPERSEDES the entourage/recursion framing above, which came from
mis-reading the moves as relocating the blockers — the kit's swaps
move ONLY the descending event past a stationary `z`):

**THE PO-MINIMAL-WITNESS DISCIPLINE.**  Attack `w` = the gmo-MINIMAL
violating write, `e*` = the PO-MINIMAL witness of `w` (all witnesses
are same-hart as `w`, so po-minimal is well-defined).  Then:
- every `¬gppo z e*` and `¬gpo z e*` side condition along the descent
  is VACUOUS: such a `z` is same-hart, po-before `e*`, hence po-before
  `w`, hence itself a witness in the interval — contradicting
  po-minimality;
- a SAME-HART rf-source of a read `e*` cannot sit in the interval
  (it would be an earlier write-witness) — only CROSS-HART sources
  block;
- the FINAL swap `(w, e*)`: `e*` cannot read `w` (poloc would
  contradict the violation), byte-disjointness for the write case is
  DERIVABLE (a shared byte gives poloc `e* → w`, contradicting the
  violation), and `(w, e*) ∉ gd_deps` is FREE from `gdeps_wf`
  (source must be po-before target; `e* po< w`).
So the descent needs NO entourage and NO recursion: each swap is
B2a/B2c/B2b with vacuous-or-derivable side conditions, EXCEPT exactly
three residual configurations (K3 found while finalizing the B2d
spec):
- **K1** (`e*` a read): its cross-hart source sits gmo-in `(w, e*)` —
  S6's reader-of-the-early-write shape, entered from the witness side;
- **K2** (`e*` a write): some interval event reads a byte of `e*` at
  an index `< gwix e*` — the MP-STALE-READER shape.  Verified
  genuinely un-normalizable when live: the mixed read (stale byte of
  `e*`, and transitively a fresh read of `w`) cannot exist in ANY
  rule-14 graph with the same rows (graph co-maximality refuses it),
  so it MUST be killed, and its kill is the same inventory routed
  through the STALE byte (the writer-fence case kills the violation
  itself by rule 4; the φ/lock cases kill the stale read at the
  realized prefix);
- **K3** (`e*` a write): a CROSS-HART SAME-BYTE WRITE sits gmo-in the
  interval — the kit's excluded (W,W) case, and correctly: pre-swap
  consistency forces every same-byte reader above the pair to read
  `e*` (the co-max), and the swap would make `z` the max, breaking
  them.  The configuration is a write-write RACE interleaved with an
  early-store window; for xv6's rows same-byte cross-hart writes are
  protocol-governed (lock words, φ-owned bytes, single-writer
  flags) — B2e's third obligation.
Each completed descent strictly reduces |violations| (the interior
swaps are viol-monotone with vacuous side conditions; the final swap
is `gswap_resolves`/`gswapw_resolves`); the measure is |V| with an
inner induction on the descent length.  **B2d is therefore
delegate-ready as a KILL-PARAMETERIZED theorem**: `normalize` takes
`kill_K1`/`kill_K2` as explicit hypotheses (discharged by B2e, the
kill package, which needs B1's realized prefix); the capstone stays
premise-free by discharging them there.  The rows correspondence is
a write-index permutation `π` (the composition of the adjacent
transpositions): same image, same row lengths, labels equal modulo
`π`-renaming of ts entries.

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
- **B2d — LANDED (2026-08-21): `iris/WeakRvwmoNorm.v`,
  `normalize` — the kill-parameterized exchange normalization, Closed,
  no axioms.**  Consistency + `kill_K1/K2/K3` ⇒ a rule-14 graph with
  `rows_rel π` (rows equal modulo the write-index renaming `lbl_ren π`,
  values/bases/classes untouched), `wperm π` (write messages preserved
  under the bijection), and the SAME dep set.  The po-minimal-witness
  discipline worked exactly as designed: every side condition is one
  application of `po_min_no_blocker` (via the new
  `gppo_po_lt` — all four ppo⁻ arms pin the offset, not just the
  hart), the final swap's conditions are all derivable, and no fourth
  kill was needed.  THE ONE DESIGN DELTA: the kills quantify over the
  ROWS-EQUIVALENT ORBIT (`∀ GD', gd_equiv GD GD' → …configuration at
  GD'…`), forced twice over — the minimality clauses are
  backward-unstable (violations only shrink along the chain), and
  K2's `t < gwix e` does not transport under a non-monotone
  transposition — and `gd_equiv` is exactly the invariant the
  induction maintains (`normalize`'s own conclusion shape).  **B2e
  must discharge the kills for an ARBITRARY rows-equivalent
  consistent graph** — cheap in kind, since the realized-prefix
  argument depends on the rows and the write messages, both
  orbit-invariant.  THE NON-VACUITY CHECK, machine-checked:
  `lbgd_kill_K1_false` — the LB witness REFUTES K1, so the kill
  interface is not vacuously true and the normalization correctly
  sticks on LB (the design's sanity check in its strongest form).
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

## 4b. B1's shape (designed 2026-08-21, post-B2d)

THE SIMPLIFICATION: no prefix variant of the linearization is needed.
The kill interface's minimality clauses deliver the closure — for K1,
the po-minimal witness `e`'s po-predecessors are ALL gmo-below `w`
(a read-predecessor above `w` would be a po-smaller witness; a
write-predecessor would violate `w`'s gmo-minimality), so the
realized set is a genuine doubly-closed prefix and the LANDED
`rule14_linearization` applies to the RESTRICTED graph as-is.  B1
splits:
- **B1a — the restriction slice** (pure order theory, delegate-ready
  after B0b-1): `gx_restrict G cs n` (per-hart cut vector + a gmo
  cut, with `restr_ok` tying them: the cuts' mem events are exactly
  the gmo prefix, i.e. po-closure holds by prefixing), and the
  consistency-restriction lemmas: `gwf`/`gppo_gmo` restrict
  trivially; `gload_value`'s ∃-half lands inside by closure and its
  ∀-half (co-max) only weakens; `gatomicity` likewise; `gd_deps`
  restricts to in-cut pairs; `grule14` of the restriction ⟸ the
  prefix is violation-free (the hypothesis the induction supplies by
  minimality).
- **B1b = B0b-2 — the supply derivation**: from `gdexec_conf`'s
  per-hart emissions, derive `exec_prog_ok'` for the restricted
  cand's trace (the T2-1c enumeration of the restriction), threading
  the device witness.  Then T1 + `exec_wf_pf_run_prog'` (T1-D's)
  realize the prefix as a pf run, and the exports hold at its
  reachable configurations.

## 4c. B2e's decomposition (designed 2026-08-21, post-B0b-1)

Three stages, each smaller than the last is hard:
- **B2e-1 — the arithmetic sub-kills** (pure order theory, buildable
  once B1a lands): reduce each kill to its RACY RESIDUAL.  For K1:
  `e` an acquire (rule 5 arm of `gppo` + `gviol` = contradiction),
  `(e, w) ∈ gd_deps` (`gdeps_gmo` contradiction), or a covering fence
  (rule 4 contradiction) — so K1 reduces to `e` plain/non-aq/undepped/
  unfenced.  K2's writer-fence case likewise (rule 4 between the
  stale byte's writer `e` and `w` kills the violation).  Deliverable:
  `kill_K1_of_racy`-style reduction lemmas.
- **B2e-2 — the graph-side protocol kit**: `win_excl` as ORDER THEORY
  over the rows' lock-word messages, from the VALUE PATTERN hypothesis
  (each L-write is an acquire-RMW writing nonzero whose read names its
  co-predecessor, or a release writing zero): load-value + atomicity
  chain the windows totally.  THE KILL SHAPE THAT FALLS OUT (worked
  for K1's CS case): if `e`'s read of `w0` is CS-covered, the window
  order + rule 5 give `w0 gmo< ACQ_h gmo< w`, contradicting
  `w gmo< w0` — the export kill becomes pure arithmetic ONCE the
  pattern is in hand.
  B2e-2's DERIVATION CHAIN (worked 2026-08-21; CORRECTED at the
  landing — the chain as first recorded was ONE STEP SHORT): from
  `lock_pattern G b` (every b-write is an acquire-RMW writing nonzero
  whose read entry at b names a ZERO value, or writes zero),
  ATOMICITY makes each acquire's co-PREDECESSOR the zero-write it
  read — but that alone does NOT give window exclusion: the
  machine-found COUNTEREXAMPLE `ACQ_h · REL_x · ACQ_j · REL_h ·
  REL_j` (a THIRD hart's release separating overlapping sections) is
  pattern-legal.  The missing piece is **`lock_paired`** — every
  release closes a critical section of ITS OWN hart — taken in the
  SYNTACTIC per-site form (`lock_cs_intro` reduces it to "between my
  acquire and my release my hart writes b nowhere else", po-local,
  with same-hart co-order = po-order free from poloc), so B2e-3's
  obligation is site classification, never the conclusion.  With
  pairing, `acq_no_overlap`'s strong induction gives the total window
  order (`win_excl_of_pattern`).  The assembled `cs_kill`: given
  CS-coverage facts (ACQ_h po-before {e, w}; w0 po-before REL_j with
  the release FENCE between — rule 4), the window order gives
  `w0 gmo< REL_j gmo< ACQ_h gmo< w` (last step rule 5), contradicting
  `w gmo< w0`.  Pattern + coverage discharge = B2e-3.
- **B2e-3 — the pattern + φ discharge** (the true L2′ content, needs
  B1): the value-pattern hypothesis discharged from conformance + the
  realized prefix's exports (`wlp_at` covers prefix messages; the
  beyond-prefix messages' pattern comes from the per-site analysis of
  xv6's L-writers — acquire/release only), and the φ kill for
  non-lock bytes (owned-unpublished CS bytes) via
  `weak_ev_pf_violation_free` at the realized prefix.  K2's
  routing-by-byte-class and K3's write-write-race classification live
  here.  NOTE the E1-shape difference from route A: `w0` is OUTSIDE
  the realizable prefix (no promises exist to supply it), so the
  φ/protocol kills must run on `w0`'s MESSAGE DATA (base/values/
  class — orbit-invariant graph data) against the prefix's protocol
  state, not on a replayed read step.

## 4d. B2e-3 — the design (2026-08-22 session; supersedes the 2026-08-21
## problem statement, which is folded in below as the starting point)

THE STARTING POINT (2026-08-21): the architecture `xv6_row_ok` / kill
discharges / row_ok discharge was "settled", and the CRUX was the
WILD-VALUE OBSTRUCTION — emittability does not ground values (`pstep_ev`
accepts any read value), realization reaches only the violation-free
prefix below `w`, and the kills need site facts at `w0`/`z` ABOVE it.
Three candidates were recorded (extended realization; groundedness as an
induction invariant; a static checker).  This session ran the miniature
against all three and found that the question was mis-posed in four
places before it could be answered.  The findings first, then the design
they force.

### 4d.1 Findings that reshape the problem (each machine-checkable; see §7)

**F1 — `kill_K1` as landed is STRONGER THAN THE THEOREM NEEDS, and the
excess is exactly the undischargeable part.**  K1 fires whenever the
witness `e` is blocked at its cross-hart source `w0 ∈ (w, e)`.  But the
normalization has a second move the B2d design never used: DESCEND THE
SOURCE.  `w0`'s readers never block its downward moves, so `w0` can be
descended to just above `w` and (W,W)-swapped below it (byte-disjoint —
a shared byte would give `e` a same-byte po-earlier write and poloc
orders it), after which `e` descends freely.  `w0`'s descent is blocked
only by `w0`'s OWN po-earlier events in the interval (rule 1–5 pins) —
which descend first, recursively — i.e. by `w0`'s causal past inside
`(w, e)`.  The recursion fails exactly when that past reaches `w`'s hart
above `e`, i.e. when **`w (po ∪ rf)⁺ w0`: a causal cycle through the
violation**.  The MP-reader-without-fence shape (h: `e` reads `w0`; `w`
an independent early store; nothing reads `w` in the interval) satisfies
K1's premises verbatim and HAS a rows-equivalent rule-14 graph
(`w0 < e < w`), so no kernel fact could ever discharge K1 there — the
kill would be asking us to refute a possible execution.  Every "(d)/(e)
exhaustiveness" worry of the old §4d about dead racy reads and
unclassifiable CS reads lived in this excess.

**F2 — the genuine obligation is ONE sentence: the relation
`R := po|→W ∪ rf ∪ co ∪ fr ∪ ppo⁻ ∪ deps` IS ACYCLIC** (`po|→W` = po
edges INTO a write, i.e. rule 14's edges; `co` = same-byte write order;
`fr` = read-before-a-co-later-write).  Two facts: (i) in a rule-14
consistent graph every edge of `R` is a `gmo` edge (rule 14, load-value,
co = write order, the ppo/deps axioms), so `R` is acyclic, and
rows-equivalence preserves every edge class — hence a rows-equivalent
rule-14 graph exists ONLY IF `G`'s `R` is acyclic; (ii) conversely a
topological order of `R` IS a consistent rule-14 gmo (load-value: `rf`
puts the source before the read and `fr` puts every co-later write after
it, so the co-max before the read is its source; atomicity: co-adjacency
is preserved), so `R`-acyclic graphs normalize — with F1's extended
move set this is what the exchange kit computes.  Since `G` is itself
consistent, `rf ∪ co ∪ fr ∪ ppo⁻ ∪ deps ⊆ gmo(G)` is acyclic already:
**every `R`-cycle passes through a VIOLATING WRITE** via one of its
`po|→W` edges, so route B's kernel claim is **(T2-LIN): in every
RVWMO⁻(+deps)-consistent, conformant execution of the xv6 image, no
violation `(e, w)` lies on an `R`-cycle** — i.e. no `R`-path from `w`
back to `e`.  The pure `po ∪ rf` cycles (load buffering / thin air)
are the special case B2d's K1 enters from; the `co` and `fr` entries
are exactly B2d's K3 (cross-hart same-byte write in the interval) and
K2 (stale reader) — the kit had found the three entry kinds
correctly, it only lacked the cycle that makes them GENUINE.  (A
first draft of this finding said `po ∪ rf`; the K3 shape — `w` read
by x, x's later store to `a`, j's `w0` to `a` co-after it, `e` reads
`w0` — has no `po ∪ rf` cycle and no rule-14 graph, which is what
corrected it.)

**F2′ — THE CORRECTION P5 FORCED (third iteration, now
machine-grounded).**  `WeakRvwmoAcyc.v` proves `R ⊆ gmo` (hence `R`
acyclic) for rule-14 consistent graphs and transports `po|→W`, `rf`,
`ppo` along `rows_rel`/`wperm` — but NOT `co`/`fr`: `wperm`'s π is only
injective (B2d's (W,W) exchange is a non-monotone transposition), and
that is correct, because the co-order of two same-byte writes that NO
read distinguishes is unconstrained by consistency, so two
rows-equivalent consistent graphs can disagree on it.  So the "only if"
of F2(i) holds for `Rt := po|→W ∪ rf ∪ ppo(∪ deps)` unconditionally and
for `co`/`fr` only where a read pins them.  THE HONEST OBLIGATION is
therefore DISJUNCTIVE: `G` normalizes iff there is a per-byte write
order `co'` compatible with the rows (each read's source stays its
co-max: every other same-byte write is co'-before the source OR
gmo-after the read; RMW read/write co'-adjacent) such that
`R_{co'} := po|→W ∪ rf ∪ co' ∪ fr(co') ∪ ppo⁻ ∪ deps` is acyclic; `G`'s
own `co` is one candidate, and a cycle of `R_{co}` through a same-byte
pair that no read distinguishes is NOT a genuine kill — the
normalization must flip such pairs (B2d excluded all same-byte (W,W)
swaps; the precise rule is: adjacent same-byte writes swap when the
lower one has no reader above the pair).  The per-segment KILL
(§4d.2(3)) is unaffected — it refutes a cycle in the CHAIN'S CURRENT
graph by arithmetic on that graph's own co, with `co`/`fr` entries
only where a read pins them (K2's stale reader, K3's write race with
a reader in the interval).  Three definitional corrections from the
same file, to reuse: `po|→W` needs `gmem` of the source (fences are in
po but not in gmo); `fr` is defined on the read's own `ts` entry per
byte (a co edge at another byte of a multi-byte write carries no
load-value information); `fr` excludes the identity (a fused RMW reads
and writes the same byte — herd's `fr = rf⁻¹;co ∖ id`).

**F3 — the realizable region is NOT the gmo prefix, and B1a's `restr_ok`
cannot express what B1b needs.**  `restr_ok` demands per-hart cut = gmo
prefix.  Other harts' EARLY READS break it: hart `k` with `r1 po< r2`,
`r2` below `w`, `r1` above, is consistent (load–load reordering) and is
not a violation, so nothing in minimality excludes it; no cut vector
satisfies `restr_ok` at `n = pos w`.  §4b's closure claim holds for the
WITNESS's hart only.  The right object is the CAUSAL HULL: a set closed
under po-predecessors and rf-sources (every such set is a consistent
restriction — load-value's ∃-half by rf-closure, its co-max half only
weakens, atomicity and ppo restrict, deps restrict to in-hull pairs —
with a write-index RENAMING since the hull's writes need not be a prefix
of `gwrites`; `lbl_ren`/`hart_conf_ren` already carry renamings).  The
doubly-closed prefix below `w` is one such hull; the design below needs
arbitrary ones.

**F4 — the graph-side lock kit's GLOBAL pattern hypothesis is false for
xv6's rows, twice over.**  (a) A FAILED `amoswap.w.aq` (the spin reading
1 and writing 1) is a `b`-write that is neither an acquire-reading-zero
nor a zero write, so `lock_pattern` fails on every contended lock.
(b) Pipes are kalloc'd: the byte that is `pi->lock.locked` is later
memset to 1 (kfree) and 5 (kalloc) and zeroed by a fresh `initlock` —
plain writes outside any protocol — so no lifetime-blind per-byte
pattern holds over a whole execution.  The machine-side export is
already lifetime-aware (`wlp_at` is post-registration); the kit's
`cs_kill` arithmetic survives, its HYPOTHESES must be supplied per
configuration by exports, not assumed globally.  `lock_pattern` needs
the failed-swap arm regardless (a nonzero RMW reading nonzero — inside
someone's window, harmless to the order).

**F5 — thin-air THROUGH ADDRESSES is admitted by the declared model but
is not a problem for xv6's sites.**  Rule 9's load half is dropped (D-8),
so a load may sit gmo-before the load that computed its address, and a
self-justifying wild ADDRESS (r → addr r' → data z; z read by j; j's
write read by r) is consistent with `gd_deps` = the store fragment.
Real RVWMO forbids it (rule 9).  But every pointer read in xv6 that
feeds a later load is acquire- or fence-covered or same-hart, and rule 5
/ rule 4 pin the dependent load after the covering event, which kills
the cycle by the ordinary window/fence arithmetic.  So rule-9-load is
NOT required BY THE KILLS (but see F5′: it IS required by the
certification step); it was first recorded as an option (it would make the capstone's
hypothesis strictly closer to RVWMO at the cost of an opcode-carrying
admin label — `LInstr` carries none and announce nodes are silent).
What IS required: the W-TV edges (every read of a store instruction →
the store) must be in `gd_deps` — `dstep` already accumulates `ds_ld`
per instruction and `dedges` does not consume it; the fix is one line
in `dedges`, and it is what keeps walker reads and the walker's A/D
pair from ever being witnesses (they are dep-pinned below the store).

**F5′ — CORRECTION (2026-08-22, late): rule 9's load half IS needed,
by the certification step, not by the kills.**  §4d.2(2) certifies a
`K`-write `z` by a solo run in which a witness read `r₁` (source above
`z`) reads the log instead, and claims `z`'s label is unaffected
because every source of `z` is in `gd_deps`, hence below `z`.  That
claim has a hole exactly the size of D-8: `r₁ →addr r₂ →data z` with
`r₂` a LOAD.  `(r₂, z) ∈ gd_deps` pins `r₂ < z`, but nothing pins
`r₁ < r₂` (no address sources on loads), so `r₁` can be a witness whose
substituted value changes `r₂`'s ADDRESS, hence `r₂`'s value, hence
`z`'s data — the certified message is then NOT `G`'s.  (Control through
a witness is excluded: a branch before `z` is a ctrl edge into `z`, so
its read is below `z`; same-byte later reads of a substituted read
are themselves witnesses by poloc; fences and aq reads are rule-4/5
pinned below `z`.  The load-address chain is the only leak.)  THE
CHEAPEST HONEST FIX is TRANSITIVE PROVENANCE THROUGH LOAD ADDRESSES
in the emission: the load's result register write names its address
sources too — `LRegW rd (DLdRes :: address srcs)` at the instance
(`WeakEvInst`) — and `row_deps`' `dprov` composition then yields
`(r₁, z)` with no opcode data and no PTE/data distinction (rules 9+10
composed are RVWMO-honest, so the assumption side stays ⊆ RVWMO).
Instance-band cost: the `LRegW` emission for loads and whatever
consumes its `srcs` (the D2/D3 view machinery sees one more source —
check `srcs_view` users).  Without it, B2e-3b's "true label" claim is
false and must be restricted to writes with no load-address chain
from a witness — unworkable to classify.  DECISION: build the
provenance extension as a B2e-3b prerequisite.
**LANDED 2026-08-22 (F5′).**  `WeakDeps.deps_addr` is now the single
place a base register is read as an address source; `deps_asrc` masks
its load arm (D-8 UNCHANGED — the `LLoad` label still carries `[]`, the
`read_ok_d` vaddr floor is still untripped) and `deps_rd`'s `ORload` arm
uses it raw, so a load's result write is `LRegW rd (DLdRes :: address
srcs)`.  `dstep` needed NOTHING (its `LRegW` arm already composes
provenance); the smoke tests are `WeakRvwmoConf.row_deps_addr_chain` and
its `_before` twin.  No tier-1 proof moved: every consumer of `LRegW`'s
`srcs` speaks through `DLdRes ∈ srcs` and `srcs_view` monotonicity, so
the extra source only RAISES a dependency view.  An AMO needs no patch
(its address sources are on the `LRmw` label already, so a chain through
its `rd` is pinned by two dep edges and gmo transitivity).

**F6 — the per-site fact the lock kill cannot do without, named.**  Every
CS-to-CS step of a cycle needs `(P)`: "the message a CS read of byte `a`
under lock `L` observes was written INSIDE the writer's CS of the SAME
`L`".  It is not a row-syntactic fact (the byte's protecting lock is a
value), it is not exported today (the lock payload `R` is opaque to the
state interpretation), and the old §4d's `xv6_row_ok` would have had to
carry it as a premise.  It IS cheaply exportable through the φ
mechanism (§4d.3, F3″).

### 4d.2 THE DESIGN — strong induction on |V| over causal hulls, with the
### SCC of a cycle certified by solo runs (route A's E1, done right)

The theorem to build is T2-LIN (F2).  Proof shape, by strong induction on
the number of events:

1. Suppose `G` has a causal cycle; let `K` be the cycle's SCC of
   `(po ∪ rf)⁺` and `P := past(K) ∖ K` (everything causally before `K`,
   not in it).  `P` is a causal hull (F3), a proper sub-graph, consistent
   and conformant (rows are prefixes, `hart_conf_prefix`/`_ren`).  By IH
   it is cycle-free, hence (the extended normalization, §4d.4) it has a
   rows-equivalent rule-14 graph, hence (T2-1c + T1, LANDED) a
   promise-free run `R_P` with final configuration `σ_P` at which EVERY
   export holds and every event of `P` is a real machine step.
   NOTE the non-saturated case needs nothing else: if the cycle's hull
   `past(K)` is itself proper, IH on it says it is cycle-free — it is not
   — contradiction.  So the only case with content is the SATURATED one,
   `V = past(K)`: the cycle is causally last.  (This is why the old
   candidates all looked circular: every informative hull of a saturated
   cycle is the whole graph.)

2. Events of `K` are not realizable as rows (that is what a causal cycle
   means for a promise-free machine).  They are CERTIFIED instead, in gmo
   order, exactly as a promising machine certifies a promise: for a
   `K`-write `z` of hart `x`, run `x` SOLO from its state in the current
   run up to `z`; every read of `x` whose G-source is already in the log
   reads it (true value); a read whose source is above the current
   position reads the log instead (a SUBSTITUTED read — it is exactly a
   violation witness, and `z`'s label does not depend on it: every
   address/data/control source of `z` is in `gd_deps`, hence gmo-below
   `z`).  So `z`'s message is TRUE and appears at a pf-reachable
   configuration; the exports apply to it.  The cost is that a hart whose
   witness was substituted is POISONED from there on: its later labels
   may differ from the row.  Two facts keep the kill from needing
   poisoned labels: (a) a substituted read keeps its TRUE ADDRESS and
   site (address sources precede it; only the value changes), so the
   site record of the witness read itself is grounded; (b) a release's
   base is the acquire's base by the hart's own forwarding (the lock
   pointer is reloaded from the hart's own stack), so the CS structure
   after a substitution is grounded too.  Everything the cycle kill
   reads — entry reads' sites, exit writes' messages, acquires,
   releases — is either in `P`, a first-generation `K`-write, or a site
   fact of a witness.

3. THE KILL is graph arithmetic around the `R`-cycle with the exports
   supplying the per-configuration facts.  The cycle alternates
   cross-hart edges (`rf`, `co`, `fr`) with same-hart runs (`po|→W`,
   `ppo⁻`, `deps`); each same-hart run from its entry event to its exit
   write is one of S6 §3's classes, now stated as gmo-inequalities
   (below for an `rf` entry at a read `r_i`; a `co`/`fr` entry is the
   same arithmetic routed through the shared byte — B2d's K3/K2):
   - PINNED: `r_i < w_i` by rule 5 (`r_i` aq), rule 4 (a fence between),
     or `gdeps_gmo` (addr/data/ctrl into `w_i` — spin loops and
     `holding()` are here, as are W-TV pins);
   - CS-CHAINED: `r_i` is a CS read of `L` (site record) and `w_{i-1}`,
     which it observes, was written in ITS writer's CS of `L` (`(P)`,
     F3″) — then `w_{i-1} < r_i` (rf), `r_i < REL_i` (rule 4, release
     fence), and the ALTERNATION export (F3′) at the certifying
     configuration orders the windows: `REL_{i-1} <co ACQ_i`, while
     `ACQ_i < w_i` (rule 5); so `w_{i-1} < w_i` through the window;
   - BAD: `w_{i-1}`'s message is owned-unpublished when `r_i`'s site
     reads it — `weak_ev_pf_violation_free` refutes the certifying
     configuration directly (this needs `r_i`'s read step in a pf run:
     it is one iff `w_{i-1}` is certified before `r_i`'s hart runs past
     it, which holds iff `w_{i-1}` is gmo-below `r_i`'s hart's next write
     — otherwise the CS-chained arm applies with `(P)`, since the kill
     only needs `w_{i-1}`'s message and `r_i`'s site).
   NOTE (2026-08-22, late): in the CS-CHAINED arm the window order
   between the two sections is ROW DATA whenever the later acquire's
   `ts` entry names the earlier section's release (atomicity +
   `hren`), so for "both segments under the same lock" the kill is
   pure arithmetic with NO export.  The exports enter only to REFUTE
   the other case — the writer's row has no acquire of that lock
   before the write (F3″: the byte is protected, so the writer must
   have held it), or the reader's section is open and the writer's
   acquire would have to read a release the log does not contain
   (F3′).  So B2e-3c's classification is: per cross-hart edge, does the
   writer's row carry the reader's lock?  yes ⇒ arithmetic; no ⇒ F3″
   at the certifying configuration.
   Composing the inequalities around the cycle yields `w_1 < w_2 < … <
   w_1`.  The xv6-level EXHAUSTIVENESS CLAIM is that every segment falls
   in one of the three arms — the per-site classification, now with
   every wild-value concern removed: the classes are read off the
   emission (site records, deps) and the certified configurations.

4. With T2-LIN in hand, the exchange normalization runs with NO kills
   (§4d.4), T2-1c linearizes, T1 realizes, tier-1 adequacy finishes (B3).

### 4d.3 The exports the design consumes (two new, both T2-0's mechanism)

- **F3′ — ALTERNATION (pairing) of the lock word.**  `wlp_at` gives
  shapes only; `cs_kill` needs "only the holder releases".  The lock's
  ghost already knows the holder (`lock_auth γ (Some i)`; the token is
  hart-indexed).  Move the holder into the `WLock` byte state (or carry
  it alongside) so the state interpretation can export the LOG predicate:
  after registration the byte's messages alternate
  `acquire(i) · release(i) · acquire(j) · release(j) · …` with matching
  authors, failed swaps (nonzero over nonzero) interleaved freely.  Two
  leaf touches (`WeakAcquire`/`WeakRelease`), one export lemma.
- **F3″ — PROTECTED-BYTE FOOTPRINT + ACCESS RECORDS.**  At `wlock_alloc`
  the client declares the payload's bytes; they flip to a `WProt γ`
  flavor.  The plain store rule refuses `WProt` bytes; the `WProt` store
  rule takes the holder token and returns it; the `WProt` read rule
  records the access.  Exported: every post-registration message to a
  `WProt γ` byte is by the holder of `γ` at that position, and every
  recorded read of a `WProt γ` byte is by a holder.  This is `(P)` (F6)
  at every pf-reachable configuration, lifetime-aware for free
  (deregistration precedes kfree).  COST (scoped 2026-08-22): NEAR ZERO
  RETROFIT.  The tier-1 capstone takes the kernel EWPs as a HYPOTHESIS
  (the "WP package" of `xv6_srvwmo_safe`), and the weak-logic port of
  the kernel (M4, `projects/weak-memory-porting.md`) has landed only a
  handful of leaves — `WeakLock.v` has no kernel client yet.  So the
  `WProt` store/read rules and the footprint parameter of `wlock_alloc`
  are shaped NOW as the weak logic's lock interface, and the sweep uses
  them from the start; the only cost is the two rules + the export
  lemma + a footprint expression at each `initlock` spec.  Decide the
  interface before the sweep reaches the first lock client.

#### 4d.3′ The exports, concretely (orchestrator spec, 2026-08-22; build
#### as T2-0′ against `WeakGhost.v`/`WeakLock.v`/`WeakEvAdequacy.v`)

Read first: `WeakGhost.v`'s `wcds` states (the `WLock base n0` note and
`wcds_ok_store_lock`), `WeakLock.v`'s `wlock_inv`/`wacquire_core`/
`wrelease_core`, `WpLock.v`'s `lock_state := option (CPU * bool)`.

**F3′ — ALTERNATION.**  A pure fold over the post-registration
messages of the word overlapping byte `a`:
`alt_step (h : option nat) (m : wmsg) : option (option nat)` —
zero data (release-shaped): `h = Some (wm_tid m)` required, result
`None`; exclusive nonzero: if `h = None` then `Some (wm_tid m)`
(a successful acquire) else `h` unchanged (a failed swap; the
message's read value is not in the log, so the fold cannot tell a
failed swap from anything else — and need not).  `wlp_alt log a base n0
h := fold over positions ≥ n0 = Some h`.  The `WLock` state gains the
holder: `WLock base n0 (h : option nat)`, `wcds_lock := clean ∧ wlp_at
∧ wlp_alt … h`.  Two facts make the leaf rules LOCAL: (i) `wlp_alt …
h` ⇒ (the word's current value is zero ⟺ `h = None`) — so the acquire
leaf, which already case-splits on `v = lock_zero`, knows the fold's
state; (ii) `wlock_inv` gains the tie `h = tid_of st` (`Some (fin_to_nat
i)` for `st = Some (i, _)`), so the release leaf, holding `locked γ i`,
knows `h = Some i`.  Both leaves must TIE THE MESSAGE'S AUTHOR TO THE
TOKEN: add `tid = Some (fin_to_nat i)` to `wacquire_core` and
`wrelease_core` (true at every xv6 site — `holding()` — and the only
way the fold's author bookkeeping is sound).  The export
(`weak_ev_adequacy_lockalt`, a sibling of `_lockproto`): `∃ n0 h,
wlp_alt (wglog σ2) a base n0 h` for a registered byte.  What the kill
consumes: with two acquires `A_i <co A_j` by harts `i ≠ j` in the
suffix, a release by `i` sits co-between (else `A_j`'s prefix fold has
holder `Some i` and `A_j` is a failed swap — but a SUCCESSFUL acquire
is one whose READ ENTRY is zero, a ROW fact; relate the two through
(i): the value is zero at `A_j`'s read ⟺ the fold is `None` there).
The graph-side `cs_kill` keeps its arithmetic; its `lock_pattern`/
`lock_paired` hypotheses are replaced by `wlp_alt` at the certifying
configuration plus the row's read entries.

**F3″ — PROTECTED BYTES.**  A fifth state `WProt (γ : gname) (base : Z)
(r0 : nat)`: the byte is in the payload of the lock registered at
`base` with ghost `γ`, protected from log position `r0`.
`wcds_ok log a (WProt γ base r0) := clean ∧ ∀ p ≥ r0, m at p writes a ∧
wm_ak m = WCplain ⇒ wm_tid m = holder_at log base p` where `holder_at`
is F3′'s fold evaluated at `p` (a pure function of the log — no new
ghost).  ENFORCEMENT needs the holder to be provable at a store site
from what the site has, which is `locked γ c`: so `lock_auth` MOVES
from `wlock_inv` into `weak_state_interp` (a `gmap gname lock_state`
auth; `wlock_alloc` allocates the entry; `wlock_inv` keeps `lock_frag`
for the free arm as today), with the state-interp invariant "for every
registered `(γ, base)`: `tid_of (auth γ) = holder_at log base (length
log)`".  Then `wp_store_prot` takes `locked γ c` and returns it; the
update agrees the fragment with the auth and the invariant supplies
`holder_at = Some c`.  A WProt byte REFUSES the plain store rule
(`is_wprot` threaded like `is_wlock`).  `wp_load_prot` is the ordinary
load plus a RECORD: a persistent fact `prot_read γ base a p` ("at log
position `p`, hart `c` read a `WProt γ base` byte `a`") appended to a
monotone ghost list in the state interp — its only purpose is to let
the kill know `a` was protected at `e*`'s read.  Registration:
`wlock_alloc lk R F` with `F : gset Z` (the footprint); the client's `R`
must contain full-fraction points-to's for `F` (flipped `WClean →
WProt` at registration, like `wcds_ok_register`); deregistration
(pipe free) flips back with full fractions in hand.  EXPORTS:
(a) `wprot_at (wglog σ2) a γ base r0` for a byte in `WProt`;
(b) every recorded `prot_read γ base a p` has the byte in `WProt γ
base` at `p` with `r0 ≤ p`.  What the kill consumes (`(P)`): `e*`'s
site is a `prot_read` of `a` under `L`'s `γ` ⇒ `w0`'s message (plain,
to `a`, at `p0 ≥ r0`) was written by `holder_at log base p0` = `j` ⇒
`j` holds `L` at `p0` ⇒ (fold) `ACQ_j` is the last `base`-acquire
before `p0` and no release by `j` lies between — the CS-coverage
hypotheses of `cs_kill`, machine-grounded.

### 4d.4 Staging (replaces the B2e-3 / B1b / B3 items of §4)

- **B2e-3a — T2-LIN's ARITHMETIC CORE (delegate-ready, pure graph
  theory):** (i) `lin_acyclic`: a rule-14 consistent graph has acyclic
  `R` (every `R` edge is a gmo edge), and the edge classes transport
  along `rows_rel`/`wperm`; (ii) every `R`-cycle of a consistent graph
  contains a `po|→W` edge that is a violation; (iii) the
  SEGMENT-COMPOSITION lemma: given per-segment
  inequality certificates of the three arms (as explicit hypotheses in
  `cs_kill` style), the cycle is inconsistent.  Also the two kit repairs
  of F4 (failed-swap arm; `cs_kill`'s hypotheses restated per
  configuration) and the W-TV line in `dedges` (F5).
- **B2d′ — LANDED (2026-08-22) as THE DIRECT LINEARIZATION,
  `iris/WeakRvwmoTopo.v`:** `topo_linearizes` — for ANY linear extension
  `L` of `RacyD` (a permutation of the gmo list respecting every `R`
  edge), `retime G L` (gmo := `L`, rows renamed by the write-rank map
  `tren`) is deps-consistent, rule-14, `rows_rel`/`wperm`-related to
  `G`; `topo_exists` — a finite topological sort from acyclicity (the
  minimal-element descent needs `Decision (RacyD GD x y)`, an instance
  still to be PROVED: every existential in `greads_byte`/`gwrites_byte`/
  `gfence_between` is a bounded row search); `normalize_of_acyclic` —
  exactly `WeakRvwmoNorm.normalize`'s conclusion from acyclicity.  So
  the exchange normalization is RETIRED as the chain's first step: the
  chain is now `T2-LIN ⇒ RacyD acyclic ⇒ topo ⇒ T2-1c ⇒ T1`.  B2a–d
  stay as the landed analysis (their kit and witnesses are what found
  the three entry shapes).  Three statement corrections recorded in the
  file's header: the co-max half has the RMW's own write as a case
  (discharged by `gvisible`'s irreflexivity, since `fr ∖ id`); atomicity
  needs same-byte monotonicity of the rank map in BOTH directions; the
  rank map's identity branch off the write range is what makes `wperm`'s
  injectivity fall out of its own `gwrite_at` clause.
- **B1a′ — LANDED (2026-08-22), `iris/WeakRvwmoHull.v`:** `gx_hull G cs`
  = cut each row at `cs` (po-closure by construction), gmo := the
  FILTERED gmo (a subsequence, no prefix cut), labels renamed by `hren`
  (write rank inside the hull; identity off it); `hull_ok` = lengths +
  RF-CLOSURE.  `hull_consistent`, `hull_rule14` (given violation-freeness
  inside the cut), `gd_hull`/`hull_deps_consistent`, `hull_linearizes`
  (rows = renamed prefixes, log = the hull's messages), `hull_rows_rel`
  (the seam B1b uses: `hart_conf_prefix` then `hart_conf_ren`), full-cut
  identity, and the `erg` instantiation where `restr_ok` fails
  (`erg_hull_beats_restr`).  Factored as cut-then-rename so B1a's label
  layer is reused by conversion; the rename layer is `WeakRvwmoNorm`'s
  plus `WeakRvwmoAcyc`'s transports.  All Closed.
- **T2-0′ — F3′ LANDED (2026-08-22):** `WLock base n0 h` with the fold
  `alt_step`/`wlp_holder_at`/`wlp_alt` in `WeakGhost.v`, the rules
  `wcds_ok_store_lock_{acq,fail,rel}`, the tie `h = tid_of st` in
  `wlock_inv`, the author hypothesis `tid = Some (fin_to_nat i)` on
  both cores (threaded through WeakAcquire/WeakCtxLock/WkOwnPingPong/
  WkYieldFrame/WkCtxSurface), the export
  `weak_ev_adequacy_lockalt` (assumptions identical to `_lockproto`'s),
  and the two kill lemmas `wlp_alt_two_acq` (no `i ≠ j` needed) and
  `wlp_alt_open` (needs "p is i's LAST acquire" — load-bearing).  Note
  `wlp_alt` carries no `base` and requires `n0 ≤ length log`;
  `wlp_alt_value` is stated at the latest writer.
- **T2-0′ — F3″ LANDED (2026-08-22):** the PROTECTED-BYTE FOOTPRINT.
  A fifth C/D/S state `WProt γ base n0 r0 d` in `WeakGhost.v` with
  `wprot_at log a base n0 r0` = "every `WCplain` message at `p ≥ r0`
  writing `a` is authored by `wlp_holder_at log base n0 p`", the rules
  `wcds_ok_register_prot` / `wcds_ok_store_prot` / `wcds_prot_flip` /
  `wcds_ok_deregister_prot`, φ's fifth arm `nv_byte_prot`, the kill
  lemmas `wlp_holder_acq_exists` + `wprot_writer_cs` (the plain writer's
  acquire is identified and no release of the word lies between it and
  the write — `(P)` of §4d.1 F6 in machine-checked form), the read-record
  ghost (`prot_recs`/`prot_read`, class `wprotG`), the seams
  `wprot_regd` / `wprot_rd_regd` and the exports
  `weak_ev_adequacy_prot` / `_protread`.  THREE SHAPE DECISIONS the
  mechanization forced, all recorded in the file's state comment:
  (i) the state carries the DIRTY AUTHOR `d : option CPU` — a protected
  byte is not unconditionally clean, since the holder's own plain stores
  are owned-unpublished until it releases, so φ's conjunct is
  `wcds_ob_ok d` and the store rule takes `d = None ∨ d = Some c`
  exactly as `wcds_ok_store_own` does; (ii) the state carries the lock
  word's registration point `n0` AS WELL AS the byte's `r0`, and the
  footprint's `WProt` fragments therefore live INSIDE the lock's own
  invariant (`WeakLock.wplock_body γ γr lk R n0 F`, with `n0` a
  parameter where `wlock_inv` hides it) — `wprot_at` is a statement
  about the fold at `n0`, nothing relates two independently-quantified
  registration points, so the tie must be a resource fact and only an
  invariant makes a resource fact persistent; (iii) the protected
  RELEASE core pins the message's class at `WCrel` (where
  `wrelease_core` makes do with `≠ WCplain`), because the footprint's
  D→C flip is about PUBLICATION — true at every xv6 site (a plain `sw`
  under the `fence rw,w`'s `w_relp`).  ENFORCEMENT needed no threading:
  the generic plain store rule's `s = WClean ∨ s = WDirty c` premise
  refuses `WProt` outright, and the NON-plain rule is *true* at `WProt`
  (the clause speaks of plain messages only), so `is_wprot` exists as
  the boolean but is threaded nowhere.  OPEN: the Iris-level protected
  store rule is SINGLE-BYTE (`wprot_store` / `WeakLock.wprot_store_core`);
  the width-4/8 lift is the mechanical `wcds_agree_nonplain4/8` repeat.
- **B2e-3b — THE CERTIFICATION MACHINERY (the E1 build, the route's
  largest item):** the gmo-ordered solo certification of an SCC's
  first-generation writes from `σ_P`, with the substituted-read
  bookkeeping and the two groundedness facts of §4d.2(2).  Reuses T1-D's
  `exec_prog_ok'` supply and `hart_conf`'s emission; new is the
  interleaving and the "true label" argument via `row_deps`.
- **B2e-3c — THE PER-SITE CLASSIFICATION (L2′ proper):** every
  hart-segment of a conformant row is PINNED, CS-CHAINED, or BAD, as
  facts about the emission + the certified configuration.  This is the
  kernel-level exhaustiveness claim; its failure mode is a site whose
  xv6 code is genuinely weak-memory-unsafe, and it is repaired by the
  Iris invariant (a fence or a lock), never by a premise.
- **B1b — DESIGNED (2026-08-22, on a read-only probe; the earlier
  "`Rdev` from the labels" idea is WRONG and retracted).**  Facts:
  MMIO loads/stores of a hart are NOT memory events — the instance
  emits the admin label `LDev` for any `dev_addr` access
  (`WeakEvInst.v` ~296/329), so `proj_lbl … LDev = None` and no graph
  row carries a fabric access; `LDev` is admitted in both `adm_star
  true` and `adm_star false`, so any hart's administrative run may
  move the fabric; the disk is a graph agent (its DMA is real
  `LLoad`/`LStore`) whose device steps are likewise admin.
  `pdev_ev_ok` (`WeakEvInst.v` ~1496) says non-`LDev` steps are
  fabric-PRESERVING and fabric-BLIND (`∀ d0, pstep p d0 l p' d0`).  In
  `exec_prog_ok'` the fabric therefore moves only inside the admin
  stars, and a global `dv` for an interleaving of per-hart emissions
  exists iff the per-hart fabric sequences CHAIN across the trace
  (DEV-CHAIN: hart i's k-th post-fabric = the next step's hart's
  pre-fabric).  STAGING: (B1b-1) FABRIC QUIESCENCE — `em_devfree em :=
  LDev ∉ em_labels em`; then every `dvp i` is constant `d0`, `dv :=
  λ _, d0` threads through ANY interleaving, and by fabric-blindness
  the emission replays at whatever fabric the run is at.  Two pure
  lemmas carry it (`hemit_devfree_const`, `hemit_devfree_reindex`,
  both by induction on `hemit` with `pdev_ev_ok`); then the
  interleaving theorem `gdexec_qconf boot GD → hull … → ∃ c pst,
  srvwmo_consistent c ∧ cd_img c = gx_img ∧ pst 0 = boot-list ∧
  exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c)`, plus
  the `pst 0`/`dv 0`/`cd_img` boot equations T1 consumes.  This is an
  HONEST MILESTONE (the tier-2 capstone for device-quiet executions),
  not the final theorem.  (B1b-2) THE FABRIC ORDER AS BUNDLE DATA: the
  conformance bundle gains the global fabric trace and, per row
  event, the fabric positions its block's `LDev` items occupy; the
  induced order on row events (`gd_dev`, ⊆ gmo as an axiom — the M5
  fence discipline is what makes hardware honor it) becomes a sixth
  `R` arm, so `R_acyclic`/`topo_linearizes`/hulls extend as for
  deps, and DEV-CHAIN holds for every linear extension.  The
  single-active-agent relaxation (`ρ i k = k`, `dv := dvp i`) is what
  §4d.2(2)'s solo runs need and comes for free.
- **B1b-2 RESIDUE LANDED (`WeakRvwmoFabInd.v`: O1–O5, `gfexec_conf_hull`,
  the `cycle_kill_F` skeleton, `cycle_kill_of_F`) WITH A FINDING THAT
  REVISES THE DEV-ORDER AXIOM.**  T2-1c's trace is built from rank
  blocks (`grank e` = the gwix of `e`'s next po-write), so cross-hart
  order agrees with gmo ONLY on writes (`glin_gmo_writes`); on the LB
  witness the cross-hart read pair is reversed
  (`lin_cross_hart_gmo_reversed`), and `lbf` (the LB bundle with
  `gf_dev = [(1,1); (0,0)]`) satisfies `gfexec_consistent` yet no
  `tr_dev_ordered` trace comes out of `lin_cand` — `fconf_supply`'s
  last hypothesis is therefore handed back as a guard in
  `hull_realizable_of_acyclic_F`.  THE DEEPER POINT: `gdev_adj ⊆ gmo`
  is NOT the honest axiom.  A dev block's fabric time is its hart's
  PROGRAM-ORDER time (MMIO is issued in order; the `LDev` rides the
  admin run of the next tagged event), not that event's gmo position —
  a dev block hung on an EARLY read can be fabric-late.  There is a
  rule-14 consistent graph with `dev ⊆ gmo` (hart a: `r' (reads z')`,
  `y_a`, `r_a` early; hart b: `r_b`, `z'`; `r_a <dev r_b`) that NO
  trace realizes: `y_a →po r_a →dev r_b →po z' →rf r' →po y_a`.  The
  honest axiom is **`po ∪ rf ∪ gmo|W ∪ dev` ACYCLIC** (exactly "the
  fabric order is realizable by the machine's own ordering"), and the
  build item is **T2-1c′ — the trace-flexible linearization**: any
  trace that is a linear extension of `po ∪ rf ∪ gmo|W (∪ dev)` with
  every read at its `G`-source is `srvwmo_consistent` (reads may sit
  anywhere between their source and their hart's next write; the cand's
  load-value is coherence-based, which is why SB-both-0 linearizes at
  all).  Generalizes `WeakRvwmoLin`'s proof; sizeable.  PARKED behind
  slice 3 / B2e-3c: the device-quiet milestone (B1b-1) does not need it.
- **B1b, B3, R6** as before (B1b now supplies `exec_prog_ok'` for a hull's
  linearization).

### 4d.5 What this retires

`xv6_row_ok` as a capstone conformance clause (its value-dependent half
is F3″'s export; its syntactic half is read off the emission inside
B2e-3c); the three 2026-08-21 candidates as stated (R1 survives as the
certification machinery, R2 as the |V| induction over hulls, R3 only as
"the classes are read off the emission"); `kill_K1/K2/K3` as the
normalization's interface (B2d′ makes them the single cycle
obligation); and the global `lock_pattern`/`lock_paired` hypotheses of
B2e-2 as anything but the arithmetic core's per-configuration inputs.

## 4e. B2e-3b's crux, identified (2026-08-22, late): DEPENDENCY SOUNDNESS

The certification step (§4d.2(2)) claims a solo run emits the `K`-write
`z` with `G`'s label when every read feeding `z` reads its true source.
That is a VALUE-DETERMINISM property of the emission — "the label at
row position `k` is a function of the values of the reads in
`row_deps⁻¹(k)` (transitively) and of the hart's non-memory state" —
which tier 1 never needed: it used the dependency annotations for
ORDERING (views) only, and nothing in the tree states that the Sail
instruction semantics reads exactly the registers the decoded roles
name.  B2e-3b must prove it, per instruction class, as
"two emissions from the same program state that agree on the named
sources agree on the label" (the `LRegW rd srcs` annotation's
soundness; `WeakDeps` is the decoder, `WeakEvInst`/`WeakEvLang` the
instrumented step).  Mechanical but wide (every instruction form in
the image: `tools/gen_code.py`'s whitelist is the inventory).

THE HARD PART IS NOT REGISTERS BUT CSRs AND TRANSLATION.  `WeakDeps`
gives SYSTEM instructions no role (D-4 — RVWMO's syntactic
dependencies are on integer/FP registers, and a CSR is neither), so a
witness value can flow `ld → csrw satp → (sfence.vma) → store` into
the STORE'S TRANSLATION with no `row_deps` edge — and no RVWMO ppo
edge either: CSR-mediated ordering is the privileged spec's
`sfence.vma` discipline, outside RVWMO.  In the declared model the
store may therefore be gmo-early relative to the load that produced
its page table, which real hardware cannot do.  RESOLUTION TO BUILD
(a boundary clause, the W-TV sentence's sibling): the emission records
a `csrw satp`'s source provenance and gives every later memory event
of the hart a dependency edge from it (the translation depends on
`satp`; `sfence.vma` is what makes hardware honor it) — computable in
`dstep` by a per-hart "translation-context provenance" register,
value-independent, still ⊆ what hardware enforces.  With that edge
the soundness statement's "non-memory state" is only the PC path (a
ctrl-dep matter, already in deps) and the CSRs whose sources are
tracked.  xv6 writes `satp` at exactly two sites (`kvminithart`,
`usertrapret`/`trampoline`), from `kernel_pagetable` (static) and
`p->pagetable`.

REFINEMENTS (same day, while the satp slice was being built):
- `satp` is one of several.  `sepc`/`mepc` decide the `sret`/`mret`
  TARGET (a control dependency the decoder drops with SYSTEM, so a
  witness value could choose the user program's resumption PC);
  `sscratch` carries the trapframe pointer through `csrrw`;
  `stvec`/`mtvec` the trap entry.  The honest, uniform rule: EVERY CSR
  that xv6 writes from a GPR gets a pseudo-register with provenance
  (`csrw/csrrw/csrrs/csrrc` = an ALU role writing it from `rs1`,
  `csrr` = an ALU role reading it), `sret`/`mret` = a `jalr`-like role
  on `sepc`/`mepc` (so their sources join `ds_ctl`), and `satp`'s
  provenance joins every store's sources (the translation context).
  Then the soundness lemma's "non-memory state" is exactly GPRs + the
  named CSRs, all provenance-tracked, and no per-site "this CSR is
  written from constants" side argument is needed.
- STATE THE SOUNDNESS LEMMA PER INSTRUCTION, not per row position: two
  emissions that agree on the named sources of instruction `n` (GPRs/
  CSRs it reads, and the VALUES of its own memory reads — the walker's
  PTE reads included, which is why W-TV's `ds_ld` is in the provenance)
  emit the same memory-event sequence for instruction `n`.  Event
  positions need not align across emissions (a walk's A/D exclusive
  pair appears or not depending on PTE contents), so the certified
  write is identified by INSTRUCTION index, and the kill reads its
  message, never its row position.
- A solo run is a genuine pf run of the verified program (the other
  harts idle), so it cannot fault where the verified kernel cannot:
  "the substituted value does not derail the run before `z`" is the
  EWPs' content, not a new obligation — PROVIDED the control path to
  `z` agrees, which is the ctrl-provenance clause (branches, `jalr`,
  and now `sret`/`mret`).
THE SOUNDNESS LEMMA'S TWO SHAPES (decide before slice 2).  The program
state is `PHart cpu m rs fn ib` — `m` the Sail continuation, `rs` the
FULL `regstate` (GPRs and CSRs alike) — and the Sail interaction monad
answers every register read through a `RegRead` node and every memory
read through the label.  So the GENERIC fact is free: two runs of the
same continuation from regstates that agree on every register the run
actually `RegRead`s, given equal memory-read answers, are identical.
What provenance soundness then needs is only "the registers the
instruction actually reads are covered by the sources the emission
names", and there are two ways to get it:
  (i) DECODED ROLES (today): prove per instruction class that
  `deps_of_bits`' sources ∪ the constant CSRs cover the `RegRead` set —
  an inventory-sized proof over the Sail code of every form the image
  contains (≈60 forms; the `tools/gen_code.py` whitelist is the list),
  with the CSR read sets per class (memory ops read `satp`/`sstatus`
  bits, `sret` reads `sepc`/`sstatus`, …).
  (ii) DYNAMIC PROVENANCE: compute `LRegW rd srcs` from the registers
  the instruction ACTUALLY read since its `LInstr` (captured from the
  monad's `RegRead` nodes by the instance), not from the decoder — then
  coverage holds by construction and the soundness lemma is the
  generic one.  Honesty: dynamic sources ⊇ RVWMO's syntactic ones and
  include CSRs the instruction consulted (`sstatus` for a permission
  check); an edge from such a CSR exists only when the CSR's own
  provenance is non-empty, i.e. it was written from a value with read
  provenance — a chain real hardware also orders (CSR writes
  serialize).  Cost: the instance's `LRegW` emission and whatever the
  machine's view machinery does with extra sources (views only rise).
  (ii) is cleaner and sound-by-construction; (i) keeps the machine
  untouched.  Lean (ii) unless the instance's `RegRead` capture is
  awkward; probe that first.
DECIDED (2026-08-22, on the read-only probe): **(ii) DYNAMIC
PROVENANCE.**  Evidence: `RegRead` is answered silently from `rs`
(`WeakEvLang.v` ~687, `WeakEvInst.v` ~284) with no accumulator, and the
one natural home for a per-instruction read set is the announced-bits
channel `oib32 := option (mword 32)` widened to carry `list wreg`,
reset at the two instruction boundaries (`Ret tt` and
`InstrAnnounce`); `erw_of`'s SOURCE component is the only consumer to
change (the DESTINATION stays decoded — D-4's "which node is `rd`"
join); the machine only joins `srcs` into views (`srcs_view`,
`regw_post`, `ctrl_post`) and its sole side condition
`srcs_view_bounded` is `∀ l`; `dstep`/`dedges` are generic; nothing
outside `WeakEvLang`/`WeakEvInst` ties `srcs` to `deps_of_bits` (the
`vm_compute` witnesses are `Example`s to re-record).  The generic
determinism spine exists: `WeakEvLift.esil_node_agree` /
`erun_silent_sound` (silent nodes) and `WpDecodeBridge.exec_goodb_congr`
(decode); the soundness lemma adds "equal memory-read answers".
Option (i) would be ≈20 base forms × (execute + fetch + walk + CSR)
Sail inventories with no memory-arm congruence to lean on.  FIRST
PROBE (the build's step 0): widen `oib32`, make the `RegRead` arm
record `r` and the boundaries reset, and check `pcls_ev_erasable` and
`esil_node_agree`/`erun_silent_sound` still go through; ~64 `wgib`
sites are the mechanical blast radius.
SLICES 2b/3, STATED (2026-08-22, post-DEC-7).  THE CERTIFICATION
INVARIANT, per hart `x`: a certified program state `p_x` (in the
certified run) and the G-emission state `q_x` (`hemit_states` at the
same row position), a TAINT set `T_x ⊆ wreg`, with `dreg_agree
(complement T_x) p_x q_x`, and `T_x` = the dynamic-provenance closure
of the substituted reads so far.  Because DEC-7 makes `row_deps` the
SAME dataflow the taint follows (the `LRegW` sources ARE the
instruction's carrier read set), "`z`'s instruction reads no tainted
carrier" ⟺ "no `row_deps` path from a substituted read to `z`" —
and every read with a path to `z` is `gd_deps`-below `z`, hence not a
witness.  So the per-instruction lemma (2b) is: iterate
`pnode_step_dagree` through one instruction's nodes from `p_x`/`q_x`
agreeing off `T_x`, with equal memory-read answers at its memory
nodes (PTE reads included), to conclude equal emitted labels and
equal destination writes; a memory read whose answers DIFFER (a
witness) instead adds its destination to `T_x` (`pnode_step_channel`
/`erun_ib_rds` give the read set; the destination is the decoder's).
Slice 3 then runs the gmo-ordered induction over `K`'s writes
maintaining the invariant, with the fabric at `d0` (B1b-1's
quiescence) and the log = `P`'s messages ++ the certified ones.  The
"substituted read" is any read whose G-source is not yet in the log
— its value is the log's current message (the machine's latest,
always admissible); its hart's later same-byte reads are witnesses
too (poloc), and its taint reaches exactly the registers the dynamic
flow says.
SLICE 3's SHAPE AND ITS ONE OPEN RISK (2026-08-23, before building).
Certify only what the cycle kill reads: around the `R`-cycle, start at
a BACKWARD step `(r₁, z₁)` (`z₁ < r₁`, `r₁` the witness — every cycle
has one, `caus_cycle_gviol`/F2) and certify the exit writes in CYCLE
order: `x₁` runs through `z₁` with `r₁` substituted; then `x₂` runs
through `z₂` with `r₂` reading `z₁` truly (in the log); … up to `z_k`.
Nothing po-between a witness `r` and its `z` can depend on `r` (such a
dependent write `y` would have `r < y` by deps, so `y` is not below
`z` … and if `y` is an acquire, rule 5 puts it below `z` and so below
`r`, contradiction) — so the segments' lock operations are untainted
and `instr_dagree` applies to every instruction of each segment.  A
hart's events AFTER its substituted witness are poisoned and are not
certified; the kill never needs them.  THE OBJECT is a CAND extended
by solo blocks: from a realized `c_P` (`hull_realizable_of_acyclic`)
append, per instruction, the hart's block at the current log — a read
whose G-source is in the log reads it, otherwise the latest message —
keeping `exec_prog_ok'` (the per-block `adm_run`/`pstep_ev` shape is
`hemit`'s, re-indexed to the trace) and `srvwmo_consistent`.

THE OPEN RISK: the certified run's `co` need not be `G`'s `co` for
pairs the cycle entangles (a write `v` causally after `z` but `co`
-before `x`'s own earlier write `y`), and a read-pinned disagreement
would mean the certified run is a legitimate execution that is NOT
`G`'s — its export facts then do not transfer to `G`'s lock-byte
order.  Expected resolution: the cycle kill needs `co` only on lock
bytes and only between the segments' own acquires/releases, which the
cycle order itself pins (F2′: read-pinned pairs are preserved);
confirm this when stating the kill arms (B2e-3c), and if a
counter-shape appears, certify in a `co`-respecting order instead of
cycle order (the two agree on pinned pairs).

SUB-SLICES: (3a) `cand_extend_block` — append one hart's next
instruction block to a realized cand at the current log, reads taking
the latest message (always admissible) or a named in-log source
(admissible under the cand-side coherence rule — check
`WeakAxiomatic`'s load-value/`ax_*` for reading an older message),
preserving `exec_prog_ok'` and `srvwmo_consistent`; (3b) the segment
certification (iterate 3a with `instr_dagree`/`taint_closure_load`
from the `hemit_states` of `G`'s emission), concluding the exit
write's label; (3c) the cycle-order iteration.
Order of work for B2e-3b, revised: (1) the satp-provenance edge in the
emission (`dstep` + the instance's CSR write annotation); (2) the
soundness lemma, stated once over `pstep_ev` ("agreement on named
sources ⇒ agreement on the emitted label and on the named
destinations"), proved by the instruction inventory; (3) only then the
solo-run certification of §4d.2(2).  Do (1) and (2) as their own
slices; each is delegate-sized once the statement is fixed.

**LANDED (1), 2026-08-22:** `satp` is the pseudo-register `SATP = 32`
(`WeakDeps.SATP`/`wsatp`; `wreg` is `nat` and every consumer is a
`gmap` with a default, so no bound is tripped) — decoder DEC-5 gives
`csrrw/csrrs/csrrc(+i)` on csr `0x180` a role (`csrw satp,rs1`
↦ `ORalu SATP [rs1]`, `csrr rd,satp` ↦ `ORalu rd [SATP]`; every other
CSR and SYSTEM form stays `ORnone`, D-4 intact), `WeakEvLang.ereg_num`
routes the model's `RegWrite satp` node to it, and
`WeakRvwmoConf.dedges` adds `dprov s wsatp` to every store's/RMW's
sources (scope note S-a''; `dstep_within` took one extra `elem_of_app`
case, nothing else moved).  Witnesses: `row_deps_satp_chain` +
`_before` twin + `row_deps_satp_read` (transfer AND the overwrite that
unlinks a stale context).  Tree green; both capstones at the five
rv64d axioms.

**LANDED (1) EXTENDED TO EVERY CSR, 2026-08-22 (DEC-6):**
`WeakDeps.csr_reg` is now a TABLE — the 21 CSRs xv6 touches ↦ the
pseudo-registers `32..52`, `satp` still `32`, with `sstatus`/`mstatus`,
`sie`/`mie` and `sip`/`mip` SHARING a key (they are one physical
register, and the Sail model has only the M-mode one) — `deps_of_csr`
gives every Zicsr form a role, the new constructor `ORcsr p srcs rd`
plus the second projection `deps_rd2` give a `csrrw/csrrs/csrrc(+i)`
with `rd ≠ x0` BOTH destinations honestly (the image has one:
`csrrci a5,sstatus,2`), and `sret`/`mret` take the jalr-like role
`ORjalr 0 SEPC`/`MEPC` so the resumption PC's provenance reaches
`ds_ctl` through the existing `LCtrl` path.  `WeakEvLang.ereg_csr_num`
is the Sail-side half (including the `pmpaddr_n`/`pmpcfg_n` vector
registers and 32-bit `mcounteren`); `erw_of` tries `deps_rd` then
`deps_rd2`.  `WeakRvwmoConf.dedges` is UNCHANGED — `satp` is still the
only CSR that feeds translation (scope note S-a''').  RESIDUAL: trap
ENTRY takes no `stvec`/`mtvec` edge — the only control hook is
`erw_of`'s `nextPC` arm, driven by the CURRENT instruction's decoded
role, and nothing there distinguishes a trap redirect from the
instruction's own; xv6 writes both CSRs from constants, so no witness
value reaches them.  Witnesses: `row_deps_sret_chain` + `_before` twin
+ `row_deps_csr_readback`, and per-form decoder/`erw_of` tests for all
24 GPR-write sites' CSRs, the pure reads, the immediate forms and the
two returns.  Tree green; both capstones at the five rv64d axioms.

**LANDED — SLICE 2a, DYNAMIC REGISTER PROVENANCE, 2026-08-22 (DEC-7):**
the per-instruction channel is now a record, `WeakLang.ibch = { ib_bits :
option (mword 32); ib_rds : list wreg }` (`oib32` is a notation for it), with
`ib_none` / `ib_ann w` at the two boundaries and `ib_read i (ereg_num r)` at
every `RegRead`; `WeakEvLang.ib_rd` is the instance-side spelling.  The
language's `RegRead` arm is no longer σ-silent — it writes `ewg_ib σ c
(ib_rd (wgib σ c) r)` — which cost `WeakEvLift.esil_sigma` a FOURTH shape
(`∃ v, σ' = ewg_ib σ c v`, invisible to `weak_state_interp` by conversion,
so `weak_state_interp_ib` closes it), one extra bullet in
`ewp_ev_sil_node`/its `WeakEvFunnel` twin, one extra `esil_case`-exempt arm
in `ecycle_step_factor` (new lemma `elab_apply_ib`), and a
`rewrite weak_state_interp_ib` in `WeakEvWire`'s two `RegRead` WP rules.
`erw_of` takes the read set as a second argument and builds the SOURCE list
as `erw_srcs dec rds = (if has_ldres dec then [DLdRes] else []) ++
(DReg <$> remove_dups rds)`; the decoder keeps the DESTINATION (DEC-4's
join), the `DLdRes` flag, and — crucially — the CONTROL GATE: `deps_ctrl
role = []` still means "not a control node", because handing every
instruction's read set to `ERWctrl` would make each instruction a
control-dependency point, far beyond RVWMO and beyond hardware.  All 29
`erw_of_*` witnesses are re-recorded with the decoded registers as the read
set and return the DECODED answers unchanged; five new ones record the
strict superset (`ld` whose run read `satp`/`sstatus`), the dedup, the
control gate and the branch.  `WeakRvwmoConf`'s `row_deps_*` rows are
hand-written label lists and did NOT move.  THE SOUNDNESS LEMMAS are the
new file `iris/WeakEvProv.v`: `dreg_agree S rs1 rs2` ("agree on every
non-carrier register and on every carrier named in `S`"),
`pnode_step_regread_agree` (the per-step sentence),
`pnode_step_dagree`/`pstep_hart_dagree`/`pstep_ev_dagree` (the whole node
dispatch, PLIC wire included), `esil_node_dagree` +
`erun_silent_dagree` (the silent-run induction on
`WeakEvLift.erun_silent`'s spine, at the WEAKER hypothesis — agreement on
what the stretch READ, not on the owned frame `D`), and the coverage bridge
`pnode_step_channel` / `ibn_step_rds` / `erun_ib_rds` ("away from an
instruction boundary the channel accumulates exactly the stretch's carrier
reads") with the corollary `erun_silent_dagree_channel`.  ALL `Qed`; the
per-INSTRUCTION statement (memory answers included) is NOT stated — its
four obligations (P-a..P-d) are enumerated in the file's header, and three
of them are already discharged; the fourth needs slice 3's certification
statement to exist.  Tree green; both capstones and `gdexec_conf_deps_wf`
at the five rv64d axioms.

## 5. Honest residual risks — OPEN

- **THE K2-KILL'S PRECISE MECHANISM (flagged 2026-08-21):** K2's
  stale read is of a PREVIOUS message of the byte — which may be
  published and φ-innocent (φ's `violation_hart` speaks of
  owned-UNPUBLISHED messages; a stale read of an old published value
  is not by itself a violation).  The kill's real content is the
  MP-shape analysis: either the writer fence exists (rule-4 graph
  arithmetic kills the violation), or the byte pair (stale byte,
  the flag/lock byte whose fresh read pins `z` above `w`) falls to
  the lock-protocol/CS-coverage cases — i.e. K2's φ/lock discharge
  needs the SAME per-site classification as S6's kernel claim, routed
  through
  which byte `z`'s stale entry actually is.  This is B2e's core
  design question; do not assume the K2 kill is a one-liner.

To be priced during B1/B2 design: (i) the prefix variant of T2-1c (the
full theorem assumes grule14 of the WHOLE graph; the prefix form needs
"grule14 below the frontier" only — expected clean, the construction is
per-segment); (ii) case 2's absorption argument (cross-hart same-byte
co swaps); (iii) the exhaustiveness of the kernel-level read classes
(S6 §3's kernel claim) when expressed at the frontier — this is L2′'s
old obligation in new clothes and remains the route's largest single
item.

## 6. Model correction at the witness slice (2026-08-21)

**`cs_kill` as first landed was VACUOUS, and the model was the
reason** — the non-vacuity witness discipline caught it one slice
after the flag: `gacq_po` (ppo⁻ rule 5) left its SUCCESSOR
unconstrained, and `gwf`'s membership clause then made any
fence-po-after-an-acquire graph inconsistent — `cs_kill`'s coverage
hypotheses were jointly unsatisfiable for EVERY graph.  The fix is
riscv.cat's own typing, `ppo ⊆ M × M`: `gacq_po` gains `gmem G e2`
(the only leaky arm — the other three pin both endpoints via their
classifiers), `gppo_gmem` is now the exported theorem, and the change
WEAKENS `rvwmo_minus_consistent` (more graphs consistent — the safe
direction for the safety theorem).  Every landed leaf repaired
mechanically (five sites); `WeakRvwmoLockWit.v` carries the
satisfiability witness `cs_kill_hyps_sat` (a real two-hart
acquire/release graph, windows genuinely ordered, rule-14 clean so
the kill is silent rather than firing).  THE GENERAL RULE, added to
the durable pattern family: for every arm of a ⊆-axiom into a
data-carried order, check BOTH endpoints are in the order's domain —
a one-endpoint arm is a silent strengthening that becomes outright
unsatisfiability when the order carries a membership clause.
FLAGGED, NOT FIXED: `WeakAxiomatic.acq_po` has the identical
unconstrained-successor shape on the cand side — harmless today
(`ax_ord`/`ax_rel_ord` consume it only at reads), narrow it the next
time that file is touched (R6-adjacent debt).

## 7. Probes of the 2026-08-22 design session (machine-checked witnesses)

Each finding of §4d.1 with a checkable claim got a witness file; the
outcomes are recorded here as they land (an honest "did not go as
described" is the more valuable outcome):

- **P5 / F2** — `WeakRvwmoAcyc.v` (LANDED, Closed): `R_acyclic`/
  `RD_acyclic` (rule-14 consistent ⇒ `R ⊆ gmo`, acyclic), `gcaus_acyclic`
  (po ∪ rf), `caus_cycle_gviol` (every causal cycle of a consistent
  graph carries a violation), transport of `Rt` and `gcaus` along
  `rows_rel`/`wperm` (`Rt_acyclic_orbit`, `gcaus_acyclic_orbit`); `co`/
  `fr` transport only under a monotone π (`gco_rows_rel_mono`) — the
  negative result that produced F2′.
- **P4 / F1** — `WeakRvwmoProbeK1.v` (LANDED, Closed): `mpgd_kill_K1_false`
  and `mpg_normalizes : ∃ GD', gd_equiv mpgd GD' ∧ grule14 (gd_g GD')` —
  `kill_K1` demands refuting a graph that provably normalizes.
- **P2 / F3** — `WeakRvwmoProbeRestr.v` (LANDED, Closed): `erg_no_restr :
  ∀ cs, ¬ restr_ok erg 1` with `erg_w_min_viol` — unconditional: the tie
  itself is unsatisfiable, not a bad choice of cut.
- **P1 / F4(a)** — `WeakRvwmoProbeSwap.v` (LANDED, Closed):
  `swg_consistent`, `swg_no_pattern`, and `swg_paired` (pairing survives;
  only the pattern breaks).  Also noted there: `acq_src_rel` ("a nonzero
  read index names a release") is false once failed swaps exist.
- **F5, F6** are code-reading findings (`dedges` ignores `ds_ld`; no
  operand data in labels or admin items; `R` opaque to the state
  interpretation) — no witness needed.
