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
NOT required; it is recorded as an option (it would make the capstone's
hypothesis strictly closer to RVWMO at the cost of an opcode-carrying
admin label — `LInstr` carries none and announce nodes are silent).
What IS required: the W-TV edges (every read of a store instruction →
the store) must be in `gd_deps` — `dstep` already accumulates `ds_ld`
per instruction and `dedges` does not consume it; the fix is one line
in `dedges`, and it is what keeps walker reads and the walker's A/D
pair from ever being witnesses (they are dep-pinned below the store).

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
- **B2d′ — THE KILL-FREE NORMALIZATION, two options; RECOMMENDED: the
  direct linearization.**  (a) DIRECT: by F2(ii), ANY topological order
  of `R` is a rows-equivalent consistent rule-14 gmo (rows renamed by
  the write-index permutation, exactly `normalize`'s `rows_rel`/`wperm`
  conclusion).  This is a finite-graph topological sort over `gevs'`
  plus the consistency check of F2(ii) — smaller than the exchange
  kit and with NO kill interface at all; `normalize`'s statement is
  then a corollary of T2-LIN.  (b) KIT: extend `normalize` with the
  source-descent move (F1) so the only residual is "an `R`-cycle
  through `w`".  Build (a); keep B2d/B2a–c as the landed analysis that
  found the three entry shapes (their non-vacuity witnesses remain the
  kill interface's sanity checks).  Probe (a)'s consistency claim
  first (F2(ii) is an argument, not yet a theorem): the load-value
  co-max half under a topological order is the one clause to check.
  With F2′: `R` is taken with `G`'s own `co`; when `R_{co}` has a cycle
  through an unread same-byte pair, flip that pair (a legal (W,W)
  move) and retry — only read-pinned cycles reach the kill.
- **B1a′ — CAUSAL HULLS:** generalize `gx_restrict`/`restr_ok` from
  prefixes to arbitrary po-/rf-closed sets with the write-index renaming
  (F3); `restrict_linearizes` restated for hulls.
- **T2-0′ — the two exports (F3′, F3″)** — scope F3″ first.
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
