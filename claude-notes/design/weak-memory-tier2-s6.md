# S6 — the tier-2 gate: the two-hart L2′ paper exercise (2026-08-20)

**VERDICT: GO**, on the certification route (layer2 §8), with:
- **one new export required** (F3: the lock-word value protocol as a
  state-interp ghost — the φ mechanism applied to `wlockN`'s content);
- **one new definitional layer required by BOTH routes** (F1/F2: the
  graph-presentation front-end for a declared RVWMO⁻ — the `cand`
  presentation provably cannot express the behaviors tier 2 is about);
- the §5 Ψ items `w_rdw`/`w_lock` **not needed** (their duties are covered
  by the landed machine dependencies, W-TV, and the L2-M1 lemmas);
- the direct graph-linearization route (B) recorded as the fallback.

This document is the exercise the sRVWMO design §4 mandated before any D8
porting: the two-hart, one-lock, one-racy-byte, one-PTW-read miniature,
with every cross edge of every potential rule-14-violating cycle killed
from {machine facts, φ, the exported lock protocol} alone — no premise
about the kernel anywhere.  Where a kill leans on something not yet built,
the build item is named.

## 0. What tier 2 owes, restated with tier-1's assets

Tier 1 (`xv6_srvwmo_safe` + `t2_ev`) proved sRVWMO ≡ pf.  Tier 2 owes ONE
lemma — **(RVWMO-GAP)**: every RVWMO⁻-consistent, xv6-conformant execution
over the boot image has a same-log sRVWMO-consistent execution — after
which the tier-2 capstone is tier-1's composition file with
`srvwmo_consistent` weakened, nothing else moving.  "Same log" is the
right equivalence: T1/T2 are log-indexed, and it is what makes the
historical harmless-cycle problem (the walker twin: same behavior,
different events) survivable.

## 1. F1/F2 — the declared model needs a NEW presentation, and it should
##    be RVWMO⁻

**F1 (machine-checked already, by A5).**  The `cand` presentation
identifies gmo with trace order, so a store can never be early in it:
`lb_values_forbidden` shows the LOAD-VALUE axiom alone refutes LB there.
The behaviors tier 2 must contain are therefore INEXPRESSIBLE in `cand` —
the declared RVWMO⁻ needs a herd-style presentation (events; po, rf, gmo
as separate data; consistency as axioms over them), plus the two
translation lemmas: an rvwmo⁻-graph with rule 14 LINEARIZES to a `cand`
(this IS the normalization content), and a `cand` reads back as a graph.
Both routes (§5) consume this front-end; it is pure definitional/graph
work in the A1c style.

**F2 (the model choice).**  Declare **RVWMO⁻ = RVWMO minus ppo rules 6 and
9–13** (keep 1–5, 7, and atomicity for the fused RMW; no rule 14).
Dropping ppo rules only ADDS behaviors, so `xv6_rvwmo⁻_safe` implies
xv6-safe-on-RVWMO — the theorem gets STRONGER, and the D-8 obstacle to
declaring full RVWMO (rules 9–11 need syntactic dependencies, which the
axiomatic alphabet deliberately lacks) dissolves: RVWMO⁻ needs no
dependency data.  Rule 6's omission also keeps the recorded machine
residue honest.  RVWMO⁻ is litmus-testable per core exactly as sRVWMO is
(it is sRVWMO's own axiom set minus the rule-14 arm and the two
promise-free strengthenings).

## 2. The miniature

Lock word `L` (RMW-only in program text: acquire = `amoswap.w.aq` spin —
reads `L`, branches on the result, writes 1; release = `fence rw,w`;
plain store `L:=0`, which the machine classes `WCrel` via `w_relp`).
Protected byte `x` (accessed only between acquire and release).  Racy
byte `s` (a `started`-style flag: writer `i` stores init data `d`, then
`fence rw,w`, then `s:=1`; reader `j` spins `while (s==0)`).  Hart `j`'s
CS access to `x` translates: the walker reads a PTE `p` (a plain load,
D-8), possibly performing the A/D exclusive pair on `p`.

  hart i:  d:=v0 ; fence rw,w ; s:=1 ;
           ACQ(L) ; x:=v ; REL(L)
  hart j:  spin: r0 := s ; beqz r0, spin ;
           ACQ(L) ; [walk: r_p := PTE ; (exload p ; exstore p)?] ;
           r1 := x ; REL(L) ; y := f(r1)   (a later store)

The full machine's extra behaviors are promises (early stores).  A
rule-14-violating cycle needs, per hart segment `[h..f]` (entered by a
cross rf edge at read `h`, exited at fulfil `f`), the S1 failure
`µ_entry ≥ ts(f)`.  The exercise: enumerate every cross edge the
miniature can put at a segment head and name its kill.

## 3. The edge inventory

Notation: kills marked **M** are machine facts (hold of every trace by
the step relation — nothing to export); **X** are exports at pf-reachable
states (φ or the lock protocol), applied through the GROUNDING move
(layer2 §8: extend the pf-real ancestry with the promiser's certifying
run — a pf run by `cert_step_rtc_wpstep` — so the questionable read IS a
read of a pf-reachable configuration and the export applies).

| # | entry `h` (reader j) | message read (author i) | kill | status |
|---|---------------------|--------------------------|------|--------|
| 1 | acquire RMW on `L` | release `L:=0` (WCrel) or init | **C2/M**: aq raises `vrNew`; every later fulfil's EXT ≥ read ts (`S1_of_aq`) | L2-M1 landed |
| 2 | spin read of `s` | `s:=1` (WCplain, published by nothing yet) | **C3/M**: the branch is control (`LCtrl`, D3); every later store's EXT covers via `fcov_of_dep_chain`.  The message CAN be read early — harmless: the segment's S1 holds regardless | L2-M1 landed |
| 3 | read of `d` after seeing `s=1` | `d:=v0` (WCplain) | **C4/M**: `fence rw,w` between `d` and `s` gives `ts_d < ts_s` machine-side (EXT of `s`'s fulfil); the release-chain lemmas (`covered_of_release_chain`) carry the coverage to j's segment | L2-M1 landed |
| 4 | read of `x` inside CS, message UNPUBLISHED (i has not released) | `x:=v` (WCplain, `SCowned`, ¬pub) | **bad → X(φ)**: ground via the certifying extension; the extended pf configuration has a foreign `obs_flr` over an owned-unpublished message = `violation_hart` — impossible by `weak_ev_pf_violation_free`.  §8.4's discipline applies: refute the `gdep3`-MINIMAL bad edge (provably off every cycle, `bad_min_not_on_cyc`), hence no bad edge at all (`scc_no_bad_of_phi`) | mechanized skeleton landed (L2-M2); the E1 glue (cone replay + solo runs) is the build item |
| 5 | read of `x` inside CS, message PUBLISHED (proper handoff) | `x:=v` then i released | **C4/X(lock protocol)**: `cs_read_covered_window` gives S1 from the two CS windows and `win_excl`; `win_excl` = the CS windows are gmo-exclusive, which needs `excl_ok` (M: the RMW reads latest) PLUS the VALUE protocol (acquires read 0/write 1, releases write 0, so an acquire's read names its co-predecessor release) — the ONE exported fact | L2-M1's lemma landed; the EXPORT is the build item (F3) |
| 6 | `holding()`-style plain read of `L` | any | **C3/M**: the value feeds a branch (`if(holding) panic`) — D3 control dependency | landed |
| 7 | walker's plain PTE read | another hart's PTE write (under lock: WCplain-in-CS → cases 4/5) or another walker's A/D exstore (WCexcl = `SCexcl`, never bad) | **W-TV/M**: the walker read banks `w_tbank`, consumed into `w_vcap` at the translated access; every po-later STORE's fulfil EXT covers the walker read's ts (`fcov_of_vcap`, "the free consumer") | W-TV landed (production); the consumption slice is an owed build item (R-track) |
| 8 | walker's A/D exload | another walker's A/D exstore | **W-TV/M** as #7 (the exclusive read banks too), plus the pair's own `rv_view` domination at its exstore | same as #7 |
| 9 | j's segment EXITS at the walker's A/D exstore | — | its fulfil EXT dominates `rv_view` (the exload's banked post-view), and §13's decision makes the walker RMW non-promisable (Sail fidelity), so it is never itself the early store | W1/W2 (naming walker traffic) owed |

**Exhaustiveness check for the miniature**: every read in the programs is
one of #1–#8; every store is plain-in-CS (killable at the READER per
#4/#5), the release (WCrel — publishes, never bad, and `fence rw,w` gives
C1 at its own segment), `s:=1` (fence-covered, C1), `y:=f(r1)` (data
dependency on `r1` — D2's `vsrc`, C3), or the walker pair (#9).  No edge
lands in C6.  ∎

**The kernel-level exhaustiveness claim** (the L2′ obligation proper):
every racy read in xv6 is (a) an aq RMW, (b) branched on (spin loops,
`holding`, `killed`, `started`, the disk's `used` index — all
control-feed), (c) data-fed into later stores (D2), (d) CS-covered, or
(e) reads a message that is bad (φ) / a lock word (protocol) / a device
ring slot (the M5 fence discipline).  This is checked MECHANICALLY per
site when L2′ runs — and a site that fails either repairs by
strengthening an Iris invariant (the allowed move) or is a genuine kernel
bug.  The miniature covers every CLASS the kernel-defects and racy-site
notes list; no class is outside C1–C5.

## 4. F3 — the one new export, and its mechanism

Case #5 needs, at pf-reachable configurations, the lock-word VALUE
protocol: writes to `L` alternate acquire-RMW (reads 0, writes ≠0,
WCexcl) / release (writes 0, WCrel), so `excl_ok` totally orders the CS
windows (`win_excl`).  This is NOT machine-derivable (nothing stops a
program from plain-storing 5 to `L`; xv6 just doesn't), and it is NOT
adequacy-visible today: `wlock_inv` is a NAMESPACE invariant, and the
export seam only sees `weak_state_interp`.  The mechanism is φ's own
(§5(β)): a ghost map `lockwords : gmap Z lock_protocol_state` resident in
`weak_state_interp`, updated ONLY by the acquire/release leaves (which
already open `wlock_inv` — the ghost update rides the same fancy update),
with the pure per-state projection exported at every step like
`no_violation` is.  Cost profile: one ghost, two leaf-proof touches
(`WeakAcquire`/`WeakRelease`), one export lemma — the φ precedent makes
this a well-understood, bounded piece.  `w_rdw`/`w_lock` (§5's other Ψ
items) are NOT needed: their duties in the case tree are carried by D2/D3
and W-TV (M) and by the C4 lemmas.

## 5. Route decision: A (certification), B (graph linearization) as fallback

Both routes share the F1 front-end and the F3 export.  They differ in the
middle:

- **Route A** (layer2 §8, the plan of record): declare RVWMO⁻ on graphs;
  port `axiomatic_to_promising` (promise everything up front — our
  `WPPromise` shape; M6's W4 characterization is the banked half) to get
  RVWMO⁻-graph → full-machine behavior; then the CERTIFIED containment
  (D8-2/D8-3 + E1 + L2′) discharges `main_premises` and `Hfused` in the
  ALREADY-LANDED `xv6_ev_weak_robust`, giving full ⊆ pf; tier-1 adequacy
  finishes.  ~90 % of the containment tower is banked (M6, A0″, L2-M1/M2,
  D8-1, the PARM recon with `RES = ts` provably unused).
- **Route B**: prove RVWMO-GAP directly as a graph linearization — an
  exchange-lemma induction ordering stores back to rule-14 position,
  maintaining "the normalized prefix is pf-realizable (T1)" so the
  exports constrain each exchange's obstruction analysis (same C1–C5
  tree, on graphs).  No simulation port, no `sim_dev`; but nothing of the
  induction exists, and the exchange lemma's commutation cases are the
  M6 W2 permutation arguments in new clothes.

**Decision: A.**  The deciding facts: the banked tower; §8.4's SCC
subtlety already has its mechanized resolution (`scc_no_bad_of_phi`);
and A's residual risks are NAMED and bounded (below).  B is the recorded
fallback if D8-2's `sim_dev` stalls — its trigger condition: if the
restriction simulation's device component costs more than the G4/G5
`qfab`/`gdev` reuse estimate, stop and switch.

## 6. The revised tier-2 staging

- **T2-0** — F3: the lock-protocol ghost export (φ mechanism;
  `WeakAcquire`/`WeakRelease` leaves + `weak_state_interp` +
  `weak_ev_adequacy_lockproto`).
- **T2-1** — F1: the RVWMO⁻ graph presentation + the two translation
  lemmas (A1c-style definitional work; litmus-check the declared model
  against A5's table — RVWMO⁻ must ALLOW LB and reader-fence-only MP).
- **T2-2** — R-track debts the containment needs: R4/S4 (pair-form tower
  re-index — deletes `Hfused`), R6 (contract), W1/W2 (walker traffic
  naming), the W-TV consumption slice.
- **T2-3** — D8-2 (the restriction simulation `sim_wpcfg`, budgeted on
  `sim_dev`), D8-3 (`certified_exec_complete`'s backward induction).
- **T2-4** — E1: the extended exhibit (cone replay ++ certifying solo
  runs ++ the early read), spending `head_prestate_pf_real`.
- **T2-5** — L2′: the per-site case analysis discharging `sf_edges` from
  {M, φ, lock protocol}; then `main_premises` is a theorem and
  `xv6_ev_weak_robust` goes premise-free.
- **T2-6** — `axiomatic_to_promising` port + the tier-2 capstone
  `xv6_rvwmo_safe` (tier-1's composition with `srvwmo_consistent`
  weakened to `rvwmo⁻_consistent`); `Print Assumptions` target: the five
  reservation axioms + the declared hardware-fidelity clauses (walker A/D
  non-promisable, no-icache) + the WP package.  Zero kernel premises.

## 7. Honest residual risks

1. `sim_dev` (T2-3) — PARM has no shared fabric; the G4/G5 machinery is
   the reuse bet.  Fallback trigger defined in §5.
2. The E1 glue (T2-4) — replaying `U ++ solo runs ++ read` preserves
   `readable` at the reader's views; the cone-replay machinery exists,
   the solo-run splice is new.
3. Kernel-site exhaustiveness (T2-5) — per-site, mechanical, repairable
   by invariant strengthening; the failure mode is BUDGET, not
   soundness.
4. The front-end's realizability direction (T2-6) — promising everything
   up front must land in OUR `WPPromise` shape; M6's W4 is the head
   start.
