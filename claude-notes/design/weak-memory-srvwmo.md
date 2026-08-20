# Design: sRVWMO — the declared-model plan (2026-08-19)

**STATUS: PLAN OF RECORD (user decision, 2026-08-19).**  This supersedes the
framing in [`weak-memory.md`](weak-memory.md) "The end-state theorem" in ONE
respect: the promise-free machine's behavior set is promoted from
*scaffolding awaiting the M6 robustness discharge* to a **declared,
axiomatically characterized model contract** named sRVWMO, with its own
tier-1 final theorem.  The certification route
([`weak-memory-layer2.md`](weak-memory-layer2.md) §8/§10/§11, D8/E1/L2′)
is NOT cancelled: it is the tier-2 upgrade that later deletes the sRVWMO
hardware assumption for stock xv6.  Nothing in the WP tier moves in either
tier.

## 0. The decision criterion (recorded verbatim in spirit)

The user's rule for every hypothesis of every top-level theorem:

- **Assumptions about hardware** (the 5 `rv64d` platform axioms, no-icache,
  A-bit timing, sRVWMO itself) are acceptable: they delimit the machine
  class, carry zero xv6 content, and are per-core falsifiable by litmus
  testing.
- **Assumptions about xv6's behavior over weak memory** are acceptable ONLY
  as theorems — machine-checked consequences of the WP proofs, exported
  through adequacy (φ, the lock-word value protocol, and their kin).
  Unverified side conditions about the kernel are rejected.
- **Syntactic/binary-analysis side conditions are rejected outright** (the
  fence-discipline image-scan route is dead): a scan certifies an
  instruction pattern, not the view-arithmetic property the reduction
  consumes, and the branch's own refutation history (`holding()`'s plain
  read, the walker's A/D CAS killing `edges_split`-family premises and
  even `gdep2_acyclic`) is the empirical record of that bridge failing.

A structural fact makes the tier split forced rather than chosen: **"no
side conditions" and "more behaviors than our machine" are jointly
unsatisfiable.**  For any machine M whose reachable program states strictly
exceed the promise-free machine's, the separating behavior is itself a
program safe on pf and unsafe on M — so unconditional per-program safety
transfer to M is impossible by construction.  The maximal no-premise
theorem is a behavior-set EQUALITY, and the freedom is in the presentation
of the other side.  sRVWMO is that presentation.

## 1. sRVWMO, the model

**Definition (candidate axiomatization).**  sRVWMO = RVWMO (same gmo, same
load-value/atomicity/progress axioms, same 13 ppo rules) plus ONE added ppo
rule:

    ppo rule 14:  b is a store        (i.e.  po ∩ (M × W) ⊆ gmo)

— stores enter the global memory order after ALL po-earlier accesses of
their hart; stores are never early.  Slogan for a hardware audience:
in-order store visibility (FIFO store-buffer drain, no early commit).
Implicit accesses included: the rule covers the PTW's A/D updates, which
ABSORBS the former standalone "A-bit updates not observed early"
assumption into the model definition (privileged spec permits speculative
A-bit setting, so this genuinely narrows the hardware class; D-bit is
exact by spec).

**Why one rule suffices.**  `po ∩ (M×W) ⊆ gmo` subsumes the earlier
conjecture's `(po ∩ W×W) ⊆ gmo` and implies `acyclic(po ∪ rf)`: a po∪rf
cycle decomposes into per-hart segments each entered at a load (rfe
target) and exited through a po edge into a store (rfe source); rule 14
puts every exit edge into gmo and rfe is forward in gmo, so the cycle is a
gmo cycle.  Whether the machine matches rule 14 EXACTLY or the two-conjunct
form is what the characterization proof (T1/T2 below) settles; any residue
adjusts the MODEL DEFINITION (a hardware-class statement), never a kernel
premise.  Known residues to settle in the proof: ppo rule 6 (`.rl`
successor ordering — the machine is WEAKER there; vacuous for this image,
but the axiom set must say so honestly), ppo 12/13 details, own-store
forwarding's placement of loads in gmo, and the fabric agent's accesses.

**SETTLED AXIOMATIZATION (2026-08-19, from the machine-checked evidence —
the A0/A1a ledger in
[`../projects/weak-memory-srvwmo.md`](../projects/weak-memory-srvwmo.md)).**
sRVWMO's ppo = RVWMO rules **1–5, 7, 14** (7 in the machine's `w_vRel`
form, stated on the `aq`/`rl` label bits unconditionally — coincides with
RVWMO 7 under RISC-V's all-RCsc annotations; forced by the T1 refutation
`promise_free_complete_false`), plus the load-value, atomicity and progress
axioms.  Exclusive pairs stay FUSED in the axiomatic presentation (the
projection re-fuses a split machine pair — sound because `excl_ok`'s window
makes re-fusion value-exact; a DANGLING exclusive read projects as a plain
load with no atomicity obligation).  Rules absent relative to RVWMO, each
with its reason of record:

- **6, 8, 10, 11, 13, and 9's store half — REDUNDANT under rule 14** (their
  right end is a store; rule 14 already orders it after everything).
  Machine side proved: the pf fulfil check is vacuous at the top timestamp
  in BOTH conjuncts (`fulfil_ok_d_top`, A1a).  Rule 6's only non-redundant
  corner is a release-annotated LOAD (`lr.rl`) — omitted; the machine does
  not enforce it and no ISA-sane code emits it.
- **9's LOAD half (address-dependent loads) — OMITTED BECAUSE OF D-8, not
  vacuity.**  The pf machine DOES enforce it for dep-carrying loads
  (`read_ok_d`'s `vaddr` floor is a live binding site — A1a's
  machine-checked MP+addr witness), but the xv6 instance's loads carry
  `asrc = []` (D-8: a PTE read and a data load are the same node), so the
  site is unreachable and T1's realization (empty operand lists) never
  trips it.  **If D-8 is ever dropped — loads gaining a real `asrc` —
  rule 9 comes straight back into the definition.**
- **12 (forwarding pipeline) — OMITTED via the `dep_dom` domination
  argument** (every dependency view is dominated by `w_vrOld` at every
  pf-reachable state; the D-7 bank's residues are then absorbed), NOT via
  top-timestamp vacuity.  The ~90-line `dep_dom` invariant must LAND
  before the definition relies on it (A1a scratch, `A1aDom.v`).

**THE T2 CARRIER PIPELINE (A2, designed 2026-08-19).**  From a real xv6
pf event-language run to an sRVWMO execution, three stages, each its own
simulation:

1. **ERASURE — LANDED (`iris/WeakErase.v`, `460ba147`)** (instance run →
   dep-free run of the same pf machine): relabel `LRegW`/`LCtrl`/`LInstr`
   to `LSilent` and blank every operand list.  The state relation as
   PROVED (three corrections to this block's first draft): `er_ws` =
   `ws_le` (erased ≤ instance) ∧ `w_relp` EQUAL ∧ `fwd_le` (the D2
   producer banks `(t, vf)` where erased banks `(t, 0)` — the ≤-form
   absorbs it; `dep_dom` is NOT needed) ∧ `res_rel` (same `rv_base`/
   `rv_ts`, `rv_view` erased ≤ — exactly what `PFExStore` reads; the
   one-way `Some` shape covers the `LInstr`-clear divergence).  The pf
   fragment has NO `fulfil_ok` at all, so only `coh`/`w_vrNew`/`w_vRel`/
   `w_res`/the log ever bind.  The class is pinned by `pcls_erasable`
   (`w_relp`-indexed — a label-only equation cannot pin it), discharged
   by the instance (`pcls_ev_erasable`).  Payoff: `erase_bridge_log` =
   T2 containment with `pstep_depfree` DELETED; `pstep_fused` is the
   only remaining gate (stage 2's).
2. **RE-FUSION — LANDED (`iris/WeakRefuse.v`, `e20044c6`), and it is NOT
   unconditional.**  Machine-checked obstacle: the fused read happens at
   the WRITE's position, so an agent step that raises its own read floor
   inside the window (one `fence r,r` suffices) gives the fused run a
   strictly higher post-view — `lr x; fence; sc x` has NO fused
   counterpart, and both fallbacks are refuted by the class/log (a
   conditional write is `WCexcl`; an early plain read invents an event).
   Hence the premise **`pstep_paired`**: between an exclusive read and
   its conditional write the agent takes only `wstate`-inert steps —
   true of the erased instance's windows (post-erasure they are
   `LSilent`/`LDev` only), and the reason stage 1 must run FIRST.  Every
   `LExLoad` maps to `LSilent` (a DANGLING read loses its axiomatic
   event — deciding "dangling" needs lookahead; log-level T2 loses
   nothing).  `pcls_fusable` is quantified OVER A STEP (an unquantified
   equation is false — the class lives on the monad node).  Endpoints:
   `refuse_run`, `t2_bridge` (premises: `pcls_erasable`, `pcls_fusable`,
   `pstep_paired (erase_pstep pstep)`).  **OPEN — the instance discharge
   of `pstep_paired`** (worklist A2-s3).  The 2026-08-20 recon SUPERSEDES
   the abandonment-refinement note that stood here: `pstep_paired` as
   landed is UNIMPLEMENTABLE for the instance, three ways, and the repair
   is a redesign, not a refinement.  The findings (all read off the code):

   - **Clause 1 is UNUSED** — `refuse_step` destructures `Hp1` and never
     applies it.  Deleting it (strictly weaker premise) retires the
     abandonment problem in its recorded form: an abandoning exload simply
     never enters `expend`.
   - **Clause 2 cannot pin the timestamps.**  Two exload steps that differ
     only in timestamps (equal values) land in the SAME program state
     (`m' = k (inl (w, None))` absorbs only the value), so no
     state-predicate `expend p aq base tvs` can satisfy clause 2's
     label-equality disjunct.  Repair: the pending invariant goes to an
     ∃-FORM keyed on the machine's `w_res` — `rv_base`/`rv_ts` pin base
     and timestamps, `(aq, tvs)` are existential in `rf_pend` and are
     established from the exload label's own data — and `expend : P → Prop`
     loses all indices.
   - **Clauses 2+3 are jointly history-dependent.**  The same monad state
     (`sc;rest`) is reachable through a clean window AND through a
     fence/load-dirtied one (and the FETCH is a plain `LLoad` —
     `WeakEvStarted` proves the model's fetch classifies `AK_explicit`,
     not `AK_ifetch`; the comment at `WeakEvInst.v` §6 saying otherwise is
     stale), and the two clauses make contradictory demands on that state.
     No state-only `expend` exists.  Repair is MACHINE-SIDE: the agent's
     own plain LOADS and FENCES clear `w_res` (stores and `LInstr` already
     do; ISA-legal — a reservation may be invalidated at any time, and the
     ISA's own LR/SC forward-progress guarantee excludes loads/fences
     inside constrained loops; no real window contains either, so the WP
     tier never sees the difference).  Then every dirty-label obligation
     dies by the `w_res = Some R` GUARD, the `lr;fence;sc` counterexample
     becomes machine-unreachable (`PFExStore` starves; the retry arm
     spins), and — a free bonus — the erased run's stale reservations
     (erasure drops `LInstr`'s clear) die at the next instruction's FETCH
     load.

   The REDESIGNED discipline: `pstep_paired := W1 ∧ W3` with
   `expend : P → Prop` — W1: an (erased-)`LSilent`/`LDev` step into an
   `expend` state comes from an `expend` state; W3: every `LExStore`
   step's pre-state is `expend` — both guarded by an instance-supplied
   invariant `PI : P → Prop` (plus a `PI`-preservation clause and `PI` on
   the initial programs), because the raw monad space contains adversarial
   shapes (`RegRead;sc`) that no structural predicate survives.  The
   instance's `expend` is structural — "the continuation's next memory
   event is the paired conditional write", walking ONLY
   `{RegWrite, pure-silent}` nodes, hence REGISTER-FILE-INDEPENDENT, which
   trivializes W1's PLIC arm (the PLIC rewrites `sig_seip` under the
   window) and makes W1's boundary arm a small concrete walk
   (`riscv_step`'s dispatch prefix dead-ends at its first
   `RegRead`/fetch).  `PI` is the one WHOLE-MODEL fact: "every latest-write
   node is guarded — reachable from its latest-read through
   `{RegWrite, pure-silent}` nodes only", ∀-quantified at every answer —
   a boolean-state traversal of `riscv_step` in exactly the
   port-the-driver family (`DecodeSetU.goodbP` state-pinned /
   `WeakShapeOverrides2.gpost` ∀-quantified; durable-notes: the drivers
   transfer line for line).  That traversal (s3d) is A2-s3's irreducible
   cost; everything else is per-arm mechanical.
3. **THE EXISTING PROJECTION** (`wp_pf_step_mstep`): the output of
   stages 1–2 is `lb_depfree ∧ lb_fused`, discharging the gates by
   construction.  T1's realization side names the SAME gates
   (`WeakAxRealize.lbl_realizes`), so both directions relax in lockstep.

Scope clause: sRVWMO covers RAM accesses of harts and the disk agent;
MMIO, the UART thread and the PLIC wire are outside it, under the retained
device-ordering assumption.  Projection route for T2's carrier: the
ERASURE SIMULATION (on the `lb_ldepfree` alphabet, blank every operand
list; project the erased run with the existing `wp_pf_step_mstep`, whose
`lb_depfree` premise is then discharged by construction) — zero changes to
`mstep`/`lbl`/the `WeakAxiomatic` tower; the one real work item is the
`w_fwd` component of the erasure invariant, where `dep_dom` does the work;
fallback is the prototyped `mstep_d` re-land.

**Relation to RC11 (for the paper).**  Same genre of move — strengthen the
model by an ordering axiom to make it interleaving-representable — but NOT
the same axiom: RC11 adds exactly `acyclic(po ∪ rf)` and deliberately
keeps W→W reordering legal (compilers reorder stores).  sRVWMO's rule is
strictly stronger because promises are the machine's SOLE early-store
mechanism, so removing them strengthens the ld→st and st→st axes at once.
Also unlike RC11: RVWMO already preserves dependencies (no OOTA problem to
fix — the motivation is representability, not thin-air), and a language
gets to CHOOSE its contract while we only narrow a hardware class — hence
sRVWMO stays an assumption for non-Ztso cores, and is litmus-testable
(LB, 2+2W, S) per core.  **Ztso implements sRVWMO outright** (Ztso puts
R→R, R→W, W→W into ppo — strictly more than rule 14), so the tier-1
theorem is unconditional for the Ztso class.

## 2. The two characterization theorems (program-independent, no premises)

Over the existing `WeakAxiomatic` vocabulary:

- **T1 (realizability / the soundness direction; the hard one).**  Every
  sRVWMO-consistent execution is realizable by the promise-free machine
  (same program states and memory).  This is the direction tier-1 safety
  consumes: hardware ⊆ sRVWMO ≡ pf.
- **T2 (containment / no invented behaviors).**  Every pf run projects to
  an sRVWMO-consistent execution.  This is the existing "RVWMO
  containment" worklist item (WeakCompose §6(5) upgrade), retargeted at
  sRVWMO where it becomes an equality partner rather than a one-sided
  sanity check.

Precedent for T1's shape: PS1 Thm 5 (promise-free PS1 ≡
acyclic(sb ∪ rf ∪ sc)).  Since D2/D3 landed dependency tracking (ppo 9–11
now IN the machine), the sandwich is far tighter than when the two-conjunct
conjecture was first written; T1/T2 together are what make sRVWMO "RVWMO
plus one named rule" instead of "whatever our interpreter does".

## 3. The tier-1 final theorem

    [WP package]  ⇒  (adequacy over the pf event language, EXISTS:
                      xv6_ev_weak_robust's adequacy component)
                  ∘  [T1: sRVWMO ≡ pf]
                  =  xv6 is safe on every hart of every machine
                     implementing sRVWMO.

Hypothesis footprint: the WP package, the fresh-era/boot facts, the 5
platform axioms, no-icache, funext.  **Zero side conditions about xv6's
weak-memory behavior — not even WP-derived exports**: φ and the protocol
exports are not consumed at this tier.  The whole `main_premises`/
`robust_main` tower is OFF this path (parked for tier 2); none of its
premises appear.

Corollaries to state: (a) unconditional on Ztso; (b) the litmus suite as
the model's empirical evidence artifact (LB must be unobservable;
everything else must match riscv.cat verdicts).

## 4. Tier 2 — the RVWMO upgrade (unchanged plan, restated under the criterion)

D8/E1/L2′ per [`weak-memory-layer2.md`](weak-memory-layer2.md) §8/§11.
Data-flow clarification worth recording (it answers a recurring
confusion): **certificates are not derived from WPs.**  Certification
completeness (D8) is pure machine theory (PARM's arch-generic
`CertifySim` restriction line; no xv6 content).  What the WPs contribute
is invariants over pf-reachable configurations (φ; the lock-word value
protocol exported from `wlockN` through adequacy — the §5(β) ghost-export
mechanism applied to lock words ONLY, which are machine-identifiable as
aq-RMW targets; more exports if L2′ demands, each repaired only by
strengthening an invariant in the logic, never by an external premise).
The two compose because **a certifying run is a pf run of the same
program**, so every configuration it passes through is pf-reachable and
the WP exports constrain it.  Tier-2 hypothesis footprint: hardware
assumptions + the WP package, nothing else.

Decisive next experiment BEFORE any D8 porting: the two-hart LB-shaped
L2′ argument on paper (one lock, one racy byte, one PTW read), checking
every case discharges from {machine facts, φ, exported lock protocol}
alone.  Residual risks stand as recorded: the restriction simulation over
interspersed sub-logs, certifying runs reading on-cycle promises (the
mutual-grounding shape the minimal-SCC structure must break), `sim_dev`
for the fabric, the fused-RMW window.

## 5. Read-only / frozen sharing (recorded 2026-08-19)

The `struct file` pattern (type/readable/writable frozen while
refcount > 0; recycled after) FITS both tiers with no new machinery class:

- WP tier: counting-permission escrow — fractional SUBJECTIVE `↦ₘ{q}`
  (NOT the objective write-once `↦□`: slots are recycled, many messages
  per era) tied to a refcount ghost; fractions travel through the existing
  lock-transfer chains (`ftable.lock` for dup/close; the `p->lock`/swtch
  chain for fork inheritance); the reader pays the acquire once at fd
  receipt, then every read is a PINNED read (bridge case 2) — leaves stay
  SC-shaped, no per-read fences, matching the code.  New artifact is a
  spec shape only (`file_frozen`-style predicate); same pattern serves
  `ip->dev`/`ip->inum` and pipe identity.  xv6's refcounts are
  lock-protected, so none of the lock-free-refcount (Arc-style) hardness.
- Reduction tier: these edges land in landed cases — C3 (the value is
  branched on / data-flows into stores; D2/D3's `fcov_of_dep_chain`) or
  C4 (the publication release chain; the fork/swtch path is the longest
  `covered_of_release_chain` instance and should be L2′'s test case) —
  and the freeze write is φ-legitimate (performed under full ownership).
  **The reduction never enumerates frozen bytes** — no freeze map, no
  byte classification; the discipline lives entirely in the WP tier.

## 6. Worklist

- **S1**: define sRVWMO in Coq over the `WeakAxiomatic` vocabulary (rule
  14 incl. implicit walker stores; the honest `.rl`/ppo-12/13 residue
  notes as part of the definition).
- **S2**: T2 containment (the WeakCompose §6(5) upgrade, retargeted).
- **S3**: T1 realizability — the characterization's hard direction; PS1
  Thm 5 shape; this is the tier-1 long pole.
- **S4**: restate the capstone as tier-1 (adequacy ∘ T1) and diff the
  assumption footprint (`Print Assumptions`: platform axioms + no-icache
  + funext + WP package; NO main_premises anywhere on the path).
- **S5**: litmus suite verdicts re-checked against the sRVWMO definition
  (not just against the machine).
- **S6**: the two-hart L2′ paper exercise (tier-2 go/no-go gate).
