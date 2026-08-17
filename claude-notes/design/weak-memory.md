# Design: weak memory (RVWMO)

STATUS (2026-08): M0–M3 are LANDED on branch `weak-memory` (the promise-free
machine + litmus suite, the weak interpreter/language/base logic with a
closed adequacy skeleton, the vProp surface with the split axiom, the
pinned-fragment transfer bridge, fence/AMO rules, the instruction-leaf layer,
and the vertical slice: the step certificate, the spinlock and the `started`
escrow). M4 (the sweep) is next; its recipe is
[`projects/weak-memory-porting.md`](../projects/weak-memory-porting.md). The staged worklist with per-stage established-facts blocks is
[`projects/weak-memory.md`](../projects/weak-memory.md); where a landed
stage corrected a decision below, the correction is noted inline at that
decision.

## What we are trying to say

Today the machine is sequentially consistent: `gstate` holds ONE flat
`gmem : gmap Arch.pa (bv 8)`, `prim_step` interleaves whole instructions, and
every hart's load reads the single current byte map (`RiscvLang.run`'s
MemRead/MemWrite arms). Real rv64 hardware implements RVWMO, which is weaker,
so `xv6_power_adequacy` is currently a theorem about an idealized
SC multiprocessor. The goal: replace the memory semantics with an honest
RVWMO-class model and give the proofs reasoning principles that keep the
existing lock-protected code cheap while making the fence/AMO idioms
(spinlocks, the `started` handoff, forkret's `first`, the virtio ring) carry
real ordering obligations.

## The related-work map (read once, then use the decisions below)

- **RVWMO** (unpriv spec ch. "RVWMO Memory Consistency Model" +
  mm-explanatory/mm-formal appendices): axiomatic — a total *global memory
  order* over all memory operations constrained by 13 preserved-program-order
  rules + load-value / atomicity / progress axioms. Two facts shape
  everything: (1) RVWMO is **multi-copy atomic** (a store visible to any other
  hart is visible to all; only the writer may see its own stores early), so
  one global write order suffices and fences are non-cumulative; (2) RVWMO
  **allows load buffering** (`po ∪ rf` cycles: a store may enter the global
  order before a po-earlier load resolves), which is the one behavior an
  interleaving machine cannot produce without extra machinery.
- **Promising-RISC-V** (Pulte, Pichon-Pharabod, Kang, Lee, Hur, PLDI 2019;
  Coq: github.com/snu-sf/promising-arm): operational model proven equivalent
  to axiomatic RVWMO. Memory = append-only `list Msg`; timestamps = list
  indices; per-thread views are plain naturals (MCA!). Threads execute in
  program order; load reordering comes from *reading old messages*; store
  reordering comes from **promises** (append a write early, certified by a
  thread-local solo run against current memory, fulfilled later).
  Deadlock-free and certification-precise for RISC-V (unlike ARMv8).
- **SLR** (Svendsen et al., ESOP 2018): the only separation logic over a
  promising model. Not mechanized — soundness needs transfinite (ℕ×ℕ)
  step-indexing because certification runs are unbounded; vanilla Iris cannot
  express it. Its key structural moves (prove rules against the non-promising
  machine, transfer because certifications are promise-free runs of the same
  program; erasure demands a promiser can *acquire* the write permission) are
  the playbook if we ever do promises in-logic.
- **iGPS** (ECOOP 2017) / **iRC11+ORC11** (RustBelt Relaxed, POPL 2020) /
  **Cosmo** (ICFP 2020) / **Compass** (PLDI 2022): the Iris recipe for
  view-based models *without* load buffering: instantiate Iris with the
  view machine to get an explicit-view base logic, then define
  `vProp := View →mon iProp` and re-derive the surface logic; restrict
  invariants to **objective** (view-independent) assertions; subjective
  content moves through synchronization via a duplicable seen-assertion `⊒V`,
  a view-at modality `@V P`, and the split axiom `P ⊣⊢ ∃V. ⊒V ∗ @V P`;
  fence modalities Δ/∇ (FSL lineage) handle fence-based publication. Cosmo's
  headline: the non-atomic points-to's rules are exactly the SC rules, so
  lock-protected code verifies as in SC.
- **AxSL** (POPL 2024): Iris over the *axiomatic* Arm-A model directly
  (guess a whole candidate graph, threads validate against it; resources
  tied to event ids, flowing along ordered-before edges). Faithful including
  LB — but it abandons the operational adequacy/interleaving structure this
  tree is built on (prim_step, device threads, the power loop, reducibility
  adequacy), has no coherence reasoning story yet, and would be a rewrite of
  the world. Rejected for this project; noted as the fallback if operational
  turns out unworkable.

## Decision 1: view-based operational model, promise-free first

We adopt the **Promising-RISC-V machine shape with the promise machinery
deliberately omitted** (empty promise set, every store = append-at-end).

### The promise-free gap, precisely

**What load buffering is.** The LB litmus test:

```
Hart 0:            Hart 1:
r1 := load x       r2 := load y
store y := 1       store x := 1
```

Can r1 = r2 = 1? RVWMO says YES: no ppo rule orders a load before a
po-later store to a different address with no syntactic dependency (rule 1
needs overlapping addresses, rules 9–11 need deps, rule 13 needs an
intervening address dep), so there is a legal global memory order with both
stores before both loads. Microarchitecturally: a core may commit a store
(make it globally visible) before a po-earlier load to a different address
has resolved. RVWMO's syntactic-dependency rules make the *dangerous*
variants forbidden — LB with a data/address dep on both sides (= out of
thin air) cannot happen — but plain and fake-dep LB is architecturally
allowed.

**Why no interleaving machine can represent it.** In any interleaving
semantics where (a) threads execute their instructions in program order and
(b) a load can only return a value some already-executed store put in
memory — no matter how stale — every reads-from edge points backward in
real time, so `po ∪ rf` is acyclic in every execution. LB *is* a `po ∪ rf`
cycle: for r1 = 1, H1's store must precede H0's load in real time, hence
(H1 in-order) H1's load precedes it too, hence (r2 = 1) H0's store precedes
THAT, hence (H0 in-order) H0's load precedes its own rf-source. The
mechanisms that break (b) are exactly the known heavyweight ones: promises +
certification (Promising), speculative execution + restarts (Flat/rmem, the
spec's own operational appendix), event structures, or guessing the whole
execution graph up front (AxSL's opax). For a WP logic, promises are the
lightest of these and STILL force transfinite step-indexing (SLR) — an
unbounded certification run is re-verified at every step, giving ℕ×ℕ
lexicographic indices vanilla Iris cannot express.

**What the promise-free machine actually excludes — more than LB.** Because
the log is append-at-execution and threads run in po, each hart's stores
enter the global order in program order — for ALL addresses, not just
same-address (RVWMO rule 1). So observable **W→W reordering** is also
excluded: MP with an unfenced writer and a `fence r,rw` reader has its weak
outcome allowed by RVWMO (nothing orders the writer's two stores) but
unreachable in this machine. In PARM, promises are the *sole* mechanism for
any early store, so the honest name for the gap is "store reordering", not
"load buffering". Conjectured axiomatic characterization (an M6-adjacent
lemma to prove, precedented by PS1 Thm 5, which characterizes promise-free
PS1 as acyclic(sb ∪ rf ∪ sc)):

    promise-free machine  ≡  RVWMO ∧ acyclic(po ∪ rf) ∧ (po ∩ W×W) ⊆ gmo

**This is NOT TSO.** A total store order is shared by both, but TSO
additionally forces every load to return the newest write in that order
(modulo own-store-buffer forwarding) — reads are coherent-latest, R→R is
program-ordered. The promise-free machine keeps almost all of RVWMO's
READ-side weakness: a load may return any write not superseded within the
reader's view, and views advance only via fences/acquires/coherence. So
unfenced MP stays weak (reader sees y=1 then stale x=0 — forbidden under
TSO), R→R reordering is observable, and every reader-side fence and
acquire obligation in the kernel remains load-bearing. Strict containment
both ways: TSO ⊊ promise-free ⊊ RVWMO (witnesses: unfenced MP separates
TSO from promise-free; LB separates promise-free from RVWMO). What the
machine temporarily trivializes is only the WRITER-side (predecessor-W)
fence obligations — exactly the M6 gap.

**Is this an established model class, or an invention?** The *genre* is
established; the RVWMO instance is ours to define. RC11 (Lahav et al., PLDI
2017) is exactly this move at the C11 level — C11 strengthened with
acyclic(po ∪ rf), adopted precisely to kill thin-air and enable
reasoning — and ORC11/iRC11 operationalize and build the logic over it;
Cosmo's OCaml model and iGPS's RA are likewise LB-free by construction.
SLR is the only logic ever built on the far side of the line, and paid the
transfinite toll. So: crisply axiomatizable, well-precedented shape, but
nobody has written down "promise-free RVWMO" — the definition and its
characterization lemma are our artifact, and the characterization is what
keeps it from being ad hoc.

**The alternative machine that makes the gap exactly LB** (recorded,
rejected): an ORC11-shaped machine with per-byte timestamp orders and
view-carrying messages represents W→W reordering without promises (a
relaxed write takes a fresh per-location timestamp and carries no view of
the hart's other stores; a fenced reader can then see the writes out of
order). Cost: views become per-location timemaps everywhere, messages carry
views (infecting the log, the base state interpretation, and every leaf
rule), and the PARM lineage (equivalence theorem, deadlock-freedom) is
lost. Rejected because the M6 robustness obligation is the same shape
either way — the fencing discipline that discharges LB discharges W→W
identically, promises being the single mechanism behind both — and the
single-list state is simpler at every other point of the design.

**Why the gap is safe for THIS kernel, and how it is accounted.** A store
preceded (transitively) by `fence rw,w`/`fence rw,rw`, or ordered after an
acquire-AMO, cannot be promised early in the full machine: its fulfilment
pre-view would exceed the promised timestamp (certification runs the real
code, so the fence raises `w_vwNew` before the store can fulfil). xv6's
entire cross-hart discipline — lock CS stores bracketed by aq-AMO and
fence-release; the `started`/`first` sites written with C11
release/acquire (`fence rw,w ; sw` on the writer, `lw ; fence r,rw` on the
reader — the image contains no `fence rw,rw` at all); virtio's MMIO seams
with `io_fence()` = `fence iorw,iorw` — is in that class; the gap is real
only for racy unfenced stores,
which the verified kernel should not have. **Until M6 this is a documented
model assumption** in the same epistemic category as the 5 `rv64d.*`
platform axioms: stated once, visible in the final theorem's footprint,
discharged by later work (M6 = the robustness theorem: for
release-fenced/lock-mediated programs, full-machine behaviors =
promise-free behaviors; operational-level, no Iris; PS1's DRF-Promise /
PS2's Thm 6.5 are the language-level precedent). Full promises-in-logic
(SLR-style) stays on the shelf unless robustness fails.

**The end-state theorem (what the plan is FOR).** The strengthened model is
scaffolding, not the final claim. Final shape: [adequacy over the
promise-free machine, M1–M5, Iris] ∘ [M6 robustness: every full-machine
execution of THIS kernel is matched by a promise-free execution with the
same observable states] ∘ [Promising-RISC-V ≡ axiomatic RVWMO, Pulte et
al., Coq] = adequacy over real RVWMO, no strengthening in the statement.
Robustness is a program property ("reordering is unobservable"), not
"hardware doesn't reorder". Preferred M6 proof route: extract it from the
Iris proof itself — the WP proof already shows every store is either to
exclusively-owned bytes (`↦ₘ`) or at an enumerated fenced sync site, which
is exactly the per-store side condition a simulation needs to delay each
promise to its fulfilment point unobserved (precedent: PS1/PS2's DRF
theorems; iGPS/iRC11 deriving NA-race-freedom from the logic). Fallback
route: standalone Lahav–Margalit-style robustness analysis. Interim value
if M6 is unfinished: the characterization lemma makes the assumption a
clean axiomatic statement, and **Ztso hardware implements the strengthened
model outright** (Ztso's implicit RCpc annotations put po∩W×W into ppo and
forbid LB), so the interim theorem is already unconditional for the Ztso
class and assumption-carrying only for weaker RVWMO implementations.

**Polarity note.** Decision 3 (dropping dependency tracking) makes the
model *weaker* than hardware — sound for adequacy, costs nothing. THIS
decision makes it *stronger* — adequacy needs hardware ⊆ model, and the
strengthening is exactly what the declared assumption covers. Keep the two
directions straight when evaluating any future simplification: adding
behaviors is free, removing them needs a theorem.

One recorded exception to "strictly stronger", found by W4 slice 1
(`WeakAxiomatic.v`, 2026-08-11): RVWMO ppo rule 6 — a store with the `.rl`
annotation is ordered after po-earlier accesses — is NOT enforced by this
machine (`w_vRel` is inert on the store side promise-free), so on that one
axis the model is *weaker* than RVWMO. Free for adequacy (weaker adds
behaviors), and vacuous for this kernel — the image contains no `.rl`
store (release is fence-based) — but the honest statement of the model's
relation to RVWMO is "stronger on the writer-order axes covered by the M6
assumption, weaker on `.rl`-successor ordering and the dropped ppo 9–13".

Why not promises from day 1: (a) no vanilla-Iris logic over promises exists,
for the transfinite-indexing reason above; (b) reads can observe
never-to-be-fulfilled promises in doomed runs, so a safety/adequacy statement
over the full promising machine needs either SLR-style ownership erasure or a
reformulated adequacy — both research projects in themselves; (c) the
promise-free machine already forces every reasoning-principle change we need
(views, objective invariants, lock rework, fence rules), so nothing built in
M1–M5 is thrown away if/when promises land.

## Decision 2: the machine state

Granularity is the **byte**, as today (RVWMO's load-value axiom is per-byte;
misaligned accesses decompose; the tree's points-to is per-byte).

```
(* one write event; tid None = DMA/boot-era agents *)
Record wmsg := { wm_pa : Arch.pa; wm_data : list (bv 8); wm_tid : option CPU }.

(* per-agent (hart or disk) weak state -- the PARM thread state minus
   promises, minus register views (see Decision 3), minus the exclusives
   bank until LR/SC is needed *)
Record wstate := {
  w_coh   : gmap Arch.pa nat;   (* per-byte coherence floor; default 0 *)
  w_vrOld : nat; w_vwOld : nat; (* max post-view of past loads / stores *)
  w_vrNew : nat; w_vwNew : nat; (* pre-view floors for future loads / stores *)
  w_vRel  : nat;                (* release view; inert until .rl appears *)
  w_fwd   : gmap Arch.pa (nat * nat);  (* forward bank: ts + fwd view *)
}.
```

Key type, DECIDED at M1: the weak-memory maps (log addressing, `w_coh`,
`w_fwd`, histories) are keyed by **`Z`** (`uint` of the physical address),
converted once at the interpreter seam — `WeakMem.v` is used as-is and the
`gmap Arch.pa` Countable-instance trap (durable notes) never arises. RAM
addresses cannot wrap, so `uint (pa_add pa j) = uint pa + j` on every
address the kernel uses.

`gstate` changes: `gmem : gmap Arch.pa (bv 8)` becomes the **era-initial
image** `gmem0` plus the **global write log** `glog : list wmsg` (timestamp 0
= `gmem0`, timestamp i+1 = `glog !! i` — one shared total order, which is
exactly what MCA licenses); plus `gws : CPU → wstate` and a disk-agent
`wstate` (see Devices). The SC machine is the degenerate instance where every
view is `length glog` — useful for sanity lemmas, not for migration.

Step rules (the PARM rules, dependency components dropped):

- **Load** of byte a: pre-view `vpre = w_vrNew ⊔ (aq ? w_vRel)`; may read
  timestamp t iff t writes a and no message writes a in
  `(t, vpre ⊔ w_coh(a)]`; post-view `vpost = vpre ⊔ t` (or the forward-bank
  view if t is the agent's own last write to a); updates
  `w_coh(a) ⊔= vpost`, `w_vrOld ⊔= vpost`, and if acquire also
  `w_vrNew, w_vwNew ⊔= vpost`. Multi-byte loads read per-byte.
- **Store**: append at `t = length glog + 1`; `w_coh ⊔= t` on its bytes,
  `w_vwOld ⊔= t`, forward bank updated. (Promise-free: no early stores, so
  the store rule has no constraint to check.)
- **AMO**: one `prim_step` is a whole instruction, so the read and write
  halves interleave with nothing. The read half carries an EXPLICIT
  latest-read side condition — `¬ writes_in log a t (length log)`, i.e. no
  message after `t` writes the byte — it does NOT follow from `readable`
  (which only bounds `t` by the hart's own floor); M0's `amo_latest_unique`
  shows the condition pins `t` uniquely. The write appends. `.aq` applies
  the acquire updates to the read half; `.rl` the release side (raises the
  store's effective pre-view — inert constraint promise-free, but keep the
  bookkeeping so `w_vRel` is honest; NB the `w_vRel` term in the acquire
  pre-view is faithful-PARM bookkeeping that no xv6 idiom can exercise —
  flagged unvalidated by M0, keep it faithful).
- **FENCE pred,succ** (the `Interface.Barrier` arm of `run`/`exec`, today a
  no-op): `v1 := (R ∈ pred ? w_vrOld) ⊔ (W ∈ pred ? w_vwOld)`; then
  `R ∈ succ → w_vrNew ⊔= v1`, `W ∈ succ → w_vwNew ⊔= v1`. `fence.tso` =
  `fence r,r ; fence rw,w`. The generated model already emits the full
  `Barrier_RISCV_*` kind lattice, so this is a `match` on data we get for
  free. NOTE the promise-free subtlety: predecessor-W fences constrain
  nothing in this machine (stores are never early) — their obligation
  reappears in the M6 robustness theorem, which is where `fence rw,w`'s
  soundness role lives. Reader-side (succ-R) fences are the live ones here.
- **LR/SC**: not used by the kernel (acquire is `amoswap.w.aq`). Keep the
  existing 5 reservation platform axioms untouched; add the exclusives bank
  only when something needs it.

The Sail `ReadReq`/`WriteReq` already carry `Access_kind` (explicit with
`Access_strength` relaxed/rel-or-acq, `AK_ifetch`, `AK_ttw`) — the `run`
interpreter dispatches on data already present. No Sail regeneration needed.

## Decision 3: drop syntactic dependency tracking (ppo 9–13)

PARM tracks a view per architectural register (`regs : Reg → Val × View`) to
give syntactic address/data/control dependencies their ordering force, plus
`v_CAP`. Omitting all of it — no register views, loads/stores ordered only by
fences/acquires/coherence — makes the model **strictly weaker** (fewer
orderings, more behaviors), which is the sound direction for adequacy, and it
means **`regstate` and every register/CSR/decode/interrupt proof in the tree
is untouched**: the weak state is a side record consulted only at the
MemRead/MemWrite/Barrier arms. xv6 relies on no dependency ordering (all
idioms are fence/AMO-based; virtio's addr-dependent ring reads sit between
explicit fences). If a future proof needs ppo 9–13 (e.g. a seqlock), register
views can be added then — the cost lands in `run`/`exec`'s RegRead/RegWrite
arms and nowhere in the logic's interfaces. The forward bank stores the
weakest sound view (the store's fence floor `w_vwNew` at store time; 0 is
also sound) — over-weak is safe, over-strong is not.
**CORRECTION (2026-08-17, deps design §2.3′ D-7): that parenthesis had the
polarity backwards — `w_vwNew` is LARGER than PARM's `FwdItem` view
(`V(asrc) ⊔ V(dsrc)`, RVWMO ppo 12), so it removed hardware behaviours;
`WeakMem.store_post` now banks `0`, the dependency-free PARM value, and D2
will replace it by `V(asrc) ⊔ V(dsrc)`.**
DECIDED after M0: the
bank gets **wired into the load rule at M1** (a load reading the hart's own
latest store takes the banked view instead of the timestamp). M0 left it
write-only (`vpost = vpre ⊔ t` unconditionally), which is sound-but-
stronger; leaving that permanently would silently widen the documented gap
(a forwarded load would gain ordering hardware does not give it), and the
wire-in is a one-arm change to `load_post`.

## Decision 4: exec, the oracle, and the leaf-lemma seam

`exec` is deterministic and the whole tree feeds `exec … = Some (tt, σ')`
witnesses (`wp_exec_step`); a weak load has many admissible results. Handle
it exactly like the nondeterministic clock tick, whose precedent already
exists in `riscv_step`:

- `run` stays relational: reads ∃-quantify admissible timestamps.
- `exec` takes a **read oracle** χ (a list of per-byte timestamp choices,
  consumed in order by MemRead arms; it *checks* admissibility and returns
  None otherwise). `exec_run_det` becomes `exec_run` per oracle (exec success
  at χ implies run; determinism only GIVEN χ).
- `prim_step` ∃-quantifies χ; `wp_exec_step` ∀-quantifies the continuation
  over admissible χ. The Iris layer is what collapses the quantifier: a leaf
  holding `a ↦ₘ v` (see below) proves every admissible choice returns v — the
  timestamp may vary, the value cannot. Leaves over racy cells (the lock
  word, `started`) genuinely case-split, which is the point.
- The decode/fetch path never touches the oracle: text bytes have exactly one
  write (timestamp 0), so any admissible choice returns the same byte and
  fetch stays deterministic. Same for all `↦□` bytes — this is what keeps
  the decode bridge and `instr` machinery valid verbatim.

## Decision 5: the Iris architecture (Cosmo-shaped, two layers)

**Base layer** (explicit views, few users): instantiate Iris with the new
language. `mstate_interp` grows: `mono_list_auth` over `glog` (append-only —
the log's own algebra gives persistent per-timestamp agreement snapshots),
auth over each hart's `wstate`, and the per-byte history auth replacing
today's flat `gen_heap_interp` (per-byte map of timestamp → value, derived
from log + image; `dq`-governed like today).

**Surface layer**: `vProp := monPred (View, ⊑) (iProp Σ)`. DECIDED
(pre-M2, from the M0/M1a shapes): `View := nat * gmap Z nat` — a SCALAR
floor plus a sparse per-byte map, denoting `flr V a = V.1 ⊔ (V.2 !! a)`,
ordered pointwise on `flr`, joined componentwise (`⊔` on the scalar,
union-with-max on the map), bottom `(0, ∅)`. Why the pair: a hart's
semantic read floor for byte a is `w_vrNew ⊔ coh(a)` — a scalar joined
with a finite map, which a bare `gmap` cannot represent (infinite
support) and a bare scalar cannot either (per-byte points-to floors).
The hart's logical index at a program point is `(w_vrNew, w_coh)`; a
points-to needs only a singleton-map view; and a release deposits the
SCALAR view `(t_rel, ∅)` — the timestamp of the releasing store bounds
every component of the releaser's floor because timestamps below the
log's length bound all views, which is what keeps lock-transfer
statements tiny. Iris 4.4's monPred + proofmode support is battle-tested
(iRC11/gpfsl track modern Iris). The pieces:

- `⊒V` — duplicable, persistent "I have observed V"; anti-monotone; joins.
- `objective P` + `@V P` (view-at) + the split axiom
  `P ⊣⊢ ∃V. ⊒V ∗ @V P`. **Invariants may contain only objective
  assertions** — this is the soundness linchpin the whole design turns on.
- **What is objective by construction** (i.e. unchanged in meaning and
  freely shareable exactly as today): every register/CSR assertion (`↦ᵣ`,
  `pc_is`, `hw_config`, sconf/sie, minstret/clock cells), all device-fabric
  assertions, all pure facts, all ghost state (unsynchronized by default, the
  iRC11 stance), and — because a write-once byte has a single message any
  view can read — **every discarded-fraction points-to** (`↦ₘ□`, `↦ₓ□`,
  `↦₈□`, `↦ₛ□`, `kernel_text`, `kernel_data_string`). The subjective
  footprint is exactly: mutable RAM bytes.
- `a ↦ₘ{dq} v` (same notation, new meaning): "some timestamp t holds the
  latest write to a, it wrote v, and my view includes t" — the Cosmo
  non-atomic points-to. Its load/store rules ARE the SC rules, so **every
  function proof that owns its memory (directly or through a lock) keeps its
  statement and its proof script shape**. The kmap/translation conjuncts
  inside `mem_pointsto` ride along unchanged.
- **Fence modalities** for the publication sites (`fence rw,w` on the
  writer, `fence r,rw` on the reader — see the note above; nothing in the
  image is `rw,rw`). REVISED at
  M2b, and the revision is forced by the index: the frontier a succ-R fence
  delivers is `View (vrNew ⊔ vrOld ⊔ vwOld) coh`, and `vrOld`/`vwOld` are
  not part of the `biIndex` — so `∇ P` cannot be a `vProp → vProp` without
  iRC11's THREE-view index (cur/acq/rel). It is delivered instead at the
  `vwp_hold` altitude, where the hart's `wstate` is in hand:
  `vwp_acq P ws := monPred_at P (acq_view ws)`, with
  `vwp_acq P ws ⊢ vwp_hold P (fence_post ws true true true sw)` (an
  equality of views, so the rule is `reflexivity`). REVISED AGAIN at batch
  5's second half: that identity needs pred-RW, but the kernel's reader-side
  fence is pred-R only, and the SCALAR bound the delivery actually uses
  holds at `pw = false` — so the kind-dependence is now abstracted as
  `WeakFence.acq_pred_r b` ("the read frontier `acq_view_r` is below the
  hart's index after `b`", instances `rw,rw`/`rw,r`/`r,rw`/`r,r`) with
  `view_scl_acq_pred_r` the one delivery fact; no lemma is duplicated per
  fence kind. And `Δ` is NOT a
  modality: promise-free, a predecessor-W fence constrains nothing, and the
  writer side's real content is the timestamp-domination lemma — the
  releaser's whole index is below `S (length log)`, so it may deposit
  anything it holds at the objective scalar view `view_scl (S (length log))`
  (`WeakFence.release_deposit`, resting on `WeakMem.ws_bounded`). Ghost
  state passes through both freely.
- **Locks**: `is_lock γ lk s R` keeps its interface; `lock_inv` becomes
  objective by storing `∃V. lk-word-history-tied V ∗ @V R`: release (fence
  rw,w + sw) deposits the holder's view at the new lock-word message's
  timestamp; acquire (`amoswap.w.aq`) reads the latest lock word, joins that
  timestamp into vrNew/vwNew, and the acquire leaf turns "my view now covers
  the depositor's floor" into `R` via the split axiom. Re-prove
  acquire/release once; **lock clients are untouched in statement**. The
  same pattern reworks the escrows that carry memory (`StartedInv`'s
  payload becomes `@V`-frozen with `⊒V` delivered by the spin-read + fence).
- WP: `vProp`-level `WWP Loop` (Φ-free since main's postcondition removal;
  `WeakGhost.wwp_triv`) defined over the base WP à la Cosmo
  (`wp e := λ V, ∀ V' ⊒ V, seen V' -∗ base_wp …`). The `wp_exec_step`
  layering, masks-at-⊤ discipline, and `iInv` patterns survive with
  objectivity side conditions where invariants open.

## Decision 6: devices, MMIO, DMA, fetch, translation

- **Disk DMA gets a view.**  SUPERSEDED (2026-08-17) by
  [`weak-memory-m5.md`](weak-memory-m5.md): the device is a program that
  acquire-loads `avail->idx` and reads/writes at its own view; the notify
  carries NOTHING.  Historic text follows. The disk agent's `wstate` advances when the hart
  writes the queue-notify MMIO register: the notify transaction carries the
  writing hart's current view floors to the device, and `DiskStepDma`'s
  `mem_view` reads through the device's view (per-byte staleness allowed
  below it) instead of the flat map. DMA writes append to `glog` as the disk
  agent. The wild/stalled arms are unchanged.
- **MMIO ordering: model the architecture strictly; fix the driver, not the
  model.** RISC-V FENCE has separate device-I/O bits (PI/PO/SI/SO);
  accesses to the virtio-mmio window (PMA IOMemory) are class I (reads) /
  O (writes), not R/W. So a `fence rw,rw` before the QUEUE_NOTIFY
  store does NOT order the RAM ring writes (class W) before the MMIO store
  (class O) — that needs `fence w,o` — and the completion path's MMIO
  status read vs RAM used-ring reads needs `fence i,r` (exactly what
  Linux's riscv `writel`/`readl` emit: `__io_bw() = fence w,o`,
  `__io_ar() = fence i,r`). That `rw,rw` was the old `__sync_synchronize`
  driver, which worked only because QEMU and typical interconnects order
  these edges anyway. DECIDED (2026-08): the model
  classifies MMIO accesses by the I/O fence bits — no permissive
  accommodation of a driver that does not fence I/O. **The driver side of
  this is already in the tree**: virtio_disk.c's four barrier sites are
  `io_fence()` = `fence iorw,iorw` (`0ff0000f` in `kernel.asm`), which
  subsumes both `w,o` and `i,r`, so the M5 patch is spent and only the
  model half is owed. The verification forcing this is the system working
  as intended.
  Mechanically: the device-agent view advances only per the hart's
  I/O-ordering state, so a missing `fence w,o` leaves the DMA `mem_view`
  able to read the ring stale — which is what makes the driver proof fail
  without the patch. Caveat to resolve early in M5: the generated Sail
  model's `barrier_kind` vocabulary (`Barrier_RISCV_rw_rw` … `_tso`, `_i`)
  is MEMORY-only, so check how the model decodes/executes FENCE words with
  I/O bits set (they must not be dropped; if the Sail model normalizes them
  away, the fence kinds need to be recovered at the `run` layer from the
  instruction word, or the model config fixed).
- **Instruction fetch and page-table walks are PLAIN WEAK LOADS — found at
  M1a, superseding the planned coherent-read dispatch.** rv64d picks
  read/write kinds from the (aq, rl, reserved/conditional) flags alone;
  `AK_ifetch`/`AK_ttw` are never emitted — fetch (`fetch_bytes`) and the
  walker (`read_pte`) are indistinguishable from `lw` at the interface
  seam (the coherent arms exist in `WeakInterp` but are dead for rv64d).
  This is FINE, and better than the old plan:
  - Fetch: kernel text bytes have exactly one message (timestamp 0), so
    every admissible weak read agrees and fetch stays deterministic — no
    assumption needed for kernel text. USER text (written by exec) is
    ordinary weakly-read memory, covered by the same lock/view discipline
    as any data. What remains declared is only **no-icache**: real
    hardware has incoherent icaches and xv6 issues no `fence.i` (a real
    upstream gap); our model has no icache, hence is stronger than such
    hardware on this one axis.
  - Walks: a walk is a weak read at the hart's own views — SOUND (more
    behaviors than an SC walker, in the safe direction) and arguably
    faithful: same-hart PTE writes are seen via coherence, cross-hart
    staleness composes with the existing TLB model (the orthogonal axis;
    sfence.vma stays outside RVWMO by the spec's own statement). **The
    planned SC-walker declared assumption is DROPPED** — walks need no
    special arm at all. PTE A/D updates are plain stores to the log.
- **UART/PLIC**: never touch RAM; unchanged.
- **Crash/power**: a PowerOn resets `glog` to empty over the new `gmem0`
  (boot image) and zeroes every `wstate` — the generation machinery is
  untouched; the durable disk image lives device-side as today.

## Migration strategy (the 734-file question)

The explicit-cpuid retrospective applies verbatim: staged expand/contract,
never big-bang, with the porting guide written BEFORE the sweep. What makes
this tractable:

- Statements are overwhelmingly `↦ₘ`/`↦ᵣ`/`instr`/WP-shaped; `↦ᵣ`, `instr`,
  `↦□` are objective and `↦ₘ`'s rules are SC — so the sweep is mechanical
  for every function proof that takes and returns its memory. Genuinely new
  proofs: the base logic + adequacy, the leaf WP files' memory arms, WpLock,
  the fence leaves, StartedInv-style escrows, and the virtio cone's device
  seam. The interesting *spec* changes are confined to the sync primitives.
- **The pinned-fragment transfer bridge (found at M2a) is the sweep's
  force multiplier — LANDED at M2b as `iris/WeakBridge.v`.** Every existing
  decode lemma (~1220) and exec-level instruction leaf is stated over
  `RiscvExec.exec` / `mstate` (flat mem). When every read of a run is
  PINNED, the collapse lemma (`readable_latest_pin`) says each read returns
  `wflat`'s value, so `wexec` on `wmstate` corresponds to `exec` on
  `wflat_st σ = MState (wm_regs σ) (wflat (wm_img σ) (wm_log σ)) (wm_dev σ)`
  — both directions, `exec_of_wexec_pinned` (what a leaf CONSUMES inside
  `wp_wexec_step`'s ∀-oracle continuation) and `wexec_of_exec_pinned` (the
  reducibility witness), packaged as `wexec_pinned_agree`. A read is pinned
  three ways: the access kind forces it (`ak_coh`, and `ak_latest` — so
  **every AMO read transfers with no ownership at all**), the byte is owned
  at the hart's index, or the byte was never written this era (all kernel
  text: so fetch and decode ride for free). Only genuinely racy DATA
  accesses (lock words, `started`, virtio ring) drop to the weak arm and get
  new leaves — which is exactly the design's intended split. Port no leaf by
  hand that the bridge can carry.
- **The step CERTIFICATE is the sweep's second force multiplier — LANDED at
  M3b as `iris/WeakCert.v`.** The per-instruction obligation the bridge does
  NOT discharge is the structural one — "which bytes does this step touch",
  i.e. `WeakBridge.wstep_ok` over the whole `riscv_step` — and M3a estimated
  it at the size of the model walk `exec_riscv_step_hart_active` /
  `exec_hart_active_progress` do, per instruction. It is instead ONE
  instruction-independent theorem: run the SC interpreter on a memory
  RESTRICTED to the instruction's window, and since `exec`'s read arm fails on
  an absent byte, every read is inside the window by construction (writes by
  the final memory's domain; `Choose` is impossible because `exec` is stuck
  there). Per instruction the cost drops to re-instantiating the leaf's OWN
  SC lemma at the restricted state. What the certificate cannot give is the
  instruction's weak-memory EFFECT (`.aq` raising the scalar floor, the fence
  moving the index, the store's message identity) — `exec` ignores access
  kinds and barriers, so that stays a per-instruction ISA obligation, and only
  the three sync instructions have one. CORRECTED at batch 5: a racy READ's
  view GAIN ("the timestamp behind the byte I read is under my read floor")
  looked like it belonged in this class and does not — the bridge's own
  traversal already knows the timestamp list, so it is a theorem
  (`WeakRacy.wgain`, from `exec_of_wrun_gain`), not a premise. Check the
  bridge before making a leaf pay for a view fact.
- Build the new tree in parallel namespaces first (M0–M3 touch no existing
  file), validate the interfaces on a vertical slice (spinlock + one client
  cone + the started handoff), THEN sweep.
- `tools/lemma_diff.py` + `spec_vacuity.py` after every ported batch; the
  final `Print Assumptions` diff must show: 5 platform axioms + funext + the
  4 assumed kernel contracts + the NEW declared assumptions
  (store-reordering gap/M6, MMIO-ordering, no-icache) and nothing else
  (the SC-walker assumption was dropped at M1a — walks are weak reads).

## Validation

The model is hand-rolled; transcription errors are the top risk. Standing
obligation from M0 on: a litmus suite (SB, MP±fences, LB (must be
UNOBSERVABLE promise-free — documents the gap), CoRR, IRIW, MP+amoswap.aq,
release-fence variants) as executable `exec`-oracle lemmas checked in CI,
with expected verdicts taken from riscv.cat/herd. Divergences from the
axiomatic model other than LB are bugs.

## Rejected alternatives (decision record)

- **AxSL/opax over axiomatic RVWMO**: faithful incl. LB, but incompatible
  with the operational adequacy/device/power architecture; no coherence
  reasoning; would orphan the entire WP stack. Fallback only.
- **Full promising machine day-1**: unsound-in-vanilla-Iris (transfinite
  certification indexing); doomed-run reads break safety statements without
  SLR-style erasure machinery. Deferred to M6 as ONE option.
- **Ztso as the model**: spec-sanctioned but assumes hardware most RISC-V
  parts don't provide; would still need all the view infrastructure to state
  (TSO = the same machine with implicit RCpc annotations), so it buys only
  weaker theorems, not less work. Could become a cheap intermediate
  *instantiation* if migration wants a half-step.
- **SC + informal DRF claim**: not a theorem; RVWMO has no DRF-SC result
  covering xv6's fence-based (genuinely racy) idioms, and stating one
  requires formalizing the weak model anyway.
