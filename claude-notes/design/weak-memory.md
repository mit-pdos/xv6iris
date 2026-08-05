# Design: weak memory (RVWMO) — PROPOSAL, nothing landed

STATUS: design proposal (2026-08). No code. The staged worklist is
[`projects/weak-memory.md`](../projects/weak-memory.md). Everything below is a
plan to be validated by the M0 spike; decisions here are starting positions,
not settled law like the other design files.

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
What that machine is, honestly:

- It is RVWMO **minus load buffering**: reads may be arbitrarily stale
  (bounded by views), stores enter the global order in each hart's program
  order. SB, MP-weak, CoRR, IRIW-MCA behaviors all present; LB absent.
- The gap is *directional in our favor for every fenced idiom*: a store
  preceded (transitively) by `fence rw,w`/`fence rw,rw`, or ordered after an
  acquire-AMO, cannot be promised early in the full machine anyway — its
  fulfilment pre-view would exceed the promised timestamp. xv6's entire
  cross-hart discipline (lock CS stores bracketed by aq-AMO and
  fence-release; the `started`/`first`/virtio sites bracketed by
  `fence rw,rw`) is in that class. The gap is real only for racy unfenced
  stores, which the verified kernel should not have.
- **The LB gap is a documented model assumption until M6** (the robustness
  theorem: for release-fenced/lock-mediated programs, full-machine behaviors
  = promise-free behaviors — provable at the operational level, no Iris,
  as a separable research artifact; SLR/PS1's DRF-promise theorems are the
  language-level precedent). This is the same epistemic category as the 5
  `rv64d.*` platform axioms: stated once, visible in the final theorem's
  footprint, discharged by later work. Full promises-in-logic (SLR-style)
  stays on the shelf unless robustness fails.

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
  halves interleave with nothing. Atomicity + coherence force the read to
  take the per-byte **latest** message; the write appends. `.aq` applies the
  acquire updates to the read half; `.rl` the release side (raises the
  store's effective pre-view — inert constraint promise-free, but keep the
  bookkeeping so `w_vRel` is honest).
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

**Surface layer**: `vProp := monPred (View, ⊑) (iProp Σ)` where
`View := gmap Arch.pa nat` (per-byte observation floors; a hart's logical
view is `λ a. w_vrNew ⊔ w_coh(a)`-shaped). Iris 4.4's monPred + proofmode
support is battle-tested (iRC11/gpfsl track modern Iris). The pieces:

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
- **Fence modalities** for the `fence rw,rw` publication sites:
  `Δ P` ("P at my release floor" — what a later store publishes) and
  `∇ P` ("P at my acquire frontier" — what a later succ-R fence delivers),
  with `{P} fence-with-pred-RW {Δ' …}`-style leaf rules mapped onto the
  vrOld/vwOld→vrNew/vwNew lattice. Ghost state passes through both freely.
- **Locks**: `is_lock γ lk s R` keeps its interface; `lock_inv` becomes
  objective by storing `∃V. lk-word-history-tied V ∗ @V R`: release (fence
  rw,w + sw) deposits the holder's view at the new lock-word message's
  timestamp; acquire (`amoswap.w.aq`) reads the latest lock word, joins that
  timestamp into vrNew/vwNew, and the acquire leaf turns "my view now covers
  the depositor's floor" into `R` via the split axiom. Re-prove
  acquire/release once; **lock clients are untouched in statement**. The
  same pattern reworks the escrows that carry memory (`StartedInv`'s
  payload becomes `@V`-frozen with `⊒V` delivered by the spin-read + fence).
- WP: `vProp`-level `WP Loop {{ Φ }}` defined over the base WP à la Cosmo
  (`wp e := λ V, ∀ V' ⊒ V, seen V' -∗ base_wp …`). The `wp_exec_step`
  layering, masks-at-⊤ discipline, and `iInv` patterns survive with
  objectivity side conditions where invariants open.

## Decision 6: devices, MMIO, DMA, fetch, translation

- **Disk DMA gets a view.** The disk agent's `wstate` advances when the hart
  writes the queue-notify MMIO register: the notify transaction carries the
  writing hart's current view floors to the device, and `DiskStepDma`'s
  `mem_view` reads through the device's view (per-byte staleness allowed
  below it) instead of the flat map. DMA writes append to `glog` as the disk
  agent. The wild/stalled arms are unchanged.
- **MMIO ordering is a declared platform assumption.** Strictly, `fence
  rw,rw` (I/O bits clear) does not order RAM writes before an MMIO store —
  xv6 would need `fence w,o`; QEMU and common implementations order them
  anyway. We model MMIO stores as waiting on `w_vwNew` (so `fence rw,rw`
  covers the virtio ring→notify edge) and record this next to the platform
  axioms. Revisit if the model should someday expose the strict reading.
- **Instruction fetch (AK_ifetch)**: reads stay coherent-SC. Kernel text is
  immutable post-boot (single message per byte ⇒ no weakening exists to
  express); user text written by exec is covered by xv6's own
  coherent-icache assumption (it uses no `fence.i` — upstream shares this);
  declared alongside the MMIO assumption.
- **Page-table walks (AK_ttw) / sfence.vma**: outside RVWMO by the spec's
  own statement. The walker keeps reading the coherent latest state;
  the existing TLB model remains the (orthogonal) staleness axis. Declared.
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
- Build the new tree in parallel namespaces first (M0–M3 touch no existing
  file), validate the interfaces on a vertical slice (spinlock + one client
  cone + the started handoff), THEN sweep.
- `tools/lemma_diff.py` + `spec_vacuity.py` after every ported batch; the
  final `Print Assumptions` diff must show: 5 platform axioms + funext + the
  4 assumed kernel contracts + the NEW declared assumptions (LB-gap/M6,
  MMIO-ordering, coherent-ifetch, SC-walker) and nothing else.

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
