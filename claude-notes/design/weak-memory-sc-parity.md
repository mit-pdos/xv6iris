# SC parity for lock-disciplined code (PROPOSAL — nothing here is built)

Sibling of [`weak-memory.md`](weak-memory.md), which is the RVWMO model
proper.  This file is about a narrower question:

> **Can a function that follows locking discipline be proved under the weak
> model with the SAME proof it has under SC?**

"Locking discipline" means: the function touches only memory it owns —
privately, or through a lock it holds — and every cross-hart transfer of
memory goes through an acquire/release pair.  That is the regime nearly the
whole kernel is in; the exceptions are the lock implementation itself, the
`started` one-shot flag, and (later) the virtio ring.

The target is **unchanged proof text above the leaves**.  Leaves are
expected to be rewritten; that cost is per instruction SHAPE and amortises.
What must not cost anything per FUNCTION is the porting of the code above
them.

---

## 0. Where the current 3× comes from (measured, not estimated)

`WkStartNew.wwp_start` (39 instructions) against `WpStartNew.wp_start`: 471
SC proof lines vs ~1400.  Per instruction, categorised:

| what | lines/instr | weak-memory content? |
|---|---|---|
| `Hal2_`/`Hal4_`/`Hacc_`/`Hram_`/`Hcond_` asserts | 6 | no — decode/text scaffolding |
| `winstr_bytes_of_text` + `wkb_window` block | 4 | no |
| the `kd_*` ∀-state decode lambda | 2–3 | no |
| `assert (P_n)` + two `iEval (rewrite P_n)` | 3 | no — SC inlines this in one |
| **`vwp_hold_mono` bump** | **1** | **yes — all of it** |
| leaf application + register bookkeeping | ~8 | matches SC |

So ~15 of ~25 lines were an interface tax and exactly ONE line was weak
memory.  Two of the three causes are already fixed on the branch:

- **`iris/WeakLeafM.v` (landed)** — `winstr_m`, the leaf-altitude twin of
  SC's `InstrBytes.instr`, minted once per instruction in an aux file.  This
  deletes the whole decode/alignment block.  `wwp_lui` is the worked
  wrapper; ~19 remain.
- **frame threading (landed)** — a leaf takes `(F : vProp Σ)` and
  `vwp_hold F ws`, returns `vwp_hold F ws'`, and does the `vwp_hold_mono`
  itself.  `F` is inferred by unification, so the call site pays one `_`.

Measured on instruction 35 (`c.lui`): **28 → 12 → 11 lines**, vs SC's 6.
What remains is the `ws` binder, the `⌜ws_le ws ws'⌝`, and pc bookkeeping.

**This document is about the residue, and the claim is that it is entirely
an artifact of two representation choices — not of weak memory.**

---

## 1. The two representation choices

### 1a. The hart's weak state is an EXACT-valued ghost var

```coq
Definition hart_ws (c : CPU) (ws : wstate) : iProp Σ :=
  ghost_var (weak_ws_name c) (1/2) ws.
```

`ghost_var` can only be updated by naming both the old and the new value.
That — and nothing else — is why every leaf reads `ws` in, `ws'` out, and
carries `⌜ws_le ws ws'⌝`.  It applies even to instructions that touch no
data at all: `c.lui` still advances the hart's view, because **every
instruction fetches its own text and the fetch is an ordinary view-raising
weak read** (`WeakFetchEff.wak_plain` — rv64d emits `Read_plain` for
instruction fetch, not `AK_ifetch`).

### 1b. The points-to is subjective, and that is ONE conjunct

```coq
Definition wpt (a : Z) (dq : dfrac) (v : bv 8) : vProp Σ :=
  (∃ t : nat, ⎡ wlat_pointsto a dq t v ⎤ ∗ ⊒(view_byte a t))%I.
```

`WeakVProp.v`'s own comment: the first conjunct is the base-layer element
and is **objective** (an embedded `iProp`); the second "is the receipt that
makes the assertion SUBJECTIVE, and is the entire difference between this
and the SC points-to."

---

## 2. Part I — the monotone view (the load-bearing half)

**`ws_le` is pointwise `≤` on every field, with no non-monotone
component:**

```coq
Definition ws_le (w1 w2 : wstate) : Prop :=
  (∀ a, (coh w1 a ≤ coh w2 a)%nat) ∧
  (w_vrOld w1 ≤ w_vrOld w2)%nat ∧ (w_vwOld w1 ≤ w_vwOld w2)%nat ∧
  (w_vrNew w1 ≤ w_vrNew w2)%nat ∧ (w_vwNew w1 ≤ w_vwNew w2)%nat ∧
  (w_vRel  w1 ≤ w_vRel  w2)%nat.
```

So `wstate` under `ws_le` is a product of `auth (gmap Z max_nat)` (the
per-byte coherence floor, whose `flr` semantics is already "default 0", i.e.
pointwise max) and five `mono_nat`.  Entirely standard Iris algebra.

**Replace the `ghost_var` with that authority and hide its value:**

- `hart_view c` — the authority, value existentially quantified INSIDE the
  definition.  A leaf takes it and hands it back; the step obligation is
  "there EXISTS a larger `wstate`", which the leaf discharges internally.
  No binder, no `ws_le`, nothing visible above the leaf.
- `view_lb c V` — the `◯`, **persistent and duplicable**.  Code that cares
  about views (§4) snapshots before a step and relates after.

The idiom is already native to the file: `wpt`'s `⊒(view_byte a t)` IS a
view lower bound.  What is new is applying it to the hart's own state.

**Why this is stronger than the frame threading already landed.**  Frame
threading HIDES the `vwp_hold_mono`; monotone ghost state makes it
**unnecessary**.  An untouched fact does not have to be moved from `ws` to
`ws'` — a persistent lower bound is simply still true.  This subsumes the
frame-parameter work, and it does so for subjective resources too, not only
objective ones.

---

## 3. Part II — the objective points-to for owned memory

For memory under locking discipline, drop the receipt:

```coq
Definition wpt_own (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
  ∃ t, wlat_pointsto a dq t v.
```

An `iProp`.  Objective.  No view coordinate.  **This is an SC points-to.**

Soundness rests on one theorem, which is what makes locking discipline pay:

> **OWNERSHIP-COVERAGE INVARIANT.**  For every element fragment a hart
> holds, that hart's index covers the element's timestamp.

Both halves already exist as landed lemmas:

- **establishment** — an acquire's view-raising edge (`amo_acq_gain`, the
  `WeakAcquire` transfer);
- **preservation** — `WeakInstr.wstep_post`'s `ws_le` conjunct: views only
  grow, so once covered, always covered.

What is missing is stating it ONCE as a `wmstate_interp` conjunct instead of
re-carrying it in every assertion.  With it, `wpt_own`'s load and store
rules are SC's verbatim, at `iProp` altitude.

### The boundary — deliberately two points-to's

- **`↦o` (objective, `iProp`, SC rules)** — private and lock-protected
  memory.  Everything above it transplants.
- **`↦w` (subjective, `vProp`, current rules)** — the racy sites ONLY: the
  lock word, the `started` flag, the virtio ring.

These MUST stay subjective: the entire content of `WeakStarted` is that a
reader may legally observe a stale message, which is precisely the coverage
invariant failing at an unowned location.  That is not a gap — it is the
theorem the escrow exists to prove.

And it does not leak upward: the porting guide already records that the
lock's exported interface is unchanged (`wlocked γ i` IS `WpLock.locked
γ i`), so clients of the lock never see a view.  **The lock implementation
pays the weak-memory cost once, on behalf of every client.**

---

## 4. Part III — what a leaf then looks like

With §2 and §3, a leaf's statement is its SC twin plus ONE threaded opaque
token:

```coq
  mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
  pc_is pc -∗ gpr_file m -∗ winstr_m pc is_rvc <AST> -∗
  hart_view cpu_id -∗
  ( mmode_config (DfracOwn q) -∗ ... -∗ hart_view cpu_id -∗ WWP Loop) -∗
  WWP Loop
```

No `ws`, no `ws'`, no `ws_le`, no `vwp_hold`.  A caller's per-instruction
text is then the SC text with one extra name in the `with "…"` and
`iIntros` patterns — names that ride inside lines that already exist.  That
is the 1.0× target.

Code that DOES care about views (the lock, the escrow) takes a
`view_lb cpu_id V` snapshot, which being persistent survives every
intervening step for free.

---

## 5. Obligations, in the order they should be discharged

1. **The algebra.** `auth (gmap Z max_nat)` × 5 `mono_nat`; `hart_view` with
   the value existentially hidden; `view_lb` persistent; the update lemma
   "any `ws_le`-larger state is reachable".
2. **Re-base `wmstate_interp`** on the new authority and repair
   `hart_ws_agree`'s consumers.
3. **The coverage invariant** as a `wmstate_interp` conjunct + its two
   obligations (acquire establishes, step preserves).
4. **`wpt_own` and its two rules**, stated in SC's shape.
5. **The `↦o` / `↦w` boundary**: acquire moves ownership INTO the covered
   registry, release moves it OUT.
6. **One leaf** end to end, then one function, then measure against SC.

---

## 6. Risks — the three places this could fail

Recorded so the next person does not have to rediscover them.  None of the
below has been checked.

1. **Read fragments.**  `dq < 1` shared across harts is the case I trust
   least.  The coverage argument should still go through — every fragment
   was obtained through a synchronising edge — but the invariant has to be
   stated per-fragment-holder, not per-exclusive-owner, and it is not
   obvious the ghost accounting supports that.
2. **Exactness vs lower bounds.**  A lower bound is sound in the direction
   owned memory needs: knowing your floor is AT LEAST `V` is what rules out
   reading stale, and a larger real view only makes reads fresher.  The
   opposite direction is the risk: `WeakRacy.wp_wracy_load` quantifies over
   the ADMISSIBLE READ RESULTS, and that set is computed from the hart's
   actual weak state, which a lower bound may under-determine.  If so, keep
   an exact fragment available for the racy sites — `mono` ghost state
   supports both — but this must be CHECKED, not assumed, because it decides
   whether the racy layer survives unchanged.
3. **The boundary seam.**  Ownership must enter and leave the covered
   registry at exactly the acquire/release points.  If a soundness bug
   exists, it is here.

---

## 7. What this does NOT buy

- **The leaf library.**  Objective points-to makes the layer ABOVE the
  leaves free; it does not make the leaves free.  Batch 6's ~42 sconf leaves
  still get written.
- **The racy functions.**  `acquire`/`release`, the escrow, virtio.  Their
  content IS weak memory.
- **Anything about the sconf tier's funnel.**  Orthogonal (batch 6).

The claim is only, but exactly: **for lock-disciplined code, the proof above
the leaves should be the SC proof.**
