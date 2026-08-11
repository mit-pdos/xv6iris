# SC parity for lock-disciplined code (PROPOSAL — §5.1 built, §6.2 settled)

> **Status.**  Landed: §5.1 (the algebra, `iris/WeakViewMono.v`) and §5.4
> (`↦o` with fractions, `iris/WeakPtOwn.v`).  Risks §6.2 and §6.1 are both
> checked and resolved (`iris/WeakViewRacy.v`, `iris/WeakPtOwn.v`).
> Obligations §5.2, §5.3, §5.5, §5.6 are NOT built, and nothing in the tree
> consumes any of it yet — `WeakGhost.hart_ws` is still the exact-valued
> `ghost_var` every leaf threads.
>
> **One design change from what §3 below proposes**, made while building
> §5.4 and load-bearing for the §6.1 result: the coverage fact lives INSIDE
> the points-to, as a per-hart `coh_lb` conjunct, rather than as a global
> `wmstate_interp` invariant over a registry of owned locations.  See §3a.

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

### 3a. What was actually built, and why it differs

`iris/WeakPtOwn.v`.  The registry-plus-invariant shape above turned out to
be the wrong factoring.  What is built instead is:

```coq
Definition wpt_own (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
  ∃ t, wlat_pointsto a dq t v ∗ wflr_lb a t.
```

where `wflr_lb a t` is the persistent, per-hart ghost floor from
`WeakViewMono` — `coh_lb (γ c) a t ∨ mono_nat_lb_own (vrNew (γ c)) t`,
matching `flr (ws_view ws) a = max (w_vrNew ws) (coh ws a)` on the nose so
that both directions of the bridge below are exact.

Read the two side by side and the whole idea is one substitution:

| | second conjunct | altitude |
|---|---|---|
| `WeakVProp.wpt` | `⊒(view_byte a t)` — *the index THIS ASSERTION is read at covers `t`* | `vProp`, subjective |
| `WeakPtOwn.wpt_own` | `coh_lb (γ c) a t` — *hart `c`'s floor at `a` covers `t`* | `iProp`, objective |

Same content; the difference is that one constrains the assertion's own
`monPred` index and the other is a ghost fact about a **named hart**.  That
is what makes it objective, and being a lower bound on monotone ghost state
it is also persistent — so it survives every intervening step for free.

This is not a new axiom, it is the generalisation of something already in
the tree: `WeakVProp.wpt_img` is exactly the `t = 0` case, objective because
`view_byte a 0` is the bottom view.  Its header says the converse is false
for `t > 0` — "a hart that has not observed that timestamp cannot read the
byte".  Naming the hart is what repairs that.

**The drop-in theorem** is what makes this cheap rather than a rewrite:

```coq
Lemma wpt_own_to_wpt a dq v w : ws_auth γv w -∗ wpt_own γv a dq v -∗
                                ws_auth γv w ∗ vwp_hold (a ↦w{dq} v) w.
Lemma wpt_own_of_wpt a dq v w : (* the exact converse *)
```

Under the authority at the true state the two points-to's are
**interchangeable**, so every rule already stated over `wpt` — the whole of
`WeakVProp`, `WeakInstr`, `WeakStore` — applies to `↦o` by sandwiching, and
nothing has to be re-derived.  `wpt_own_load_rule` is `wpt_load_rule` with
its rebasing side condition and its threaded post-state deleted, which is
the SC shape verbatim.

**Objective but NOT hart-agnostic.**  `↦o` is tied to a hart — currently an
explicit `γv : wview_names` parameter, in the real wiring
`weak_view_name cpu_id`, a `weakGS` field mirroring the existing
`weak_ws_name : CPU → gname`.  That tie is the mechanism, not an artifact:
the floor is a fact about one hart's view.

Objectivity makes `⎡↦o⎤` admissible in an invariant, but a whole `↦o` in a
SHARED invariant is sound and useless — hart B opening it gets
`coh_lb γ_A a t`, and reading the byte needs `ws_auth γ_A w`, which B does
not hold.  That is the model being right: B has not synchronised, so B may
genuinely read stale.  Nothing unsound comes of a mismatched `γv` either;
`wpt_own_to_wpt` just yields a `vwp_hold` at the wrong hart's state, which no
leaf can consume.

So: the `wlat_pointsto` element is hart-agnostic and transfers freely; the
floor is not.  A shared invariant should hold the **element**, with the
acquire minting the acquiring hart's floor.  Lock CLIENTS — the SC-parity
case — never see any of this, because within one hart the floor never moves.

**What this costs.**  Soundness now rests on the acquire handing out a
points-to that already carries the right floor, rather than on a global
invariant.  That is the same obligation as before, moved: §5.5 and risk §6.3
now carry all of it, and §5.3 as originally written is not needed.

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

1. **The algebra.** — **LANDED**, `iris/WeakViewMono.v`.  `auth cohUR` × 5
   `mono_nat`; `ws_auth` the authority, `ws_lb` the persistent floor,
   `ws_update` ("any `ws_le`-larger state is reachable", and crucially the
   caller does not name the old value), `ws_lb_valid` (`ws_le w0 w`),
   `ws_lb_mono`, `ws_alloc`, and the opaque token `hart_view γ := ∃ w,
   ws_auth γ w` with `hart_view_step` / `hart_view_snapshot`.

   Two things had to be got right, both recorded in the file:

   - **The coherence camera is NOT `auth (gmap Z max_nat)`.**  `gmap`
     inclusion is pointwise inclusion in `option`, and `Some x ≼ None` is
     FALSE — so a state carrying an explicit zero entry is not included in
     one omitting the key, even though `ws_le` holds (both read `coh _ a =
     0` through the `default 0`).  Any `ws_le → ≼` lemma against the naive
     encoding is unprovable.  The camera used is
     `cohUR := discrete_funUR (λ _ : Z, max_natUR)`, for which pointwise `≤`
     IS inclusion on the nose.  This matches the intended semantics rather
     than patching it: `ws_le`'s coherence conjunct is already stated over
     the TOTAL `coh`, not over the map.
   - **The `Finite` side condition does not bite.**  Iris states the `↔`
     between inclusion and pointwise inclusion (`discrete_fun_included_spec`)
     only for a `Finite` index, which `Z` is not.  It is not needed: that
     restriction exists because a general camera's difference must be built
     pointwise by choice, and for a max-camera the witness for `f ≼ g` is
     `g` itself.  `coh_fun_incl` is three lines.
2. **Re-base `wmstate_interp`** on the new authority and repair
   `hart_ws_agree`'s consumers.
3. ~~**The coverage invariant** as a `wmstate_interp` conjunct.~~ — **NOT
   NEEDED** in this form; superseded by §3a, which carries the floor inside
   the points-to.  Preservation comes free from `ws_le` monotonicity (the
   floor is a lower bound on monotone ghost state); establishment is
   obligation 5.
4. **`wpt_own` and its two rules**, stated in SC's shape. — **LANDED**,
   `iris/WeakPtOwn.v`: the points-to, the `Fractional`/`AsFractional`
   instances, agreement/validity/persist, `Objective`, the drop-in bridge
   both ways, `wpt_own_load_rule` and `wpt_own_flat_lookup` in SC's shape,
   and `wpt_own_survives_step` (whose proof does not use its `ws_le`
   hypothesis — there is nothing to rebase).
5. **The `↦o` / `↦w` boundary**: acquire moves ownership INTO the covered
   registry, release moves it OUT.
6. **One leaf** end to end, then one function, then measure against SC.

---

## 6. Risks — the three places this could fail

Recorded so the next person does not have to rediscover them.  None of the
below has been checked.

1. ~~**Read fragments.**~~ — **RESOLVED by §3a's factoring**, which is most
   of the reason for that factoring.  The worry was that coverage has to be
   stated per-fragment-holder rather than per-exclusive-owner, and that the
   ghost accounting might not support it.  Putting `wflr_lb` inside the
   points-to makes it per-fragment **by construction**: each fragment
   carries its own hart's floor, two harts sharing `dq = 1/2` hold two
   DIFFERENT `coh_lb`s, and each is separately true.  There is no single
   "the view" that has to be split, so there is no accounting to get wrong.

   `WeakPtOwn.wpt_own_split` is the `⊣⊢`.  The `→` direction is free — the
   element halves, the floor is persistent and duplicates.  The `←`
   direction has exactly the content the subjective `wpt_split` has and no
   more: two points-to for one byte may a priori carry different timestamps,
   and element agreement forces them equal before the fractions recombine.
   `wpt_own_load_rule` is stated at arbitrary `dq`, so a fractional
   objective points-to reads exactly like a full one.

   The residual obligation is not gone, it MOVED: an acquire must hand out a
   points-to already carrying the right floor.  That is now entirely §5.5 /
   risk 3 below.
2. ~~**Exactness vs lower bounds.**~~ — **CHECKED, AND IT IS FINE.**
   `iris/WeakViewRacy.v`.  The worry was that `WeakRacy.wp_wracy_load`
   quantifies over the ADMISSIBLE READ RESULTS, computed from the hart's
   actual weak state, which a lower bound might under-determine.

   It does not, because **admissibility is ANTITONE in the hart's state**.
   `WeakInterp.wbyte_ok` depends on `wm_ws` only through

   ```coq
   readable img log ws vpre a t :=
     is_Some (log_byte img log t a) ∧ ¬ writes_in log a t (Nat.max vpre (coh ws a))
   ```

   with `load_vpre ws aq := Nat.max (w_vrNew ws) (…)`.  A LARGER `ws` raises
   the exclusion window and therefore excludes MORE timestamps.  Racy clients
   only ever want to SHRINK the admissible set — to rule out stale reads —
   and shrinking is driven by knowing the hart's view is at least something.
   That is exactly a lower bound.

   The landed exclusion lemmas already say so in their own statements:
   `WeakKpt.wbyte_ok_ge` and `wbyte_ok_variant_from` each take
   `(tc ≤ w_vrNew (wm_ws s))%nat` — a bare inequality, not an equation.
   `WeakViewRacy.wbyte_ok_ge_from_lb` discharges it from `ws_lb` alone, and
   `wracy_exclusion_after_step` shows the floor snapshotted at the OLD state
   still lands the exclusion at the NEW one, across an arbitrary `ws_le`
   step, with nothing rebased.

   **So no exact fragment is needed anywhere.**  One persistent `ws_lb` is
   the single client-facing fact for the owned layer and the racy layer
   alike, and the racy layer survives the change unchanged.
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

---

## 8. The composability problem, and `wobj` (LANDED — `iris/WeakObj.v`)

**Raised by the user, 2026-08-11.** §5.5 landed two conversions at the lock
boundary, `wpt_own_release` and `wpt_pub_acquire`. Both are stated at a
single byte. That is fine for a byte and useless for anything real: a
composite predicate — an fd table, a buffer cache entry, anything built from
points-to facts nested several definitions deep — is a *different
proposition* on the two sides of the boundary. So it would have to be
written twice, or carry a `T` parameter threaded through every definition
and every intermediate lemma. That is a tax on all client code, levied for a
boundary the client is not reasoning about.

### The resolution

The parameter you would be threading by hand is **exactly what `vProp` is**,
and `monPred_at R V` instantiates it *without unfolding `R`*. The freezing a
lock does was never a rewrite of the payload; it is one application of
`monPred_at`. So:

```coq
Definition wobj (R : vProp Σ) : iProp Σ := ∃ V, view_lb V ∗ monPred_at R V.
```

— "R holds at some view I have already reached". `view_lb V := ∀ a, wflr_lb
a (flr V a)` is §3's per-byte floor lifted to a whole view, stated pointwise
through `flr` so its validity *is* `wflr_lb_valid` at every `a`.

What this buys, all for **arbitrary `R`**:

- `wobj R : iProp` ⇒ objective ⇒ invariant-admissible, no `wstate`
  threading. The §3 property, without §3's construction.
- Structural laws for `∗ ∃ ⌜⌝ ∨ emp ⎡⎤ ▷ big_sepM big_sepL`. **These are the
  transport.** No definition below the boundary is restated,
  reparameterised, or reproved — which is the whole answer to the question.
- `wobj_release` / `wobj_acquire` / `wobj_handoff`: §5.5's conversions off
  the single byte. One lemma each. The lock's side conditions are unchanged,
  but are now paid once for the whole payload rather than once per byte.
- `wobj_to_hold` / `wobj_of_hold` against `vwp_hold`, so a caller can hold a
  frame objectively and hand it to an **unmodified** leaf. This is what lets
  a leaf wrapper carry a real frame instead of discharging it at `⌜True⌝`
  the way `WeakLeafO.wwp_lui_o` does.

And `wpt_own_wobj : a ↦o{dq} v ⊣⊢ wobj (a ↦w{dq} v)` — **§3 was never a
separate construct.** It is this modality at a single byte, and everything
in §5.5 generalises.

### Honest limits

- `wobj` does **not** commute with `∀` in the useful direction: `∀ x, wobj
  (Φ x) ⊬ wobj (∀ x, Φ x)`, because each `x` may hold at a different view and
  there is no join over an infinite family. Finite conjunctions and
  `big_sepM` over a finite map are fine, which is what data-structure
  predicates actually use.
- Nor with `-∗` or `→`, in either direction — same reason it does not for
  `monPred_at`.
- `▷` passes *out* of the modality freely but back *in* only up to `◇`
  (`wobj_later_1` / `wobj_later_2`): the floor is timeless, not later-free.
  Free wherever an invariant is being opened.

### A note on the typeclass alternative

The natural first guess is a "current view" typeclass that a hart and a lock
invariant both instantiate, so `↦o` refers to whichever is ambient. That does
give write-once definitions — but it threads the parameter *syntactically*,
at the Coq level, so the acquire-time conversion `fdtable (LockView T) ⊢
fdtable (HartView c)` still needs a congruence lemma **per definition**,
which is the cost we were trying to avoid. `monPred` threads the same
parameter *semantically*, which is precisely why its conversions are generic
in `R`. The typeclass idea is right; `vProp` is its principled form, and
`wobj` is the adapter that makes the result an objective `iProp` at both ends.

### What this changes about the plan

§3's `↦o` stops being the primitive and becomes a derived instance. Client
data-structure predicates should be written as **`vProp`s over `↦w`**, and
`wobj` applied at the two places where objectivity is actually needed: the
lock invariant, and the caller's frame. Nothing in the leaf layer changes.
