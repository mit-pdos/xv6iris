# M6 — closing the store-reordering gap (design)

**Status (2026-08-11): not started; this file is the tee-up.** Everything
below is either (a) established and cited, (b) a decision already taken and
recorded, or (c) explicitly marked OPEN. Read
[`weak-memory.md`](weak-memory.md) Decision 1 first — it states the gap and
why it is safe for this kernel; this file does not repeat that argument, it
says what has to be PROVED and in what order.

---

## 1. What the end-state theorem is

The promise-free machine is scaffolding. The final claim composes three
pieces, only the middle one of which is missing:

```
  [ Iris adequacy over the promise-free machine ]        -- HAVE (M1–M5)
∘ [ M6 robustness: every full-machine execution of      -- THIS FILE
      THIS kernel is matched by a promise-free one ]
∘ [ Promising-RISC-V ≡ axiomatic RVWMO (Pulte et al.) ] -- HAVE (published, Coq)
= adequacy over real RVWMO, with no strengthening in the statement.
```

What we have today, verbatim (`iris/WeakAdequacy.v:91`,
`Theorem weak_system_adequacy`): given the boot resources and a proof of
`WWP` for every hart and device loop,

```coq
  forall t2 g2 e2,
    rtc erased_step (wcpu_pool cs, g) (t2, g2) ->
    e2 ∈ t2 ->
    reducible (Λ := weak_riscv_lang) e2 g2.
```

Two things follow for M6's shape.

- The conclusion is **reducibility over `weak_riscv_lang`** — the
  promise-free machine. Robustness has to transport exactly this, i.e. it is
  a statement relating executions of the SAME program under two machines, not
  a statement about xv6's source.
- It is stated over `rtc erased_step` from the boot state, so the Layer-1
  lemma must be about **reachability from a fixed initial state**, which is
  what makes the PARM `pf_exec` skeleton (below) usable.

**Robustness is a program property** — "this program's reorderings are
unobservable" — not "hardware does not reorder". Keep that framing: it is
what makes the obligation finite and extractable from the Iris proof.

---

## 2. What PARM actually gives us (RESOLVED — do not re-derive)

Read from the snu-sf/promising-arm sources (2026-08). This was the main
unknown and it is settled:

- **The base machine has NO certification.** `Machine.step` lifts
  `state_step ∪ promise_step` with promising unconditional. Doomed threads
  are trivially reachable and are pruned only EX POST: a "behavior"
  (`Machine.exec`) is a run whose FINAL state has all promise sets ⊥. Both
  directions of the axiomatic equivalence, and Thm 7.1, quantify over
  `Machine.exec` only.
- **Consequence (a):** full-machine adequacy must be stated over
  **completable prefixes** — prefixes extendable to a `no_promise`
  completion. Doomed runs are model artifacts hardware never exhibits, which
  is exactly what `Machine.exec` already prunes. Do not try to prove anything
  about arbitrary prefixes.
- **Consequence (b), the important one:** their **Thm 7.1
  (`promising_to_promising_pf`, `PtoPF.v`) is a reusable Layer-1 skeleton.**
  Every behavior factors as a promise PHASE from init, then per-thread
  `state_step`s against FROZEN memory (`pf_exec`). So robustness reduces to:

  > for our kernel, a nonempty front-loaded promise set admits no
  > `no_promise` completion beyond what the empty phase admits

  — a statement about frozen-memory per-thread runs, which is enormously more
  tractable than arbitrary interleavings. **Start here.**
- The certified machine (`lcertify/Certify.v`) checks only the STEPPING
  thread post-step. All-threads-certified is preserved only via
  `interference_certify` (certification survives arbitrary memory extension),
  which exists ONLY for RISC-V (`arch == riscv` hypothesis) — hence Thm 6.3's
  deadlock freedom being RISC-V-only.
- Coq 8.15 + sflib + hahn, ~17k lines; the architecture is a parameter, not a
  separate RISC-V file.

---

## 3. Layer 1 — the operational lemma

Program-independent, no xv6 and no Sail in the statement, no Iris:

> if no promise-free execution of P reaches the **violation pattern**, then
> every full-machine execution of P is matched by a promise-free one (same
> observable states, and reducibility transports).

Proof idea = **delay simulation**: a promise matters only if some other agent
reads it before it is fulfilled; unread promises commute forward to their
fulfilment point; an early read implies the violation pattern *back in the
promise-free semantics* (which is what makes the premise checkable by the
Iris proof rather than by an analysis of the full machine).

Precedents to mine, in order of closeness: PS1 **DRF-Promise** (same
structure at language level), PS2 Thm 6.5, then the robustness literature —
Shasha–Snir, Bouajjani–Derevenetc–Meyer (TSO), Lahav–Margalit (RA).

### THE CRUX, AND IT IS OPEN: what is the violation pattern?

This is the one piece with no candidate written down, and everything else
depends on its exact shape. Constraints it must satisfy:

- **Sufficient** — its absence must really imply the simulation goes through.
- **Checkable from the Iris proof** — it has to be refutable by a per-store
  side condition the WP already establishes, else Layer 2 cannot supply it.
- **The fenced empty-predecessor wrinkle** (recorded, unresolved): a
  release-fenced store with *nothing to order* CAN be promised, and must
  commute harmlessly. So "po-after a release fence" is not by itself the
  right pattern; the pattern has to be about a promise being READ early, not
  about the promise existing.
- **Byte granularity and mixed-size** need care — the log is per-byte
  (`WeakMem.wmsg`), and a promise/fulfilment pair at different widths must
  not fall through a crack.

---

## 4. Layer 2 — what the Iris side must export

The premise of Layer 1, extracted from the WP proof rather than from a
separate whole-program analysis. The intended statement:

> every store is either (i) to bytes the storing hart exclusively OWNS, so no
> other agent can read the promise before fulfilment, or (ii) an enumerated
> FENCED sync site, where certification arithmetic pins the promise —
> fulfilment po-after `fence rw,w` forces the timestamp above everything the
> fence covers.

### What the tree gives today, and what it does not

Every store leaf concludes `WeakInstr.wQ_store_w n tid ea v` (or
`wQ_amo_aq_w`), which says: the message lands at `S (length log)`, the image
is unchanged, views only grow, and the hart's own floor covers the new
message. **That is a statement about the MESSAGE, not about the store's
protection class**, so nothing in the current certificates distinguishes (i)
from (ii). Layer 2 needs a new export.

The store-side surface to cover (all of `iris/`):
`WeakLeafSd8.v`, `WeakLeafSw4.v`, `WeakLeafSdspOff.v`, `WeakLeafTor.v`,
`WeakLeafAmo4Leaf.v` (the invariant-form lock leaf), plus the generic
certificates `WeakCert.wcert_store`/`wcert_amo_aq`/`wcert_amo_aq_pin`,
`WeakEff.wcert_store_gen`/`wcert_amo_aq_gen`,
`WeakEffSkel.wcert_store_via_skeleton`, and the fetch-alignment instances in
`WeakFetchEff.v` / `WeakFetch2.v`.

Two candidate mechanisms — **DECISION NEEDED, this is the first real fork**:

- **(A) Ghost trail.** The state interpretation carries a per-message tag
  beside `wlog_auth`; each store rule sets it; adequacy exports "every
  message in the final log is tagged owned-or-fenced". Costs: touches the
  state interpretation and every store rule (~10 leaves plus the generic
  certificates), i.e. the same blast radius as the width generalization.
  Buys: the premise is a THEOREM of the same Iris proof, with no separate
  argument, and it survives refactors.
- **(B) Meta-theorem over the leaf rules.** Prove, outside Iris, that any
  store admitted by these leaves falls in one of the two classes, by
  inspecting the rules' premises. Costs: a side argument that must be redone
  whenever a leaf is added, and it is not machine-checked against the actual
  call sites. Buys: zero churn now.

Recommendation (not a decision): **(A)**, because the enumeration in (B) is
exactly the kind of "checked once, silently invalidated later" claim this
project has already been bitten by, and because the tag is cheap next to what
6c will cost anyway.

### A THIRD STORE CLASS THE OLD PLAN DOES NOT COVER (new, 2026-08-11)

The M6 block was written before the update cone landed. **The hardware
walker's A/D write-back is a store that is neither software-owned nor
fenced.** In the landed model
(`model-xv6iris/rv64d.v:24965 update_and_write_pte`) it is the conditional
half of a CAS: `read_pte_exclusive` (`Read_RISCV_reserved`) then
`write_pte_conditional` (`Write_RISCV_conditional`), both classifying to
`AkInfo false true false` — exclusive, `ak_latest`, not synchronising
(`iris/WeakUpdEff.v` header).

So the Layer-2 enumeration needs a third arm, and the question to answer
first is: **can an exclusive-conditional write be promised at all in PARM?**
If exclusive writes are excluded from promising (as one would expect of an
RMW whose read half must read the coherence-latest), this arm is free and
should be recorded as such. If not, it needs its own argument — note that
the write value is derived from the `ak_latest` read, so the write is pinned
to the latest message, which is the natural lever.

This is cheap to settle and should be settled BEFORE designing the tag, since
it may add a case to it.

---

## 5. The open tension to resolve early

`interference_certify` as paraphrased — certification survives ANY memory
extension, on RISC-V — **seems to contradict the critical-section-store
scenario**: a thread that promised a CS store while the lock was free looks
uncertifiable once another hart's acquire lands, since its certification run
must re-execute the AMO, read lock = 1, and spin.

One of the paraphrase, the scenario, or our reading of the lock leaf is
wrong. Read the exact side conditions in `CertifyProgressRiscV.v`. **The
resolution determines what the robustness invariant can assume**, so do this
before writing any Layer-1 statement.

---

## 6. The characterization lemma (independent, do it early — it is cheap and it de-risks)

Conjectured, precedent PS1 Thm 5:

```
    promise-free machine  ≡  RVWMO ∧ acyclic(po ∪ rf) ∧ (po ∩ W×W) ⊆ gmo
```

Value out of proportion to cost: it turns the interim model assumption from
"we omitted a mechanism" into a crisp axiomatic statement a reader can check
against RVWMO, and it is what keeps the promise-free machine from looking ad
hoc. It does not depend on Layers 1–2 and can be done in parallel.

---

## 7. Fallbacks, in order

1. **Ship the interim theorem.** Already unconditional for **Ztso** hardware
   (Ztso's implicit RCpc annotations put `po ∩ W×W` into ppo and forbid LB);
   assumption-carrying only for weaker RVWMO implementations. The assumption
   is declared in the same epistemic category as the five `rv64d.*` platform
   axioms — stated once, visible in the final footprint.
2. **Standalone Lahav–Margalit-style robustness analysis** instead of
   extracting the premise from the Iris proof.
3. **Promises in the semantics + SLR-style logic.** Transfinite Iris
   (ℕ×ℕ lexicographic step indices — an unbounded certification run is
   re-verified at every step, which vanilla Iris cannot express). On the shelf
   unless robustness genuinely fails. Do not start here.

---

## 8. Recorded rejections — do not reopen without new information

- **The ORC11-shaped machine** (per-byte timestamp orders, view-carrying
  messages) represents W→W reordering without promises. Rejected: views
  become per-location timemaps everywhere, messages carry views (infecting
  the log, the base state interpretation, and every leaf rule), the PARM
  lineage (equivalence theorem, deadlock freedom) is lost — and the M6
  obligation is the SAME SHAPE either way, since promises are the single
  mechanism behind both LB and W→W.
- **Full promises-in-logic** as the primary route (see fallback 3).

---

## 9. Suggested order of attack

1. Settle §5's `interference_certify` tension (read `CertifyProgressRiscV.v`).
2. Settle §4's third store class: can an exclusive-conditional write be
   promised?
3. Decide §4 (A) vs (B) for the Layer-2 export.
4. In parallel and independent of 1–3: §6, the characterization lemma.
5. Write the violation pattern (§3's crux), now constrained by 1–2.
6. Layer 1 over the `pf_exec` skeleton (§2 consequence (b)).
7. Layer 2's certificate emission, per the §4 decision.
8. Compose; re-run the final `Print Assumptions` diff — baseline axioms plus
   the declared weak-memory assumptions and nothing else.

**Polarity check to keep in mind throughout** (Decision 1's closing note):
dropping dependency tracking makes the model WEAKER than hardware — free for
adequacy. The promise-free choice makes it STRONGER — adequacy needs
hardware ⊆ model, and that strengthening is exactly what M6 discharges.
Adding behaviors is free; removing them needs a theorem.
