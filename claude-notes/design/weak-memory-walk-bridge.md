# The walk's racy leaf: the peel/bridge split (DECIDED: option (a))

**DECISION (2026-08-12, the φ-upgrade author, as §5 requested): take
option (a), and do NOT start until the in-flight C/D/S points-to surgery
lands.**  Rationale beyond §4's (which stands):

- **Under C/D/S a translation is not a racy-window consumer at all.**
  The PTE bytes' wlat elements live in the kpt/proc-pt resources as
  CLEAN fragments (the surgery leaves `wlat_pointsto`'s meaning
  unchanged), and BOTH of the walk's reads — plain-stale and
  exclusive-latest — discharge the φ obligation through the clean arm
  of the new load trichotomy (clean element ⟹ clean-purity ⟹ every
  WCplain message on the byte is published ⟹ no violation whichever
  timestamp is read).  The patched-`exec` bridge and the sync-token
  racy rules are for genuine single-occurrence racy windows (`started`);
  the walk fits neither, so (b)/(c) would weld walk handling into
  machinery whose premises the surgery and the upcoming site-predicate
  work keep churning.  (a) is the only shape CONSISTENT with the φ
  upgrade, not merely the smallest.
- **The two-reads divergence is absorbed for the same reason M6's
  SCexcl arm worked**: the translation's result is a function of the
  coherence-latest PTE (the stale first read only decides whether the
  CAS fires; the CAS re-reads the latest), which is what the absorption
  theorem already states off the canonical tree — a structure-only peel
  with no patched-`exec` conclusion is sound and sufficient.
- **Sequencing**: (a) is additive and design-independent of the
  surgery, but the surgery's agent is editing `WeakRacy.v`/`WeakKpt.v`/
  the started cone RIGHT NOW — wait for it to land (file conflicts, not
  design).  §5's caution on (b)/(c) stands permanently.
- **New obligation inherited from C/D/S — put it on the walk worklist:**
  kernel PTE STORES are WCplain and come out DIRTY; their publication
  points are the boot `started` release (kernel table) and the
  scheduler/lock releases that migrate a user table's process — the
  FLIP BUNDLES at those release sites must include the PTE bytes, after
  which the kpt/proc-pt invariants hold the elements clean, which is
  exactly what the walker's clean-fragment reads consume.  General port
  recipe, no walker special-case.

**Original status (2026-08-12): BLOCKED on a design decision, analysis complete, no
code owed until the decision is taken.** This is 6a's last item — the S-mode
fetch-chain restatement — and it is the gate on 6b/6c and therefore on every
real S-mode weak proof.

Written up separately from the worklist because it is one self-contained
question with three answers and a sequencing interaction; the worklist's
narrative version is the "SLICE 2 … BLOCKERS" block in
[`projects/weak-memory.md`](../projects/weak-memory.md).

---

## 1. The issue, in one paragraph

The page-table walk reads the LEAF slot TWICE in one machine step: once
PLAIN (racy — the hardware walker A/D-writes it from any hart, so it is not
`pinned_read`) and once EXCLUSIVE (`read_pte_exclusive`, `ak_latest`, hence
necessarily the newest message), **with no intervening write**. The racy
bridge describes a weak run as an SC run at
`WeakRacy.wpatch_st` (`iris/WeakRacy.v:274`) — the flat memory with ONE value
written at the racy window — and `RiscvExec.exec` is KIND-BLIND. So in the SC
run both reads return the patch value, while in the weak run the first
returns a possibly-stale variant and the second returns the latest. When they
differ the two runs diverge and the bridge's equation is false.

**This is not a premise that can be strengthened.** Patch with the stale
value and the exclusive read is wrong; patch with the latest and the plain
read is wrong. A single-memory SC run cannot model a location read twice with
two different values and no write between them — that is exactly what "racy"
means. The obstruction is in the SHAPE of the bridge's conclusion, not in any
lemma's hypotheses.

Note it bites even in the arm where nothing is written: if the stale word
lacks A, `update_PTE_Bits stale` fires, the CAS re-reads a word that already
has the bits, and the run lands in O-FRESH — read only. Two reads, two
values, still.

---

## 2. Exactly what is and is not covered

`WeakKpt.wtlb_res_pt_translateAddr_at` (`iris/WeakKpt.v:1189`) enumerates five
trace shapes. Only ONE is blocked:

| # | trace | racy window? | producer |
|---|---|---|---|
| 1 | `[]` (TLB hit) | none | ordinary `wstep_ok` (WeakCert) |
| 2 | `[read a2; read a1; read la]` (walk, no writeback) | one, tail empty | **covered** — `WeakVarCert` |
| 3 | `[read(excl) la]` (refresh) | none — `ak_latest` ⇒ `ak_pins` ⇒ self-pinning | ordinary `wstep_ok` |
| 4 | `[read a2; read a1; read la; read(excl) la; write(excl) la lw']` | **BLOCKED** | — |
| 5 | `[read(excl) la; write(excl) la lw']` (hit + writeback) | none — as 3 | ordinary `wstep_ok` |

Shape 4 is "TLB miss → walk → the PTE needs A/D bits → CAS writes them", i.e.
the first access to a page whose PTE lacks the bits after a miss. Reachable
and common on secondary harts; it must be handled.

**Do not** try to route shapes 3/5 through the racy peel — they need no racy
window, and `trace_racy`'s pre-phase forbids the write anyway. The caller
already case-splits on the absorption theorem's disjunction; each arm picks
its own producer.

---

## 3. What exists today (all green, all axiom-free)

- `WeakRacy.wstep_ok_racy` (`:327`) — the peel, since slice 1 carrying a
  value filter `Φ : (nat -> bv 8) -> Prop`, with `wadm_filter` as the
  soundness side condition that REPLACES pinnedness.
- `WeakRacy.exec_of_wrun_win` (`:554`) — the post-racy traversal whose
  single-patched-`exec` conclusion is the obstruction.
- `WeakRacy.wp_wracy_load` (`:1113`) / `wracy_cert` (`:1096`) — the WP rule,
  which delivers the peel and the bridge TOGETHER. Its only consumer is the
  `started` cone.
- `iris/WeakVarCert.v` — the producer. `wstep_ok_racy_false_of_confined`
  (`:114`, post-racy), `wstep_ok_racy_true_of_confined` (`:451`) and
  `wstep_ok_racy_true_of_window` (`:648`, from a FAMILY of confined runs, one
  per Φ-admissible window value), over `trace_pin_off` (`:339`) and the
  ordered `trace_racy` (`:393`).

None of this is wasted by the decision below: it is what the `started` load
needs — a genuine single-occurrence racy window whose consumer DOES want the
patched `exec` — and shape 2 rides it unchanged.

---

## 4. The three options

**(a) Give the walk its own rule that never produces a patched `exec`.**
RECOMMENDED. The leaf never needed an `exec` fact spanning the translation:
on the SC side `SmodeCorePt.tlb_inv_pt_fetch` (`iris/SmodeCorePt.v:888`)
ABSORBS the translation in a `==∗` and hands the caller a fact about what
FOLLOWS, and `wtlb_res_pt_translateAddr_at` is already the weak twin — it
delivers `exec_eff (translateAddr …) (wflat_st σ)` at the UNPATCHED state
together with the ∀-variant collapse conjunct. So: give `translateAddr` a
bespoke peel lemma proved from the absorption theorem (structure only, no
patched-`exec` conclusion), compose it with the ordinary machinery via
`WeakEff`'s composition kit, and the leaf's `exec` fact concerns only the
EXECUTE, where no racy window appears. Smallest change; does not disturb the
`started` cone; very likely what 6c's "the absorption theorem hides the racy
continuation from specs" always meant.

**(b) Split `wp_wracy_load`'s peel-and-bridge coupling** so a caller can
discharge the peel without committing to a patched-`exec` conclusion. More
general than (a); more churn; disturbs the one existing consumer.

**(c) Sequence-of-occurrences bridge** — the patch becomes a LIST, re-chosen
at each window access. The fully general answer, and it subsumes the
multi-window question below. Widest change: `wpatch_st` becomes a fold of
patches, and `read_bytes_patch_disj` / `write_bytes_patch_comm` need list
versions.

### The multi-window question, which (a) may dissolve

An S-mode load with paging on performs TWO translations in one step — fetch
and data — at two DIFFERENT leaf slots, and `wstep_ok_racy` carries one
window plus one phase bit, so the second leaf read has no arm. Under (a) a
translation never contributes a racy window to the peel at all, so two of
them cannot collide, and the question does not arise. Under (b) it still
does. Under (c) it is already solved. **This is a reason to prefer (a)
beyond its size.** (Independently: the TLB-hit shape costs no window either,
so a fetch translation held as a hit by the resource also sidesteps it.)

---

## 5. The sequencing interaction — please weigh this before starting

[`weak-memory-phi-upgrade.md`](weak-memory-phi-upgrade.md) §2–3 says the
framework surgery lands BEFORE the mass SC→weak port, and item (2) of that
list is **site predicates on the racy-load and release leaves** — the
racy-load leaf gains `⌜decode(pc+4) = fence r,rw⌝`, discharged per site by
`vm_compute` and backed by a generated whole-image enumeration.

The racy-load leaf is exactly what `WeakVarCert`'s producers feed. So the
options are:

- **do (a) first** — it is additive (a new bespoke lemma over the absorption
  theorem) and touches neither `wstep_ok_racy` nor the leaf interface, so the
  site-predicate surgery lands on top of it without rework; or
- **do the C/D/S + site-predicate surgery first** and then (a), if the
  surgery is expected to change what a racy-load leaf's premises look like in
  a way that would make (a) rework.

My read is that (a) is safe to do first precisely because it is additive and
avoids the leaf interface — but the φ-upgrade author knows what the surgery
does to those premises and should make the call. **(b) and (c) are NOT safe
to start before the surgery**: both rewrite `wstep_ok_racy` or `wpatch_st`,
which the surgery's leaf rules sit on.

---

## 6. Pointers

- Worklist narrative + the accounting table's provenance:
  `projects/weak-memory.md`, the "SLICE 2, SECOND HALF" and "THE TWO
  BLOCKERS" blocks.
- The kind-blindness fact this turns on is recorded independently in
  `projects/weak-memory.md`'s model-regeneration blast-radius entry
  ("`RiscvExec.exec` is KIND-BLIND, so SC behavior at one memory is unchanged
  (fresh = stale there)") — the same sentence that makes the SC update-cone
  rework cheap is what makes this bridge impossible.
- The landed atomic-recheck walker: `model-xv6iris/rv64d.v:24781`
  (`write_pte_conditional`), `:24795` (`read_pte_exclusive`), `:24965`
  (`update_and_write_pte`); classifications in `iris/WeakUpdEff.v`'s header.
