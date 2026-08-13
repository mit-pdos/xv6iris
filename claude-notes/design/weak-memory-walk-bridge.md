# The walk's racy leaf: the peel/bridge split (DECIDED: option (a))

**STATUS (2026-08-12): §8.3's six items are ALL LANDED, and the store-case
restriction is CLOSED** — the stale mirror (`iris/WeakStale.v`), the walk
at it (`iris/WeakWalkStale.v`), the racy absorption theorem
(`iris/WeakKptStale.v`, `wtlb_res_pt_translateAddr_stale_at`), and the
phase-flip design (`W` parameter + `wstep_ok_racy_phase_mono` +
`wstep_ok_racy_bind_false`, §8.3 item 6) that lets a walking STORE
compose, and the SEQUENTIAL-WINDOW widening (`WeakStale` §9, see §8.2)
that lets a fetch-miss + data-miss instruction compose.

**AND THE CONSUMER'S FIRST SLICE IS IN (2026-08-12): the peel of the
translation.**  `WeakKptStale` §4's `wwalk_peel_of_exports` (pure,
`plat_term_write` only) turns the absorption theorem's exports into
`wstep_ok_racy tid la 8 wak_plain (wwalk_filter w0 lw) wD_any True true
(translateAddr …) σ` plus its `wadm_filter` — i.e. everything the racy
side of a 6c leaf rule needs about the translation, ready for the §9
seq/bind kit.  The plumbing that made it possible: `exec_stale_restrict`
(`WeakStale` §6b — the footprint-restriction transport, which needs no
`acc_wf`: the unpinned arm patches both maps identically), the
absorption exports strengthened with the two slot-disjointness facts and
a σ-uniform write-arm trace selector `wtr : bool` (the shape is
hit-vs-miss determined, not per-member — a consumer choosing its
producer route must know which), and `acc_win` (windows as `gset` built
on the RIGHT `Countable` instance — in files importing
`SailStdpp.Values`, a `gset Arch.pa` written in binder position
elaborates against `Countable_mword` and mismatches `WeakCert`'s
machinery; never spell the set type there, use `acc_win`).  Route per
arm: read-only and miss-write (`wtr = true`) through the stale producer;
hit-write (`wtr = false`, the `[excl-read; write]` trace with its
pre-racy write) through ordinary certification + the §4 embedding +
phase-mono — legal because that trace has NO unpinned read, so the
backward transfer (`trace_off_win`, vacuous) applies and the family is
constant.  NO `trace_stale` widening was needed.

**AND THE FETCH PEEL IS IN (2026-08-12, `iris/WkFetchPeel.v` — 6a's
restatement, the peel half, ALIGNED case).**  `wfetch_peel_of_exports`
(+ the CPS `wfetch_peel_k`, the form 6c's funnel consumes; both
`plat_term_write` only): the walk-peel premise bundle at
`acc := InstructionFetch tt` plus a tail interface gives the peel of
`fetch tt` at the PC page's leaf window.  THREE findings that shape the
rest of 6a/6c:
- **There is no `Defs.bind (translateAddr …) rest` seam in the base
  monad** — the translation sits two `catch_early_return` levels down,
  under `liftR`, in the early-return monad, and `try_catch` is a
  fixpoint, not a bind.  The fix is generic and landed: `WkFetchPeel`
  §1's **`wstep_ok_racy_kR`** — the CPS peel restated over
  `Defs.monadR` (early return is a VALUE of the peel) with transports
  to the `M`-level kit (`_kR_bind`, `_kR_liftR`, `_k_cer`).
  Window-generic; anything else stated over `catch_early_return`
  (i.e. every real instruction body) will peel through it.
- **The 2-aligned (straddling) fetch is TWO translations at two
  DIFFERENT leaf windows** (`fetch_bytes va va 2` then
  `fetch_bytes va (va+2) 2`) — precisely the §9 seq-kit shape; TODO
  recorded in the file header (aligned `F_Base` delivered; RVC-4 is
  single-window and near-verbatim).
- **The σ → post-translation pinnedness transport is NOT
  peel-derivable** at `wD_any`/`W := True` (the write arm constrains no
  address there, and the run-level exports sit at `W := False`), so the
  tail rides an interface premise `wfetch_tail` at the post-translation
  states — its READ half's producer is supplied
  (`wfetch_tail_read`, from per-byte text pinnedness via
  `wstep_eff_confined_pin`); its OUTCOME half (the translation's result
  value and the post-state's text-pinnedness) is exactly what the IRIS
  half of the restatement must discharge from the absorption theorem's
  register wand + log arms.  That ghost half is 6a's remaining piece.

**AND THE ⇐-BRIDGE IS IN (2026-08-13, `WeakStale` §10 — the
ghost-matching keystone, all exports closed under the global context).**
`wrun_exec_stale_elim` (+ `wexec_exec_stale_elim`): peel + the actual
weak run ⇒ the run's result and post-state MATCH some Φ-admissible
family member — `exec_stale ra rn w m (wflat_st s) = Some (x,
wflat_st s', es)` — so a consumer pins result / post-registers /
post-memory / trace by rewriting against the family it already owns
(`exec_stale` is a function).  This is the walk's replacement for the
started cone's patched-exec bridge.  THREE things to know:
- **The correspondence needs the family's `trace_stale` traces as a
  premise — nothing weaker works.**  Two irrefutable failure modes kill
  any "no window read after a window write" attempt: (i) write-then-read
  (a store raises the writer's own `coh`, making `pinned_read` true and
  the machine read its own write while the mirror reads the patch), and
  (ii) READ-ONLY — after a stale racy read, observing ANY newer message
  anywhere (or a fence) pushes `w_vrNew` past the window's `latest_ts`,
  `pinned_read` flips true, and a second unpinned window read returns
  the latest while the mirror still returns the patch.  So the post-racy
  tail must be `trace_off_win` — i.e. exactly `trace_stale`'s tail —
  and the ⇐-bridge takes the SAME family-with-`trace_stale` bundle the
  peel producer consumes.  One hypothesis serves both directions.
- **The peel can take the AWAY arm at the window** (with `D := wD_any`
  nothing forbids treating a pinned window read as ordinary), so the
  witness discipline has three sources: the racy arm's value, the
  coherent word when the run ends pre-racy, and the coherent word at an
  away-arm window read.  The core elim is phase-GENERIC for this reason.
- **The sixth shape (TLB-hit write-back `[excl; write]`) is refused by
  `trace_stale`** (pre-racy write) and needs its own constant-family
  elim `wrun_exec_stale_elim_const` (§10d) — vacuous `trace_off_win`,
  no witness quantification — mirroring the peel side where that arm
  also takes the non-stale route.  A consumer case-splitting on the
  absorption arms gets ONE postcondition shape from both routes.

What remains of this front: the Iris half of the fetch restatement
(discharge `wfetch_tail` — its outcome half now follows from the
⇐-bridge + the family's Ok-result equations), the straddle/RVC fetch
arms over §9 + `wstep_ok_racy_kR`, and 6c's funnel (`wwp_instr_s`)
composing the CPS fetch peel with the execute phase, whose Q-half is
now statable by rewriting against the family.

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

---

## 7. MEASURED: the phase-`false` disjointness serves ONLY the bridge (2026-08-12)

The datum that decides option (a)'s cost, and it is machine-checked rather
than argued.

Shape 4 is blocked by `wstep_ok_racy`'s PHASE-`false` demand that every
later access be `racc_disj` from the window — a property of the PEEL, not of
the bridge's conclusion.  So the question is whether that demand earns its
keep anywhere except the bridge.  It does not:

> Replacing the disjointness binder with `_` at BOTH of its phase-`false`
> destruct sites — in `WeakRacy.wexec_of_exec_racy` and
> `wrun_wexec_racy` — leaves `WeakRacy.v` compiling with zero errors.
> `exec_of_wrun_win`, the patched-memory bridge, uses it four times.

(Experiment run 2026-08-12 against the post-C/D/S tree and REVERTED; the
file is unchanged.  Re-run it in one line if you doubt the claim.)

**Consequence.** An "unbridged" peel — one that permits the window to be
re-touched after the racy read — supports the two `wexec`-direction
traversals VERBATIM, hence supports REDUCIBILITY, which is what
`WeakAdequacy` actually needs.  All it gives up is the patched `exec` fact,
which option (a) does not want.  So (a) is not merely the smallest option:
the peel already does not depend on the restriction that blocks shape 4.

**Concrete shape for the implementation.**  Do NOT add a second fixpoint.
Remove the `racc_disj` conjunct from `wstep_ok_racy`'s phase-`false` read and
write arms, and give it back to `exec_of_wrun_win` / `exec_of_wrun_racy_gen`
as an EXPLICIT premise — `WeakVarCert.trace_disj` is already exactly that
predicate, with its transports proved.  Then:

- the `started` cone keeps the bridge by supplying `trace_disj` (it has it:
  its trace touches the flag window once);
- the walk supplies no `trace_disj`, gets no patched `exec`, and takes its
  outcome facts from `WeakKpt.wtlb_res_pt_translateAddr_at` instead;
- `WeakVarCert`'s producers need only drop the now-unnecessary conjunct from
  what they prove.

The one thing to check while doing it: `wp_wracy_load`/`wracy_cert` deliver
peel and bridge together, so the split has to reach them — that is §4(b)'s
churn, but confined to the one consumer rather than to the peel's definition.

**LANDED (2026-08-12), and in the form that costs the `started` cone
nothing.** The `racc_disj` conjunct is now a PARAMETER of the fixpoint —
`wstep_ok_racy tid ra rn rak Φ D b`, with `D : Arch.pa -> N -> Prop` standing
where `racc_disj ra rn` stood in the read arm's off-window disjunct and in the
write arm. One fixpoint, no second traversal, no new premise shape:

- the five bridge lemmas (`exec_of_wrun_win`, `exec_of_wrun_racy_gen`,
  `exec_of_wrun_racy`, `exec_of_wrun_gain_gen`, `exec_of_wrun_gain`) gained
  the premise `∀ pa n, D pa n → racc_disj ra rn pa n`, which is where the four
  uses of the conjunct now get their disjointness from;
- the two `wexec`-direction traversals are `D`-GENERIC and need no premise —
  §7's measurement, now a typing fact rather than an experiment;
- `wracy_cert` and both WP rules are stated at `D := racc_disj ra rn`, so
  `WkStartedLoad` and `WeakVarCert` are unchanged but for the instantiation.

The walk's peel is then `D := λ _ _, True`: shape 4's exclusive re-read and
its CAS write both have an arm. **That makes shape 4 STATABLE. §8 is why it
is not yet PROVABLE, and what to build.**

---

## 8. THE PRODUCER GAP — §4(a) as written does not close shape 4 (2026-08-12)

**Finding.** Liberating the peel is necessary and not sufficient. §7 asks
whether the phase-`false` disjointness earns its keep in the peel's
CONSUMERS, and correctly answers no. The question it does not ask is what
produces the peel — and there the same two-reads-two-values obstruction
reappears one level down, in a place `D` cannot reach:

> `wstep_ok_racy`'s off-window read disjunct hands the continuation the
> value at `coh_ts` — the coherence-LATEST word `lw`. Every producer we
> have (`WeakVarCert.wstep_ok_racy_{false,true}_of_confined`) supplies that
> continuation from a confined SC run at the memory PATCHED with the racy
> value `w`, where the same read returns `w`. For shape 4 those two reads
> are the walk's plain leaf read and its CAS re-read, and `w ≠ lw` is
> exactly the case the shape exists for. The producer cannot close.

So `RiscvExec.exec`'s kind-blindness bites twice: once at the bridge's
conclusion (§1, which (a) sidesteps by not producing one) and once at the
producer's premise (here, which (a) does not address). Patching the memory
is wrong for the CAS read; not patching it is wrong for the plain read; and
no `D` changes which value the fixpoint demands.

### 8.1 The fix: give the SC mirror a STALE memory, keyed on `ak_pins`

The obstruction is that one memory has to answer both reads. Give the
confined interpreter TWO — not two states, one state and one patch, selected
per read by the access kind the weak machine itself uses to decide
pinnedness:

```coq
Definition stale_mem ra rn w ak (s : mstate) : gmap Arch.pa (bv 8) :=
  if ak_pins ak then s.(mem) else write_bytes s.(mem) ra rn w.

(* exec_eff, arm for arm, with the RAM READ arm reading [stale_mem …] *)
Fixpoint exec_stale (ra : Arch.pa) (rn : N) (w : bv (8 * rn)) {X}
    (m : M X) (s : mstate) : option (X * mstate * list weff)
```

`ak_pins = ak_coh || ak_latest` (`WeakBridge.v:163`) is precisely "this read
returns the latest whatever the hart's view is", so:

- the walk's PLAIN leaf read (`wak_plain = AkInfo false false false`,
  `ak_pins = false`) reads the patched memory and returns the racy `w`;
- the CAS's `read_pte_exclusive` (`AkInfo false true false`, `ak_pins =
  true`) reads the real memory and returns `lw` — which is what the peel's
  off-window disjunct demands, since `mm ⊆ wflat …`;
- everything off the window is unaffected either way (the patch is
  invisible there — `WeakRacy.read_bytes_patch_disj`), so no lemma about a
  non-window access changes.

This is option (c) done RIGHT. §4(c) imagined a patch SEQUENCE folded into
the state; that cannot work, because an SC run has no write between the two
reads and a state-level fold still answers both from one memory. The
sequence has to be consumed by the READ ARM, and keying it on `ak_pins`
makes it a function rather than a list — which is why it needs no ordering
bookkeeping, no phase, and no second window.

### 8.2 What it buys beyond shape 4

- **Multi-window (blocker B) dissolves for free.** Nothing in `exec_stale`
  is single-window; the patch is a memory. An S-mode instruction whose fetch
  and data translations walk two DIFFERENT leaf slots patches both. (The
  peel is still single-window, so this is the direction a later widening
  takes, not something available today.)

  **AND THE WIDENING IS LOAD-BEARING FOR 6c, NOT A CORNER (2026-08-12).**
  Do not assume the two-translation case away: kernel PTEs are INSTALLED
  WITHOUT A/D (`kvmmap`/`mappages` write `PTE_R|PTE_X` / `PTE_R|PTE_W` and
  nothing else — `kperm_flags`'s `(true, true)` is only the A/D-CANONICAL
  ghost representative, not what the code writes), so fetch walks DO miss
  and DO write back on first touch.  And first touch is the COMMON case:
  every `sfence.vma`/satp switch empties the TLB, and xv6 crosses one on
  every user/kernel transition — so the first memory-touching instruction
  after any crossing can pay a fetch miss AND a data miss in one step: two
  racy windows, with the fetch's CAS write PRECEDING the data walk's racy
  read (which the phase-flip design's renunciation forbids at one window).
  Consequences: (i) per-vpn "A already set" tracking in the invariant
  makes steady-state fetch walks read-only but does not remove the second
  window and does nothing for first touch — insufficient alone; (ii) the
  widening shape is SEQUENTIAL windows via the CPS kit (translations never
  interleave); (iii) the WP rule for a post-crossing instruction cannot be
  stated without it.

  **THE WIDENING IS LANDED (2026-08-12, `WeakStale` §9, closed under the
  global context).**  No multi-window fixpoint: the two certification
  traversals are generalized to `bind m f` over the NESTED CPS peel —
  `wexec_of_exec_racy_kseq` / `wrun_wexec_racy_kseq`, which are the
  `WeakRacy` single-window inductions with the `Ret` case deferred to a
  TAIL-DISCHARGE premise ("whatever `K` holds at the seam, the tail's
  `wexec` witness exists").  The tail can be certified by window₂'s
  single-window traversal (`wexec_of_exec_racy_seq2` /
  `wrun_wexec_racy_seq2`, the two-window instances with window₂'s peel
  AND `wadm_filter` riding the seam continuation), by ordinary
  certification, or by another nesting level — n windows by iteration.
  Producer side: `wstep_ok_racy_k_seq_intro` (plain peel of the prefix +
  per-run-result window₂ peel/filter ⟹ the nested object; the
  continuation ignores window₁'s final phase, so `_k_of_run`'s
  both-phases demand is trivial).  **And the predicted `wadm`-transport
  price DISSOLVED**: window₂'s peel is produced AT THE SEAM STATE, after
  window₁'s CAS write is already in the log, so the cross-window write
  never crosses window₂'s admissibility analysis — the Iris consumer
  simply sequences two absorption fupds.  What remains deliberately
  unbuilt: a two-window PATCHED-exec bridge (the started cone's artifact;
  the walk takes none) and interleaved windows (the machine never
  produces them).
- **`acc_wf` gymnastics at the window disappear** for the mirror: the patch
  is byte-addressed, so a partially-overlapping access needs no case split.
- **It subsumes the `started` cone.** For a trace that reads the window once
  at a non-pinning kind and never re-reads it, `exec_stale ra rn w m s =
  exec_eff m (wpatch_st …)`-shaped, so the existing patched-`exec` bridge
  stays available to whoever wants it.

### 8.3 The build order — ALL SIX ITEMS LANDED (2026-08-12)

**`iris/WeakStale.v` is in and axiom-free** (`Closed under the global
context` on every export; tree green). It carries items 1–3 below:
`stale_mem` / `exec_stale` (§1), the `WeakEff`-shaped bind kit (§2) — note
`exec_stale_bind_nil`/`_bind_Some` are direct inductions, since `WeakEff`
kills their `None` case through `exec_eff_exec` and the mirror has no such
bridge to `RiscvExec.exec` — the two transfers and `read_bytes_stale_win`
(§3), the phase-`false` embedding `wstep_ok_racy_false_of_wstep_ok` (§4),
and **the producer `wstep_ok_racy_true_of_stale` (+ its `wmem_restrict`
instance) (§5)**. With it, shape 4 is producible: a family of `exec_stale`
runs, one per Φ-admissible window value, yields
`wstep_ok_racy … wD_any true`.

**`iris/WeakWalkStale.v` is in too, and it is item 4 — the walk itself.**
Headline: **`exec_stale_translateAddr_pt_miss_cases`**, one `translateAddr`
fact at the stale mirror covering every outcome a TLB-miss walk can take
when its plain leaf read returns a variant `pv` of the memory's word `p0`.
`Print Assumptions` gives `rv64d.plat_term_write` and nothing else — the
same single platform axiom every walk head in the tree carries.

The file is short because of the transfers, and that is the whole design
claim made good:

- `exec_stale_pt_walk_user` is `WeakWalkEff.exec_eff_pt_walk_user` AT THE
  PATCHED STATE plus `exec_stale_of_patch_id` — no walk chain re-proved;
- the CAS arms are `WeakUpdEff.exec_eff_update_and_write_pte_{none,fresh,
  written}` AT THE REAL STATE plus `exec_stale_of_exec_eff` — no update
  chain re-proved.  Those arms already separate the stale word from the
  freshly-read one, so no new model reasoning was needed anywhere;
- what IS re-proved is exactly the glue that crosses the two halves: the
  three `exec_stale_translate_TLB_miss_{none,fresh,written}` composites
  (~35 lines each, the `exec_eff` scripts with the bind kit renamed), the
  `translate` head, and the `translateAddr` front.
- The front forced ONE piece of generic infrastructure: **`execR_stale`**,
  the early-return interpreter's mirror (`WeakEffSkel` §§1–3 replayed, with
  `_bind_eq`'s `None` case a direct induction because the mirror has no
  bridge to `RiscvTryStep.execR`).  It is generic, not walk-specific, and
  anything else stated over `catch_early_return` can use it.

**THE SIXTH OUTCOME IS REAL AND IS NOW PROVED**: `..._miss_fresh` is the
arm where the gate fires on the racy word and the freshly-read one needs
nothing — four reads, NO write.  Unreachable at `exec_eff` on the miss path;
reachable here.  Its outcome disjunct is the one an absorption theorem must
grow.

1. **`iris/WeakStale.v`** (new, additive): `exec_stale` + the bind kit
   mirroring `WeakEff` §2 + the TRANSFER lemma — a run whose non-pinning
   reads are all `racc_disj` from the window has `exec_stale … m s =
   exec_eff m s`, so *every existing lemma about a window-free sub-run
   transfers with no re-proof*. That transfer is what keeps this from being
   a mirror of `WeakWalkEff`.
2. **The phase-`false` embedding**: `WeakBridge.wstep_ok tid m s →
   wstep_ok_racy tid ra rn rak Φ (λ _ _, True) false m s`, one induction.
   With `D = True` the phase-`false` peel IS `wstep_ok`, so the walk's
   post-racy tail is discharged by `WeakCert.wstep_eff_confined_pin`
   verbatim — no post-racy producer of its own.
3. **The phase-`true` producer** `wstep_ok_racy_true_of_stale`, modelled
   line for line on `WeakVarCert.wstep_ok_racy_true_of_confined`, with two
   changes: the family member at `w` is an `exec_stale ra rn w` run, and the
   tail after the racy read goes to (2) at the UNPATCHED flat memory instead
   of to `wstep_ok_racy_false_of_confined` at the patched one. Its trace
   premise replaces `trace_racy`'s "`trace_disj` from here on" tail by the
   weaker "every NON-PINNING read from here on is off the window" (the CAS
   read and the CAS write are then admitted, which is the whole point).
4. **The walk's dispatch at `exec_stale`**: the one place a mirror is really
   owed. `WeakUpdEff`'s arms already take the STALE word as a parameter
   separate from the freshly-read one (`exec_eff_update_and_write_pte_fresh`
   / `_written`, `:550` / `:582`) — that is the sail fork's atomic recheck,
   and it means the model-level statement of shape 4 already exists. What
   has to be re-derived at `exec_stale` is only the chain that FEEDS them
   the leaf read: `WeakKpt.wptree_translate_miss_eff_core` and the
   `translate` / `translateAddr` heads it calls. Everything else in
   `WeakWalkEff` is window-free and rides (1).
5. **The racy absorption theorem — LANDED (2026-08-12, `iris/WeakKptStale.v`,
   `Print Assumptions` = `plat_term_write` + funext, same as the SC twin).**
   `wtlb_res_pt_translateAddr_stale_at`: identical premise list to
   `wtlb_res_pt_translateAddr_at`, the five pure exports unchanged (lw
   variant-ness, the three `pt_slot_mem` facts, pointer pins, the collapse
   fact, `nv_free`), and THREE interface deltas where the SC theorem's
   single-run headline cannot survive:
   - **the headline is a per-variant FAMILY**, `∀ av dv` with
     `pte_ad_le (pte_set_ad w0 av dv) lw`, of `exec_stale la 8 pv` runs of
     `translateAddr` — one fupd cannot commit per-variant ghost outcomes,
     and it does not have to: the read-only/write-back split is
     family-UNIFORM because the write-back event is decided by the LATEST
     word (`update_PTE_Bits_fires_mono`).  **The `pte_ad_le` index bound is
     load-bearing, not cosmetic**: a variant NOT below the latest could
     carry bits the latest lacks and refuse the gate while the latest
     fires, splitting the family across the two ghost arms.  `ad_le` is
     exactly the second collapse conjunct, so consumers lose nothing.
   - **the read-only arm's trace set grows by the sixth outcome**
     (walk ++ CAS-read), the one interface growth §5 predicted.
   - **registers come back as a WAND**, not updated in the main line:
     `∀ av dv sg' es, ⌜ad_le⌝ -∗ ⌜the member's exec_stale equation⌝ -∗
     reg_interp (wm_regs σ) ==∗ reg_interp (sregs sg') ∗ wtlb_res_pt …`.
     `exec_stale` is a function, so the caller's equation pins `sg'`
     against the proof's stored family analysis, and `tlb_ok_pt_fill`
     absorbs whichever A/D-variant walk entry the run installed (any
     variant of the mapped leaf is a legal cache entry).  The theorem
     "declines to pin the tlb register" became this wand.
   Supporting pieces, same file: `wptree_translateAddr_stale_cases` (the
   pure dispatch twin, covering HIT and MISS — hit arms are the `exec_eff`
   runs transferred, since their traces have no unpinned read), and the §1
   derivation that slot disjointness is FREE (`pt_slot_racc_disj`: 8-aligned
   slots either coincide — forcing the words equal, refuted by
   `pte_ptr` vs `pte_leaf` — or are `racc_disj`), so the transports need no
   new invariant conjunct.  Two consumer-driven strengthenings landed in
   `WeakWalkStale.v` on the way: the miss lemma's read-only arms now carry
   the gate equations that DECIDED them (an arm you cannot refute from its
   content is an arm a keyed dispatch cannot exclude), and its sregs
   conjunct pins the installed entry concretely (`∃ tv` is not consumable
   by a caller that must re-establish `tlb_ok_pt`).
6. **The peel's BIND composition** — **LANDED** (`WeakStale` §7), and it is
   what makes item 5 usable; a discovery of the item-4 work, not part of the
   original plan.
   `wstep_ok_racy_true_of_stale`'s family is over the WHOLE step monad, so
   taken literally it would demand an `exec_stale` fact for `riscv_step` —
   i.e. the entire fetch/decode/execute skeleton mirrored, which is far more
   than the walk. It is not needed: give the peel a CPS form
   (`wstep_ok_racy_k`, the fixpoint with `K : X -> wmstate -> bool -> Prop`
   in the `Ret` arm) and one `bind` lemma, and then only `translateAddr`
   rides `exec_stale` while everything around it rides the ORDINARY
   `WeakCert` machinery through §4's embedding. The phase must be an
   argument of `K` — that is why a plain (non-CPS) bind lemma does not work:
   at `m`'s `Ret` leaf the phase is whatever `m`'s racy read left, and the
   tail's obligations differ between the two.
   What landed: `wstep_ok_racy_k` (the fixpoint with `K : X -> wmstate ->
   bool -> Prop` in the `Ret` arm), `wstep_ok_racy_k_triv` (the trivial
   continuation IS the peel, both directions), `wstep_ok_racy_k_of_run` (a
   peel plus a fact about every state the run can reach is a CPS peel),
   `wstep_ok_racy_k_bind`, and the user-facing `wstep_ok_racy_bind`.
   **THE STORE CASE IS CLOSED (2026-08-12), by the PHASE-FLIP design** —
   a third route, cheaper than both this note used to list (no run
   companion, no §8.5 `wadm` transport).  The observation (user's): the
   phase bit's only power is gating the racy-read disjunct, so FLIPPING to
   phase-`false` early merely RENOUNCES the racy read — always sound.  The
   only obstruction was the write arm's `b = false` conjunct, and
   measurement showed it served the peel's consumers unevenly: the two
   wexec-direction traversals never use it for the exec construction (only
   for a `wadm_filter`-transport premise, see the delta below), and the one
   real consumer is `exec_of_wrun_racy_gen`'s write-refutation — a BRIDGE
   concern, the same situation §7 found for `racc_disj`.  Same cure: the
   peel gained `W : Prop` ("pre-racy writes permitted") — the write arm's
   conjunct is `(b = false ∨ W)` — with the bridge cone at `W := False`
   (byte-identical strength) and traversals/producers/CPS kit W-generic.
   New exports (`WeakStale` §8, all closed under the global context):
   `wstep_ok_racy_phase_mono{,_gen}` (at `W := True`, a phase-`false` peel
   IS a phase-`true` peel), `wstep_ok_racy_k_of_run_false` (K-monotone
   variant demanding the tail at phase `false` only), and the
   consumer-facing `wstep_ok_racy_bind_false` — racy prefix at `W`, WRITING
   tail certified at phase `false` only, which the W-generic §4 embedding
   supplies from an ordinary `wstep_ok`.  A walking STORE now composes.
   **The one semantic delta, forced by measurement:** the write arm's
   continuation runs at phase `false` UNCONDITIONALLY (was: at the current
   phase) — i.e. a permitted pre-racy write itself renounces the racy read.
   This is what keeps the traversals' `wadm_filter`-transport discharge
   (`b = true → wadm_filter …` becomes vacuous post-write; with `D`
   generic the permitted write may hit the window, where the filter
   genuinely does not transport).  It is a no-op for every existing
   instantiation and for the walk shapes (racy read THEN write).  What it
   deliberately gives up: a write-then-racy-read peel at one window — the
   same two-translation shape the single-window peel could not express
   anyway; if that widening is ever built (§8.2's window-set direction),
   the `wadm` transport across off-window writes returns as ITS price,
   not this design's.

### 8.4 The variant arithmetic, worked out (why the outcome is still absorbed)

With `pte_ad_le w lw` (the collapse conjunct) the weak run and the SC run at
the FLAT memory differ ONLY in whether the CAS path is entered, and the
model recomputes the written word from the FRESH read — so:

| access | latest `lw` | stale `w` | weak run | flat SC run |
|---|---|---|---|---|
| Load | (0,0) | (0,0) | writes (1,0) | same |
| Load | (1,0) | (0,0) | **O-FRESH: extra excl read, NO write** | O-UNCHANGED |
| Load | (1,1) | (0,0) or (1,0) | O-FRESH / O-UNCHANGED | O-UNCHANGED |
| Store | (1,0) | (0,0) | reads + writes (1,1) | reads + writes (1,1) |
| Store | (1,1) | (0,0) or (1,0) | **O-FRESH** | O-UNCHANGED |

so the divergence is always "one extra exclusive READ, no extra write, same
memory, same `pa`" — the TLB entry records `Some fresh = lw` on the O-FRESH
arm and the walked `lw` on the O-UNCHANGED arm, i.e. the same word.  The
absorption theorem's conclusion already declines to pin the `tlb` register
(`sregs sg' = wm_regs σ ∨ ∃ tv, …`), so nothing in the interface moves.

**And note what this table refutes**: patching the memory with the stale `w`
for the WHOLE run (the naive fix) is not merely unprovable, it is WRONG —
at Load/(1,1)/(0,0) the patched SC run writes (1,0), clobbering the D bit
the atomic recheck exists to preserve. The mirror must read the real memory
at the CAS, which is exactly what `ak_pins` selects.

### 8.5 What the producer's proof settled (read before extending it)

- **The trace premise has THREE arms, and every one of them is decided by
  data the MONAD fixes.** `WeakStale.trace_stale` splits a pre-racy read on
  `ak_pins ak` first and `racc_disj` second — the read's kind, address and
  width — never on the value. That is forced, not stylistic: the induction
  must pick ONE of the peel's arms while holding a whole FAMILY of runs, so
  the choice cannot vary with the patch. It is the same constraint that made
  `WeakVarCert.trace_racy` an ordered fixpoint, and the pinned arm is the one
  it adds: a PINNED read of the window is legal anywhere, before or after the
  racy read, because it reads the real memory in the mirror and the
  coherence-latest word in the machine.
- **`ak_pins rak = false` is a new top-level premise** (vacuous for the
  walk's `wak_plain`). Without it the arms are not exclusive: a racy read
  whose own kind pinned could take arm 1, and `trace_stale_pin_tail` would
  be false.
- **The post-racy tail needs no producer.** It goes to
  `WeakCert.wstep_eff_confined_pin` at the UNPATCHED confined memory —
  §3's backward transfer turns the family member's tail into an ordinary
  `exec_eff` run, and §4's embedding turns `wstep_ok` into the phase-`false`
  peel at `wD_any`. This is where the design pays off twice: the same
  `exec_stale` run supplies the racy value AND a tail that the SC-shaped
  library already knows how to certify.
- **A RAM WRITE BEFORE THE RACY READ IS STILL REFUTED, NOT MERELY
  UNPROVABLE** (`wstep_ok_racy`'s write arm demands `b = false`), so
  `trace_stale` still has `WEwrite … :: _ => False`. That is the remaining
  ordering restriction, and it is what a two-translation instruction will
  hit first (a fetch walk that writes A/D back, then a data walk that reads
  racily): the peel — not the mirror — is what has to widen for it, either
  by admitting pre-racy writes off the window (needs a `wadm` transport
  across a log extension that misses the window) or by carrying a window
  SET. §8.2 says the mirror is already ready for either.
