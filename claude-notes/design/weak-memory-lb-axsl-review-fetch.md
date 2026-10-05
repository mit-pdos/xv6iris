# Review: "∀v reads everywhere + instruction fetch as an addr-dependent read" (C14 pivot)

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../claude-notes/LEAN.md)).

Adversarial review, 2026-09-24. Against design rev 6 §0.5/§5, tracker C0/C6/C14, AxSL source.

## Verdict: FAILS as stated. The core idea is WORKS-WITH-CHANGES, recut as a "ctrl gate" (below).
Why it fails as stated. (1) "Phase 1 is just a replay" and "wrong targets are vacuous at the fetch"
contradict each other. In AxSL a lob-delivered fact reaches only the *successor's FE* and the post.
It never reaches the WP continuation (read.v:84-103: the FE concludes `eid ↦ₐ R`; weakestpre.v:57
`post_lifting` hands local annotations only to Φ/chk). A pure replay therefore still needs a WP for
every in-image garbage pc, which is C0 again. For vacuity the continuation must sit under the fact.
Then phase 1 cannot run ahead of phase 2, and you need a joint induction (Q4).
(2) Putting fetch in ob, as the current emission does, gives fetch OUTGOING edges (Q2).
(3) If the gate hands the WP a lob annotation in general (not only a pure fact), MP+ctrl becomes
unsound (Q2).
Why the idea survives: RVWMO rule 11 orders EVERY po-later store after the loads a branch/jump
depends on. So after a pc-dependent control transfer, the only events that can come gmo-before the
gating load are READS. Reads deposit nothing anyone else needs. That asymmetry is exactly what
review 3's argument missed (Q3).

## Q1: hard requirement
AxSL itself gives nothing for owned bytes. `mem_read_external` requires `last_local_write tid addr
None` (read.v:71), so AxSL has no rfi read rule: a stack reload after a spill cannot be stated. The
rfi variant is commented out (read.v:338-387). The fact must come from the project's L2 read rule:
R := ⌜v = last H⌝, case (ii) via `own_forward_cat` (graph-decidable), case (i) via the tie piece plus
C6 coverage at the read's gmo position. That validation is exactly rev 4's. The proposal does not
remove C6. It only makes C6 non-circular (Q4).
(a) `sd ra; ...; ld ra; ret`: OK with the gate. `ld ra` ∈ pc-provenance of the post-`ret` fetch, the
  gate gives ⌜v = ra0⌝ before the continuation is chosen, and the WP continues at ra0 only. Code
  between `ld ra` and `ret` runs with ra symbolic, which is harmless.
(b) `ld a0; addi; sd a0`: the value never reaches the WP. a0 holds `v+1` for a ∀v. The sd's FE gets
  ⌜v = x⌝ along the data edge, and the write rule's `⌜data_gr = data_exp⌝` lets H := H++[x+1]. This is
  SC-like ONLY with a provenance-fact register surface: `r ↦ᵣ⟨x⟩ := ∃ v P, r ↦ v ∗ prov r = P ∗
  (annots(P) ⇒ v = x)`, propagated by every ALU rule. L3 today plans pure-value registers over
  `wp_exec_step` (§1-L3). That must change: the leaf layer is re-derived "∀v, then fact". It is
  mechanical but it is the whole 60-instruction cone.
(c) `ld t0; beqz t0`: OK. Branch sources go to LCtrl, the gate makes the wrong arm vacuous, and in
  the right arm the fact is a real hypothesis.
(d) The value is kept, then used as an address much later: OK if provenance survives (`dt_prov`
  through moves, CSRs and spills; a spill is a data edge, then a new owned read). The FE of the later
  ld/sd gets the fact. The garbage-v case needs no ownership up front, because the AxSL FE obtains
  `『addr|prot』` from annotations (read.v:~78). BUT the T2 progress obligation at that step has no
  fact. If Sail is GenericFail-stuck outside `gx_img` (open CHECK, §0 L0), the WP cannot be proved
  for garbage v. Either Sail access-faults (a trap, which is then gated via the trap hook) or the
  progress obligation must be `annots -∗ reducible`.
(e) The value is only compared and put in a register: fine at the surface (symbolic x). The fact is
  delivered at a store, a branch, or chk (post_lifting-style, needs local annotations). It is LOST if
  the only consumer is an `LDev` oracle write (UART "printed") until K2 makes devices graph agents.
Summary: the WP never needs v for register arithmetic if specs and ghost updates are stated in x.
It needs v only where identity or continuation is chosen: pc (the gate) and progress (see (d)).

## Q2: soundness of load →addr(pc)→ fetch
- As a *sink* the edge is sound (no new cycles). But today a fetch is not a sink. `dstep_t`'s LLoad
  arm puts every row read, including the fetch, into `dt_ld` and `dt_adr` (AxDeps.v:453-458).
  `dedges_w` then emits `DTtrans fetch→W` (AxDeps.v:432-435). With the new edge in, `ld→fetch→W` is
  harmless only given a lemma pc-prov ⊆ `dt_ctl`, which is not proved.
- Rules 1–3 (po-loc) and `fr` from a fetch are outgoing and must be excluded. A data load of a text
  address after a fetch of the same address gives `ld ra→fetch→ld x`. That is ctrl;R, falsified by
  MP+ctrl-reader when chained through `ld x →addr ld z →fr` a foreign write. "T is never written"
  does not save it: that is xv6 content, which fails §0's audit criterion.
- Fetch-PTW reads (§0: they are row events): making them pc-addr-dependent is a real strengthening.
  With a correctly predicted RAS/BTB, hardware walks for the target before `ld ra` completes and
  keeps the result. Their fr to later PTE writes and their rule 2 against data-PTW reads are outgoing.
  Only the immutability of kernel text PTEs (xv6 content again) makes this unobservable. Do NOT
  extend the edge to the walk.
- rf into the fetch: oracle (`AStepFetch`, AxOpsem.v:582). Fine. Fetch coherence is unchanged.
- ctx CSRs: incoming only. Fine.
- Trap entry: pc = stvec/mtvec is constant, but WHETHER a trap happens depends on loaded values
  (fault on a loaded address). Its sources must be in BOTH the gate set and `dt_ctl`. `erw_of`
  emits `LCtrl []` at the redirect today (§5 pt 2), so this is a hard prerequisite, not G3 polish.
- sret/mret: `LRegW wsepc` + `LCtrl [DReg wsepc]` exists (WeakRvwmoConf.v:1255-1275). Fine.
- Interrupts: the decision comes from the oracle plus sie/mie/mstatus provenance. Check that
  sstatus/sie are covered by `ctx_csrs` (AxDeps.v ctx list: MSTATUS, MIE only).
- Gate content must be PURE. If the gate hands the WP the whole annotation of `ld flag` (say □P
  from Φ_flag), the prover can frame □P into a ctrl-only `ld data`'s FE. That proves data=42 in
  MP+ctrl, where RVWMO allows 0. Pure facts validated true are meta-level truths and are safe.
- The fetch does not need to be in ob or gmo at all. The gate is an adequacy device. Keeping fetch
  out of `rvwmo_cat_consistent_t` avoids the whole audit.

## Q3: review 3's C0 argument (§0.5: "prefix-indexed hypothesis / rely-guarantee WP is circular
under LB, po-later is gmo-earlier")
Review 3 never considered fetch or ctrl as a gating point. Its argument is correct for a gate AT
THE LOAD: a non-dependent po-later store can be gmo-earlier, which is exactly the C14 cycle. It is
FALSE for a gate at a ctrl node whose sources include the load. Every po-later store is then
ctrl-after the load (`dedges_w` includes `DTctrl` from `dt_ctl`, and gtdeps ⊆ ob, AxDeps.v:325). So
the only gmo-earlier po-later events are reads. The proposal refutes review 3 only in this recut form.

## Q4: phase 1 / phase 2
It is not a replay. Needed: a joint gmo induction with a per-hart frontier. A hart's WP advances to
its next gate. Gated events that are passed in gmo while the hart is locked are provably reads
(lemma: W po-after gate ⇒ gmo-after all gate sources). Those reads are DEFERRED. When the last gate
source is validated, the hart unlocks, runs forward, and discharges the deferred reads with superset
handout (`flow_eq_dyn`'s ⊇ form, §1-L1 dev 1).
There is no deadlock: gate sources are po-earlier, and nested deferrals close before any write
because `ds_ctl` accumulates.
C6 closes in gmo order: writes are never deferred, so every gmo-earlier write has its FE (token or
class right). Coverage is still owed as a lemma, but it is no longer circular.
Gains: `wp_steps_expected`, `read_pin_hyp` (AxAdequacy.v:477), the AxPair `tpdd`/`sw_not_tpar`
gap, and phase-1 use of `ident_stop_lemma` all disappear, because the WP runs on graph values.
Costs:
- `adequacy_ord_aux` (a plain gx_gmo list walk) becomes a scheduler, with a lexicographic measure of
  gmo index × deferred set.
- The tie lemmas (AxGraphCat §7, GMO form) must hold when ghost pulls happen in PROCESSING order for
  deferred reads. This is the main new proof risk: same-byte pre-gate writes can be forwarded to a
  deferred read.

## Q5: recommended design ("ctrl gate")
1. Reads stay ∀v everywhere (AxSL-faithful). Owned R := ⌜v = last H⌝, validated at the read's gmo
   position (or its deferred position), cases (i)/(ii) as now.
2. New WP step form at every LCtrl / trap-redirect node:
   `∀ s', astep s s' → (⌜pure facts of annotations of loads in dt_ctl⌝ -∗ wp s' Φ)`.
   The pure part only. Gate on `dt_ctl` (every later W is ordered after it), not just pc-prov.
3. No fetch edge in the model. Fetch stays an oracle sink. Drop the fetch position from `dt_ld`, or
   prove the pc-prov ⊆ ctl lemma.
4. L3 registers `r ↦ᵣ⟨x⟩` (value, provenance, fact), refreshed to concrete at each gate.
   Specs and ghost updates use x.
5. Prerequisites, in order: the trap-entry emission hook with sources; the Sail out-of-image CHECK
   (or gated progress); sstatus/sie in `ctx_csrs`; a "stores after gate are gmo-after gate sources"
   lemma on `dstep_t`; the scheduler adequacy; tie lemmas in processing order.
Rejected alternatives:
- (α) Pin owned reads at the read via rules 1–3 / `own_forward` only. Covers case (ii) only; case
  (i) re-opens C0 (§5 "best alternative").
- (β) Angelic ghost-determined values at the read (rev 4). C14's cycle is a gate at the load.
- (γ) A "lob-closed sequential block". Sound only if the block ends at a ctrl node, which is (2).
