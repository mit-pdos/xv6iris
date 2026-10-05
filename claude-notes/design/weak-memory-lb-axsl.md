# Design: load buffering via an axiomatic (AxSL-style) base logic

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../claude-notes/LEAN.md)).

STATUS (2026-09-24, rev 6 — TARGET RAISED by user decision: the capstone
must keep ALL of tier 1's conclusions, see §0 "The target"; rev 5's mechanism
unchanged): PLAN; G0.5 done, foundations tracks and the L1 port in flight.  Exploration of AxSL's approach for the tier-2 gap (LB).  Tracker
(terse): `projects/weak-memory-lb-axsl.md`.  Machine-checked so far:
`iris/AxGraph.v` (ob ⊆ gmo, the owned-read lemma family, LB non-vacuity);
`iris/AxGraphCat.v`/`AxGraphWit.v` in flight (faithful ppo, witnesses).

**rev 7 (2026-09-24) — CTRL-GATE PIVOT, owner-ADOPTED** (adversarial review:
`design/weak-memory-lb-axsl-review-fetch.md`). Supersedes rev 4's
expected-value owned-read mechanism (§0.5, §5/§C14 — left in place with
SUPERSEDED markers, not deleted); authoritative spec: §7. Owner HARD
REQUIREMENT, binding on every choice in §7: simple SC-like, pure-value
verification of sequential code must remain possible.

## 0. Goal and final statement

### The target (user decision, 2026-09-24 — NON-NEGOTIABLE)
The capstone must be STRONGER than `WeakSrvwmoCapstone.xv6_srvwmo_safe` on
both axes: the sRVWMO hardware assumption is gone (LB and store-buffer
forwarding admitted) AND nothing tier 1 concludes is lost.  Rev 5 gave up
three conclusions; each is now a required deliverable, not a stated loss:
- **(K1) `¬violation_hart`.**  `WeakRobust.violation_hart` is stated over
  promise-free configurations (log, `obs_flr`, `pub`), which do not exist
  here.  Deliver: a graph restatement `gviolation_hart GT` (an `SCowned`,
  unpublished hart write whose byte a FOREIGN hart reads by rf, with no
  publication ob-between) refuted by the DRF export, PLUS a SUBSUMPTION
  corollary: on an `srvwmo_consistent` execution realized by a pf run,
  `¬gviolation_hart` ⇒ `¬violation_hart` of that run — the check that the
  restatement is not weaker than the original.
- **(K2) `reducible` for the disk/UART/PLIC threads.**  The per-hart device
  oracle cannot give it.  Deliver: devices as graph agents with real state
  (disk row non-empty, UART/PLIC/CLINT MMIO events against a device-state
  interpretation) — pulled forward from G5; `disk_row_empty` and the
  per-hart `LDev` oracle stream are SCAFFOLDING and must be gone from the
  final statement.
- **(K3) the multi-era crash story** (`crash.md`: power loss at any cycle,
  disk persists, reboot at `_entry` in a fresh generation, one
  crash-spanning disk invariant).  Deliver: the capstone quantifies an
  ERA SEQUENCE — per era g a graph `GT_g`, consistent, CUT at the power-off
  point; era g+1 boots from reset state + the disk image left by era g's
  cut.  Design items (open, see §2 G4c): (a) the cut = a `WeakRvwmoRestr.restr_ok G cs n`
  cut of `GT_g` (per-hart row prefixes `cs` AND a gmo prefix `n` with the
  same memory events). A plain gmo-prefix is WRONG under store forwarding:
  a forwarded load can be gmo-before its po-earlier source, so the prefix
  keeps the load and drops its source (`AxCutProbe.gfwd`,
  `fwd_prefix_drops_source`, `fwd_naive_not_wf`). Preservation is proved for
  both cat models (`AxCutProbe.restrict_cat_consistent(_t)`); both closures
  are needed (po for ppo rules 2/12, gmo for write indices). Hardware claim
  (C12) to justify: rows = retired prefixes, gmo = performed order with
  retired-but-buffered stores drained first;
  (b) the persisted disk = the disk AGENT's own performed writes (a program
  prefix of the device agent), not "co-last disk-address writes of the cut"
  (which would count a buffered CPU store as persisted); the torn-write
  knob of `crash.md` stays a knob; (c) the crash-spanning invariant lives
  in the disk agent's protocol Φ and survives the cut because it is
  deposited only at performed (prefix) events; (d) fresh ghost names per
  era, as the SC tier's power thread.
- **Assumption audit.**  `Print Assumptions` alone is NOT the audit: the
  context-CSR serialization, precise-trap ctrl, and the fetch-coherence
  statement live INSIDE definitions (`rvwmo_cat_consistent_t`, the fetch
  oracle).  The capstone's doc comment lists every in-definition hardware
  strengthening; each must be justified per the sRVWMO note's criterion
  (hardware-only, zero xv6 content, litmus-falsifiable).

The statement below is rev 5's single-era core; K1–K3 extend it.

Same claim as `WeakSrvwmoCapstone.xv6_srvwmo_safe` with sRVWMO replaced by an
RVWMO model that ADMITS load buffering, for every hart, no xv6 side
conditions, in the T4 (checkpoint) form so it speaks about the
non-terminating harts:

    xv6_rvwmo_safe_ax :
      fresh_era gen σ0 → awp_package Σ gen σ0 D →
      ∀ GT : gdexec_t, rvwmo_cat_consistent_t GT → disk_row_empty GT →     (* TAGGED deps: AxDeps.v *)
      ∀ i row em, gx_prog GD !! i = Some row → hart_conf i row (xboot σ0 i) (oracle i) em →
        (∀ s ∈ boundary_states em, chkp i s)                       (* T4 *)
      ∧ reducible_or_row_exhausted (em_fin em)                     (* T2 *)
      ∧ (∀ w ∈ writes GD, ¬ text_byte (addr w))                    (* fetch oracle discharged *)

- `hart_conf`/`hemit` (WeakRvwmoConf.v:813-857): the hart's Sail program from
  boot EMITS the row; the row IS the hart's event set (= AxSL `tpcoverage`).
  Quantified over the emission `em`.  `chkp i s`: pure predicate on the
  program state at `LInstr` boundaries via `chk_pure`.  T2 covers the
  emitted prefix — prefix-closed safety, as for every axiomatic model.
- **The model `rvwmo_cat_consistent`** := the tree's `gdexec` vocabulary
  (`gwf`, `gload_value`, `gatomicity`, `gdeps_wf/gmo`) with ppo :=
  rule 1 `[M];po-loc;[W]` · rule 2 `[R];po-loc;[R]` minus same-source pairs,
  no intervening same-hart store · rule 3 (fused `LRmw` → later R by rfi) ·
  rule 4 `gfence_covers` · rule 5 `.aq` load/RMW → all later · rule 7 RCsc
  only · rules 9/10/11/13 as `gd_deps` edges INCLUDING rule 9's load half
  (address-dependent loads and PTW reads; D-8 lifted at the row level: every
  `MemRead` of an instruction depends on its decoded address registers and
  on `satp`) · **rule 12 as a DERIVED edge** `same hart ∧ ∃ m, (a,m) ∈
  gd_deps ∧ grf m b` (a forwarded load completes after its store's data is
  known — load-bearing for the gmo induction, review 3 F1) · **rule 13 in
  its GENERAL form** (a store is ordered after every read that some
  po-earlier instruction's ADDRESS depended on; the tree's `ds_ld` is reset
  at `LInstr` and covers only the instruction's own PTW reads — review 4 F1:
  without it `ld a0,[y]; ld a1,0(a0); sd [z]` admits `sd < ld [y]` and the
  gmo induction meets an unannotated write) · **execution-context CSR edges**
  (every memory event depends on the provenance of `satp, mstatus, mie,
  medeleg, mideleg, stvec, mtvec` — DEC-5's satp edge generalized; a
  hardware-strengthening: serializing CSR writes; review 4 F2) · **trap entry
  is a control node** carrying the trapping instruction's decoded sources
  (+ `satp` for translation faults): the handler's events are ctrl-dependent
  on the faulting access (precise exceptions; adds ppo only; needs an
  emission hook at the trap's `nextPC` redirect — `erw_of` emits `LCtrl []`
  there today; sources ⊇ the trapping instruction's decoded sources and the
  context-CSR provenance, so interrupts are covered too; needed from G3).
  Deps are TAGGED (addr/data/ctrl/trans/r13/ctx; `AxDeps.v`, `gdexec_t`):
  rule 12 ranges over addr/data only — the capstone MUST quantify the tagged
  model (`forget` reinstates an unsound ctrl;[W];rfi;[R] rule 12, witness
  `tw`); `gtdeps_wf` admits read targets (rule 9's load half).  The D-8
  unmasking of the LLoad `asrc` is load-bearing for BOTH rule 9-load and
  general rule 13: the F5′ detour (reading address sources off the `LRegW`
  list) is unsound because the emitted list (`erw_srcs`) is the DYNAMIC set
  of carriers the instruction read, which for AMO/SC includes the DATA
  register — so `dt_adr` is fed from `asrc` only.  OMITTED, each enlarging the model:
  6 (`.rl` successor), 7-RCpc, 8.  `rvwmo_minus_deps_consistent ⇒
  rvwmo_cat_consistent` (its `gpoloc` ⊇ rules 1–3 and 12's target, its
  `grel_acq` ⊇ 7-RCsc); the converse fails (FWD+acq): RVWMO⁻ forbids
  store-buffer forwarding and the logic must not rely on it.
- **Instruction fetch is an ORACLE on the physical text region T** (as
  AxSL's `gimem`/`TStepReload`): the fetch returns the boot image; the fetch
  PTW reads are row events like data PTW reads.  T = `.text` incl. the
  trampoline; `.rodata` lies after `etext` and is ordinary `ro`-class data.
  Hardware AXIOM (declared, load-bearing for phase 2): a fetch observes only
  writes performed before the fetching instruction's events (fetch precedes
  execution; staleness without `fence.i` only removes writes), and the
  i-cache is coherent with the boot image at reset.  With it, the capstone's
  "no write targets T" (every write needs a token of class ≠ ro) makes the
  oracle coincide with real fetch reads.  xv6 never writes kernel text (`fence.i`
  only on the U-mode trampoline path).  User text: G5.
- Footprint: WP package + five `rv64d` axioms + the in-definition hardware
  statements (see "Assumption audit").  Rev 5 listed `¬violation_hart`,
  device `reducible` and the crash story as LOST; rev 6 makes them K1–K3.

## 0.5 THE FINDING (why this is not plain AxSL)

**SUPERSEDED by §7 (rev 7)** — the expected-value owned-read answer to C0
below, and the phase-1/phase-2 split it forces, are replaced by the ctrl
gate; left in place for the record.

AxSL delivers a read's VALUE only as a resource tied to the read event
(`∀ val` continuation).  Exact for weak memory, but the WP must SELECT the
next instruction before phase 2 delivers resources: after `c.ldsp ra;
c.ret` the fetch address is `ra`, and a `∀ val` continuation must verify
every kernel instruction under arbitrary registers (garbage `ra` INSIDE the
image; out-of-image garbage terminates the AxSL thread and is dischargeable
from the tied annotation).  Every function return has this shape, so plain
AxSL cannot be the base logic for xv6.  Counter-designs checked (review 3):
a prefix-indexed hypothesis or rely-guarantee WP is circular under LB
(po-later is gmo-earlier, so no hart's prefix is available first); an
invariant in `gconst_interp` or a class annotation on the graph is a kernel
side condition (rejected) or the same gmo induction.  The shape is forced:
**phase 1 runs on GUESSED values, phase 2 validates them in gmo order.**

Rev 4's mechanism (L1 deviation 4):
1. **Identity-only step hypothesis.**  The WP's per-step graph fact is
   kind + address + size + deps (aq/rl bits; NOT the write class — that is an
   L2 ghost): THE identity erasure is `AxPair.lbl_ident`; `AxGraphCat.ident_t`
   is a coarser presentation with a bridge function.  NEVER values (AxSL's `gs_graph !! eid =
   IEvent req resp` is value-inclusive and would stop phase 1 at the first
   data-divergent store, stranding independent later writes).
2. **Owned reads return the EXPECTED value `last H`** to the continuation;
   racy/protocol reads stay `∀ val` with tied protocol content.  A write's
   flow equation concludes `⌜data_gr = data_exp⌝ ∗ deposit`.
3. **Validation at the event's own gmo position.**  At an owned read `r`:
   every write gmo-before `r` is expected (a non-expected write is
   gmo-after its hart's responsible read by rules 11/13 or trap-ctrl, which
   would already have derived False), so `owned_read` + coverage pins
   `rf r = last H`, or False.  At a write: data sources are gmo-before
   (rule 10), validated by IH.
4. **No deferral.**  Phase 2 is the plain gmo induction; a read WITHOUT a
   flow equation (po-after its hart's identity-stop) deposits nothing and is
   skipped; a write without one is impossible at the point reached.
   Racy-read speculation needs nothing: the WP is `∀ val`, phase 1
   instantiates the real value.  Post-join writes ARE ctrl-dependent
   (RVWMO's syntactic definition; `ds_ctl` never shrinks) — only reads can
   be speculated.  Plain-read protocol opens are persistent-only (an L2
   rule; every L2 open at a plain read already is).
5. **Run pairing.**  "The real event equals the expected event once every
   read feeding its identity/data is validated" is a semantic lemma on
   `pexv6` runs agreeing off a tainted register set — built on
   `WeakEvProv2.tpar` (`AxPair.v`: `pair_ident`, `pair_ident_full`,
   `pair_resume`).  OPEN (foundations review): `tpid` is not closed under a
   shared non-writing prefix — Sail's `execute_STORE` reads rs2 (the DATA)
   BEFORE the address, so two runs differing in a tainted data register
   diverge at a `RegRead`, which `tpar`'s arms reject (`sw_not_tpar`).  The
   pairing relation must tolerate divergent register reads whose values flow
   only into store data (a `tpdd` relation); per-event validation form
   (only THIS write's data sources validated) to be stated.
This is an AxSL-structured logic (per-hart WP against a fixed graph, tied
annotations along lob, protocols along rf, gmo-order adequacy) with an
expected-value read rule for owned bytes.

**SUPERSEDED by §7 (rev 7)** — this phase-1 existential-run construction is
dropped; reads go back to ∀v and phase 2 becomes the gmo scheduler of §7(5).

**Phase 1 CONSTRUCTS the expected run (finding of the A4/A5 port,
2026-09-24).**  AxSL's `wp_steps`/`adequacy_po` replay a GIVEN run `σs → σs'`
against the WP; that shape is wrong here: under angelic reads the WP's
continuation carries the PROVER's value, so a shadow state produced by
`step_annot` agrees with an externally given step only in row position
(`AxAdequacy.v` §4, proved).  The port's phase 1 must therefore be an
EXISTENTIAL run construction — `wp_steps_expected : wp s Φ ∗ … ⊢ ∃ run
of astep_any from s, each step the WP's own choice, with the annotation
bookkeeping` — and the real run enters ONLY through `hart_conf` + the
identity-stop lemma (`AxGraphCat.ident_stop_lemma`) + `AxPair.pair_ident_dd`
(identity agreement until the first mismatched read) + the gmo induction's
per-read validation.  `AxAdequacy.step_annot` (one step, base case) is
correct as built; its iteration and `adequacy_ord` (phase 2 along `gx_gmo`)
are the OPEN items of G1.

**The step case, precisely (review 4 F3 — this shapes `wp_pre`).**  With
identity-only step facts the value of a read is FREE in the step relation,
so AxSL's uniform `∀ s'` is wrong: it would make the owned-read rule handle
every value (C0 again).  The opax semantics exposes reads with their
continuation, `aread_step GD i s ident (k : bv → athread)` ("s is about to
perform the read `ident` = `row !! at_k s` in identity; `k v` is the state
after reading `v`"), and writes/admin/fetch/fence as `astep s s'`.  Then

    step case at a READ:   ∀ ident k, ⌜aread_step s ident k⌝ →
                             ∃ v R na_used na_unused ls', … ∗ flow_eq GD e … (R ∗ ⌜v_graph e = v⌝)
                                ∗ … ∗ wp (k v) Φ           (* ANGELIC value: the prover's expectation *)
    step case otherwise:   ∀ s', ⌜astep s s'⌝ → ∃ R …, flow_eq … (R ∗ ⌜data_graph e = data_exp⌝) ∗ wp s' Φ
                                                          (* DEMONIC; vacuous at an identity mismatch *)

A racy read chooses `v := v_graph e` (the graph is quantified in `wp_pre`,
so the value is available).  An owned read chooses `last H` and its flow
equation carries the validation `⌜v_graph e = last H⌝`.  Consequences:
phase 1 produces the EXPECTED run (a run of the prover's choices);
`hart_conf` is about the REAL run; the two are linked by the IDENTITY-STOP
lemma — the expected and real rows agree in identity up to the first
position whose identity depends on a mismatched read, and every real write
po-after that position is gmo-after the responsible read (rules 9/10/11,
general 13, the context-CSR edges, trap-ctrl) — plus `tpar` for the
register-file agreement.  Phase 2's invariant is "every write at gmo
position ≤ n is annotated, or False has been derived" (AxSL's `na_full` is
dropped).  `progress_obl`/T2 is proved for the expected run and transported
along the identity-stop lemma.  Contractiveness is unaffected.

## 1. Architecture

```
  L3  SC-shaped surface     same names/types, DEGENERATE view; registers carry provenance
                            (dstate threaded); leaf layer RE-DERIVED from exec-level certificates
  L2  owned points-to       fraction-multiset token tied at the hart's same-byte accesses;
      (THE NOVELTY)         class-indexed universal protocol; epoch boundary invariant
  L1  AxSL base (ported)    awp/awpc over (pexv6 × position); identity-only step facts;
                            expected-value owned reads; gmo-order adequacy
  L0  opax semantics        threads = harts (pexv6), graph = gdexec, fetch oracle on T,
                            non-RAM devices = per-hart oracle stream, disk row empty
```

### L0 — opax over the event language
- Thread state `(p : pexv6, k)`.  Admin labels keep `k`; a memory label
  realizes `row !! k` in IDENTITY (kind/address/size/deps) and advances `k`;
  `LFence` is a flow-free step (fences are row items, not `gx_gmo` members;
  lob′ uses M→M `gfence_covers`, no fence node in phase 2).  Fetch on T:
  oracle.  `LDev` (UART/PLIC/CLINT): per-hart oracle stream (shared device
  state unmodelled until G5).  Disk row EMPTY until G5.
- `reducible_or_row_exhausted`: admin step possible, or the next memory
  outcome realizable by SOME row extension; `GenericFail`/`Discard` is not.
  CHECK: Sail on an access outside `gx_img`.
- Relations (`AxGraph*.v`): `grf/gco/gfr` on distinct events (the tree's
  `gfr` excludes the fused-RMW self-loop), `ob := (gppo_cat ∪ deps ∪ rfe ∪
  co ∪ fr)⁺`, `ob ⊆ gmo_lt`; gmo is a linear extension of ob.

### L1 — the AxSL base, ported (10–14k lines measured; four deviations)
Generic core (`low/` minus `rules/`) ported PARAMETRIC in: the linear order
of phase 2, the local flow relation lob′, the handout policy, the protocol
interpretation, the step relation's value policy (angelic reads), and the
annotated set (no `na_full`) — so L2 changes never reopen `wp_pre`.
1. **gmo-order phase 2 + gmo-prefix handout**: `flow_eq_dyn` takes
   `⌜gmo_pred e ⊆ s_ob⌝` (SUPERSET, as AxSL's `obs_pred ⊆ s_ob`; equality
   would forbid late discharge); phase 2 inducts along `gx_gmo`.
2. **Conditional same-hart same-byte flow edges**: `s_lob(e) := lob_pred(e)
   ∪ {e' | same hart, same byte, po-earlier, gmo_lt e' e}` (the `ob ∪ poloc`
   cycle witness makes the gmo condition mandatory).
3. **Protocol access**: one universal class-indexed Φ; `ob_st_interp gr s :=
   [∗ e ∈ s] Φ(e)`; exclusive open of the rf-source's Φ when the source is
   in `s_ob` (rfe, or rfi with source gmo-before — lock re-acquire);
   persistent content of ANY `e ∈ s_ob` readable; plain reads open
   persistent content only.  Initials: seed with the image (`Φ_ro`/`Φ_own`
   snapshots for `gx_img` bytes); boot resources predate every event (the
   one untied-but-sound case).
4. **Identity-only steps with angelic read values, expected-value owned
   reads, write-data validation, the identity-stop lemma, run pairing**
   (§0.5, "The step case").
Exports: T2 `not_stuck`, T3 coverage (= `hart_conf`), T4 `adequate_chk` +
`chk_pure`.  No `equations`/`record-update`/`hammer` in the switch.

### L2 — the owned points-to
- **Universal protocol**: `Φ(a)(v,e) := ∃ cls, cls_at a e cls ∗ Φ_cls(a)(v,e)`;
  the class at a write comes from the byte's class ghost, whose changes are
  WRITES under the class-owner right (never deposited in a protocol);
  writers of Lock/Flag bytes learn the class from the rf-source's Φ, never
  from a stale snapshot.  Shapes: `Φ_own := hist_snap a H_e`; `Φ_ro`
  (initial only); `Φ_lock` (byte 0: `v=0 ⇒ R_e ∨ ∃e', rf e e' ∗ Tok e'`;
  bytes 1–3 pinned 0; its token carries no H); `Φ_flag` (`v=1 ⇒ □P`).
- **Epochs (review 3 F5, review 4 F4).**  `owned_read` needs EVERY visible
  same-byte write in H.  The class ghost records the BOUNDARY event `b` of
  each class change; the history ghost is APPEND-ONLY (`AxGhost.v`, a
  mono-list per byte): H spans epochs and the class-change write APPENDS to
  it under the full token (pre-boundary writes of the retired class stay in
  H as legitimate entries); `owned_read_epoch` (AxGraphCat.v §7, PROVED) weakens
  coverage to "every visible write is in H or co-before the boundary
  `b ∈ H`" — PROVIDED `b` IS VISIBLE TO THE READER (`gvisible b r`; the
  unconditional form is refuted by the `epc` witness).  In the logic the
  boundary is the class-change write at the head of the token's H, which
  reached the reader along ob, so visibility is what the token gives.  The invariant "all writes of the retired
  class are gmo-before the change" is NOT given by the lock release chain
  (a FAILED `amoswap` is a Lock-class write outside it — a hart spinning on
  a freed pipe lock); so **every RMW on a Lock byte, success or failure,
  requires a fraction of an `alive(lock)` token tied at the RMW**, and the
  class-change write requires the full token — pipe/file refcounts hold the
  fractions, which makes "nobody spins on a freed lock" a resource fact.  Page reuse
  (data → pipe lock word → page table → user page) is a sequence of such
  boundaries.
- **The token** `tok a H S := [∗ e ∈ S] (e ↦ₐ ●{q_e} H)`, Σ q_e = 1, tied
  at the token's ARRIVAL event (boot, the `.aq` RMW, the fenced plain load)
  and at each of the hart's same-byte accesses `S` since: a read PULLS a
  piece from any gmo-earlier holder in `S` (deviation 2, or rule 5 from the
  acquire) and retains it; a write pulls ALL pieces (rule 1) and re-ties,
  `S := {w}`.  Tie invariant in GMO form (the conditional edge is not ob;
  `tie_inv`, `tie_read_i/ii`, `tie_cases`, `tie_acq_case` in AxGraphCat.v
  §7; the TOKEN carries `AxToken.tie_base := last H = tie ∨ last H <gmo
  tie` — the po-branch form is FALSE right after a write re-ties, by
  irreflexivity, and is unusable for protocol-carried cross-hart ties): `last H <gmo tie ∨ last H is a same-hart po-earlier write`, and the
  read rule's case (i) additionally needs the tie to be the hart's own
  po-earlier access (`gpo tie r`); H is gmo-chained (`owned_read_with`
  needs only `R ⊆ gmo_lt`); a protocol
  deposit at a release write `R` requires `last H <gmo R` explicitly (rule 6
  is omitted; xv6's fence supplies rule 4).  One transport lemma per edge
  kind.  Cross-hart moves only via protocols.
  Surface: `a ↦ax{q} v := ∃ H S, tok ∗ ⌜last H = v⌝`.
- **Write rule** (full token): `H ++ [(w,v)]`, deposit `Φ_own`, `S := {w}`,
  flow equation concludes `⌜data_gr = v⌝`.
- **Read rule** (expected `v = last H`, any fraction, `S ≠ ∅`), validated in
  phase 2 by gmo case: (i) some `e' ∈ S` gmo-before `r`: a piece flows in;
  any visible foreign write co-after `last H` is in `s_ob` and its
  `hist_snap` contradicts the fragment algebra (growth needs the full
  fraction; mixed fractions across a release/acquire chain are fine —
  agreement pins the auth); (ii) all of `S` gmo-after `r`: the hart's last
  local write `w ∈ S` is forwarded, every other visible write is gmo-before
  `r` hence co-before `w`, own earlier writes co-before `w` by rule 1, so
  `rf r = w` by load-value (`own_forward_cat`).  The IDENTITY-STOP lemma
  (`ident_stop_lemma`, AxGraphCat.v §7): with `d_covers` (every real write
  at or after the stop depends on a pre-stop read — supplied by AxDeps'
  tagged extraction: rules 9/10/11, general 13, context CSRs, trap-ctrl) and
  `D ⊆ gmo`, every unannotated real write is gmo-after a pre-stop read of
  its hart; the `isw` witness FAILS with the tree's untagged deps and HOLDS
  with the rule-13 edge.
- **Racy reads**: `∀ val`, tied protocol content; usable after `fence r,rw`
  / `.aq` or at ctrl-dependent stores.  Image sites: `holding` (second load
  ctrl-dependent on the first; persistent open), `started`/`first`
  (fenced), `panicked`/`pr.locking` (value reaches no obligation), virtio
  `used->idx` (fenced).
- **DRF export**: every read's rf-source is initial, own, or ob-before it.

### L3 — the SC-shaped surface
- Keep the TYPES of `view`/`vProp`/`⊒V`/`cobj`/`wptsto`/`whart_run` with
  DEGENERATE view content (every points-to objective; `cobj ξ R := R @@
  view_bot`; `wrunning ξ := ∃ ls, hart_local cpu ls ∗ ctx_migr ξ cpu`).
  `wpt_own`, `wpt8_own`, `wstack_own_phys`, `wkernel_text` re-defined with
  the same types; `WkTimerinit`/`WkStartNew` statements typecheck unchanged
  (track E).  Migration of stack tokens across `swtch`: a protocol at the
  scheduler-lock release/acquire (G3).
- **Registers carry provenance**: thread the tree's `dstate`
  (`ds_prov/ds_ld/ds_ctl`, WeakRvwmoConf.v:567) through the leaf layer as a
  pure component updated by `dstep`; `gpr_file` stays a projection.
- Ledger ξ: events whose annotations are usable at every later event (boot,
  `.aq`, covering fences per kind); tokens received at a plain racy load
  are usable after the fence (as `wstarted_deliver_gen` required).
- **Leaf layer RE-DERIVED** from the existing `exec`-level certificates:
  `wp_ainstr` has `RiscvExec.wp_exec_step`'s shape over the flat memory
  "gmo-prefix latest + own pending writes"; the 60-instruction M-mode cone
  needs `regonly_es`, `exec_eff_ld8_at`, `exec_eff_sd8_at`, the CSR family
  (all `mstate`-only, present; ~19.8k reusable lines; ~475 pf-level decls
  to re-derive).  **AxBridge** := an instruction's graph events realize the
  `exec` successor when every read is owned/oracle/own-last-written.

## 2. Staging, gates, parallel tracks

G0    rev 4 (this) — design complete for G1's generic core.             ← now
G0.5  MACHINE-CHECKED MODEL LEMMAS (`AxGraphCat.v`, `AxGraphWit.v`, in
      flight): `gppo_cat` incl. rule 12 + `rvwmo_cat_consistent` + `minus ⇒
      cat`; `AxGraph.v` restated; witnesses with proved verdicts: FWD+acq
      (separates the models), release-then-read (refutes tokenless rfi),
      `ob ∪ poloc` cycle (forces the gmo condition), stranded token +
      fraction-flow prototype, the RULE-12 witness (consistent without 12,
      deadlocks the induction; refuted with 12), the coverage form of
      `owned_read`, LB — DONE (`AxGraphCat/Dec/Wit.v`, 51 lemmas).  Owed,
      in flight as foundations tracks: tagged deps with general rule 13 and
      context-CSR edges + the `ld; ld 0(a0); sd` example (`AxDeps.v`),
      litmus conformance (`AxLitmus.v`), the ghost algebra incl. `alive`
      (`AxGhost.v`), `tpar` restated (`AxPair.v`), `owned_read_epoch`
      (`AxGraphCat.v`), the identity-stop lemma (pure, on rows).
G1    L0 + L1 generic core (parametric in order/lob′/handout), identity-
      only steps, T2/T4 adequacy on `gdexec`; LB litmus with a protocol fact.
G2    L2 tokens + class/epoch ghost + expected-value read; `wp_ainstr` +
      AxBridge for M-mode; vertical slice: 1 hart, `sd a5,0(a4); ld
      a5,0(a4)` with `gmo ld < sd` (case ii) from the real Sail rows via
      `hart_conf`, concluding `a5 = stored value` at the boundary; then
      leaves `ld/sd/csr/lui`, `WkTimerinit` re-checked.
G3    `Φ_lock`/`Φ_flag`; `acquire/release`, `started`; `WkStartNew`; 2-hart
      MP `sd; fence rw,w; sw lock` / `amoswap.w.aq; ld` (case i + `Φ_lock`);
      class-change write (`initlock` on a kalloc'd page); stack-token
      migration protocol.
G4a   single-era capstone core (the statement above); `Print Assumptions`
      = five `rv64d` + the audited in-definition list.
G4b   K1 + K2: `gviolation_hart` + DRF refutation + the srvwmo subsumption
      corollary; disk/UART/PLIC as graph agents with state (disk as agent
      moves HERE from G5), device `reducible`; `disk_row_empty` and the
      `LDev` oracle removed from the statement.
G4c   K3: era sequence, gmo-prefix cut, persisted disk, crash-spanning
      invariant in the disk Φ; the final `xv6_rvwmo_safe_ax` must imply
      every conclusion of `xv6_srvwmo_safe` (checked as a corollary).
G5    walker A/D (`Φ_pte`, `sfence.vma`), U-mode rows and user text,
      fabric/interrupt state.  (Trap-entry emission hook: G3, needed by the
      first multi-hart theorem with a value-fed address.)

Tracks: A = L1 generic core port (can start now, parametric); B =
`rvwmo_cat` + litmus conformance (reuse `WeakSrvwmoLitmus`); C = L2 ghost
algebra + validation lemma + epoch lemma; D = `tpar` run-pairing restated;
E done.  Then F = `wp_ainstr` + AxBridge (A,C,E); G = surface instance
(E,F); H = sync protocols (A,C); I = capstone.  Estimates: L1 6–10
agent-days; L2 3–4; AxBridge 8–12; ≈ 20–25k lines to G2.

## 3. Risks (ranked) and fallbacks
1. §0.5 mechanism has a hole not caught by three reviews.  Gate: G0.5's
   rule-12 and coverage lemmas; G2's vertical slice.  Fallback: sync
   idioms as litmus theorems; record the finding.
2. Token flow (fraction multiset) vs AxSL's pull-based `na_splitting_wf`.
   Gate: the stranded-token prototype.  Fallback: token in `local_interp`.
3. Epoch/class discipline (F5) — the read rule depends on it; design in
   G0.5, not G2.
4. AxBridge / leaf re-derivation size.  Mitigation: exec-level certificates
   exist; reflective batching; M-mode first.
5. `gppo_cat` audit vs riscv.cat (rules 2/3/12/13; trap-ctrl; fused RMW).
6. Device oracle blocks `virtio_disk_intr`-style proofs until G4b.
8. K3's gmo-prefix cut is a hardware claim about power loss that RVWMO does
   not state; if it cannot be justified, the fallback is a weaker cut
   (per-hart po-prefix + performed-disk-writes) and re-deriving (c).
9. K1's restatement could silently be weaker than `violation_hart` — the
   subsumption corollary is the gate.
7. Port friction (Coq 8.19→Rocq 9.0.1, iris 4.3→4.4, no equations/hammer).

## 4. Not in scope now
The instruction-atomic SC tier (`Proof*.v`) stays on `riscv_lang`; the
whole-kernel WP package remains a hypothesis.  Liveness.  Moving fabric
and interrupt delivery beyond the oracle, user text: G5.  (Crashes/eras and
the disk are IN scope since rev 6: G4b/G4c.)

## 5. §C14 — breaking the phase-1/phase-2 circularity

**SUPERSEDED by §7 (rev 7)** — this candidate-D repair attempt is moot: the
ctrl gate removes the phase-1/phase-2 circularity a different way (no D
relation at all). Left in place; the C6-coverage argument below still
applies verbatim under the gate.

**Candidate D**: r ← rf-source(r) (`grf`, WeakRvwmoAcyc.v:134) and its
gco-predecessors; e ← every read some addr/data/ctrl/ctx dependency of e
traces to (`AxDeps.gtdeps_rel`, rules 9/10/11/13/ctx, incl. fetch/pc via a
trap-entry ctrl node).  Claim under test: `D ⊆ ob ∪ (ctrl→R)`, hence D
acyclic under `rvwmo_cat_consistent_t`.

**Verdict: FAILS as stated on two concrete, machine-checkable points; a
narrowed repair survives but does not shrink the real (C6) blocker.**

1. **rf-source edges are not always ob edges (check (b), confirmed real).**
   `own_forward_cat`/`own_forward_cat'` (AxGraphCat.v:453,494) is read-rule
   case (ii): the rf-source `w` is the hart's own po-earlier write with
   `¬gmo_lt w r` — design §1-L2 states this case as "all of S gmo-after
   r".  Every ob edge is gmo-forward (`ob_cat_t_sub_gmo`, AxDeps.v:345),
   so a forwarded read's read→source edge is in neither ob nor (a
   nonexistent) ctrl→R.  `D ⊆ ob ∪ (ctrl→R)` is false for every owned read
   resolved by forwarding.  Fix: drop this edge from D for hart-local
   forwarded reads — case (ii)'s hypotheses (`Hnmo`/`Hnoint`) are
   graph-decidable (`gwix`/`gco` data, WeakRvwmoAcyc.v:141), not iris
   resources, so such a read needs no D-predecessor to pin at all. This
   narrows D's *scope*, not just its statement.

2. **ctrl→R does not exist, and cannot be added soundly.** `AxDeps.dtag_w`
   (AxDeps.v:135) forces every `DTctrl` edge's target to be a WRITE
   (`gtdeps_wf`, AxDeps.v:149); `dstep_t`'s `LCtrl` arm only feeds
   `dedges_w` (AxDeps.v:432), never `dedges_r` (AxDeps.v:429). So
   "ctrl→W ⊆ ob" holds (`gtdeps_rel` is a direct disjunct of
   `gobr_cat_t`, AxDeps.v:325 — no ppo detour needed) but ctrl→R is not a
   relation the model emits, and the brief's own MP-with-ctrl-only-reader
   cycle is exactly why: ordering a control-dependent LOAD is a real
   hardware strengthening (speculated loads need not wait on their
   branch) and is litmus-falsified by that MP case, failing §0's own
   assumption-audit criterion. "Every D-cycle through ctrl→R shortcuts to
   an ob-cycle" is therefore not dischargeable by exhibiting the edge; it
   would need a from-scratch soundness argument that never materializes
   it, which the brief does not supply and none of the existing lemmas
   give for free. Separately, the trap-entry ctrl node this relies on for
   fetch/pc coverage is not built yet (`erw_of` emits `LCtrl []` at the
   trap redirect today; hook is a G3 item) — even a sound ctrl-edge
   argument would rest on a still-open dependency.

3. **Even granting 1+2, D-acyclicity does not discharge C6.** Coverage —
   "every visible same-byte write is in the token's Hl" (`AxGraph.
   owned_read`'s premise) — is about who may WRITE byte `a`, which the
   graph does not expose (AxAdequacy.v:444's FINDING, verbatim: "who may
   write byte a is enforced by ghost ownership, not recorded in
   `gx_lbl`"). D is built only from graph-decidable data (`grf`/`gco`/
   `AxDeps`' tagged deps — all fixed once `gload_value`/`gwix` hold,
   WeakRvwmoGraph.v:224). No acyclicity of a graph-only relation supplies
   the OWNERSHIP-EXCLUSIVITY argument (no un-owned write to `a` exists)
   that only the class/epoch/token machinery (AxGraphCat.v §7.1–7.2,
   `AxGhost`) gives. D-order induction would still need to interleave
   that same resource argument; it only tries to move *when* it starts,
   not remove it — this is exactly the candidate's own check (d), and it
   is unresolved, not resolved.

4. **Structural cost the plan understates.** Phase 2's generic core is
   hard-wired to gmo, not an abstract order: `axpol_wf_gmo`
   (AxAdequacy.v:679) requires `s_pol`/`lobp ⊆ gmo_take`, and
   `adequacy_ord_aux` (AxAdequacy.v:798) inducts on the `gx_gmo` LIST —
   chosen specifically to avoid AxSL's ~150-line `ob_set_ind_L`
   well-founded set induction (AxAdequacy.v:615). Since D ⊄ gmo (point 1),
   walking `gx_gmo` does not visit D-predecessors first "for free" the
   way it does for ob. Running phase 2 on a D/resource-flow downset is
   therefore not the drop-in the plan implies; it reinstates the general
   well-founded induction deviation 1 was chosen to avoid.

**Best alternative (the brief's own item (e)).** Split the read rule: (a)
hart-local forwarded reads pin FOR FREE at phase-1 time from case (ii)'s
graph-decidable hypotheses — no C6, no D, no `AxPair` pairing needed
(the forwarding case never needs cross-run agreement, so it sidesteps
`tpid`/`tpdd`'s open `sw_not_tpar` gap too); (b) every other owned read
stays on today's path — demonic `∀v` (AxSL-shaped) plus the tie
invariant's lob-ordered fact (`tie_inv`/`tie_read_i`/`tie_acq_case`,
AxGraphCat.v §7.2), validated at its own gmo position exactly as now.
This shrinks phase-1 guessing to the genuinely angelic cases without
inventing an unsound edge or a second induction order.

**Work estimate.** Formalizing 1 + the (a)/(b) split: 2–3 agent-days
(mostly restating `own_forward_cat`'s hypotheses as a phase-1-usable
lemma; `read_pin_hyp` narrowed to forwarding sites only). C6 (coverage)
is unaffected and stays the dominant open cost already tracked in
§1-L2 "Epochs" — this exercise does not reduce it. A genuine D/well-
founded phase-2 core, if pursued instead of (b), is a re-derivation on
the order of AxSL's original set-induction machinery — open-ended, not
recommended given 1–3 above.

## 7. rev 7: ∀v reads + ctrl gate (owner-ADOPTED — this section is the
authoritative spec; review: `design/weak-memory-lb-axsl-review-fetch.md`)

Owner HARD REQUIREMENT, binding below: simple SC-like, pure-value
verification of sequential code must remain possible.

1. **Reads.** ∀v everywhere, AxSL-faithful — no expected-value angelic
   owned reads. Owned-byte fact `R := ⌜v = last H⌝`, validated at the
   read's own gmo position, OR at a DEFERRED position when the read is
   gmo-after a still-open gate (§(5)). Racy/protocol reads unchanged.
2. **The gate.** At every `LCtrl`/trap-redirect node, the WP step form is
   `∀ s', astep s s' → (⌜pure facts of annotations of loads in dt_ctl⌝ -∗
   wp s' Φ)`. Only PURE facts cross — never a resource or an annotation's
   full content. Handing over more (e.g. a `□P` from a `Φ_flag` open) lets
   the prover frame it into an unrelated ctrl-only load's FE, proving a
   value RVWMO forbids (MP+ctrl: `ld flag; beqz …; ld data` racing a
   writer becomes provably-consistent-only, which is unsound). Gate on
   `dt_ctl` (every later W is ordered after it, `dedges_w`/`DTctrl`,
   AxDeps.v:432), not bare pc-provenance.
3. **Fetch.** Stays an oracle sink (`AStepFetch`); no fetch edge added to
   the model, `rvwmo_cat_consistent_t` untouched. Drop the fetch position
   from `dt_ld` at emission, OR prove `pc-prov ⊆ dt_ctl`. Fetch-PTW reads
   stay ordinary row events, not pc-addr-dependent.
4. **L3 registers.** `r ↦ᵣ⟨x⟩ := ∃ v P, r ↦ v ∗ prov r = P ∗ (annots(P) ⇒
   v = x)` — value, provenance, fact — propagated by every ALU/move/CSR/
   spill rule, REFRESHED to concrete only at a gate. Specs/ghost updates
   are stated in `x`, never `v`: ordinary sequential arithmetic needs no
   gate and no graph fact, which is what keeps pure-value verification
   possible. The five review snippets: (a) `sd ra;…;ld ra;ret`: the
   `ret` fetch's gate turns `ld ra`'s fact into `pc = ra0`, code in
   between stays symbolic. (b) `ld a0;addi;sd a0`: no gate; `sd`'s FE
   takes `⌜data_gr = x+1⌝` directly, SC-like. (c) `ld t0;beqz t0`: gate
   at the branch; wrong arm vacuous, right arm gets `x` as a hypothesis.
   (d) value kept, used as address later: fine if `dt_prov` survives
   moves/CSRs/spills; open item is T2 for garbage `v` outside `gx_img`
   (needs (6)-ii). (e) value only compared/stored to an `LDev` oracle:
   fact is LOST, no consumer exists before K2 (§(7)).
5. **Adequacy.** Phase 2 becomes a JOINT gmo scheduler with a per-hart
   frontier: a hart's WP advances to its next gate; writes are NEVER
   deferred (rule 11: every po-later store is ordered after the loads a
   branch/jump depends on, so a locked hart's po-later writes cannot be
   gmo-earlier); only READS may be gmo-earlier than an open gate, and
   those are DEFERRED, discharged by superset handout once the gate's
   last source validates. C6 coverage still closes in gmo order. Measure:
   lexicographic, gmo index × deferred-set size.

**Obsoleted**: `wp_steps_expected`, `read_pin_hyp`, expected-value angelic
owned reads, `AxInstrOwned` targets as currently stated, the `AxPair`
`tpdd`/`sw_not_tpar` gap (was only ever a phase-1 device).
**Survives**: the graph layer, `AxDeps`, `AxGhost`, `AxToken`, `AxBridge`,
`AxProt` (mostly — state interpretation unchanged, only the gate-node WP
form changes), the `adequacy_ord` machinery (reused by the scheduler, not
discarded), `AxFetch`.

6. **Prerequisites, in order:** (i) trap-entry emission hook with sources
   (`erw_of` must emit real `LCtrl` sources at the redirect, not `[]`);
   (ii) Sail out-of-image CHECK, or a gated-progress obligation, for
   garbage-pc T2; (iii) `sstatus`/`sie` added to `ctx_csrs` (today only
   `MSTATUS`/`MIE`); (iv) the AxGate lemma (`dt_ctl` orders every later
   write — the formal form of (2)); (v) scheduler adequacy (the joint gmo
   induction of (5)); (vi) tie lemmas restated in PROCESSING order for
   deferred reads — `AxTieProc`. Main risk: (vi) — a deferred read's
   forwarding source may be a pre-gate write whose tie fact was proved
   for the wrong (emission) order.
7. **Open question.** A value whose only consumer is an `LDev`/UART
   oracle write carries no graph fact today (no consumer exists to gate
   on) — the fact is LOST between the gate and K2 (devices as graph
   agents). Until K2 this is unverified content, not unsoundness: nothing
   downstream depends on it.

**Retired** (pre-pivot code deleted 2026-09-25; gist of each FINDING kept
here, full text was in the deleted file's header):
- `AxInstrOwned.v` (whole file, deleted). FINDING: `t_owned_read`/
  `t_owned_write` as stated in `AxInstr.v` (universal over an arbitrary
  `axirisG`/stuckness) are unprovable, three independent gaps: (1) no
  premise ties an abstract `gconst_interp` to the target's own `GD` (needs
  a concrete `graph_agree`-shaped instance); (2) `wp_pre_step_def`'s step
  clauses are universal over every step at `s`, needing an
  exclusivity/uniqueness fact (`aread_step_det`) nothing in `AxOpsem.v`
  supplies — the same gap as `AxLifting.v`'s undelivered `wp_step`; (3) for
  the write half, `Rtok`/`Rtok'` are fully abstract with no tie to
  `AxToken`'s ghost — advancing `prot_inv` across a write needs a real
  `AxToken.owned_write_rule` update, not an abstract witness.
- `AxAdequacy.v`: `read_pin_hyp`/`read_pin_val`/`aident_of_row` (deleted).
  FINDING (the phase-1/phase-2 circularity, C0∩C6): pinning an owned
  read's value ahead of phase 2 needs the very class/epoch coverage (C6)
  that phase 2's protocol/token machinery discharges — using it inside
  phase 1 to justify phase 1's own construction is circular, and under LB
  `po ∪ ob` is cyclic, so no well-founded phase-1-then-phase-2 schedule
  exists. `read_pin_hyp` broke the cycle by fiat (grant `s_pol GD e = ∅`
  per read event); moot under rev 7's ∀v reads + ctrl gate, which sidesteps
  the pin entirely (item 1/5 above).
- `AxGateWp.v`: `wp_ev_step_owned` (deleted). Superseded by
  `AxReadAll.wp_read_all`/`wp_read_all_wand` — `wp_ev_step_owned`'s
  `∀a,⌜a=x⌝→Body(a)` guard is inter-derivable with `Body(x)` alone (a
  guarded ∀ over a decidable equality does no work), so it was angelic-
  pick-`x` wearing a ∀ as a costume, not the genuinely demonic ∀v rule
  item 1 asks for; see `AxReadAll.v`'s header FINDING for the full
  argument.

### 7.H Hardware model of the LB theorem (owner-accepted 2026-09-25)
The LB capstone is the same claim as `xv6_srvwmo_safe`, over RVWMO (`riscv.cat` + tagged deps)
PLUS the explicit hardware model below. Each item is a modelling commitment `riscv.cat` does not
cover; each must appear in the capstone's audited assumption list (C13), since most live inside
definitions and are invisible to `Print Assumptions`.
- H1 fetch: instruction fetch is an oracle sink on kernel text (value = the text image; no ob/lob
  edges out of a fetch). Sound because kernel text is never written — a KERNEL INVARIANT to prove,
  not an assumption. User-mode fetch values are irrelevant to kernel safety (user code arbitrary).
- H2 trap entry: a trap redirect is a ctrl node whose sources are the loads the trap decision
  depends on (faulting address, CSR state); rule 11 orders later stores after them.
- H3 context CSRs: writes to ctx CSRs (mstatus, mie, + sstatus, sie to add) are serializing
  w.r.t. later memory events (ctx-CSR edges in AxDeps).
- H4 out-of-image access: Sail traps (access fault) on accesses outside the memory image, rather
  than getting stuck — or, equivalently, progress obligations are gated.
- Base: the 5 rv64d platform axioms of tier 1 (unchanged).
Not assumed: fence.i / cross-modifying code (kernel never writes text); store-buffer forwarding is
modelled faithfully (AxGraphCat), not assumed away.

### 7.R Realized architecture (as of 2026-09-27; supersedes 7's PLAN where built)

- **Scheduler** (`AxSchedGD`/`AxSched`/`AxAdequacyL`): a joint gmo scheduler; a
  hart LOCKED at an open gate defers EVERY later event (not just reads);
  deferred reads are validated against the FROZEN history deposited by the
  last gmo-before write (`owned_read_ghost_snap`), not replayed live — closes
  phase 2 (`sched_proc_adequate`, `adequacy_ord`).
- **Gates** (`AxGateWp`/`AxGateAdeq`/`AxProtGateN`): `wp_gate`'s step form
  hands over PURE facts only, sourced via `dt_ctl` (never bare pc-provenance
  or a resource/annotation); purity is a named, separately-discharged
  invariant (`na_pure_global`), not a free consequence of adequacy.
- **Demonic read + symbolic registers** (`AxReadAll`/`AxSymReg`):
  `wp_read_all` is the genuine ∀v rule (frame-carrying wand, not an angelic
  pick dressed as a ∀); `AxSymReg` carries `⟨v, P⟩` (value, provenance,
  validity-fact) through UNMODIFIED SC-shaped leaf specs — the HARD
  REQUIREMENT holds by construction, not a parallel proof system.
- **n-byte ownership** (`AxProtBytes`): `owned_expected_writeb` /
  `wp_write_owned_tokn` and `wp_read_owned_tokn` give owned n-byte reads and
  writes with store forwarding handled (no `Hnofwd` needed on the write
  side).
- **Protocol instance** (`AxProtCov3.axprot_pol`): the concrete `na`/`ea`
  handout is BY GCO-PREDECESSOR — each write's ghost snapshot is routed to
  its unique immediate gco-successor (`axprot_immpred`/`axprot_immsucc`),
  turning the abstract coverage obligation into one closed entailment over a
  real scheduler run.
- **Capstone** (`AxEpiChain.epilogue_consecutive_ret_own`): the three-
  instruction epilogue as one connected hart run, return target pinned BY
  OWNERSHIP; residuals are pre-spill token well-formedness, row-shape/
  decode-bridge frame-safety facts, the M-mode tower at entry only, and one
  pure geometry fact (`Hdisj_ld`) — no ownership content in any residual.

**LESSONS** (vacuity traps caught, each cost a rebuild before being caught —
always smell-test that ownership is load-bearing, not merely present):
1. Read-data hypotheses stated over ALL non-writes are vacuous on fences
   (`Hrdat_spec`/`Hrdatn_spec` bug) — restate over reads only.
2. Gate facts derived only from the graph (load-value axiom) are vacuous:
   they never tie a reader's OWN token to the graph value, so "ownership"
   did no work until the token was threaded through explicitly.
3. A "connected run" can be a free-endpoint run / free-state bridge /
   memory-derived reload value that proves the register/PC conclusion
   WITHOUT ownership ever being used (`Hram8_ld` — tracked sequential
   memory, not `graph_value`) — check ownership hyps are structurally
   required to BUILD the final call, not just present in context.

### 7.L Lock-slice theorem statement (advisor, 2026-09-27) — authoritative
Root cause of five vacuous/trivial capstones: the THEOREM AUTHOR fixed the shape of the Iris premise
(closed `⊢ own` hyps, ∀-instances, author-chosen kind-indexed annotation tables) and read the conclusion off
that shape. Rules: the CLIENT chooses the annotations (∃ ea na); ghost names are ∃-allocated inside the
soundness continuation; initial resources are WAND ANTECEDENTS, never `⊢ own` hypotheses; the instance is the
FIXED one (`ob_st_interp := prot_inv_lock'`); the discipline comes from the PROTOCOL alone (every x-write must
discharge `Φp_own`, which demands the unique full `hist_auth γ x 1`).
```
lock_client_verified GD L x := ∃ ea na, <dom/lobp side conditions> ∧
  ∀ Hinv γ γc, ⊢ hist_auth γ L 1 [] -∗ hist_auth γ x 1 [] -∗ claimed_auth γc ∅ -∗
                 ord_ea_todo_L (AxLock_inst L x γ γc) GD (ea γ γc) (na γ γc) (gx_gmo GD) 0
lock_mutex_disc : consistent ∧ lock_pattern ∧ lock_paired ∧ lock_client_verified ⇒ ∀ x-writes, xw_is_cs_write
lock_mutex_value := cs_handoff_last ∘ lock_mutex_disc
```
Certificates (mandatory, same file): (a) `lock3s_verified` (multi-writer, satisfiable); (b)
`race_not_verifiable` as a corollary of `lock_mutex_disc` + `¬ xw_is_cs_write race w_c` (uses race's graph);
(c) `race4_verified`. Smell test FIRST: the racing write is unverifiable even with the trivial annotation
under AxLock_inst (else the theorem is false). Gaps: G1 (M) derive the discipline from prot_inv_lock' +
tok_tie holder facts (Φ_lock' carries "holder is an acquire gpo-before"); G2 (M–L) the 12-event lock3s
witness (write an `ord_ea_todo_L_of_list` helper first); G3/G4 (S). Tier A (premise = per-hart WPs, maps
built inside) needs wpc_adequacy / phase-1 run-pairing and lock3s as instruction rows: separate effort (L).

### 7.T Tier B cannot make ownership load-bearing (advisor, 2026-09-27)
A premise of the form "∃ client annotations, ⊢ ord_ea_todo_L …" lets the client discharge each event's
obligation by ANY Iris proof, and the protocol's ghost updates are unconstrained, so resource-only
invariants are defeated: (a) claim-steal (a racing write adds a release to the claimed set and takes the
token); (b) genesis-steal (flip the initial-slot flag); (c) proxy-append (hist_append has no graph side
condition; a snapshot prefix certifies a racing write); (d) lobp edges admissible across harts. The only
fix inside Tier B puts the discipline as a pure conjunct in ob_st_interp — which makes each write prove its
own CS membership as a graph fact, so ownership does no work. DO NOT retry the resource-only Tier B route.
Also: `claimed_auth γc ∅ -∗` in the wand antecedent double-uses the σ0 resource (premise unsatisfiable).
TIER A is the target: premise = per-hart WP proofs; annotations constructed inside adequacy; the ONLY way to
produce a write's flow facts is the WP write rule, which demands the token.

### 7.A Tier A adequacy (advisor spec, 2026-09-27) — authoritative plan
Statement: `tierA_adequacy GD (Hcons) harts p0 pfin post (Hrun: ∀i, row_emitted_from_run over grow GD i at graph values, p0 i → pfin i) (Hwp: ∀ invGS axlogG ax_lockG γ γc, at FIXED AxLock_inst γ γc: ∀ i, ⊢ init i γ γc -∗ WPd (AThread (p0 i) 0) @ i {{ s, ⌜post i s⌝ }}) : ∀ i, post i (final state)`. Inside: allocate γ γc, σ0 with the ONE genesis `hist_auth`, and `[∗] init i` from the same allocation; phase 1 → `sched_proc_adequate` → soundness. `post` on the REAL final state.
FINDING: `wp_steps_expected` is UNPROVABLE for `wp` as defined — read arm (a) is `∃ a, …`; adequacy gets an unknown `a`, learned only in phase 2; under LB the hart must be unfolded past the read first, so the continuation can't be matched to the run (wrong-witness shadow run need not cover the row). FIX: `WPd` = same fixpoint with arm (a) pinned like the RMW sub-arm: `∀ v, ⌜graph_value GD (i,at_k s) = Some v⌝ -∗ ⌜length v = n⌝ -∗ wp_ev_step … (wp (K v) Φ)`. `WPd ⊢ WP`; derived read rules re-prove (they already take `Hgv`).
Phase 1: `wp_steps_d` by induction on `Hrun`, step_annot's script with `sw := s'` (no shadow); output static `na_i/ea_i`, `dom na_i` = row prefix, `ea_local_wf` ≅ `ord_ea_todo_L … 0`. Union over harts (disjoint domains). Fetch: via `aread_step` with R := emp, or excluded.
Why client can't cheat: not "only the write rule produces flow facts" (unenforceable) but `flow_eq_dyn`'s ∀σ ∀s_ob ⊇ s_pol: the writer must succeed against every protocol configuration; exclusive auth reachable only via own-hart `flow_in` (built by adequacy, not the client). Requires protocol conjunct on CLAIMS: `D ⊆ {r | ∃ e ∈ s, RMW e rf r}` (gatomicity uniqueness), so acquire is ∀σ-robust (`prot_inv_lock_rmw_step'` currently takes it as hypotheses = G1).
Plan: A1 (M) AxWpD.v: WPd + wpd_wp + read rules. A2 (S) run_at_graph_values + fetch. A3 (M) wp_steps_d + row coverage. A4 (S) ord_ea_todo_L_of_ea_local_wf, union. A5 (S) tierA_adequacy gate-free. A6 (M) G1 claims conjunct, ∀σ-robust flow eqs. A7 (M–L) lock3s as rows + per-hart WPd proofs; certificate: lock3s_verified ⇒ v = vx_A; race_wp_unprovable (C's `sd x` alone); sanity: Φp_own := emp makes C provable. A8 (L) gates: joint frontier induction.
First milestone: A1 + A3, one hart, skeleton instance, Print Assumptions clean. Main risks: fetch/admin arms + na_at_progress in wp_steps_d; A6 atomicity-uniqueness lemma (AxLockSerial cs_acq_src nearest).

### 7.A7 lock3s certificate plan (advisor, 2026-09-28)
AxProtLock2 honest (x-write & release need token via flow_in; non-holder L-write blocked by CLAIMS+HM). Gaps: (a) s_pol := ∅ makes lock_acq_flow_eq uninstantiable — need axpol with s_pol e := external rf-sources; (b) lemmas proved on lock2_axirisG (ax_text False), must be on AxGA2 with ob_st_interp0 := λ nm, prot_inv_lock'' nm.1 nm.2, N := gname*gname; (c) no initial-acquire rule: first RMW reads image (t=0); add genesis flag g in ob_st: (g=false ∗ hist_auth γ x 1 []) ∨ (g=true ∗ ∃ e∈s, RMW reads t=0 at L), uniqueness via gatomicity, Himg L = b0.
A7 = option (b'): hand-written pexv6 programs (Sail monad term emitting exactly the row, no decode), ABSTRACT GD with rows pinned but rf indices/values quantified. lock3s_verified (per-hart WPd, per-hart row hyps), lock3s_value (tB = A's release ⇒ vB = A's value, etc.), race_wpd_unprovable via tierA_adequacy_ann on CONCRETE race GD (legit: unprovability witness). Stages: T1 AxProtLock3 (genesis, transport to AxGA2, lock_axpol, Hob_alloc); T2 WPd amoswap/release rules + writer/reader hart lemmas (riskiest: RMW step bookkeeping); T3 assembly + race.
Reader owned read (advisor, 2026-09-28): do NOT enlarge s_pol to gmo-prefix (gmo_lt ⊄ gob_cat_flow; breaks Hs_pol_sub). Instead lock_pol_s e := rfe-sources(e) ∪ {w' | ∃ w0, grfe w0 e ∧ gco w' w0} (still ⊆ gob_cat_flow via gco;grfe); weaken flow_eq_owned_read's Hpref / prot_inv_prefix_cov_mem to byte-a writes gmo-before r; graph lemma x_writes_gmo_before_read (w = w0 ∨ gco w w0). Reader lemma lock3_read_flow_eq (tok_tie at acq ⇒ ⌜grf_at x w_x r ∧ v = vx⌝ ∗ tok_tie retied to r). Genesis reader: byte coverage vs hist_auth [] ⇒ no gmo-earlier x-write ⇒ reads image (needs bridge lemma). Reader post MUST be program-level: ⌜(grfe (j,3) (i,0) → vB = vw) ∧ (rf-src (i,0) = None → vB = img x)⌝ — the current AxLock3Reader post is VACUOUS.
Reader post (advisor, 2026-09-28b): option (a). 5th pure conjunct of prot_inv_lock'' — at each release w ∈ s writing L b0: hm !! w = Some Hh ∧ tie_base Hh.*1 w ∧ hist_x_wf Hh ∧ (∀ x-write w' gpo-before w: last Hh = Some (w',v) ∨ ∃ x-write w'' with gpo w' w'' ∧ gpo w'' w) — i.e. Hh's last = the po-latest x-write before the release (conditional; no "else = acquired history" arm; not program-specific). Reader post: ⌜(∀ j v, grfe (j,3) (i,0) → gwrites_byte (j,1) x v → vB = v) ∧ (acq reads image → vB = img x)⌝. HONESTY: lock3s_value is graph-true anyway (AxLockSerial.cs_handoff_last); its novelty is modularity; ownership-load-bearing evidence = race_wpd_unprovable, kept together in T3. ≥2 writers not required.
Vacuity audit (Fable, 2026-09-28): tierA_adequacy_ann, lock protocol/flow eqs/policy, lock_read_own(_genesis) SOUND-NONVACUOUS; capstones sound as designed modulo the section-Context leak. Before T3: (1) Φreader := λ _, ⌜Preader_pure⌝ (drop the at_p/x10 state guard — vacuous for perturbed runs); (2) race_wpd_unprovable about hart C alone: instantiate writer-gen + reader-rel at the concrete race GD, conclude ¬(∀ Hinv Hann nm, ⊢ lock3_init nm C -∗ WPd_C {{True}}), plus the Φp_own := emp sanity twin (C provable under the trivial protocol); (3) explicit T3 premise "both acquires read b0" + gx_img L = Some b0, with a genesis/rel dichotomy lemma (acquire reading an acquire-write b1 is consistent for these spin-free rows and uncovered — state the exclusion). lock3s_value only via tierA_adequacy_ann (Hrun := l3p_*_run, Hob_alloc := lock_Hob_alloc, T := λ _, False), NOT cs_handoff_last. reader_rel's j0 pin is 2-hart-only (reader-from-reader release uncovered — not modular; acceptable for lock3s).

### 7.HI MAJOR DESIGN POINT: cross-hart resources are HANDLES in phase 1 (owner-accepted 2026-10-02)
A resource transferred between harts (lock-protected data, a lock's `locked` token, anything a
protocol moves along rf/ob) exists for the receiving hart ONLY IN PHASE 2. Phase 1 unfolds every
hart's WPd before any flow equation runs, so no WPd can hold such a resource in hand: SC-tier posts
like `acquire {{ locked ∗ R }}` become handle posts `{{ ∃ c, c ↦ₐ (locked i c ∗ R c) }}`, and owned
points-to inside a critical section become HANDLE points-to `a ↦ₕ v := ∃ e, e ↦ₐ (tok a … ∧ last =
v)` moved along the hart by owned load/store leaves when e ∈ lobp r. This is FUNDAMENTAL to the
two-phase design (not a gap); the SC proof shape is preserved because the surface is already
provenance-based (AxSymReg) and value facts already surface at post_lifting / gates. Costs: per-address
handle components, a forwarded-reload leaf for read-after-write of protected locations, release
gathering components through its fence. Full statement + costs: design/weak-memory-lb-axsl-spinlock.md
"MAJOR DESIGN POINT". Also: Iris invariants over MEMORY are unavailable for the same reason (no global
"now"); ghost-only invariants are an open, unchecked question (same file, progress notes).

### Stage 4 scope (advisor, 2026-09-29)
epilogue_consecutive_ret_own has NO WP (pure conclusion, resource premises: hist_snap wand + post-spill tokn). Jobs: J1 drop unconsumed Hwelldef from AxEpiShape.epilogue_ret_target_spill_reload_of_row (AxEpilogue's run-level Hwelldef IS consumed — keep); J2 derive HVsvs from af_csdsp_row_run's LStore witness + ak_sync wak_plain = false (expose via af_csdsp_frame); J3 docs: residuals split into (H) hardware/layout/ABI (M-mode tower at σ0, Hdisj_ld, Hra/Hra2, HD_*_safe) vs (P) protocol (pre-spill wf, post-spill token); Hbytes8_ld already gone. Prop-level epilogue via tierA_adequacy_ann = stage 5, est. 25–40% weekly (needs a WPd for sd;ld;jr through riscv_step decode: ∀-successor admin steps vs AxFetch's ∃-runs = step-kind determinism). Gate: pnode_step head-determinism lemma + wpd_of_deterministic_run lifter — price as a spike first.

Stage-5 regime criteria (fixed 2026-09-29 BEFORE the spike; owner asked). The spike = three single-job workers:
S1 pnode_step head-determinism (outputs fixed by (m, rs, ib, d, l) except at Interface.Choose and the boundary
tick), S2 wpd_of_deterministic_run lifter, S3 c.jr WPd from AxFetch.af_cjr_row_run (+ optional S4: ld, for the
memory-read arm). Measured per worker from its own transcript ($ → % weekly, tool calls, proof lines). Estimate
epilogue = infra (S1+S2, paid once) + 3 × per-instruction (S3; S4 for sd/ld) + tierA_adequacy_ann wiring. Regime:
- LOW 5–10%: S1 generic (Choose/tick each discharged once, no per-constructor work); S3 falls out of the lifter
  with little instruction-specific proof (≲100 lines, no case split over the decode steps).
- MID 15–25%: lifter works but each instruction needs its own handling of the decode admin steps, or Choose/tick
  must be discharged at each place it appears.
- HIGH 25–40% (the advisor estimate above): S1 fails generically (case split per constructor/instruction), or the
  lifter's statement must change.
- RECONSIDER: the spike itself exceeds ~2% weekly, or needs a spec change ⇒ weigh Islaris-style trace extraction
  (fresh Fable advisor review).

Stage-5 FEASIBILITY (advisor, 2026-09-29, owner asked "feasible at all?"): FEASIBLE with three caveats; no step
without precedent. Evidence: symbolic riscv_step end-to-end under the M-mode tower already done at exec_eff
(WeakEffSkel.exec_eff_riscv_step_rvc/_base on WeakPmpEff incl. _rec_/Acc recursion, WeakFetchEff, WeakFetch2,
WeakTickEff); footprint evaluators exist + proven consistent (epure_exec_eff, erun_exec_eff; lui leaf re-mirrored at
epure, conversion = rename + one membership side condition per register node); certificate→WPd lift generic (spike).
Choose: 0 hits in rv64d.v; only M-extern get_16_random_bits (Zkr, unused); read_mem_* off the MemRead path;
sig_seip read at ONE site. Caveats: (1) execute bodies reading mip (csrr mip/sip, wfi, trap entry) need the
seip-split per site (≤8 sites, mword 1); (2) MMIO instructions get NO WPd this way (device arm has no graph event) —
needs a device-event WPd extension (spec) or stay out of scope; (3) data-event steps need flow_eq_dyn deposits
provable at the epilogue's real protocol, not only AxGA2. Cheapest experiment for (3): c.ldsp post-fetch at
epurew (WeakEvExecEff §5) + a wpd_load_step twin of wpd_fetch_step, value pinned to graph_value (~60–80 lines).
Architecture: NOT a model-interface change, NOT a verified symbolic evaluator (needs SMT-grade bv reasoning in the
checker); make the mirror stack EVALUATOR-PARAMETRIC (EvKit record: bind/returnm/read_reg ok_r/write_reg ok_w/liftR/
catch_early_return, instantiated at exec_eff/epure/erun/epurew/erd). Jobs: J0 ledger + concrete vm_compute instance;
J1 EvKit + one lemma per shape; J2 spine port (3–4 workers); J3 decode bridge + c.jr/sdsp/ldsp execute; J4 data-event
WPd steps + erun_to_event splitter; J5 symbolic epilogue via tierA_adequacy_ann + ∃-run corollary; J6 class funnel
wpd_instr_of_cert (amo needs an RMW step); J7 retire the ledger. Spike fixes: AxBoundaryWpd exit set → erd-computed
node, erd stops at any RAM event and splits at any finite-typed register ∉ Dr; AxRunClose aeqv parametric in a
register set; AxCjrWpd §4 generic except n = 2 (rename); AxStepDet/AxWpdLift keep.
Stage-5 CALCULUS UPDATE (advisor, 2026-09-29, after AxLdspWpd + AxTierA3): still feasible. Caveat 3 CLOSED (generic
wpd_load_step; owned deposit at the real prot_inv; sd symmetric via wp_write_owned_tokn). F1 = shape fact (Prop-level
result reads v = Vs back from the annotation at post_lifting; readback lemma unprecedented but Iris bookkeeping). F2 =
single-use token (one owned reload per spill), not soundness. F3 narrowed: _gmo form + Hpref forces s_pol r = gmo_prefix r,
satisfiable by construction; axpol_wf_L holds since gate-free s_proc = gx_gmo. ONLY in-principle open step for the
epilogue: does ea_local_wf (A4) tolerate a non-local s_pol? Gate-free limit matters only for the concurrency slice.
BUDGET (1 worker job ≈ 1% weekly): (a) concrete-instance epilogue 4–7% (driver: vm_compute through riscv_step pmp/_rec_,
fallback native_compute); (b) general symbolic epilogue J1–J5 14–24% = MID, upper end (driver: J2 spine port 6–10%;
LOW only if the EvKit abstraction makes the port search-and-replace); (c) kernel classes J6 1–2% per register/ld/sd
class, 3–4% for amo/lr-sc and mip-readers, MMIO excluded; ~10 classes 15–25%. NEXT JOB: axpol/ea_local_wf
satisfiability on a concrete 1-hart [fetch; sd; fetch; ld; fetch] gdexec (AxInstr §7 style), s_pol := gmo_prefix,
lobp := {spill}, vm_compute every pure premise of tierA_adequacy_ann_gmo + ldsp_own_ok + axpol_wf(_L) + ea_local_wf (0.5–1%).
