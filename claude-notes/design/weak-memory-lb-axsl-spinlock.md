# Design: xv6 spinlock on RVWMO (LB/AxSL), interrupts off — plan of record

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../claude-notes/LEAN.md)).

Status (2026-10-02): rev 8, validated by seven rounds of fresh-advisor review (round 7: SATISFIED;
each round's required changes are tagged [Rn.k] below). OWNER DECISIONS 2026-10-02: (i) validation
client = xv6's allocpid (the smallest real function that takes a spinlock); (ii) the page-table
simplification HAD (A/D preset, PTEs read-only) is ACCEPTED FOR NOW — it must stay removable, not
become fundamental; removal path: drop HAD, Hcons at ptw_model (AxPtwModel), PTE words under the
AxPtProt walker-RMW protocol, and the gated route re-checked there (AxPtwModel's header: the gate
route currently needs ob_cat ⊆ gmo over ALL events; expected fix = require it over non-walker
events only, since gate sources are explicit reads — UNPROVED); (iii) land Theorem 1 first.

Context:
claude-notes/design/weak-memory-lb-axsl-primer.md (file map, idioms, vacuity rules),
claude-notes/projects/weak-memory-lb-axsl.md (tracker; RESUME HERE, RELEASE STATE, COND MODEL,
A2b LOCK LEAVES, VACUITY CHECK paragraphs), claude-notes/design/weak-memory-lb-axsl.md §7.L/7.T/7.A/7.A7.

History: rev 2 = rev 1 + advisor round 1 (11 changes, [R1.n]); rev 3 = + round 2 (8 changes,
[R2.n]); rev 4 = + round 3 (6 required changes + suggestions, [R3.n]), a clean rewrite; rev 5 = +
round 4 (3 required changes + suggestions, [R4.n]); rev 6 = + round 5 (3 required + suggestions,
[R5.n]); rev 7 = + round 6 (2 required + suggestions, [R6.n]);
rev 8 = + round 7 (verdict SATISFIED; 1 required fix + suggestions, [R7.n]).

## MAJOR DESIGN POINT — handle-based ownership interface (OWNER-ACCEPTED 2026-10-02)
In this architecture a resource transferred between harts EXISTS FOR THE RECEIVER ONLY IN PHASE 2:
phase 1 unfolds every hart's WPd (in po) before any flow equation runs; phase 2 validates events in
the (gated) gmo order and moves resources along rf/ob. Hence NO WPd can hand its continuation the
LITERAL SC-tier post `locked ∗ R` — this is fundamental to the two-phase (AxSL-style) design, not a
proof-engineering gap. The interface is HANDLE-BASED: the post holds an annotation handle on the
event at which the resource will arrive in phase 2.
  acquire: is_lock lk R ∗ notheldₕ ⊢ WPd {{ ∃ c, ⌜lk_claim c⌝ ∗ c ↦ₐ (locked i c ∗ R c) }}
  release: is_lock lk R ∗ [∗ j] a_j ↦ₐ R_j a_j ∗ c' ↦ₐ locked i c ∗ ⌜gob a_j w⌝ ⊢ WPd {{ w ↦ₐ notheld i }}
(notheldₕ: in hand on the first acquire, a handle `w ↦ₐ notheld i` on the previous release after.)
WHY THE SC PROOF SHAPE SURVIVES: the weak-tier surface is already provenance-based (AxSymReg
`r ↦ᵣ⟨x⟩`, rev 7 C0/C14). Weak-tier owned points-to = a HANDLE predicate
  a ↦ₕ v := ∃ e, e ↦ₐ (tok a … ∧ last = v)
and the critical-section leaves are owned load/store rules that MOVE the handle to the new event
when e ∈ lobp r (ppo rule 5 from the claim; rule 1 for same-address stores; a load after a
same-address store: if forwarded, the value is the pure own-store data and no ownership is drawn,
else the load is gmo-after the store). Value facts surface at post_lifting / gates, as everywhere
in this tier. So a client's critical-section proof reads like the SC proof with ↦ₕ for ↦.
COSTS (Phase 2 scope): (i) per-address handle components (AxWp.annot_split) — mixed-address CS
accesses are not gmo-ordered; (ii) a forwarded-reload leaf + per-read-after-write graph case split
(neutralises AxSpinWit FINDING 1 for lock-protected bytes; allocpid does not need it, pipewrite-style
critical sections will); (iii) release gathers R's components via its fence (fe_release').
CONSEQUENCES: every later SC-tier client port (callers of acquire/release) is written against ↦ₕ
handles; anything that needs a phase-1 fact about another hart's data must get it through a gate or
post_lifting, never by holding the resource. Source: Phase 1a advisor review (2026-10-02, FINDING F1
of AxSpinProt*), accepted by the owner the same day. Also recorded in design/weak-memory-lb-axsl.md
§7.HI and the primer §2.

## Goal
The SC tier's client interface (iris/WpLock.v, SpecAcquire.v, SpecRelease.v) in HANDLE form (see the
MAJOR DESIGN POINT above), over the weak tier's WPd surface (surface v4, AxRelease*), interrupts
OFF throughout (SIE = 0 at entry and stays 0; init has noff = 0, so push_off writes intena := SIE = 0
and pop_off never re-enables). Original (pre-2026-10-02) target, kept for reference — NOT achievable
literally in this architecture:
  acquire:  is_lock nm lk R ∗ notheld nm lk i ∗ frame ⊢ WPd … {{ locked nm i ∗ R ∗ frame' }}
  release:  is_lock nm lk R ∗ locked nm i ∗ R ∗ frame ⊢ WPd … {{ notheld nm lk i ∗ frame'' }}
notheld nm lk i = exclusive per-(lock,hart) token (non-reentrance; the SC tier used panic_wp, which
is undischargeable at WPd — panic does MMIO) [R2.3]. frame = cpu_own, stack_own, callee-saved,
kernel_text. R is any client predicate satisfying the transport condition (Phase 2); owned points-to
(AxProtBytes tokn) satisfies it, so critical sections are verified SC-style. Real xv6 machine code
for allocpid/acquire/release/push_off/pop_off/holding/mycpu. Phase-5 WPds are labelled PIPELINE
MILESTONE in headers until the certificates exist.

## Fixed instance [R1.3]
Ixv6: ob_st_interp0 := λ nm, prot_xv6 nm, N := gnames — ONE joint instance (WPds do not transport
across axirisG instances), defined in Phase 1 and used everywhere. Inside adequacy:
Hob_alloc : ⊢ |==> ∃ nm σ0, prot_xv6 nm GD σ0 ∅ ∗ [∗ i ∈ harts] init nm i,
init nm i := kernel_text ∗ cpu_own nm i ∗ stack_own nm i ∗ is_lock nm pid_lock R_pid ∗
notheld nm pid_lock i — NO locked/R in init (the genesis R_pid sits in σ0's mailbox). No `⊢ own`
Rocq hyps, no ∀-over-instances, no client-chosen annotation tables (design §7.L/§7.T).

## Theorem 1 (Phase 7): allocpid2_distinct — the stepping stone
```
allocpid2_distinct (GT : gdexec_t) A B (HAB : A ≠ B)      [GD := gt_ad_gd GT below, R5.1]
  (Hcons  : rvwmo_cat_consistent_t GT)          [R3 sugg.: tagged model, no gppo12 caveat;
            walker reads are EXPLICIT reads here — sound for the real machine only because the
            walked PTEs are immutable in these graphs (HAD + the read-only PTE class) [R4.1]]
  (HAD    : every PTE walked by any hart has V/R/W/X as xv6 maps it AND A and D PRESET in gx_img;
            the PTE bytes are never written in GD) [R4.1: DEPARTURE from xv6's real page table —
            mappages does not preset A/D; lifting it = ptw_model + the AxPtProt PTE protocol, future]
  (Hharts : ∀ e ∈ gx_gmo GD, e.1 ∈ [A;B])        (no device agents: interrupts off, by design)
  (Hrow   : ∀ i ∈ [A;B], grow GD i ∈ allocpid_prefixes i)                       [R3.1, R4.3]
  (Hdeps  : prog_deps_xv6 GT ⊆ gt_deps GT)   (TAGGED edges, ctrl edges as DTctrl) [R2.4, R5.1];
            prog_deps_xv6 is CTRL-CLOSED: edges from each branch-feeding read to EVERY po-later store
            of the row [R6.1]; enumerate ALL sources incl. push_off's `if(c->noff == 0)` branch and
            the ra reloads feeding c.ret (these make tw_not_cat_forget's pattern appear) [R7 sugg.]
  (Hctrl_closed : ∀ r w e, (r,w,DTctrl) ∈ gt_deps GT → gpo (gt_g GT) w e →
            glbl_is (gt_g GT) e lb_is_w → (r,e,DTctrl) ∈ gt_deps GT)   [R6.1: over ALL of gt_deps,
            every hart; hardware-faithful — the emission's dt_ctl is never reset and dedges_w tags
            every later store, AxDeps.v:431–436]
  (Hnowrap: ∀ r, r a 4-byte nextpid read by A or B in GT → value r ≤ 2³²−2)            [R6.2]
  (Himg   : gx_img pins the REAL text bytes of allocpid/acquire/release/push_off/pop_off/holding/
            mycpu at KernelSyms; pid_lock.locked = 0; pid_lock.cpu = 0; nextpid = n0;
            cpus[i].noff = 0)
  (Hlayout: disjointness of stacks / cpus / pid_lock / nextpid / text / page-table pages;
            injectivity of cid_word_of on [A;B]; stack_own covers ≥ 32+32+32+48+48 bytes below
            stk_i; satp / page-table geometry; the walker premises listed EXPLICITLY (Hpin/HxPin,
            the walker flow WFrM — under HAD discharged by the read-only PTE class's image arm,
            `ws` fixed up front per the AxPtwModel caveat) [R4.1])
  (σ0 σf : agent → mstate)
  (Hentry : ∀ i ∈ [A;B], σ0 i: pc = allocpid, sp = stk_i, tp = cid_word_of i, ra = r_i, SIE = 0)
            [R2.2: tp holds the cpu id; cpus_ptr i = mycpu_ret (cid_word_of i), ProcGeom.v:739]
  (Hrun   : ∀ Hann nm i, i ∈ [A;B] → nsteps (tierA_astep GD … nm i) (n i) (s0 i) (sN i),
            at_k (s0 i) = 0, at_k (sN i) = length (grow GD i), state of sN i = σf i)
            (form matched to tierA_adequacy_ann_gate)
  : (∀ i ∈ [A;B], ¬ enters_panic (grow GD i))
    ∧ (complete A (grow GD A) → complete B (grow GD B) → a0 (σf A) ≠ a0 (σf B)).
```
allocpid_prefixes i [R3.1, R4.3, R5.3]: all INSTRUCTION-BOUNDARY prefixes of the event rows of the real
code's CFG paths from allocpid's entry — complete paths returning to r_i and paths taking a panic
branch, cut before panic's first memory event — quantified over the spin count k and holding's
branch bits; DATA rf sources / read values / write data EXISTENTIAL, but FETCH read values and
WALKER PTE read values PINNED to gx_img inside the row shape [R5.2] (a row whose fetch returns
garbage cannot be refuted at row end — the fact would only arrive in phase 2); every row includes
fetch reads and Sv39 walk reads (no walker writes, by HAD). Text/PTE immutability for A/B's
fetches/walks is thus a ROW premise (graph-true by gload_value + no text/PTE writes); the BLOCKED
default arm supplies only the ownership side. Prefixes are cut at instruction boundaries only
(leaf lemmas X_* / wpd_of_CertWP are instruction-positional; clause (d) is proved only at those
cuts); conjunct 1 loses nothing — a taken panic branch is itself a boundary, and every mid-
instruction graph is covered by its boundary prefix [R5.3]. complete i row := row is a full path to the return;
enters_panic row := the row's last instruction is a taken panic branch (cut immediately after it,
before the fetch of panic's first instruction) [R5 sugg.]. Prefix closure is what makes
conjunct 1 mean "no hart panics in ANY consistent execution", not just in ones where the other hart
finished. prog_deps_xv6 GD is defined from the shape (the ctrl/addr
edges of the real code at the row's positions: spin c.bnez → sd a0,16; holding's branches → stores;
pop_off's branches → stores; c.ldsp s1 → release's sd/sw addr edges) — this is what makes it
definable ∀GD. Hrow is derived nowhere; it is a premise and (a) discharges it.
Per-hart WPd post [R4.3]: post i s := ⌜¬ enters_panic (grow GD i) ∧ (complete i (grow GD i) →
∃ v, a0 s = sext32 v ∧ Pread GD i v)⌝, proved at the row end of every allocpid_prefixes row;
non-panic incomplete prefixes: only conjunct 1, trivially; panic rows: False at the ROW END from the
panic-branch load's annotation (Φ_cpu handout / owned-read fact contradicting the pinned graph
value) via post_lifting (D4). Pread = GRAPH-level fact:
i's successful RMW reads the genesis image ⇒ v = n0; reads j's release write w ⇒ v = the value of j's
po-latest nextpid write before w (gwrites_byte; position-independent). Distinctness from a PURE
dichotomy lemma over GD generalizing AxLock3Thm.lock3s_dichotomy to spin-quantified rows (reuse
lock_ext_rmw_reader0_unique and the lock3s cycle argument); the untagged graph lemmas
(cs_handoff_last, lock3s_dichotomy) are applied at GD := gt_ad_gd GT via AxDeps.cat_t_ad [R5.1].
Hnowrap [R6.2]: NOT needed for the ≠ itself (sext32 injective), but the A/B WPd lemma must
re-establish R_pid (●mono v ∗ 0 ≤ v < 2³², single instance Ixv6) after sw ((v+1) mod 2³²) — at
v = 2³²−1 the bytes wrap and mono cannot go down ⇒ the WPd lemma takes Hnowrap as a Rocq hypothesis
(like Hrow), in BOTH theorems. In Theorem 1 it follows from the Himg-side condition n0 ≤ 2³²−3
(state it there, so Hnowrap is visibly no extra restriction) [R7 sugg.]; in Theorem 2 it is genuine
(a verified C may raise nextpid toward 2³²−1). Header says so. The A/B WPd lemmas take
Hrow_i, HAD, Hnowrap as Rocq hypotheses but NOT Hharts (only the final dichotomy does) so they
instantiate on 3-hart graphs [R2.6, R3.6].
HONESTY (header) [R2.5, R3.6, R5 sugg.]: with both rows pinned to correct lock code BOTH conjuncts
are GRAPH-TRUE (conjunct 1: no write of cpus_ptr A to lk->cpu exists, by cid injectivity +
gload_value; ownership is load-bearing for conjunct 1 only in Theorem 2, where C's writes are
constrained by Φ_cpu); the distinctness conjunct is (AxLockSerial.cs_handoff_last); ownership is load-bearing in the proof route and in
(b)/(c), not in the truth of this statement. Graph/HW premises: Hcons (TAGGED
rvwmo_cat_consistent_t — no rule-12-over-ctrl over-ordering)/Hctrl_closed/HAD/Hharts/Hrow/Hdeps/
Himg/Hlayout/Hnowrap. Honesty bridge for Hdeps [R6 sugg.]: lemma (or per-witness vm_compute) that
for every row in allocpid_prefixes, prog_deps_xv6 ⊆ row_deps_t row (AxDeps §4) — so the edges are
ones the hardware emission actually generates, not just "graphs with at least these edges".
Conjunct 1's "any consistent execution" reading relies on an INFORMAL prefix-closure argument (a
panic-cut of A's row with B's full row is itself consistent because panic's writes feed no allocpid
read) — the header says it is informal, not proved [R6 sugg.].
HAD a page-table departure; fetches are explicit reads (stronger than HW, harmless for immutable
text); gate_real' proved from Hcons_t + Hctrl_closed, gate_mono by po-transitivity. Σ fixed concretely in the
final statement (no invGpreS/subG class premises left for (d)) [R5 sugg.].

## Certificates for Theorem 1 (same file) [R1.2]
(a) allocpid2_sat: concrete GD₂, σ0/σf, both harts' COMPLETE runs produced by the driver
    (drive_sound / closed_of_det_run), every premise (incl. Hrow, Hdeps, HAD)
    discharged (incl. Hcons_t by vm_compute of cat_t_consistent_b, Hctrl_closed and Hnowrap by
    vm_compute), conclusion (both conjuncts, with complete A ∧ complete B TRUE) true (∃-run
    mandatory — WPd is MaybeStuck). Plus (a-) a panic-free incomplete-prefix witness (B spinning
    while A is mid-critical-section) to show conjunct 1 is exercised on prefixes.
(b) allocpid_race_unprovable [R2.6]: hart C = `lw; addiw; sw nextpid` with no acquire row, C's
    stored value ≠ n0+1 (mod 2³²); ¬(∀ Hinv Hann nm, ⊢ init nm C -∗ WPd_C {{True}}) at Ixv6
    (AxLock3Race.v:369–373 shape), by reductio with the REAL A/B WPds on a concrete consistent
    3-hart graph.
(c) allocpid_race_sanity: same C row provable at the trivial protocol.
(d) Print Assumptions = Sail params + funext; closed type printed; ZERO λ-bound iProp premises; NO
    Cond_gate/gate_real'/gate_mono premise — gate_real' PROVED from Hcons_t + Hctrl_closed (conj 3 =
    gtdeps_gmo on the closed edge), gate_mono by po-transitivity; gsrc e := {r | ∃ w, (r,w,DTctrl) ∈
    gt_deps GT ∧ (w = e ∨ gpo w e)} for EVERY hart [R1.5, R2.4, R4.2, R5.1, R6.1].

## Theorem 2 (Phase 8): open third hart — where ownership is load-bearing in the STATEMENT [R3.2]
```
allocpid_open (GT : gdexec_t) A B C (distinct; cid_word_of injective on [A;B;C]; C's stack/cpu disjoint from
  A's/B's) (GT, Hcons_t) Hctrl_closed (all harts, C included) HAD (walks of all three harts)
  (Hharts: harts = [A;B;C])
  Hrow_A Hrow_B Hdeps_AB Himg Hlayout Hnowrap Hentry_AB
  (Hentry_C : tp = cid_word_of C, sp = stk_C, SIE = 0, pc = pcC, …) (pexC : C's program)
  (HwpC : ∀ Hinv Hann nm, ⊢ init nm C -∗ WPd (AThread pexC 0) @ C {{ True }} at Ixv6)
  (Hrun : for A, B, C to their row ends — C's row may be EMPTY: then this degenerates to Theorem 1)
  : complete A → complete B → a0 (σf A) ≠ a0 (σf B)   (+ the no-panic conjunct for A, B)
```
gate_real'/gate_mono for C's events [R4.2, R5.1]: the same tagged gsrc for every hart (C
included); they are pure lemmas over all events from Hcons_t + Hctrl_closed, and Hok for handouts to C's events
follows from pol_DS as for A/B — no per-hart special-casing of the GD-indexed policy.
init nm C as for A/B (kernel_text ∗ cpu_own ∗ stack_own ∗ is_lock ∗ notheld). C cannot cheat by
ghost updates (§7.T) because this is tier A: C's only way to produce flow facts for its writes is
the WPd write rule against prot_xv6.
Distinctness ghost [R3.3, R3.4]: R_pid := ∃ v, nextpid ↦₄ v (exact, 0 ≤ v < 2³²) ∗ ●mono v ∗
issued_auth S ∗ ⌜S ⊆ [0,v)⌝, with an EXCLUSIVE fragment RA (gset_disj, ◯ GSet {[v]}; a plain
auth-gset fragment is duplicable and proves nothing). allocpid's post deposits issued_frag nm v in an
annotation on its own event (AxEpiOwned-style readback). Joint final step via a new adequacy variant
tierA_adequacy_ann_gate_joint (Phase 3): Φ : agent → athread → iProp, each hart's Φ i (sN i)
extracted from its slice of the post-phase-2 bag `[∗ map] e ↦ R ∈ na, R` (AxTierA2
.tierA_adequacy_ann_core already holds all harts' resources at once), premise
Hjoint : ∀ Hinv Hann nm, ([∗ list] i ∈ harts, Φ i (sN i)) ==∗ ⌜P sN⌝. Φ A, Φ B := ∃ v,
⌜a0 s = sext32 v⌝ ∗ issued_frag nm v; Φ C := True. R_pid's exact bound 0 ≤ v < 2³² is what stops a verified C from bumping ●mono by 2³² while
storing the same bytes; Hnowrap only covers A/B's own increment [R4 sugg.].
Certificates: (a′) positive non-trivial C := allocpid (reuses the A/B WPd via wpd_mono;
exercises fragment minting by a third hart) with nonempty row, all premises discharged, conclusion true; (b) the race (above) — C's
WPd unprovable; (c′) sanity twin at the trivial protocol; (d) as above.

## Decisions
D1 validation targets = Theorem 1 (stepping stone) and Theorem 2 (the real validation). [owner D5:
   recommended to include Theorem 2.]
D2 lk->cpu token travels inside the lock protocol with the lock (both sd lk->cpu stores need its full
   auth) [R1.7]. K1 is NOT claimed; no racy-read class; instance not ledger-based [R1.8]. If K1 is
   claimed later, any exemption goes in the theorem header.
D3 address gate = a pol_DS handout, not a gsrc handout and not a new assumption [R1.5, R7.1]:
   gsrc collects only DTctrl sources, so the addr-dep reload r (c.ldsp s1 → sd/sw …(s1)) is not in
   gsrc e. Instead: gmo_lt r e from the direct (r,e,DTaddr) edge via gtdeps_gmo; for every s ∈ gsrc r
   (some (s,w,DTctrl) with gpo w r), gpo w e holds, so s ∈ gsrc e ∧ gpo r e — pol_DS's second
   branch. Do NOT add DTdata/DTaddr sources to gsrc (a store po-after a data-dependent store is not
   gmo-after the data source; monotonicity would be unsound); addr sources in gsrc would need a
   rule-13 closure premise (DTr13) — not needed now.
D4 panic arms [R1.6] — every panic branch is REFUTED by a gate fact; panic_wp is never a premise:
   MECHANISM [R4.3]: wpd has no LCtrl arm; the branch direction is known from the pinned graph
   value, and False is obtained at the ROW END of a panic-prefix row via post_lifting from the
   load's annotation (the fact ⌜v = …⌝ / Φ_cpu contradicting the pinned value). Panic-prefix rows
   end before panic's first memory event.
   - acquire `if(holding) panic` (non-holder, notheld in hand): protocol conjunct Φ_cpu — σ records
     for every lk->cpu write w: value = 0 ∨ value = mycpu_ret (cid_word_of (cpu_of w.1)),
     discharged by the owned-write rule (also stops a Theorem-2 C with tampered tp) [R2.2, R3 sugg.];
     plus NOTHELD_LINK as a ghost-auth-in-σ / fragment-in-hand invariant (σ holds ● of the
     per-(lock,hart) state; notheld nm lk i is the ◯ fragment; agreement ⇒ i's po-latest lk->cpu
     write, if any, is 0) [R4 sugg.]; plus graph lemma LV_po_gmo (a load returns the latest of the po-before ∪ gmo-before
     same-address stores) ⇒ the read value ≠ cpus_ptr i (cid injectivity) ⇒ panic dead [R2.3].
     (For allocpid rows i has no po-earlier lk->cpu writes; LV_po_gmo is for the modular spec.)
   - release `if(!holding) panic` (holder): owned read of lk->cpu (= cpus_ptr i), and HELD_NZ +
     LV_po_gmo (the claiming RMW's write is po-before the lw) ⇒ lk->locked read ≠ 0 [R2.7].
   - pop_off `if(intr_get()) panic`: CSR read, SIE = 0 register-level; `if(c->noff < 1) panic`: owned
     cpu-struct read, gate fact noff ≥ 1.

## Phases
0 SPEC: design section with both theorems, certificates, D1–D4, instance components, R transport;
  fresh-advisor review loop.
0.5 SIZE SPIKE [R1.11]: for the 2-hart graph of (a) AND the 3-hart graphs of (a′)/(b) [R5 sugg.]
  — vm_compute of cat_t_consistent_b, of Hctrl_closed and of the gsrc sets (closure multiplies
  DTctrl edges quadratically in row length per ctrl source; measure Hctrl_closed on (a) FIRST, before
  the 3-hart graphs) are the dominant risks [R6 sugg., R7 sugg.] — count events (fetch + Sv39 walk reads per instruction — 3 PTE reads per
  TLB miss, may dominate) [R4 sugg.]; mock a 2-hart graph
  of that size; time cat_consistent_b(_t) vm_compute and the 2-hart driver. If infeasible, (a)
  becomes the abstract-GD theorem + smaller concrete witnesses per component + the
  row_emitted_from_run bridge, stated honestly.
1 JOINT INSTANCE prot_xv6: stack words (ld_rule/st_rule), lock word, lk->cpu, struct cpu fields,
  nextpid tokn (genesis H = []/image arm, x_tok precedent) + the Theorem-2 ghosts, gate-source fact
  recording (AxLedgerG style); is_lock = persistent component.
  - Lock-word rules indexed by (address, class, read-value, WRITTEN value), NOT position [R1.4, R3.5]:
    RMW arms require written value 1 — reading nonzero ⇒ neutral (hands nothing); reading 0 ⇒ claims
    (uniqueness by RMW atomicity) and pulls the parked R. The ONLY arm admitting a written 0 is the
    release arm: WCrel store, consumes locked nm i, parks R (one mailbox PER release write). Hence
    every 0-write has a mailbox.
  - DEFAULT write arm (addresses outside stacks/cpus/pid_lock/nextpid, incl. kernel text and PTE
    pages): BLOCKED [R3.5]. With fetch/PTE values pinned in Hrow_A/Hrow_B, text immutability for
    A/B is graph-true (gload_value + Hcons) even with C present; the blocked arm is needed for the
    WPd leaves' Htext (ownership side), not for the truth of the conclusion [R6 sugg.].
    PTE bytes: READ-ONLY class (image arm: every walker read returns gx_img), consistent with HAD
    (no walker A/D writes) [R4.1].
  - Conjuncts: claims; HELD_NZ [R2.7] (while claimed by i, every lock-word write gmo-after i's
    claiming RMW other than i's release writes is nonzero; its induction uses a LEMMA about Lcanon
    ranks — for every write w, gkey w = gpos w (writes never deferred), provable via gate_real'
    conj 3, i.e. it depends on Hctrl_closed [R5 sugg., R6 sugg.]; i's own release writes are
    gmo-after its lw by ppo rule 1); Φ_cpu; NOTHELD_LINK.
  - lk->cpu rules HYBRID [R2.8]: owned write (tokn, D2) WITH Φ_cpu as side condition, and a
    demonic-read handout of Φ_cpu from the rfe source (genesis arm v = 0 via Himg).
  - Graph lemma LV_po_gmo [R2.3].
  - Hok (AxDefer5, its _t port): every handout is a write gmo-before the recipient whose gate sources are
    ppo-before it, so pol_DS discharges generically; gsrc-arm handouts are exactly the ctrl-gate
    reads (holding's lw/ld, pop_off's noff/intena loads, ra reloads feeding c.ret); addr-dep reload
    handouts are pol_DS (D3) [R7.1].
2 OWNERSHIP TRANSPORT [R1.7]: R : eid → iProp with ∀ e e', gob_cat GD e e' → R e -∗ R e'
  (tok_retie_ob shape); anchor = the hart's latest .aq RMW (ob-before every po-later access by ppo
  rule 5); a same-address store after an owned read may retie at the read (rule 1), but a read-retied
  token is NOT an anchor for other addresses. R_pid = tokn nextpid ∗ lk->cpu token (+ Theorem-2
  ghosts). Pid readback chain [R1.10]: pid lives in s1 across release (c.sdsp/c.ldsp spill, demonic
  reload, then c.mv a0,s1) ⇒ a0 = sext32 v via the owned stack-reload annotation chain (AxEpiOwned
  precedent); nextpid a 4-byte tokn; the c.sw value pinned by AStepWrite's byte check.
3 GATED ADEQUACY [R1.5] — TAGGED PORT FIRST [R5.1]: tierA_adequacy_ann_gate_t over GT : gdexec_t,
  with GD := gt_ad_gd GT, Hcons := AxDeps.cat_t_ad GT Hcons_t, and gate_real' whose third conjunct
  is `glbl_is e lb_is_w → gmo_lt (gt_g GT) r e` (the only thing AxDefer3.gate_w needs); re-prove
  Lcanon_ok_gate from it (other uses, AxDefer3:287/300, AxDefer5:74/75, need only conjuncts 1–2).
  Rationale: gt_ad_gd drops DTctrl edges (so the untagged gsrc would be empty), and
  rvwmo_cat_consistent (forget GT) is NOT derivable (AxDeps.tw_not_cat_forget — exactly the
  ctrl-dependent spill forwarded to a later reload that allocpid's c.sdsp/c.ldsp s1 reproduces).
  Then: plain-load gates (holding's c.ldsp s1 + c.ret, acquire/release c.ret,
  pop_off c.beqz on noff/intena) ⇒ tierA_adequacy_ann_gmo is NOT applicable; use
  AxDefer5.tierA_adequacy_ann_gate (P_gate policy; gate_real/gate_mono PROVED as pure lemmas from
  Hdeps + the run). FIRST land the missing WPd-level witness of the gated route (tracker VACUITY
  CHECK item (2)), at the tagged port; the witness must explicitly test a spill ctrl-dependent on a
  branch and FORWARDED to its reload (AxDeps tw's shape: Lcanon moves the reload only to just after
  its gate sources, still before the spill, so the owned-read flow equation must draw on the hart's
  token/history, not the spill's annotation), not just pop_off [R7 sugg.]. Confirm gwf gives
  "labelled ⇒ in gx_gmo" for gate_real_src_gmo (AxDefer3:284) in the tagged re-proof, else add the
  conjunct to gate_real' [R7 sugg.]. Then tierA_adequacy_ann_gate_joint(_t) [R3.3]: split the post-phase-2 bag per hart using Hharts and apply
  each hart's post_lifting (AxWp.v:783 consumes only the own-hart slice) in turn; Hjoint ==∗ ⌜P⌝
  fits inside the final |==> of tierA_adequacy_ann_core (AxTierA2.v:316–323). Ctrl leaves jal/c.beqz/c.bnez/c.ret on
  surface v4; the spin loop's c.bnez tests the amoswap.aq value ⇒ acquire gate (adequacy_ord_G_aq).
  pop_off is the first plain-load-gate consumer — use it as the probe.
4 CALLEES: mycpu; push_off/pop_off; holding (D4). release's w_hold spec "∀ return value" with the
  wrong branch refuted by D4; only s1's exactness for the stores needs the address gate.
5 acquire/release WPd: replay ProofAcquire/ProofRelease over surface v4 (AxReuseProbe verdict B),
  every λ-bound slot discharged. Acquire over an ARBITRARY number of failed iterations by induction
  on length row − at_k (the fixpoint is ▷-guarded at AxWpD.v:121/130 if Löb is needed) [R1.4].
  Compiled acquire has NO fence after the loop (0x22 c.bnez → 0x24 jal mycpu) ⇒ acquire ordering
  rests on .aq alone; amoswap_acq_ast = AMO(AMOSWAP, aq=true, rl=false) (WpAmo.v:42) [R1.9].
6 TEXT-FACT JOINT SATISFIABILITY [R1.9]: every instr4 fact (aqi_*/hi_*/poi_*/ppi_*/apdi_*/mycpu/
  allocpid) instantiated on the real bytes (AxLeafS5 is_rvc trap).
7 THEOREM 1 + certificates (a)–(d); fresh-advisor vacuity audit.
8 THEOREM 2 + certificates (a′)/(b)/(c′)/(d); fresh-advisor vacuity audit.
Order: 0 → 0.5 → (1 ∥ 3-witness) → 2 → 3-joint/3-leaves/4 (pop_off first) → 5 → 6 → 7 → 8.

## Progress and findings (2026-10-02)
- Phase 0.5 DONE (iris/AxSpinSpike.v, AxSpinSpikeRun.v): allocpid hart ≈ 309–314 memory events
  (209 instrs, 220 fetch, 15 walker); (a) 623, (a′) 932, (b) 634 events. Hctrl_closed 16–36 s.
  Existing cat_t_consistent_b ~N^3.5 ⇒ ≈16 h on (a): concrete vm_compute of consistency is the
  WRONG TOOL at this size. OWNER DECISION 2026-10-02: certificates get consistency from a GENERAL
  lemma "SC interleavings are rvwmo_cat_consistent_t" (iris/AxScCat.v, in progress), not from
  deciding big graphs; the run premise still comes from concrete execution (S-mode tracer: real
  mycpu 0.066 s; AxEpiRun.drive needs Barrier + LRmw arms + node_step_sound cases).
  Spike side note to re-check: no reload feeding a store ADDRESS was found on the path, but holding
  saves/restores s1 (c.sdsp +0xe / c.ldsp +0x26) — verify against the generator before relying on D3.
- Phase 3a DONE (iris/AxSpinGate.v): tierA_adequacy_ann_gate_t over gdexec_t (only graph premise
  rvwmo_cat_consistent_t); dev-2 corollary; gate_real'/gsrc_t_real' from Hcons_t + ctrl_closed;
  writes_not_deferred_t. FINDING: the main gated theorem needs neither gate_real' nor ctrl_closed.
- Phase 3b DONE (iris/AxSpinWit.v): spin_reload_owned + certificates (deferred spw, non-deferred spl,
  race spr_wpd_unprovable, sanity spr_wpd_trivial); closes tracker VACUITY CHECK item (2).
  FINDINGS that change later phases:
  (1) OWNED STORES APPEND THEIR HISTORY AT THE STEP (full auth stays with the hart, the flow deposits
      only a snapshot — sh_owned_store); the AxEpiOwned route (token moved through the spill's
      annotation) fails Hok on deferred graphs ⇒ the stack save/restore (st_rule/ld_rule) of Phase 1
      must use the step-append form.
  (2) Deferred owned reloads get their value by forwarding (owned_read_rule case (ii)); races must be
      exhibited on non-deferred graphs.
  (3) prot_inv records NOTHING for reads ⇒ gate handouts are taken but never consumed. D4's panic
      refutations need READ-FACT recording in prot_xv6 (the "gate-source fact recording" item of
      Phase 1) — now a confirmed requirement, not optional.
  (4) ctrl_closed is needed by the POLICY (handing out gmo-earlier writes needs gsrc_t_real'), so it
      stays a premise of both theorems.
- OPEN QUESTION, DEFERRED (owner, 2026-10-02): Iris INVARIANTS around acquire/release blocks.
  Memory-content invariants (the SC tier's `inv lockN lock_inv` opened atomically at the amoswap,
  reading `lk ↦ v` inside) are NOT available: phase 1 unfolds each hart's WPd in po, values are
  validated in gmo in phase 2, and under LB there is no global "now" at which an invariant's memory
  facts hold — the design uses location protocols instead (constraints review 2026-09-30: "no
  invariants" = fundamental). The client interface is unaffected: is_lock is a persistent
  registration that clients never open; R carries the lock's resources (owned points-to, ghost
  state, `∃ s, data ↦ s ∗ I s`), as SC-tier clients already use it. UNCHECKED: whether GHOST-ONLY
  Iris invariants (no memory facts) are sound across phase 1 / deferred phase-2 validation — plausible
  but needs a fresh-advisor review before anyone relies on them. Revisit after Theorem 1 lands.
- Phase 1a DONE (iris/AxSpinProt{,2,3,4}.v): lock component of prot_xv6 + spin_handoff with
  satisfiability / race / sanity certificates. Fresh-advisor review 2026-10-02: PROCEED, with
  REQUIRED for Phase 1b: (1) fe_release takes each R component from flow_in (no single anchor a —
  R_pid's nextpid and lk->cpu tokens sit at different anchors, joined only via the fence; keep the
  old form as a corollary); (2) fe_claim variant taking notheld through flow_in (after a release
  notheld is a phase-2 resource w ↦ₐ notheld; sw lk → later RMW on lk is ppo rule 1 ⇒ in lobp);
  (3) fe_lkread_held: locked i c in flow_in (claim ∈ lobp by rule 5) ⇒ deposit locked ∗ ⌜v ≠ 0⌝ AT
  THE READ (D4's release-panic refutation reads it from the load's annotation at the row end); the σ
  NZ conjunct is then likely redundant. lk->cpu notes: the racy read needs owned_read_rule's
  two-case split (a forwarded same-hart source may be unprocessed); an 8-byte single-source lemma
  (aligned sd writes); NOTHELD_LINK is NOT needed for D4 (pure row fact + Φ_cpu + cid injectivity),
  keep `link` only for release. initlock's unheld lk->locked = 0 has no arm: genesis = image,
  stated in the theorem header. F2/F3/F4/F5 confirmed (genesis R must have the image arm, H = []).
- INTERFACE VERDICT (advisor, 2026-10-02) — F1 RESOLVED BY DESIGN, NOT A RISK: a phase-1 post with
  the LITERAL `locked ∗ R` in hand is impossible in this architecture (phase 1 unfolds every hart's
  WPd before any flow equation runs; a resource moved from A to B exists for B only in phase 2). The
  interface is handle-based:
    acquire: is_lock lk R ∗ notheldₕ ⊢ WPd {{ ∃ c, ⌜lk_claim c⌝ ∗ c ↦ₐ (locked i c ∗ R c) }}
    release: is_lock lk R ∗ [∗ j] a_j ↦ₐ R_j a_j ∗ c' ↦ₐ locked i c ∗ ⌜gob a_j w⌝ ⊢ WPd {{ w ↦ₐ notheld i }}
  (notheldₕ in hand on first acquire, a handle afterwards). The SC proof SHAPE is preserved because
  the surface is already provenance-based (AxSymReg): weak-tier owned points-to = a handle predicate
  `a ↦ₕ v := ∃ e, e ↦ₐ (tok a … ∧ last = v)`; critical-section leaves are owned load/store rules that
  move the handle to the new event under e ∈ lobp r (rule 5 from the claim; rule 1 for stores; a load
  after a same-address store: forwarded ⇒ pure value = own store data, no ownership drawn; else
  gmo-after). Value facts surface at post_lifting / gates as today. COSTS (Phase 2 scope): (i)
  per-address handle components (AxWp.annot_split) — mixed-address CS accesses are not gmo-ordered;
  (ii) a forwarded-reload leaf + per-read-after-write graph case split (neutralises AxSpinWit
  FINDING 1 for lock-protected bytes); (iii) release gathers components via the fence. allocpid
  needs none of (ii). OWNER-ACCEPTED 2026-10-02 — see the MAJOR DESIGN POINT section at the top.
- Phase 2 DONE (iris/AxSpinH{,2,3}.v): handle points-to `a ↦ₕ{e} mv` (anchor explicit), generic
  owned-class leaves wpd_ld_own / wpd_sd_own / wpd_reload_own (gmo-vs-forwarded split inside the
  leaf), handle-form acquire/release contracts, certificate cs_reload_owned (read-after-write in a CS,
  both arms satisfiable, race + sanity). WHERE THE CLIENT PROOF DIFFERS FROM "SC WITH ↦ₕ FOR ↦" (the
  honest cost of the MAJOR DESIGN POINT): (1) anchors are visible — each access carries a ppo
  premise about the handle's anchor, existential (w or r) after a reload; (2) `ld x; ld x` is NOT
  covered — two same-address loads reading the same write are unordered in RVWMO ⇒ needs FRACTIONAL
  read handles (reads need only a fraction of hist_auth); (3) value facts are phase-2 (deposited,
  read back at row end) except the forwarded reload's v = b; (4) under handles the owned-store
  history append happens in the store's PHASE-2 flow equation (AxSpinWit finding 1's phase-1 append
  needs the auth in hand, which a handle holder lacks) — admissible because a reload draws from the
  store's annotation only when gmo-after it; (5) handle splitting only inside a step (acquire
  allocates the claim annotation pre-split); (6) release_h needs the handle anchor ≠ the claim
  (annot_merge step missing). allocpid's CS (lw; addiw; sw nextpid) needs none of (2)/(6) but needs
  n-byte leaves (hdl_n defined, leaves not written).
- Phase 3 leaves (iris/AxSpinCtl{,2,3}.v): control leaves on surface v4, instr5 text facts,
  release_wpd5 (11/14 slots; w_cret/w_hold/w_pop premised). FINDINGS: (a) AxRelease4.release_wpd4 is
  VACUOUS (instr4_rli10_false). (b) D3 CONFIRMED, the spike note was wrong: release's sd/sw (+0x12,
  +0x1a) take s1 from holding+0x26 c.ldsp (holding saves s1 at +0x0e, clobbers it at +0x14); acquire's
  amoswap (+0x1c) and sd (+0x28) take s1 from push_off+0x26's reload. No valid exact-register map
  covers this (ret_ra_not_exact). (c) every c.ret after a callee-saved ra reload has the same
  problem: phase 1 cannot know the reloaded value (it is an ownership fact, phase 2). Open design
  question — see the next note.
- RELOADED-REGISTER DECISION (advisor 2026-10-02; OWNER-DECIDED 2026-10-03: option 1, AS A
  TEMPORARY ASSUMPTION — to be removed later by the row-integrity theorem). Problem: reloaded
  callee-saved registers feed c.ret targets and store/AMO bases (release via holding+0x26, acquire
  via push_off+0x26); "reload = saved" is phase-2 only. Recommendation: (A) ROW PINNING is ALREADY
  the semantics — astep/aread_step check every label's identity (kind/aq-rl/base/size) against
  row !! k and allocpid_prefixes pins CFG path, fetch addresses/values and data base addresses; a
  diverted ra/base ⇒ label mismatch ⇒ stuck ⇒ WPd@MaybeStuck trivial on that branch. Missing only
  the leaves: generic `wpd_stuck` (Löb over the wire clause), row-pinned `wp_cret_row` (∀ra; on-row
  arm gets ⌜jalr_target ra = pinned pc⌝ as a pure ROW fact), `wp_sd_row` / `wp_amo_row` (base not
  exact; on-row ⇒ base exact), surface v4's exact map may GROW at a row-pinned access. ≈1.5–2.5k
  lines, no new adequacy. (B) a WPd gate arm is REJECTED: unsound in phase 1 (CondA_gate_trivializes;
  only phase-2 handouts / row-end readback are sound), useless under pinned rows, inexpressible for a
  fetch after c.ret (no ctrl→R edges). (C) HONESTY: Hrow makes A/B's control-flow and address
  integrity a PREMISE — both theorems' headers must say so ("proves nothing about a hart whose
  control flow or addresses are diverted; ownership is load-bearing for DATA VALUES"); add certificate
  (b″) stack_race_unprovable (C writing A's stack slot is unprovable — demonstrates the stack
  component, not used by the conclusion); add a VALUE-LEVEL integrity conjunct to the per-hart post
  (every callee-saved reload's value = its spill's data, read back from the owned reload
  annotations) so ownership is load-bearing for a stack fact in the statements. Deferred open item:
  ROW-INTEGRITY theorem (with every hart verified, each hart's row ∈ allocpid_prefixes; induction on
  prefix length via readback) — weeks; it is the same gap as the informal prefix-closure caveat.
- Phase 1c DONE (iris/AxSpinX{,2..8}.v): joint instance prot_xv6 / Ixv6 over a layout record, all
  classes (lock 4 B, lk->cpu 8 B with real cpus_ptr, holder last-value read, nextpid with Theorem-2
  ghosts, private stack/cpu fields, read-only, blocked), xv6_Hok, xv6_Hob_alloc; capstone
  xv6_handoff + non-SC satisfiability (forwarded reloads), SC twin, Φ_cpu race + sanity twin.
  DEPARTURES: private memory has NO history ghost — WOK (writer = owner) + a row fact ("w is r's
  latest earlier store") pins reloads, deferred or forwarded; the stack rules are ROW-INDEXED and
  stack_own/cpu_own/kernel_text are pure layout facts (stack migration between harts = extension
  point; AxRelease4's position-free ld_rule is not achievable this way). cl_aligned (every lk->cpu
  write is an aligned sd) is a premise. NZ still lives inside the reused 1a component (unused).
  The minted issued fragment is deposited but not yet read back (joint-adequacy phase).
- Phase 2b DONE (iris/AxSpinH{4,5,6,7}.v, instance spin_ob6): n-byte handle leaves (any width;
  4/8 instances), fractional read handles (hdlw_split, RbN_join, two-halves store), WPd-level
  wpd_annot_merge/split/entail — closes Phase-2 differences (2) ld;ld, (5) split only in a step,
  (6) release with anchor = claim. Certificates: cs_dbl_load (lw x; lw x agree; race + sanity),
  cs_untouched (CS not touching x). NOTE: the handle instance spin_ob6 is SEPARATE from Phase 1c's
  prot_xv6 (AxSpinH4 §1 copies AxSpinX3's plain rules) — the two must be unified before Phase 5
  (leaves instantiated at Ixv6). wpd_reload_own_n not yet exercised by a certificate.
- UNIFICATION DONE (iris/AxSpinU{,2,3,4}.v): handle surface at Ixv6 (generic 1-byte interface
  discharged; 4/8-byte nextpid and lk->cpu leaves written at Ixv6; real-width lock contracts
  wpd_acquire_x / reacquire / acquire_fail / release / lk_held), allocpid-SHAPED 2-hart certificate
  (acquire; lw nextpid; addiw; sw nextpid minting issued; fence; sw lk) proved only with handle
  leaves: u_alloc2 (wA ≠ wB), u_cs_src (A arbitrary), satisfiability, race (unlocked nextpid writer
  unprovable), sanity. Distinctness via the graph DICHOTOMY (graph-true); the issued-fragment route
  is proved at ghost level (upost_joint) but needs the JOINT adequacy variant (tierA_adequacy_ann_gate_joint,
  plan Phase 3) — the next prerequisite for Theorem 2. Limits: layout Lx only; no word-level generic
  interface; lk->cpu leaves, re-acquire, failed spin, holder lw proved but not exercised; hand nodes
  (PIPELINE MILESTONE). NZ removal deferred (needs the lock component re-proved).
- JOINT ADEQUACY + OPEN-THIRD-HART (hand rows) DONE (iris/AxSpinJ{,2}.v): tierA_adequacy_ann_gate_joint_t
  (iProp posts Φ, Hjoint ==∗ ⌜P⌝; core copy-adapted from AxDefer5; regression corollary re-derives
  tierA_adequacy_ann_gate_t). u_alloc2_joint (distinctness by issued-fragment exclusivity) and
  u_alloc_open — harts [A;B;C], C ARBITRARY with HwpC at Ixv6 ⇒ wA ≠ wB: the OWNERSHIP-LOAD-BEARING
  statement in Theorem 2's shape, on hand nodes. Certificates (a′) 3 harts all running the CS,
  (b) C = unlocked `sw nextpid ← 0` ⇒ wA = wB on a consistent graph ⇒ C unprovable, (c′) sanity.
  Layout L3 adds C with no private stack/cpu bytes (prot_L3_Lx bridges to Ixv6 at Lx) — C-private
  memory / stack migration not covered.
- ROW-PINNED LEAVES (iris/AxSpinRow{,2,3,4}.v): wpd_stuck (wpdM_stuck; row_stuck_of_first =
  first_ev Sail fact + row_rejects), wp_store_row / wp_amoswap_row / wp_cret_row / wp_csdsp_cond,
  exact-map growth (Ex_at, ex_ok_grow_store), release_wpd6 (s1 part of w_hold gone; Hoff_lk premised),
  stuck/not-stuck certificate on a hand fetch node. OPEN FINDINGS: (1) the off-row premises
  (OffBase/OffRet) are NOT discharged — need a Sail "first event at an arbitrary pc" fact (walks,
  traps) and positional engines; (2) c.ret needs a POSITIONAL cursor: a function called from two
  sites in one row (holding from acquire and release; mycpu) has no single return pin
  (two_site_pin) — the leaf must use the row position of the next fetch, not a per-function pin;
  (3) the pasted SC release text's w_cret slot is ∀ m and cannot be discharged by any c.ret leaf
  (cret_slot_uniform_Ex6 / _Ex_rel) ⇒ needs a CALLER-INDEXED release spec; (4) release's own entry
  spill (+0x06, rel_entry_s1_needs_exact / p6_06): the SC spill/reload slot hands back the LOGICAL
  value, a non-exact spill only the physical one ⇒ the replay's spill/reload slot shape must change.
  (3)+(4) mean the "replay ProofRelease/ProofAcquire text over an abstract interface" route (Phase 5)
  needs re-shaped slots for calls/returns and spills — recheck Phase 5's approach before starting it.
- PHASE 5 ROUTE CHANGE (advisor 2026-10-03, adopted by the orchestrator): the pasted-SC-text replay
  is RETIRED for real code — its slots are position-free (∀ m return targets, logical-value
  spill/reload, one spec per callee) while the weak tier is positional (findings 2–4 of ROW-PINNED
  LEAVES are one structural mismatch). NEW ROUTE = a ROW-DIRECTED POSITIONAL ENGINE: per-function CPS
  specs `wpd_f : ∀ k (row shape of f at k), Pre -∗ (∀ s', ⌜Post_regs k s'⌝ -∗ Handles' -∗ WPd s' {{Ψ}})
  -∗ WPd s_k {{Ψ}}`, caller-indexed by construction (return pc and base addresses read off row !! (k+j);
  holding-from-acquire / -from-release = two instantiations); register values symbolic (AxLdgSeal
  kit), memory values as handles / row-end readback; spill = physical word, reload = fresh symbol +
  ⌜reload = spill⌝ deposited at the read (Phase 1c row fact + WOK). Built on AxCert2.wpd_instr_of_CertM
  (position k, budget, continuation k'), SpineOkT_SW / SpineFetch4T_SW, X_* leaves. Off-row premises
  REPLACED by one engine lemma `wpd_node_fit_or_stuck` (at a RAM node: the label fits row !! k, or
  row_stuck_of_first fires with first_ev trivial) — plus ONE owed Sail fact: riscv_step from a boundary
  at an ARBITRARY VA is a Cert (fault arms register-only until PC := stvec; stvec ∉ lock text by
  Hlayout). Staged: (1) engine plumbing + Row f k predicates; (2) CERTIFICATE mycpu (drive2 non-
  vacuity + diverted-return stuck twin on a REAL fetch node); (3) holding at two call sites;
  (4) arbitrary-VA Cert (parallel); (5) push_off/pop_off, release, acquire (spin induction).
  SUPERSEDED as a route (headers to be marked; files kept): AxRelease4/5, AxSpinCtl3 release_wpd5,
  AxSpinRow3 release_wpd6/Ex6, AxLeafS4/AxLeafS5 §3, the Cond-mirror surface (AxSymMem3, AxCondM*);
  AxSpinRow2's OffBase/OffRet leaves. AxReuseProbe verdict B re-recorded: statement-level reuse YES,
  script-level reuse NO for code with calls/spills. Depends on Hrow pinning (the pending honesty
  decision only changes the theorems' wording / the deferred row-integrity theorem, not this route).
- OWNER DECISION 2026-10-03 — Hrow PINNING IS A TEMPORARY ASSUMPTION. Both theorems assume A's and
  B's control-flow and address integrity via Hrow (CFG path, fetch addresses/values, data base
  addresses pinned). REQUIRED with it: (i) both theorems' headers state it verbatim ("Hrow pins …;
  this theorem proves nothing about a hart whose control flow or addresses are diverted; ownership
  is load-bearing for data values"); (ii) certificate (b″) stack_race_unprovable (C writing A's stack
  slot is unverifiable at Ixv6); (iii) the per-hart post carries the VALUE-LEVEL integrity conjunct
  (every callee-saved reload = its spill's data, read back from the owned reload annotations).
  FOLLOW-UP COMMITTED TO (owner: "work to remove that limitation later"): the ROW-INTEGRITY theorem —
  with every hart verified, each hart's run row ∈ its path family (allocpid_prefixes), by induction on
  prefix length via phase-2 readback (AxEpiRet shape: reload = spill by ownership pins the next fetch /
  base address); it also closes the informal prefix-closure caveat. Scheduled after Theorem 1 lands on
  real code; then Hrow's address/CFG pinning is dropped from the theorems' premises.
- 2026-10-03 (evening): wpd_mycpu landed (AxSpinE8, statement = draft) + certificate (b) (AxSpinE8d: concrete warm-TLB row,
  diverted ra reload ⇒ row-stuck at k+18, on-row twin not stuck). VACUITY FINDING (AxSpinE8e): Xx_ret's Hinj quantifies over all
  64-bit VAs but the walk reads bits 38..0 ⇒ only satisfiable with pret unmapped; fix = canonical-VA restriction of va_rd + Hinj.
  wpd_holding (AxSpinHd…HdB; both call sites) and wpd_push_off / wpd_pop_off (AxSpinPO*; CertBm for sstatus reads) landed.
  ENGINE GAP: wpd_drd_nodeM's no-RMW premise is whole-row — false on rows with acquire's amoswap; needs a positional variant
  before the lock-word read in holding and acquire's amoswap leaf can be discharged.
- 2026-10-04: Hinj FIXED (va_rd fetch disjunct + Hinj restricted to canonical VAs; va_first_read stays true since non-canonical PCs
  fault before any RAM read, AxSpinVA7); certificate (a) cert_a (AxSpinE8f). ENGINE GAP CLOSED for plain reads: the whole-row
  no-RMW premise was only used at the node's own position (AxCertP); window-bounded bridge (AxCertP2, Fam_bound); the flow resource
  FldM also had to be window-restricted (FldMW, AxCertP3) since acquire's amoswap reads (lk,4) on the same row. holding's lock-word
  leaf discharged at both call sites (AxSpinHdC). Remaining for acquire: a CertB for amoswap.w.aq.
