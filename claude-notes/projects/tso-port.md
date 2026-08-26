# TSO port — plan of record

## 0. CHECKPOINT — READ THIS FIRST

**Where the tree is.** Legs T and M are LANDED on branch `tso`.
`iris/TsoMem.v` is the minimal Ztso machine; `TsoLitmus.v` its 8
verdicts; `TsoCtx.v` the SC-degenerate ownership surface Σ that ~600
files depend on; **`TsoCtxTwin2.v` is the CORRECTED construction, built
and green — it supersedes `TsoCtxTwin.v` (the global-map prototype) and
answers `TsoCtxRehearsal.v` (both kept as the discovery record)**.
`tools/ctx_convert.py` + the
[`interface-sweep-playbook.md`](../interface-sweep-playbook.md) are how
the sweep was done and how to repeat it.

**THE Σ REPAIR IS LANDED** (2026-08-25): `TsoCtx.v` now exports the
corrected statement list (§0.1′ below), every export names its proven
twin image in `TsoCtxTwin2.v`, and the checkpoint-0.4 items are closed
or reduced as recorded in §0.4′. Sections 0.1–0.5 below are the PRE-
repair analysis, kept because the twin's findings amended two of its
rulings-of-record (see 0.1′); read 0.1′/0.4′ first.

### 0.1′ The corrected construction, as landed

`TsoCtxTwin2.v` — read its header first; in one breath: per-context
state is ONE MONOTONE NAT (the bound, a `mono_nat` at a gname `CtxId`
itself carries), the clean/dirty bit rides INSIDE `ctx_pointsto` (clean
= a persistent bound-lb, COPIED by transport; dirty = a fragment of the
context's own dirty set, its author-tie held in the running bundle),
and BOTH per-context authorities travel IN THE TOKENS — the state
interpretation owns machine ghosts only (latest-heap, persisted log
entries, log length, hart views) and does not know contexts exist.
Consequences, all proven:

- **`CtxMorph`'s bare shape is TRUE AS WRITTEN** (`ctx_morph_pointsto`):
  `ctx_dom ξ ξ'` carries half of ξ's authorities (value-pinned by
  agreement with the halves left in the token) plus a bound-lb of ξ'.
  Statable with no machine state, exactly as Σ requires. Mints:
  `ctx_dom_to_parked` (release/fork side, INTERP-FREE — a parked
  target's stamp may be raised at will) and `ctx_dom_of_parked`
  (acquire side, the one mint needing the interp: at-the-top evidence).
- **Park, resume, exchange, fork-mint and deposit are INTERP-FREE**
  (`twin_park`, `twin_resume` — a WAND, `twin_exchange`, `twin_fork`,
  `twin_parked_alloc`, `twin_deposit`, `twin_fork_deposit`). Park is
  one bound-raise = the dirty→clean conversion; resume needs only the
  stable pair `view_lb h K ∗ ⌜T ≤ K⌝` — no relation between harts.
- **The stable view lower bound exists** (`view_lb h K`, persistent,
  monotone, carrying a log-length receipt), and the acquire-side mint
  that closes the swtch evidence chain is `twin_passed_get`: at the
  AMO's at-the-top postcondition, the parked token's own `llb T`
  receipt yields `view_lb h (tvs h) ∗ ⌜T ≤ tvs h⌝`.
- **Cross-context sharing is LEGAL** (`twin_share`): transport COPIES a
  clean justification instead of moving a ledger entry, so fractions of
  one byte live at many contexts, a discarded byte is persistent at
  every context that received it, and `ctx_pointsto_persist` no longer
  fights transport. The old per-byte-ledger-uniqueness world (and its
  `reh_pt_one_context` tension, old item 6) is GONE — no context-free
  carve-out needed.
- **TWO RULINGS AMENDED BY PROOF.** (a) `own_context_alloc`'s
  refutation was an artefact of the hart-keyed run map: a free running
  mint at bound 0 is SOUND in the corrected construction
  (`twin_run_alloc`). The interface ruling stands as kernel meaning:
  `TsoCtx.own_context_boot` (SystemAdequacy only) and the shim's
  `own_context_alloc` (sweep-era throwaways) are the two licensed
  spellings. (b) The fork stamp-at-the-parent's-counter mechanism is
  SUBSUMED by `ctx_deposit`, which raises the parked stamp per
  deposited fact — so `ProofForkretPark` mints at stamp 0 with the pure
  `ctx_parked_alloc`, and uvmcopy-after-fork deposits (dirty bytes, any
  fraction) with nothing to prove.

### 0.4′ The old open items, disposed

1. **`CtxMorph`'s shape** — FIXED before M3, as required. Class shape
   unchanged in `TsoCtx.v`; now known-satisfiable.
2. **The exchange/acquire evidence token** — CLOSED at the twin
   (`twin_passed_get` + `ctx_parked_llb`); at the surface it is
   `hart_view_lb K` (ambient-CID, persistent, sealed) consumed by
   `ctx_resume`/`ctx_exchange`. REMAINING (the honest M2 item): thread
   it from `SpecAcquire`'s AMO postcondition to `ProofSwtch`; until
   then `TsoCtxShim.hart_view_lb_any` is the licensed SC-only stopgap
   (FALSE at TSO, dies with the shim — the compile error it leaves IS
   the M2 worklist entry).
3. **The stable view lower bound** — EXISTS (`view_lb` twin,
   `hart_view_lb` surface).
4. **`own_context` hart-indexed** — the surface now says so:
   `own_context {CID : CpuId} ξ`. Ambient spellings tree-wide were
   unchanged (capability sections already carry CID); re-hosting is
   `ctx_resume`/`ctx_exchange` through swtch, never a frame.
5. **The parked-record shape** — DONE: `SwtchCtx.valid_context_pre`
   holds `ctx_parked XIp Tp` (both existential; the record stays
   migratable BECAUSE the parked token is hart-free), `ProofSwtch`
   parks the old side and resumes the new side on this CPU,
   `ProofForkretPark` mints parked, `SchedCtx` drops the token at the
   zombie park.
6. **Fractional/persistent sharing** — DISSOLVED (see 0.1′); the dq
   axis is proven at the twin (`ctx_pointsto_frac_split`/`_persist`/
   `_agree`/`_ne`, discarded-persistent instance).

### 0.5′ What I would do next

M2's honest evidence threading (`SpecAcquire` mints `hart_view_lb` at
the AMO; the proc-lock payload carries the parked record; `ProofSwtch`
consumes the real receipt and `TsoCtxShim.hart_view_lb_any` is
deleted), then M3 (lock payload `CtxMorph` obligations — now unblocked)
per §3. The `↦ₘ` notation flip (M1's tail) no longer waits on the
persist/transport audit — old item 6 is gone.

### 0.6′ THE LOCK SURFACE IS CONTEXT-SHAPED (landed 2026-08-25, in place)

M3's statement half plus M2's receipt, converted IN PLACE — no twins, no
parallel forms:

- **The payload of every spinlock is `R : CtxId → iProp`** (`WpLock.v`:
  `lock_inv`'s free arm parks `∃ ξ, R ξ`; `is_lock`/`lock_openable`/
  `lock_finisher`/the `newlock` family all at the new arity, creators
  depositing at `R cur_ctx` under a new ambient `{XI : CurCtx}`).
  Clients spell payloads with **`TsoCtx.<{ P }>`** (the weak-memory
  wrapper verbatim: binds a `CurCtx`, so a converted payload's ambient
  facts re-index under it; an unconverted payload embeds constantly).
  `Typeclasses Transparent CurCtx` is REQUIRED for instance search to
  see through the wrapper's binder type — without it every
  `Persistent (is_lock … <{P}>)`/`CtxMorph <{P}>` resolution dies.
- **`SpecAcquire`/`SpecRelease` restated**: the `CtxMorph R` obligation
  rides as an implicit class binder on the module-type Parameters (so
  every call site discharges it by instance search, zero edits); the
  acquire postcondition hands back `R cur_ctx` (bound OUTSIDE `wp_next`
  — migration survival in the statement) **and `∃ K, hart_view_lb K`**
  at the hart that won the lock (the M2 receipt; acquire-call intro
  patterns tree-wide gained one `_` slot). Release deposits `R cur_ctx`;
  no receipt (a TSO release is a plain store — that asymmetry is the
  model).
- **The two shim steps in `ProofAcquire`** (`ctx_dom_sc` for the
  ∃ξ→cur_ctx morph at the win, `hart_view_lb_any` for the receipt) are
  exactly where the cutover kit's direct proof puts the AMO's honest
  evidence (`TsoCtxTwin2.ctx_dom_of_parked`/`twin_passed_get`).
- Fallout: ~180 files, all mechanical (payload wraps at `is_lock`/spec
  applications; one receipt slot per acquire continuation; `{XI}`
  binders up the lock-CREATION call chains — creators deposit at
  cur_ctx, so `newlock`-callers to `xv6_boot_era` gained the ambient
  binder, adequacy instantiating it at a dummy identity until the kit
  mints the real boot context). Tree green on the VM; audit at
  baseline.
- REMAINING for M3 proper: convert lock USERS' payloads semantically —
  replace the constant embeddings `<{ mem-facts }>` with genuinely
  context-indexed payloads (`↦c` facts) carrying real `CtxMorph`
  instances, one lock at a time (kmem is the natural first).

### 0.7′ KMEM IS THE WORKED PAYLOAD INSTANCE (landed 2026-08-25) — THE RECIPE

The kmem lock's UNDER-THE-LOCK facts (the freelist head cell and each
free page's next-pointer word: `KallocInv.word_at`, threaded through
`run_page`/`freelist_chain`/`kmem_res`) are context-indexed; the page
BODIES (`byte_any`/`page_own`, which cross the kalloc/kfree CLIENT
boundary into ~56 files) stay `↦ₘ` until the M1 flip.  Four findings,
each now the recipe:

1. **A CONVERTED PAYLOAD NAMES ITS CONTEXT** — explicit `(ξc : CtxId)`
   argument, spelled `ctx_pointsto ξc`, and lock mentions read
   `(λ ξ : CtxId, kmem_res ξ γk fl)`.  NOT ambient-under-the-wrapper:
   the `<{ P }>` wrapper's bound instance is resolved per elaboration
   site, and the silent-drop hazard fired VERBATIM on the first try
   (one site bound the wrapper's context, another the file's ambient
   `XI` — visible only under `Set Printing Implicit`).  `<{ }>` remains
   for UNCONVERTED constant payloads only, where the ambiguity is
   harmless.
2. **`CtxMorph` instances export beside the sealed definitions**
   (`word_at_morph` → `run_page_morph` → `freelist_chain_morph` by
   induction → `kmem_res_morph`), and inside those proofs the
   structural instances must be applied AS TERMS
   (`ctx_morph_big_sepL … (λ i x, ctx_morph_pointsto …)`): instance
   SEARCH cannot do the higher-order big-op unification.
3. **ctx↔mem seams are named bridges, never unfolds.**
   `word_at_of_mem`/`word_at_to_mem` (derived from the shim; KallocInv
   imports it = the seam marker) sit at exactly the leaf boundaries in
   ProofKalloc/ProofKfree/ProofKinit.  The old blanket
   `rewrite /word_at; iExact` pattern DEGENERATES against the sealed
   ctx fact — a 157 GB, 35-minute rocqworker chewing on an
   8-byte-big-op unification (found by `ps -o rss` on the VM, the
   durable-notes diagnosis verbatim).  If a build round stalls, look
   for a worker like that before suspecting the machine.
4. **Name `ξc` where the conclusion doesn't pin it** — applications of
   lemmas whose ξ appears only in a premise or an intermediate
   (`page_head8_word_at`, `run_page_page_own`, `kmem_res_push`) leave
   an unresolved evar that surfaces as incomplete-proof-at-Qed far from
   the cause; pass `(ξc := cur_ctx)`.
5. **THE PAYLOAD ARGUMENT STAYS EXPLICIT AT CALL SITES** (owner ruling
   2026-08-25, reversing the first version of this rule).  An `_` there
   IS sound — the evar unifies from the framed `is_lock`/`R cur_ctx`
   hypotheses, verified on ProofKalloc both directions — but it is BAD
   FOR PROOF PERFORMANCE: the specs' implicit `{!CtxMorph R}` argument
   runs instance search while `R` is still a flexible evar, and the
   structural instances (`ctx_morph_sep`/`exist`/`big_sepL`) unify with
   an evar by INVENTING structure, then backtrack — the pipe proofs
   went from minutes to unbounded (15+ min rocqworkers, killed).  The
   full 156-site erasure sweep was applied and REVERTED;
   `tools/lock_ctx_sweep.py`'s `erase` mode is kept as the record of
   the experiment, marked rejected.  Consequence: a payload conversion
   includes a mechanical call-site pass (the old payload expression is
   the grep key; kmem measured ~10 sed sites per lock).
   `TsoCtx.ctx_morph_const`'s `| 100` priority stays — it is the right
   ordering for concrete payloads regardless.  If call-site erasure is
   ever wanted again, the prerequisite is a
   `Hint Mode CtxMorph - - !` suspending instance search until `R` is
   rigid — measure before adopting.

Tree green on the VM (full rebuild + 88-file follow-up, EXIT=0), audit
at baseline.  Next payloads repeat 1–4; after the M1 flip, step 3's
bridges die and step 1's spelling is what the flip's review must keep
deterministic.

### 0.8′ THE M1 NOTATION FLIP, STAGE 1 (2026-08-25/26) — ↦ₘ AND ↦₈ ARE CONTEXT-INDEXED

**THE REPLAY RUNBOOK IS ITS OWN FILE:**
[`tso-flip-replay.md`](tso-flip-replay.md) — the re-application
process for main (passes, tool invocations, the error-class → fix
table, the three probes, the landmines).  This section keeps the WHAT
and the WHY; that file keeps the HOW.

**What flipped.** `TsoCtx.v` re-declares all four `↦ₘ` spellings as
`ctx_pointsto cur_ctx …` and all four `↦₈` spellings as
`ctx_word_pointsto cur_ctx …` (a full word tower — `ctx_word_pointsto`
plus unfold/aligned_p/bytes/intro/frac_split/persist/agree and
`ctx_morph_word` — lives above the sealed byte).  Import order decides:
a file that imports `TsoCtx` (last) parses the flipped meaning, a file
that does not stays raw, and definitions are opaque names to their
consumers, so the honest fallout is exactly the fact-passing SEAMS —
found by ~30 error-driven build rounds, not by prediction.  `↦ₓ`/`↦ᵣ`
never flip; `↦₂`/`↦₄`/`↦ₛ`/`↦ₚ` are stage 2 (each remaining
`TsoCtxShim` use at a `↦₄`-split/join or string extraction is a stage-2
worklist entry).

**KMEM REDONE MINIMAL-DIFF (the acceptance test).** `KallocInv.v` is
the SC file plus: one section binder (`Context `{XIk : CurCtx}` — every
body byte-identical, `word_at` now the `↦₈` notation), `is_kmem` moved
below the section with the payload spelled
`(λ ξ : CtxId, kmem_res (XIk := ξ) γk fl)` (rule 1), and the `CtxMorph`
block (structural instances applied as terms; `page_rest` now honestly
morphs its 4088 bytes).  The `word_at_of_mem/to_mem` bridges are GONE;
`ProofKalloc`/`ProofKfree`/`ProofKinit` are their SC texts verbatim
except the payload-λ spelling at ~6 acquire/release/newlock sites.
GOTCHA: the big-op seal (`Typeclasses Opaque byte_any word_at …`) must
be `Global` — the morph section sits outside the section that declared
it, and an unsealed `page_rest` sent `iFrame` crawling through 4088
conjuncts (caught with `coqc -time`; the fix is one word).

**Rulings the flip forced (each is a design decision, revisit welcome):**
1. **`kernel_data` is ∀-CONTEXT** (`∀ ξ, [∗ map] … ctx_pointsto ξ …`):
   image bytes predate every thread (the twin's timestamp-0 story), the
   one boot mint serves every consumer at its own ambient, and all ~169
   mention sites are textually unchanged.  `kernel_data_string` keeps
   its raw `↦ₛ` conclusion via one shim use (the "flip ↦ₛ" marker); its
   proof instantiates the ∀ at a CONCRETE `MkCtxId inhabitant
   inhabitant` so the lemma does not capture the ambient (capture
   shifted call-site elaboration — ProofPanic/ProofFilewriteParts broke
   until de-captured).
2. **Lock metadata stays RAW; lock-internal cells go ∃-context.**
   `lock_name`/`sl_name` (the name field) are spelled raw
   `word_pointsto` — a context in the persistent HANDLE would make a
   boot-minted `is_lock` unstatable elsewhere.  `lk_cpu_res`'s owner
   cell is `∃ ξ, ctx_word_pointsto ξ …` (the cell belongs to whichever
   hart last stored it); the `lk_cpu_res_free/win/held` unfold lemmas
   keep their ambient statements via `WpLock.lk_cpu_cell_acc` (shim).
   Both are M4 markers — lock-internal cells become racy-kit facts.
3. **`<{ P }>` IS A COMBINATOR (`const_pay`), NOT A λ.**  Any
   `CurCtx`-typed binder — even anonymous — is a TC candidate inside
   `P`, and elaboration picked it at some sites and the outer ambient
   at others (the silent-drop hazard, observed as ~40 `proc_lock_res`
   mention sites refusing to unify).  `const_pay P` elaborates `P` as an
   ARGUMENT, outside any binder: deterministic, and `ctx_morph_const_pay`
   serves it.  The proc lock therefore STAYS on the constant embedding
   — its λ-conversion was attempted, hit the real M2 wall (the payload's
   `▷ proc_ctx`/chain-fixpoint transport), and was reverted; converting
   it is M2/M3 work with `SchedCtx`'s parked-record design, not a flip
   chore.
4. **`StackOwn` FLIPPED (left the binder blacklist).**  A stack frame is
   thread data; keeping it raw made every function proof's
   prologue/epilogue a shim seam (7 files patched one iFrame at a time
   before the pattern was recognized; the flip deleted the class).
   `stack_own_phys` stays raw; `BootBridge.phys_word_to_word` mints the
   ctx words at the boot hand-off; `stack_own_reindex` (shim-tier) is
   the swtch crossing's SC placeholder, used once in `ProofSwtch`.
5. **`cpu_ctx_free` is ∃-CONTEXT** (nobody is parked in a free save
   area), preserving the eight-hart adequacy story its header records;
   `SwtchCtx.ctx_cells_reindex` (shim-tier, outside the section) trades
   the ∃ for the scheduler's ambient — an M2 worklist entry.
6. **`wordw_pointsto`/`bb_*`/`kxc_*` interior towers** were re-spelled
   ctx so leaf plumbing frames syntactically; the machine seam
   (`s_win_write`, `gen_heap` edges, phys tier) converts through
   `TsoCtxShim.ctx_buf_of/to_mem` and the new `ctx_eslot_of/to_mem`.

**The seal is unification-PERMEABLE at SC.**  `Global Opaque
ctx_pointsto` does not stop `iApply`/`iExact`/`iMod` unification from
proving ctx-vs-mem convertible (that is also why `iExact` works as a
direction-agnostic crossing where syntactic `iFrame` fails).  Two
consequences: some seams pass SILENTLY (they surface at cutover as
compile errors, which is acceptable — the cutover list is the ultimate
inventory), and unifying two DIFFERENT context variables under the seal
can CRAWL (UsertrapRes went 35+ min on one `iExact "Hcaps"` — see
below).  `coqc -time` on the GCP VM is the diagnostic.

**Tooling (kept, per owner instruction, for the re-application to
main):** `tools/ctx_convert.py` gained `ambient` (section binders for
TsoCtx-importing files whose sections use the flipped vocabulary;
inline-skip guard; boot/adequacy blacklist) and `inline` (per-decl
binders in inline-managed files, gated on the harvested vocabulary and
enclosing-section coverage).  The harvest list in `FLIPPED` grows as
conversions land — vocabulary scanning cannot see ctx-ness that arrives
through a converted definition name, so the build's `?XI : CurCtx`
existential errors are the signal to extend it.

**NOT GREEN YET — the open tail (all M2-shaped):**
- `UsertrapRes.ut_res_bare_park` — the park protocol's capability
  crossing is UNPROVABLE post-flip, not slow: the record stores
  `park_env`/`ut_park_caps` at PARK time and replays them at the
  ∀-quantified RESUME context `Xc`, and the bundle's handles
  (`procs_inv` → wrapped proc payloads → `proc_ctx`/`valid_context`)
  are now genuinely ξ-dependent — MEASURED: `proc_ctx (XI := ξ) ⊣⊢
  (XI := ξ')` fails `reflexivity` fast with every sealed constant
  transparent, so the 35-minute `iExact "Hcaps"` was unification
  exhausting an unprovable goal.  The fix is the redesign the file's
  own M2 comments sketch: the env moves INSIDE the ∀, resumer-supplied
  (the `W`/`first_done`/`timer_cap` channel), which wants either the
  proc-lock payload λ-converted (rule 1, so `procs_inv` is a CLOSED
  term — its CtxMorph then needs a ▷-capable transport, the real M2
  machinery) or the resumer's global bundle pinned to `N`'s `un_*`
  fields.  Cascades through `ParkCap.park_chan`/`park_token` (a
  guarded fixpoint), `UtResFits`, and the resume sites.  OWNER
  DECISION RECOMMENDED before implementing.
- `ProofKernelvec` (~1681) — the trap RESUME crossing, same family:
  the kerneltrap continuation's premises will not instantiate against
  the caller's (hidden context index differs across the crossing).
- Downstream of those two files only; everything else builds.  Last
  round's numbers: full tree minus {UsertrapRes, ProofKernelvec,
  BootCarveMain (disk-record mints, fix applied unverified),
  ProofSysOpenParts, SpecKexecB2 (binders applied unverified)} and
  their dependents.

**Where the flip's honesty lives now:** grep `TsoCtxShim` (imports =
seams), `Local Transparent ctx_pointsto` (one use, `SchedCtx`'s
proc-payload morph attempt — currently unused after the revert; remove
if it stays dead), and `reindex`/`eslot`/`cell_acc` (the SC-only
transports that die with the shim and become the M2/M4 worklists).

---

**The PRE-REPAIR checkpoint follows, as history.** Its §0.1–§0.5
described the design as of the rehearsal; where it conflicts with
0.1′–0.5′ above, the primed sections govern.

**Where the DESIGN was: Σ's shape was not yet right, and the rehearsal
plus the review that followed it said exactly how.**

### 0.1 The ownership design, as it now stands

1. **`own_context ξ` is the RUNNING token — "this hart is running as ξ" —
   and is NEVER allocated from nothing.** `own_context_alloc : ⊢ |==> ∃ ξ,
   own_context ξ` is REFUTED (`TsoCtxRehearsal.no_own_context_alloc`): the
   token is keyed by the HART, so two mints collide however fresh the
   identity is.
2. **Fresh allocation yields a PARKED context**, which claims no hart, so
   it can be pure. It must be stamped with a COUNTER: the child's bound =
   the log top at creation (equivalently the parent's bound, and the top
   is strictly more permissive). **That stamp is what makes the fork
   deposit free** — the parent's facts sit below its bound, the child's
   bound equals it, so domination holds by construction and handing facts
   to the child has NOTHING TO PROVE. Verified: `twin_deposit_at_fork`.
   Caveats: the stamp only covers facts held AT the stamp (a byte written
   after the fork cannot be deposited — if `uvmcopy` runs after the child's
   record is built, stamp at the END of fork), and the deposit itself needs
   the ledger authority, so an interp-free mint buys nothing on its own.
3. **The EXCHANGE is the primitive** (`own_context C1 ∗ parked C2 ==∗
   own_context C2 ∗ parked C1`, recording C1's counter), not park-then-
   resume: a hart always runs exactly one thread. Its premise is best
   stated as **"this hart is at the log top"**, which the `p->lock`
   acquire supplies and which means the parked record need not expose its
   timestamp. `SpecSwtch` currently carries nothing that would discharge
   it (vacuous at SC).
4. **Boot is the only site of a hart's FIRST running token**, justified by
   the interp being constructed there.

### 0.2 The two refuted statements, and what is NOT the fix

- **`CtxMorph` as stated is unsatisfiable** (`no_ctx_morph_pointsto`,
  refuted inside a WELL-FORMED configuration).
- **DO NOT "thread a world" through it.** That was tried and reverted.
  Existentially closed, the caller cannot recover its specific interp
  indices to hand back to `wp_lift_step`; named explicitly, the state
  interpretation leaks into every lock client's spec. **Σ must be
  statable without naming the machine's state interpretation, because Σ
  is what 600 files depend on — that constrains the ghost construction,
  not the other way round.**

### 0.3 The ghost construction — the live design question

The twin's `ctx_pointsto ξ a v := ∃ t, a ↪[γheap] (t,v) ∗ (ξ,a) ↪[γledger] t`
has a **global** ledger whose authority sits in the interp; that is WHY
transport needs the interp. Three rounds of review on it:

- **Per-ADDRESS registration is heavier than TSO needs.** The ledger's
  value duplicates the heap cell's timestamp; only its key (who owns
  what) does work.
- **Folding the owner INTO the cell is WRONG** — read-shared bytes are
  many-to-many, and an owner field forces all holders to agree.
- **Per-FACT state is irreducible, but it is a BIT, not a ledger entry:
  clean (justified by my bound) vs dirty (justified by my own
  unpublished write).** Forwarding is keyed on the HART, not the thread
  (`visibleb h tv log t = t ≤ tv ∨ log[t] authored by h`), so a
  context-indexed persistent "ξ wrote t" is UNSOUND across a migration,
  and a hart-indexed one would put a hart in the fact and break the
  survives-migration property. Park's bound-raise is what converts dirty
  to clean, and it is mandatory: a thread that migrates without
  publishing cannot read its own recent writes. **This is the
  `weak-memory` branch's C/D/S three-state points-to, re-derived** — and
  that branch hid the conversion INSIDE THE STORE LEAF via the migration
  invariant, so client proofs never see the distinction. Preserve that.
- Direction of travel: per-context state should be ONE MONOTONE NAT (its
  bound, mirroring the machine's one nat per hart), the per-fact bit
  rides in the points-to, and the authority a transport needs should
  travel WITH THE CONTEXT'S TOKEN (the real `CtxId` already carries a
  gname; the twin's `nat` throws it away). Get that right and
  `CtxMorph`'s original bare-update shape becomes true as written, the
  mint can read the parent's bound off the token, and the exchange's
  premise becomes stable. **One correction, three problems.**

### 0.4 Open, ranked by blast radius on the swept tree

1. **`CtxMorph`'s shape** — 2 files TODAY (M3 has not run; `grep` for
   `CtxMorph|ctx_morph|ctx_dom` outside `TsoCtx.v`/twin is empty), every
   lock client if M3 runs first. **Fix before M3 and it is free.**
2. **The exchange/acquire evidence token** — forces `SpecSwtch` to carry
   a hart-view fact and `SpecAcquire` to produce one (cheapest hidden
   inside `locked`/`cpu_own`, which swtch already holds at the proc
   lock). Blocked on the item below.
3. **A STABLE view lower bound is MISSING.** "Hart h is at the log top"
   is false one step later; the honest resource is a persistent monotone
   `view_lb h K` plus `⌜T ≤ K⌝`. The twin has no monotone-view resource
   at all. **This is the largest unclosed gap** and it gates (2).
4. **`own_context` is hart-indexed**, so re-hosting across `wp_next` is a
   real ghost step needing view evidence (`twin_rehost`). Points-to facts
   are NOT hart-indexed, so the ruling they survive migration unchanged
   HOLDS; it is the token's transport that gains an obligation. The tree
   already transports the bundle explicitly at migration, so this is
   bounded in files and expensive in thought.
5. **The parked-record shape** — `SwtchCtx.valid_context_pre` should hold
   the PARKED token rather than `own_context`; `ProofSwtch` exchanges;
   `ProofForkretPark` mints parked. Confirmed bounded: one definition +
   three proofs, no consumer arity moves (the identity is existential).
6. **Fractional/persistent sharing** — under the twin all facts about one
   byte live in ONE context, so a discarded (immutable) byte is pinned
   forever and `ctx_pointsto_persist` fights transport. Likely answer:
   immutable bytes are CONTEXT-FREE, same as kernel text. Invisible today
   (the `↦ₘ` notation flip has not landed); audit before M1's flip.

### 0.5 What I would do next

Rebuild the twin on the corrected construction (one nat per context, the
clean/dirty bit in the fact, authority in the token, a monotone
`view_lb`), re-run the rehearsal against it, and only then freeze Σ and
repair `TsoCtx.v` in one change. Do NOT start M3 (lock payloads) before
`CtxMorph`'s shape is settled.



Goal: move main's memory semantics from SC to operational **Ztso**, keeping
the proof tree. The port is **interface-first**: a context-indexed ownership
surface Σ is installed on main in independently-landable sweeps while the
semantics stays SC (every Σ statement has a degenerate SC instance, so main
stays green throughout), the same Σ is proven satisfiable by the Ztso machine
on the `tso` branch (the standing cutover certificate), and the final cutover
swaps only the below-Σ kit. Nothing above Σ is reproven at cutover — it
recompiles.

The load-bearing invariant of the whole plan: **every statement above the
seam must be provable in BOTH instantiations at all times.** The `tso` branch
is the standing check for the TSO side; main's CI is the check for the SC
side.

## 0. What is inherited from the `weak-memory` branch

Read via `git show weak-memory:<path>`. The branch is a long RVWMO effort;
this port takes its *validated* pieces and drops its RVWMO-only towers.

Take:
- **The machine**: `iris/WeakMem.v` (promise-free view machine: era image +
  global append-only write log + per-hart view record `wstate`) and
  `iris/WeakInterp.v` (the Sail seam: `MemRead`/`MemWrite`/`Barrier` arms,
  `classify : accessKind → akinfo`, read oracle). Ztso is an *instantiation*,
  not a new machine: TSO ⊊ promise-free ⊊ RVWMO, and
  `design/weak-memory.md` (Rejected alternatives) records "TSO = the same
  machine with implicit RCpc annotations" — every load acquire, every store
  release, at the `classify` seam. The forward bank `w_fwd` is the
  store-buffer-forwarding (W→R) exception, already built.
- **The language pattern**: `iris/WeakEvLang.v` (event-granular: one language
  step = one Sail monad node) and `iris/WeakEvAdequacy.v`. Main's `HartE`
  per-node language was built precisely so this swap happens "under an
  unchanged superstructure" (`design/main-cycle-port.md`).
- **The context surface** (the crown jewel; substantially implemented and
  green on the branch): `iris/WeakCtx.v` (CtxId, `ctx_auth` over the
  floors-only view, persistent `ctx_view_lb`, the `cobj` modality,
  `wrunning`/park/resume with the two causality premises),
  `iris/WeakCtxPt.v` (`wptsto`/`wptsto_cl` — iProp points-to with SC-shaped
  rules; `ctx_dom` ledger domination; `CtxMorph`), `iris/WeakCtxLock.v`
  (every lock owns a context ξ_L, internal only; release/acquire re-index
  points-to via `CtxMorph` "inside these lemmas and nowhere else").
  Acceptance tests to port as-is: `WkYieldFrame.v` (same access lemma
  verbatim on both sides of a cross-hart yield), `WkCtxSurface.v`
  (machine-checked: the exported statements are free of
  monPred/⊒/view_*/⊑), `WkMemmoveLoop.v` (interruptible loop at exact
  SC proof-length parity).
- **SC-parity as the organizing goal**: `design/weak-memory-sc-parity.md` —
  "for lock-disciplined code, the proof above the leaves should be the SC
  proof". Measured on the branch: converted M-mode chains at ~1.4× (residue
  attributed to a non-memory interface), memmove at parity, zero fences in
  client proofs.
- The vProp base (`WeakView.v`/`WeakVProp.v`), `WeakGhost.v` (state
  interp), `WeakFence.v`, `WeakLock.v`, `WeakBridge.v` (the ~1220-lemma SC
  decode/leaf transfer), `WeakCert.v`, and the litmus mold
  (`WeakSrvwmoLitmus.v`).

Do NOT take (RVWMO-only; the big prize of choosing Ztso):
- the full promising machine and both robustness towers (`WeakPromise*`,
  `WeakRobust*`, `WeakRvwmo*`, Route A/B, the pin checker, taint/witness
  machinery) — Ztso is interleaving-representable (no LB), so none of it is
  needed;
- the abandoned instruction-atomic lift tower (`WeakSailLTS*`, `WeakShape*`,
  `WeakRetag`, the premises ledger) — superseded on the branch itself by the
  event language.

## 1. Leg T — the `tso` branch (experiments; nothing lands on main from here)

**T1 — the Ztso machine: `iris/TsoMem.v` (BUILT, compiles clean).**
RULING (owner): the semantics is written fresh and PRECISELY TSO — not a
port of the branch's `WeakMem.v`, whose per-hart state (per-byte coherence
map, five scalar views, forward bank, dependency views) is RVWMO
apparatus. What the minimal machine keeps from the branch is only the
memory-as-a-message-log shape. The whole machine:

- global: era image + `glog : list wmsg`, each message author-tagged
  (timestamp 0 = image, `S i` = slot `i`; log order IS the total store
  order);
- per hart: **one monotone log index** `tv` — the entire per-hart state;
- visibility: `t ≤ tv` or own message (own-always-visible IS store
  forwarding; a store must NOT advance the author's view or SB dies);
- load: advance `tv` nondeterministically (≤ log top), read
  LATEST-visible per byte (latest-only is what kills stale-after-fresh);
- store: append, view unchanged; W→R fence (`pw ∧ sr`): view :=
  max(tv, own last message) — drains are in log order, so passing one's
  own top message passes everything below; all other fences no-ops;
- exclusive/AMO: read at the log top, write appends and takes the view
  past the append; atomicity stays the LANGUAGE's reservation self-loops.

In-file theorems: `read_down_le`/`read_down_latest` (the latest-visible
characterization the forbidden litmus arms consume), `tso_read_own_top`
(forwarding is mandatory), `tso_read_top_flat` (**the SC collapse**: a
hart pinned to the top view is an SC hart — leg C's compatibility story
in miniature). `iris/TsoLitmus.v` (WeakLitmus.v mold, no annotations in
the instruction language) is LANDED and clean: SB and n6 exhibited
(forwarding is load-bearing in both); fenced-SB, MP-with-no-fences (the
headline), CoRR (two verdicts), LB, IRIW, and AMO-strength proven
forbidden, each with a reachability witness so no forbidden verdict is
vacuous.

Rulings still open at this layer:
- **MMIO stays strongly ordered** (recommended): device/`dev_addr` accesses
  drain/sequence as today — matches hardware I/O regions, keeps the whole
  device-proof tier and `device-conformance` untouched. The Sail
  FENCE-I/O-bits boundary clause from the branch carries over.
- **Crash drops unpublished writes**: the era/generation split already wipes
  RAM at a power edge, so the honest "buffer lost at crash" semantics is
  free; the disk's durability story is device-side (M5 disk-as-agent
  pattern) and unaffected. Verify against `design/crash.md`'s
  crash-spanning disk invariant.
**WHAT `TsoMem` IS, in one sentence, because the shape confuses people who
picture TSO as memory + FIFO buffers:** it is TSO in the MEMORY-ORDER
style (the SPARC/TSO formulation) — one total order on writes, and **a
hart's "view" is where that hart's reads sit in that order**, NOT what has
physically drained. That is why the per-hart state is a position rather
than a buffer. The two arms of `visibleb` are the two clauses of the
memory-order read rule: `t ≤ tv` is "already in memory as far as my reads
are concerned", and the own-author arm IS store-buffer forwarding.

**THE BUFFER-MACHINE EQUIVALENCE IS NOT OWED** (owner ruling): the
standard machine (global memory + per-core FIFO buffers) characterizes the
same model, and the port does not need the theorem. Recorded here so
nobody re-opens it — and, more importantly, so nobody assumes it would be
a BISIMULATION. **It cannot be:** the two machines fix the total store
order at different moments — the view machine when a store ISSUES, the
buffer machine when it DRAINS. Witness:

    hart A:  x := 1
    hart B:  x := 2 ; y := 1

The buffer machine buffers all three, drains B's two FIRST and A's last,
so memory order is `x=2, y=1, x=1` and a third hart legitimately reads
`y=1` AND `x=1`. The view machine reaches that outcome only under the
schedule that ISSUES B's stores before A's, because its log IS the memory
order and so must be built in drain order. Same outcome, different
interleaving — so any honest equivalence is per-program over OUTCOMES,
with each machine's schedule existentially quantified, never step-for-step.

**T2 — freeze Σ, the cutover contract.** The SC-degenerate side of Σ is
begun: `iris/TsoCtx.v` (`CtxId`, ambient `CurCtx` with deliberately NO
default instance, `own_context`, `ctx_pointsto` + its law surface
mirroring `mem_pointsto`'s, `ctx_dom`/`CtxMorph` + structural instances
with the composition acid test) — its header carries the three
owner-ratified rulings. The TSO twin (same statement list over
`TsoMem.v`, the context ledger in place of the token; the branch's
`WeakCtxPt.v` is the design source, with per-byte floors collapsing to
MaxNat ledgers over single-nat views) is what validates the freeze. Σ as
adopted by main is the statement list of `TsoCtx.v`:
- `CtxId` (explicit record) + `Class CurCtx` (ambient, invariant across
  migration — the one property `CpuId` lacks);
- `mem_pointsto` with a context index, notation-compatible with today's
  `↦ₘ{dq}`/`↦ₘ□`/`↦₈`/`↦₄`/`↦ₛ` tower, ktier axis preserved;
- the leaf AU rules of `WpSconfMem.v` shape, statement-identical above the
  seam;
- lock specs: exported handle unchanged (`locked γ i` stays), payload
  obligation `CtxMorph`, ξ_L internal;
- `wrunning ξ` and the park/resume laws; `wp_next`'s continuation re-anchors
  `CpuId` but ξ is unchanged — framing across a yield is "not a lemma at
  all";
- fence/publication leaves with their TSO-shaped postconditions.

Σ must NOT contain context-irrelevance (`wptsto ξ a v ⊣⊢ wptsto ξ' a v`) —
that is SC-only and would die at cutover. The one-time SC compat shim (§3)
is quarantined and burned.

**T2b — the TSO twin (`iris/TsoCtxTwin.v`), the leg-C gate.** A
self-contained Iris ghost theory over `TsoMem.v` (gmap-image variant), no
WP/language — ghost updates only — that satisfies `TsoCtx.v`'s exported
statement list against the real TSO rules. The design:

- interp `tso_interp img log tvs run parked` owns: the per-byte latest
  auth (`a ↪ (t, v)` — timestamp and value of a's latest write), the
  per-hart view auth, the per-context LEDGER auth (`a ↪[ctx_name ξ] t`
  frags ride inside `ctx_pointsto`, NOT persistent — re-minted at
  transport, which is why migration needs no per-fact bookkeeping above
  the seam), the running pairing (`h ↪ ξ`, whose frag is `own_context`),
  and the parked map (`ξ ↪ T`);
- the SEES invariant, pure, in the interp: for every running pair
  (h, ξ), every ledger entry (a, t) of ξ has `t ≤ tvs h` OR the log's
  message at `t` is authored by h (forwarding covers a thread's own
  unpassed stores); for every parked ξ at T: every entry ≤ T;
- the four gate lemmas: LOAD (interp ∗ own_context ∗ ctx_pointsto ⊢ the
  machine's `load_ok` at this hart returns the fact's value, for EVERY
  admissible view advance — latest-cell agreement kills later writes,
  SEES gives visibility); STORE (append re-registers the fact at the new
  top, own-author arm); TRANSPORT (`ctx_dom ξ ξ' := ∃ T, ⌜ξ's entries ≤
  T⌝-evidence ∗ ξ''s hart's view ≥ T` — minted from release/acquire,
  consumed by re-registering the fact's ledger entry under the prefix
  arm); PARK/RESUME (park publishes at T := log top; resume on any hart
  whose view passed T re-founds SEES in pure-prefix form — no relation
  between the two harts' states needed, the branch's key finding, now at
  a single nat).

THE GATE PASSED (`TsoCtxTwin.v` landed, clean, no axioms): all four
lemmas proven, load even stronger than sketched (no upper bound needed
on the view advance), `twin_init` shows the interp inhabited, and
park/resume confirmed to need NO relation between the two harts'
states. The M sweeps are safe to spend on. What the gate ADDED to the
design (the real Σ instantiation must plan for these):

- three invariant clauses beyond the sketch are load-bearing:
  RUN-INJECTIVITY (a context runs on at most one hart — the real system
  gets it from `own_context`'s exclusivity inside one `sie_cap_gpr` per
  hart), PARKED-NOT-RUNNING, and PER-BYTE LEDGER UNIQUENESS;
- `twin_transport` must run with the state interp open (re-registration
  needs the ledger auth) — fine, the real lock lemmas do;
- under TSO, `ctx_dom`'s SOURCE-side evidence is subsumed by the ledger
  bound plus acquirer-at-top — domination is strictly simpler than the
  weak-memory branch's two-sided form;
- fractional dq is the one deferred refinement: the twin's facts are
  fraction-1 (cross-context agree became exclusivity), and splitting
  registrations across contexts needs per-(byte, holder) uniqueness.

**T3 — close the branch's flagged open items, on the spike, where TSO makes
them cheap.** These are the design risks; resolve before any main sweep
depends on their shape:
- **The real `wp_next` migration** (the branch's "Stage 2", never done).
  Under Ztso every store is a release, so "publish-before-park" is expected
  to be a *theorem* about the scheduler's `p->lock` handoff rather than an
  interim rule; if so, the heavier `WDirty ξ` redesign dies here. Validate
  on the real swtch/scheduler/interrupt cone: `wrunning ξ` threaded into
  the migration, the reschedule path obliged to return it.
- **`CtxFlip`** (general owned payloads across contexts; only clean ptsto
  morphs today).
- **The boundary seam** (sc-parity §6.3, acquire hands out the right floor)
  — declare it closed or fix it.
- The per-footprint vs all-address release floor weakening — accept or
  repair.

**T4 — the standing mirror.** Script: rebase main's swept surface onto the
T-branch kit and recompile the ↦ₘ-using surface (162 files today). Run it
per main sweep (§3). This is the mechanical meaning of "the specs are true
under TSO".

## 2. The SC-degenerate instance (lands on main first)

One new file pair on main, semantics untouched:
- Σ's statements with instances where the view lattice is trivial:
  `wptsto ξ a v` unfolds (sealed) to today's `mem_pointsto a v`;
  `ctx_view_lb`/`ctx_auth` over the unit view; `wrunning ξ` an exclusive
  per-thread token; park/resume causality premises trivially dischargeable.
  All Σ laws proven. `Typeclasses Opaque` everywhere; no unfolding lemma
  exported.
- The compat shim: `↦ₘ`(old) ⊣⊢ `wptsto cur_ctx`(new), in ONE file, used
  only at sweep boundaries, deleted at cutover.

## 2b. The mixed tree — one function converted IN PLACE among unconverted ones

RULING (owner): conversions are IN-PLACE edits of the existing spec and
proof files — never wrapper files, never a second copy of a spec. The
worked instance is `memset`, the tree's first converted function:

- **The spec** (`SpecMemset.v`, edited in place): exactly three deltas —
  the ambient `` `{XI : CurCtx}`` binder; `own_context cur_ctx` threaded
  beside `sie_cap_gpr` (a stopgap conjunct — M2 folds it into the bundle
  and it disappears from spec text again); the byte window at `↦c[ktb]`
  — the `↦c` notation family (`TsoCtx.v`) mirrors `↦ₘ`'s spellings with
  the context ambient, so converted spec text reads as before; at the
  M1 notation flip `↦c` becomes `↦ₘ` and is retired. Registers,
  premises, ktier axis, `wp_next` — character-identical. At the
  `wp_next`, `CID` rebinds and `cur_ctx` does not: migration survival
  is visible in the statement.
- **The proof** (`WpMemsetArray.v`, edited in place): one `"Hctx"` per
  arm's intro pattern, `"Hctx"` at the two continuation hand-backs, and
  two shim conversions at the INTERIOR seam — the whole-function proof
  composes per-instruction parts (`SpecMemsetParts`) that are not yet
  converted, so the file is itself mixed: converted export, unconverted
  internals, shim at the boundary between them.
- **Unconverted callers** (nine files, patched at ~14 call sites; the
  reference diff is `ProofBalloc.v`): six lines per site — mint a
  context (`iMod own_context_alloc`), shim the buffer in
  (`ctx_buf_of_mem`), add `(XI := ξms)` and `"Hctx"` to the existing
  `iApply`, discard the returned token in the continuation intro, shim
  the buffer back (`ctx_buf_to_mem`). Callers' own specs, and every
  Link file, are untouched — the sweep converts one function at a time,
  in any order, with the tree green throughout.
- `TsoCtxShim.v` is the ONLY file allowed to state
  `ctx_pointsto ξ ⊣⊢ mem_pointsto` (wand directions + the `[∗ list]`
  window forms). Its import list IS the live seam inventory
  (`grep -l TsoCtxShim`): each import marks a file with an unconverted
  neighbour, and each finished conversion deletes imports. At cutover
  the file is deleted; every leftover boundary and every SC-only
  context mint becomes a compile error — the remaining worklist, not a
  soundness hole.

## 2c. Leaves and text (rulings)

**LEAF TWINS, ON DEMAND — the leaf conversion is small, not monumental.**
Measured: 0 function-proof files reach below the AU tier (the whole
`swp`/`HartSMem`/`HartMLoad`/`HartMStore` layer is below Σ, reproven only
at cutover, invisible to function proofs); the leaf tier stating memory
points-to facts is ~46 lemmas in 9 files (16 `WpSconfMem`, 9 `WpLock`,
16 PT-mem trio, 5 misc) + 13 word/string-tower lemmas in `RiscvPtsto` —
~60 statements. `WpSconfAlu`/`WpSconfBtype`/`WpSconfCtl` (95 lemmas)
mention no memory fact and need nothing. The mechanism:

- a ctx TWIN beside each original in the SAME kit file (`…_au_c` next to
  `…_au`), stated in the Σ-frozen cutover form, derived from the original
  in one line via the shim at SC — one honest proof per leaf;
- twins are minted ON DEMAND when the first converted consumer needs
  that leaf (scoreboard discipline, as in the instr-subgoal sweep);
- WHICH leaf a proof calls is compiler-enforced, not policed:
  `ctx_pointsto` is `Global Opaque`, so an `↦ₘ`-stated leaf cannot unify
  against a `↦c` goal — converted and unconverted proofs cannot cross
  wires by accident;
- at cutover the twins get their direct TSO proofs (statements
  unchanged), the originals are consumer-free and die with the shim.

**TEXT AND `instr` ARE CONTEXT-FREE — better than a shared context.**
Timestamp 0 is the era-initial image and `visibleb` at t = 0 holds for
every agent at every view; kernel text is loaded in the boot image and
never written, so a text byte's latest write is timestamp 0 forever and
every hart at any view reads it. `kernel_text`, `↦ₓ□`, and every `instr`
premise stay untouched through the whole port — no index, no twins, no
sweep. Fetch reads at the hart's view like any load and latest-at-0
immutable bytes are view-independent (no-icache boundary clause as on
the weak-memory branch). Text that is WRITTEN during execution (kexec's
new kernel, user-level instruction facts) has no obligations in today's
tree; DEFERRED by owner ruling — cross that bridge when the tree grows
such facts.

## 2d. The M1+M2 sweep, as run — and what a script can and cannot do

`tools/ctx_convert.py` (mode `binders`) is the sweep tool. Measured on the
real tree:

- **1342 edits over 402 files, fully scripted**: 302 section `Context`
  lines and 1040 inline definition binders gained `` `{XI : CurCtx}``,
  plus the `TsoCtx` import. Idempotent; a dry-run mode prints the
  scoreboard.
- **Two script rules that are NOT optional**, each learned from a
  compile failure: (a) a BLACKLIST for files below `TsoCtx` in the
  import order (`RiscvPtsto`, `RiscvLang`, `Ktier`, …) — and for
  `WpNext.v`, which must stay context-TRANSPARENT because the whole
  point is that ξ is fixed across the CPU binder; (b) comment-stripping
  before the vocabulary match — 37 files matched only in prose and were
  reverted.
- **`own_context` rides in `sie_cap`, one level BELOW `sie_cap_gpr`**, so
  the 20 `rewrite /sie_cap_gpr` sites, the ~55 four-tuple destructs, and
  `sie_cap_gpr_split`/`_join`/`IntoSep`/`FromSep` all keep their shape.
  Only capability OPENERS see the new conjunct.

THE REPAIR CLASSES (the whole fallout of the sweep falls in these four):

1. **Capability destructs** — `(Hstk & Htr & Harm & #Htc & #Hwit)` gains a
   `Hctx` slot. Diagnosed by one error, always: `iIntuitionistic:
   own_context not persistent` (the old pattern's trailing name silently
   absorbed the remainder). Regex-automatable once seen.
2. **Explicitly-quantified statements** — a statement that binds
   `∀ (CID : CpuId)` by hand rather than through the section needs the
   matching `∀ XI` (`SpecPrintk.printk_gen_contract`). Script-detectable.
3. **Bundle-residue definitions** — a definition naming "everything in
   the capability except X" (`WpIntrInv.sie_cap_rest`) must carry the new
   conjunct, and its producers/consumers with it. Needs a human to
   notice; trivial to fix.
4. **Design-level seams** — where "which thread of control is this?" is a
   real question. Exactly four, all recorded below.

THE FOUR DESIGN SEAMS, and their rulings:

- **The handler contract is CONTEXT-GENERIC** (`IntrDefs.ihs_body_of`):
  `∀ XIb` in the □-prefix beside its hart genericity, with the
  postcondition at the NEW hart `c'` but the SAME `XIb`. The trap serves
  whichever thread traps, and a trap that reschedules moves the hart,
  never the context — which the contract now says out loud.
  `ihs`/`intr_res`/`trap_csrs` came out ξ-INDEPENDENT: the per-hart
  resource stays one per hart, not one per thread.
- **A parked context OWNS its thread token, existentially**
  (`SwtchCtx.valid_context_pre`): a parked context IS a thread of
  control, so its resume wand demands the bundle at ITS identity — the
  facts its closure captured are the facts it wakes holding. Existential
  like the lock's internal ξ, so no consumer's arity moves.
- **swtch EXCHANGES tokens** (`ProofSwtch`): the parker's token goes INTO
  the record it builds, the target's comes OUT of the record it resumes.
  That is what "the hart keeps running while the thread changes" means,
  and it is the one place in the kernel a token moves between records.
- **`own_context` IS THE RUNNING TOKEN, AND IT IS NEVER ALLOCATED FROM
  NOTHING** (owner ruling, from the leg-C rehearsal). `own_context ξ`
  says "this hart is RUNNING as ξ", which cannot be conjured: the SC
  instance's `own_context_alloc : ⊢ |==> ∃ ξ, own_context ξ` is a free
  ghost var and hides the obligation. Three primitives instead:
  1. **Fresh allocation yields a PARKED context**, not a running one — a
     context that has never run makes no claim about any hart, so the
     mint is pure. That is what fork needs: `ProofForkretPark` creates
     the child, and the child does NOT get `own_context` yet.
     **THE CHILD IS STAMPED AT THE PARENT'S COUNTER**, at the moment of
     creation — not zero, not arbitrary: `ctx_fork : own_context ξp ==∗
     own_context ξp ∗ ctx_parked ξc T` with `T` = ξp's current bound
     (the mint BORROWS the parent's running token to read it, and hands
     it back; no state interp). **This is what makes the deposit free.**
     The parent hands the child points-to facts registered at ξp with
     entries ≤ ξp's bound; since ξc's bound is EQUAL, `ctx_dom ξp ξc`
     holds BY CONSTRUCTION and re-registering them at ξc has nothing to
     prove. If depositing into the child's WP ever needs a side
     condition, the stamp is wrong. It also closes the exchange's
     premise: `T` is ≤ the log top at fork and therefore ever after, and
     the resuming hart's `p->lock` acquire takes its view to the top.
  2. **The EXCHANGE is the primitive**, not park-then-resume: a hart
     always runs exactly one thread, so
     `own_context C1 ∗ ctx_parked C2 T2 ∗ ⌜T2 ≤ this hart's freshness⌝
     ==∗ own_context C2 ∗ ctx_parked C1 T1`, with T1 RECORDED so C1 can
     be resumed later. The premise — the CPU is at least as fresh as the
     resumed context requires — is what `p->lock`'s acquire supplies in
     the kernel, and `SpecSwtch` currently carries nothing that would
     give it (vacuous at SC).
  3. **Boot is the only place a hart's FIRST running token appears**,
     justified by the interp being CONSTRUCTED there.

  Consequence for the swept tree, expected to be a bounded delta:
  `SwtchCtx.valid_context_pre`'s record should hold the PARKED token
  rather than `own_context`, `ProofSwtch`'s exchange consumes
  parked(target) and produces parked(parker), and `ProofForkretPark`
  mints parked.

- **Boot TAKES, adequacy MINTS — one token PER HART.** `boot_bridge`
  (and `boot_entry_bridge`/`boot_hart_primary`/`_secondary`) take
  `own_context cur_ctx` as a premise; the mints sit in
  `SystemAdequacy.xv6_boot_era`, one per hart, each hart's chain
  instantiated at its own `(XI := ξ)`. **There is no "single mint":**
  `own_context` is exclusive and eight harts need eight capabilities,
  so there are eight tokens at eight distinct `CtxId`s and no ambient
  system-wide context exists. The mint belongs at the first layer that
  HAS per-hart identity — `SystemAdequacy`, not the machine-level,
  xv6-agnostic `RiscvAdequacy`: putting it lower would force a per-hart
  `∃ ξ` row into `power_boot_res`/`boot_shared_alloc` and make
  `PowerBoot`'s interface know about threads of control, for a resource
  nothing between the two layers reads. For the same reason the token
  is a SIBLING premise of the boot-chain lemmas rather than a member of
  `boot_hart_res` (which is produced eight times under one ambient
  context). Token lifecycle, entire: **born once per hart at
  `xv6_boot_era`, exchanged at swtch, dropped at a zombie park.**

**THE STANDING PRINCIPLE, which decides every seam:** a resource
describing THIS thread carries the ambient ξ; a resource describing
ANOTHER thread — parked, or not yet born — carries that thread's ξ
INTERNALLY: existentially in a record, or ∀-quantified in a wand the
resumer will apply. Instances: `ut_trap` (this thread) ambient;
`valid_context` (a parked thread) existential; `ihs_body_of` (whichever
thread traps) ∀; `ParkCap.park_pkg` (a child) ∀, quantified beside the
hart it already quantifies for the same reason. The principle is what
keeps `park_token` and therefore `ProofSyscall.syscall_env` ξ-FREE, so
`SpecSyscall.v`'s "HART-FREE, AND THAT IS PART OF THE CONTRACT"
paragraph stands verbatim and none of its Parameters move.

**A USER EXCURSION IS NOT A CHANGE OF THREAD.** `ut_trap` is at the
ambient ξ, not an internal one, because nothing but this thread can
resume its own residue — unlike a swtch record, which the SCHEDULER (a
foreign thread) resumes, which is the only reason THAT one needs an
internal identity.

**THE SCRIPT'S FUN-POSITION EDIT IS ONLY HALF A REPAIR.** A lambda cannot
carry an implicit binder, so a `` `{XI : CurCtx} `` the sweep writes inside
a `fun` is silently DEMOTED to a positional argument (Rocq says "Ignoring
implicit binder declaration in unexpected position" — a warning, not an
error). The fix is never to delete it: the lambda has a partner
`Hypothesis`/`Parameter` that must gain the matching `∀ XI0`. Worst
instance found: `ProofKvmmake`'s `wp_memset` hypothesis, whose COMMENT
already asserted it was context-generic while the statement was not.

**THE SILENT-DROP HAZARD HAS A SECOND FORM, and it is worse than the
wildcard one:** `f (GEN := …) (CID := …)` with `XI` left to typeclass
resolution COMPILES and picks the most-recently-introduced `CurCtx` —
which, inside a `Prop`-carried contract that quantifies its OWN, is not
the one the contract means. Two such sites existed (`ProofBmap`'s balloc
and log_write producers) and are now explicit. **The tree is audited
clean:** only three files have two contexts in scope at once
(`IntrDefs`, `ProofBmap`, `SpecPrintk`) and all three now name it
explicitly (`(XI := XIb)` / `(XI := XIc)` / `(XI := XIp)`). Do NOT try to
audit this by grepping `(CID := ` without `XI :=` — there are ~974 such
sites and almost all are correct, because one ambient context resolves
unambiguously. The rule: **wherever a statement quantifies its own
context, every application inside it must NAME that context.**

**PREFER A SECTION BINDER TO AN INLINE ONE — a section variable is
SELF-CLEANING, an inline binder is not.** Rocq generalizes a section
variable only where it is USED, so an over-inclusive section sweep costs
nothing. An inline `` `{XI : CurCtx} `` is always in the signature, so on
a statement that mentions nothing context-dependent it becomes a PHANTOM
argument: unifiable from nothing, and the consumer that lacks an ambient
context fails at `Qed` with an unresolved evar — far from the cause.
Confirmed instance: `UserTrap.swp_handle_interrupt_u` (an `swp`-tier
lemma, entirely below the bundle) propagated a phantom into
`WpUmodeStep`'s deliberately hart-free engine section. The workaround
(give the consumer an ambient context) is in place; the ROOT fix is to
drop the phantom binder where a statement does not use it, and that is a
CLEANUP ITEM, not a blocker. Do not try to find these by grepping for
absent vocabulary — a lemma whose statement merely NAMES a
context-dependent body does not spell it, so the scan is mostly false
positives; the compiler's unresolved-evar-at-`Qed` is the real detector.

**RULES OF THUMB FOR THE REWRITES THEMSELVES**, learned the hard way:
anchor a rewrite to a SYNTACTIC POSITION (declaration line, binder slot),
never to a token that can appear anywhere — a raw `(CID0 : CPU)` rule
fired inside `(CID1 : CPU) = (CID0 : CPU)` in 27 places across 12 files,
and the build hid all but one behind the first. Prefer the version that
UNDER-fires: a miss is a compile error next round, a corruption rewrites
a theorem. And every pass must be idempotent with a dry-run FIXPOINT
check, because each of this sweep's tooling bugs was a rule whose own
edit invalidated its precondition (the last `Require` line; "this file
has a section binder"; file-level vs section-level scope).

**TWO TRAPS THE SWEEP FOUND, both worth a check of their own:**

- **A TRAILING WILDCARD IN A CAPABILITY DESTRUCT IS A SILENT LEAK.**
  `iDestruct "Hcap" as "(Hstk & Hstr & Harm & _)"` swallows the new
  conjunct, and the file COMPILES — the resume direction fails loudly
  (`iApply` mismatch) but the park direction just drops the thread's
  identity into the affine void. Grep every capability opener for a
  trailing `_`; the compiler will not find these. ONE KNOWN BENIGN HIT to
  waive rather than "fix": `ProofKerneltrapParts`'s pure-extraction open
  (`iDestruct "Hcgat" as "(_ & … & _)"` inside an `iAssert (⌜…⌝)%I as %H`)
  restores the context afterwards, so its wildcard drops nothing.
- **BINDER POSITION IS LOAD-BEARING IN A MODULE TYPE.** Section
  variables are PREPENDED, so a `Parameter` declaring
  `∀ {riscvGS} {GEN} {XI}` does not match an implementation that
  inherits `XI` from its section (`∀ {XI} {riscvGS} {GEN}`) — subtyping
  breaks with no clue at the definition site. A module-type Parameter
  needs `` `{XI : CurCtx} `` hand-placed in the slot the implementation
  uses; the two must move together.

**`CtxId` NEEDS `Inhabited`, and it is load-bearing.** A `CtxId`
existentially bound inside a ▷-guarded record (the parked context) can
have its later pushed inward only by `bi.later_exist`, which holds only
over an inhabited domain — without the instance a resumer cannot open the
record it is about to run. General rule: any type existentially
quantified inside a later-guarded resource needs `Inhabited`.

## 3. Leg M — the main sweeps (each independently landable, main green after each)

Precedents that say this scale of sweep is routine for this tree:
`completed/explicit-cpuid.md` + its porting guide (an interface axis added
to every WP statement), `projects/instr-subgoal-sweep.md` (214-file
scoreboard), `xv6-bump-playbook.md`. Use the same scoreboard discipline;
spawn subagents for the mechanical files per the orchestration note.

- **M1 — ambient context.** `Context {XI : CurCtx}` into every WP-statement
  file; rebind the `↦ₘ` notation tower to the context-indexed sealed
  definition. Statement-identical above the seam; the explicit-cpuid guide
  is the recipe. Guard the branch's measured `CurCtx` hazard (two instances
  in scope resolve silently to the last).
- **M2 — `wrunning` through the spec spine.** Fold `wrunning cur_ctx` into
  `cpu_own` (recommended: `cpu_own` already appears in every whole-function
  spec and already transports across `wp_next` via `cpu_own_transport`, and
  with M1's ambient ξ its visible arity does not change). Restate
  `wp_next`, swtch (`valid_context`/`SpecSwtch`), the scheduler protocol,
  and the interrupt/reschedule path to carry and RETURN it — proven at SC
  where it is trivial, so the plumbing exists before it matters.
- **M3 — lock payload morphability.** Restate `SpecAcquire`/`SpecRelease`/
  `WpLock` client obligations with the `CtxMorph` premise; derive instances
  structurally (ptsto, pure, persistent — note plain ghost state is
  objective, so ghost-heavy FS payloads morph for free; `∗`/`∃`/big-ops).
  `completed/lock-set.md`'s audit bounds the client list. **Any payload
  that fails `CtxMorph` here is a real TSO bug found early** — that is the
  incremental validation paying off.
- **M4 — the deliberately racy sites.** The only places whose specs
  genuinely change meaning: the lock word itself, `started`, the virtio
  ring/DMA handoff (`design/virtio-driver.md`'s protocol), and any
  flag read outside a lock. Convert to the subjective interface (the
  branch: these "MUST stay subjective — stale reads there are the theorem,
  not a gap"). Give the fence leaves (`WpSconfCtl.v`) and release-store
  leaves their TSO-shaped postconditions, trivially provable at SC, so call
  sites consume the final shape.
- **M5 — audits.** Re-run `main-cycle-port.md` §4's two audit classes
  (invariants opened across an instruction; interrupt-delivery timing) for
  the store-buffer delta; audit `state_interp`-adjacent pure clauses
  (`resv_ok`, DMA's `all_resv` guard) for gmem-vs-log meaning; check
  `design/fs-state.md`'s predicates are built only from Σ-morphable parts.

After every M-sweep: run T4's mirror recompile on the `tso` branch. A sweep
is DONE only when the mirror is green too.

## 4. Leg C — cutover

Only after M1–M5 are everywhere and T4 is green: swap the below-Σ kit for
the T-branch one. The kit (the bounded reproof set, ~20–40 files, from the
seam survey): `RiscvLang.v` (mnode_step memory/Barrier arms, gstate),
`RiscvExec.v` (`wp_hart_step`), `RiscvPtsto.v` (`mem_pointsto`,
`mstate_interp`/`era_interp`/`power_interp`, `resv_*`), `HartSwp.v`,
`HartSMem.v`/`HartMLoad.v`/`HartMStore.v` (the `Mobl/Wobl` obligation
shapes), `WpSconfMem.v`/`WpSconfCtl.v` leaves, `WpLock.v`/`SpecAcquire.v`/
`SpecRelease.v` internals, `WpIntrInv.v`'s engine, `RiscvAdequacy.v`/
`SystemAdequacy.v` (WeakEvAdequacy is the pattern; adequacy's φ export and
the 5-axiom budget must survive `Print Assumptions`). Burn the compat shim.
The 1000+ files above Σ recompile. Flip main.

## 5. Optional aftermath

- A Ztso axiomatic characterization (machine ≡ Ztso ppo) in the branch's
  `WeakAxiomatic` vocabulary — expected far smaller than sRVWMO's T1/T2
  since Ztso is interleaving-representable; the litmus suite stays as the
  definition's regression harness.
- The RVWMO door stays open: same surface Σ, weaker instance, reader-side
  obligations added — the `weak-memory` branch's tier-2 work continues to
  apply.

## 6. Decisions

RATIFIED (owner):
- The semantics is precisely-TSO, written fresh (§1 T1) — minimal per-hart
  view state (one log index), message-log model inherited, no RVWMO
  apparatus. Extend toward RVWMO later, not now.
- The context rides in `sie_cap_gpr`: the bundle exposes the context name
  and internally owns `own_context` (the tie to the current CPU's view
  state), so no proof threads a new SL resource — the bundle already moves
  everywhere the context is needed. `CurCtx` is ambient wherever `CpuId`
  is. (Encoded in `TsoCtx.v`'s header rulings; the M2 sweep edits
  `IntrDefs.v` in place.)
- Staffing: Fable defines the TSO semantics and the context machinery;
  once the leg-M porting recipe is well-defined, Opus/Sonnet agents crank
  the mechanical transformations.
- Leg C is PROTOTYPED EARLY: after the leg-M machinery exists, merge it
  onto leg T and instantiate the context machinery with TSO for real, so
  a wrong-shaped context definition is caught before the M sweeps spend
  effort. (This is the T2 twin + T4 mirror, promoted to a gate.)

OPEN:
1. Lock payload signature: `R : iProp` + `CtxMorph` premise (recommended —
   no arity change at ~every `is_lock` mention) vs the branch's
   `R : CtxId → iProp` with internal ξ_L.
2. MMIO ordering ruling (§1 T1; recommended: strongly ordered).
3. Sequencing against in-flight projects: the M-sweeps touch the same spec
   spine as durable-disk 2c and the sp-migration/instr sweeps — freeze Σ
   first (T2), start M1 only after 2c-body lands or with 2c's predicates
   audited as Σ-morphable (M5 item), and fold the M1 axis into the standing
   sweep scoreboards rather than running competing sweeps.
