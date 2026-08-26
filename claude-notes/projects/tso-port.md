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

### 0.9′ THE CUTOVER REHEARSAL: THE SEAL WENT HERMETIC (2026-08-26)

The experiment the owner asked for -- "cut over to the real thing, see
what breaks, oscillate back if needed" -- run in its cheapest faithful
form: `TsoCtx`'s five surface facts are now **Qed-opaque** (the
sig-projection seal; each has a named `_unseal` equation, and
`TsoCtxShim` unseals by name).  This makes `ctx_pointsto` genuinely
non-convertible to `mem_pointsto` everywhere -- the exact
statement-level failure set the `TsoCtxTwin2` swap produces -- without
the tsoG camera threading and machine-interp swap the full swap needs.

**The result validates the conversion's shape.**  First hermetic build:
4 red files out of ~430.  Full inventory after the error-driven rounds:
~15 files, every one in the tier the plan already expected to be
kit/seam territory:
- the gen_heap leaves (WpSconfMem, WpSmodePtLeaves, WpSmodePtMem,
  SmodeCorePt): acc/pin/chunk/win-write now cross through named shim
  bridges; the ↦₈ leaf wrappers get ONE equivalence
  (`WpSconfMem.wordw8_ctx`) with a hand-written continuation adapter --
  `setoid_rewrite` fails with undefined evars under `wp_next`'s binder,
  so the adapter re-intros the continuation and rewrites the fact at
  the top level on both sides;
- the phys/ident tier (DiskInv, ProcPtOwn, KstackOwn, ProcInv,
  BootBridge);
- the unflipped ↦₂/↦₄ towers (word2/4 intro/bytes/split/join sites);
- `mem_ktier_mono` (tier weakening rides the raw law between two
  shims);
- the boot mints (BootCarveMain).
Notably the rehearsal DELETED several flip-era conversions that had
been wrong-direction no-ops the permeable seal silently tolerated --
the hermetic seal is also a correctness audit of the shim usage itself.

**It also strengthened the M2 finding**: under the hermetic seal the
park lemma fails at `first_done`/`W`, not just at the caps -- every
fact crossing the ∀-bound resume context is real M2 transport.  The
`Abort` moved to the top of that proof.

**Where this leaves the oscillation**: going back to SC-permeable is
one edit (plain definitions in `TsoCtx` again); staying hermetic is
STRICTLY better discipline (silent seams cannot re-grow, failures are
fast instead of 35-minute unification crawls) and is the recommended
resting state.  The remaining distance to the REAL swap is now sharply
scoped: (1) the tsoG ghost class threading (TsoCtxTwin2 carries its own
Σ assumptions), (2) replacing the `_def` bodies with the twin's and
re-proving the law surface (each law already has a named twin image),
(3) the kit re-proofs against TsoMem where today's shim bridges sit --
the `Require TsoCtxShim` grep is now an HONEST inventory again, plus
(4) the two M2 protocol items (park/resume, trap-handler caps).

Residual red at the rehearsal commit (8f675587): BootCarveMain's
`bpay_raw`/`buf_raw` whole-body conversion wants a named bridge
(address equations + shim on the byte run); the adapted leaf wrappers
and the `SpecSyscall.syscall_env_park` Parameter binder pending one
verification round.

### 0.10′ HANDOFF (2026-08-26, end of session) — EXACT STATE AND WORKLIST

**Branch state.** `tso`, HEAD = d3db2b27.  The relevant commits, newest
first: d3db2b27 (rehearsal wide layer), 8f675587 (THE HERMETIC SEAL),
b7bb2990 (the replay runbook, `tso-flip-replay.md`), fba0ae63 + 3dfbcfcc
(the M1 notation flip of ↦ₘ/↦₈ + the kmem minimal-diff redo).  Build on
the GCP VM only, from the REPO ROOT:
`./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- bash -c
'cd iris && make -f CoqMakefile -j180 -k'`; watch
`--no-sync ps -o pid,etime,rss -C rocqworker --sort=-etime` and autopsy
any 8-min-plus worker with single-file `coqc -time`.

**What the tree IS right now.**
1. `↦ₘ` and `↦₈` (all four spellings each) denote
   `ctx_pointsto ξ a q v` / its 8-byte tower at the ambient `cur_ctx`,
   in every file that imports TsoCtx (import order decides; `↦ₓ`/`↦ᵣ`
   never flip; `↦₂`/`↦₄`/`↦ₛ`/`↦ₚ` still plain).  At SC the definition
   ignores ξ.
2. THE SEAL IS HERMETIC (8f675587): `ctx_pointsto`, `own_context`,
   `ctx_parked`, `hart_view_lb`, `ctx_dom` are Qed-opaque via the
   sig-projection idiom; each has an `X_unseal : X … = X_def …`
   equation.  Coq's unification can no longer δ-cross ctx↔mem as a
   fallback (it could under plain `Global Opaque`, which is how the
   tree had accumulated ungreppable implicit uses of the equality).
   ONLY TsoCtx's own law proofs and TsoCtxShim use the unseal
   equations.  To revert to the permeable SC seal: make the five plain
   Definitions again (one block in TsoCtx.v, marked "CUTOVER
   REHEARSAL") and restore the shim's `Local Transparent` proofs.
3. `<{ P }>` is the combinator `const_pay P` (any `CurCtx`-typed λ
   binder — even anonymous — is a TC candidate inside P, resolved
   site-dependently; measured).  Converted lock payloads are spelled
   `(λ ξ : CtxId, pay (XI := ξ) …)` and bring a CtxMorph (kmem is the
   reference, KallocInv.v).
4. Design rulings in force (0.8′ has the WHY): kernel_data is
   ∀-context; lock_name/sl_name raw; lk_cpu_res ∃-context behind
   `WpLock.lk_cpu_cell_acc`; cpu_ctx_free ∃-context with
   `SwtchCtx.ctx_cells_reindex`; StackOwn flipped (stack frames are
   thread data; `stack_own_reindex` marks the swtch crossing);
   `WpSconfMem.wordw_pointsto` deliberately RAW with named shim
   crossings; the ↦₈ leaf wrappers bridge via `WpSconfMem.wordw8_ctx`
   with hand-written continuation adapters (setoid_rewrite leaves
   undefined evars under wp_next's binder — adapters re-intro the
   continuation and rewrite the fact top-level on both sides).

**RED, exactly (46 files, from the last full round; log
`gcp-sealH.log` in the session scratchpad, but just re-run make):**

```
BootCarveMain.v:1028
DinodeSlot.v:523
ProofAllocproc.v:1866
ProofArgfd.v:681
ProofArgraw.v:253
ProofBinit.v:637
ProofBread.v:1833
ProofBrelse.v:202
ProofDirlink.v:653
ProofFilestatParts.v:333
ProofFilewriteParts.v:1258
ProofKexecTail.v:409
ProofKexit.v:1163
ProofKfork.v:82
ProofKforkB5.v:408
ProofKvmmake.v:1161
ProofKwait.v:1318
ProofMain.v:962
ProofMemcpy.v:122
ProofMemmove.v:1014
ProofPipealloc.v:949
ProofPipewrite.v:574
ProofPrintk.v:2189
ProofReparent.v:801
ProofSysClose.v:526
ProofSysExec.v:1768
ProofSysExit.v:167
ProofSysKill.v:99
ProofSysLinkParts.v:636
ProofSysMkdir.v:303
ProofSysMknod.v:1049
ProofSysOpenParts.v:669
ProofSysPause.v:1896
ProofSysPipe.v:1146
ProofSysRead.v:427
ProofSysSbrk.v:609
ProofSysUnlinkParts.v:909
ProofSysWrite.v:450
ProofSyscall.v:2064
ProofUvmcreate.v:559
ProofVirtioDiskInit.v:720
ProofVirtioDiskRwD.v:1053
ProofWalk.v:696
UtResFits.v:56
WpSconfLock.v:435
WpSmodePtMem.v:2006
```

All of these are the THREE mechanical classes — no new class has
appeared for many rounds:
- (a) a `word_pointsto_*` / `mem_pointsto_*` / `word{2,4}_pointsto_*`
  law applied to a now-ctx fact → use the `ctx_word_pointsto_*` /
  `ctx_pointsto_*` twin (arity gains a leading ξ: one extra `_`), or
  where the target really is the unflipped ↦₂/↦₄ tower or gen_heap,
  insert the named shim conversion
  (`TsoCtxShim.ctx_pointsto_of/to_mem`, `ctx_word_of/to_mem`,
  `ctx_buf_of/to_mem`, `ctx_eslot_of/to_mem`);
- (b) a flip-era shim conversion that the permeable seal tolerated in
  the WRONG DIRECTION (it was a no-op then) → delete it or reverse it;
  the error names it precisely;
- (c) a decl whose `?XI : CurCtx` cannot resolve → binder
  (`tools/ctx_convert.py ambient|inline`, or a backward-walk inline
  `\`{XI : CurCtx}` after the decl name; QUALIFIED
  `\`{XI : TsoCtx.CurCtx}` in boot files that must not import TsoCtx).
Two known specifics: `UtResFits.v:56` and `DinodeSlot.v:523` are class
(c); `BootCarveMain.v:1028` needs a NAMED bridge
`bpay_raw (pa_of_z (buf_base + buf_stride*k)) ⊢ buf_raw k` (the two
bodies are shape-identical but the whole-body conversion that used to
close it can no longer see through the seal — address equations plus
`ctx_buf` shims on the 1024-byte run).  Expect ~10 more error-driven
rounds at ~3-6 files each; the loop and fix recipes are
`tso-flip-replay.md` verbatim.

**THE TWO DESIGN PROBLEMS (not mechanical; owner-decided direction):**
1. *sleep/swtch parking.*  A parking proc stores, under `p->lock` and
   a ▷, a continuation wand for its resumer.  The wand's premises
   include the persistent handle bundle — `is_lock` for
   kmem/virtio_disk/per-proc locks, `procs_inv`, bcache/log invariant
   handles.  `is_lock γ lk R = lock_name ∗ inv lockN (lock_inv γ lk R)`
   and R now contains ctx-indexed points-tos, so the HANDLE PROPOSITION
   depends on ξ.  The record fixes ξ = the parker's; the continuation
   ∀-quantifies the resumer's ξ'.  `is_lock γ lk R(ξ)` vs
   `is_lock γ lk R(ξ')` are invariant assertions with different bodies:
   NOT interderivable, and MEASURED not convertible with every seal
   removed (`proc_ctx (XI := ξ) ⊣⊢ (XI := ξ')` fails `reflexivity`
   fast under full transparency).  FIX DIRECTION (sketched in
   UsertrapRes.v at the aborted lemma): the bundle is persistent and
   every thread already threads it through its syscall spec, so the
   RESUMER supplies it — the same channel the statement already uses
   for `timer_cap`/`first_done`/the fs resource `W`.  Cascade:
   `UsertrapRes.ut_res_bare_park` (proof currently ends in `Abort`,
   deliberately, so the build fails fast there — the old body is kept
   in a comment), `ut_park_intro_body`, `ParkCap.park_chan`/`park_cap`/
   `park_token` (a guarded fixpoint), `UtResFits`, `ProofForkretPark`,
   `ProofUserretClosed`, and the resume sites in the scheduler chain.
   One open sub-question: `park_env N` is keyed by `un_* N` fields of
   which only `un_s N = γs` is pinned at the channel — either pin the
   rest as pure ties, or split the bundle into the global part
   (resumer-supplied) and the N-specific pure facts (record-carried).
2. *kernelvec/kerneltrap.*  Same shape: the interrupt handler's spec is
   installed once (inside intr_res) with its `devintr_caps`
   (dev_inv + console/disk `is_lock` handles) captured at the
   installing thread's ξ; the handler body runs at the trapping
   thread's ξ'.  Site: `ProofKernelvec.v:1681` (an iApply already pins
   `(GEN:=GEN) (CID:=CID) (XI:=XIc)` — the entry context bound at
   line 1429 — the remaining mismatch is the caps premise).  Fix
   direction: caps premise moves inside `intr_handler_spec`'s ∀,
   supplied by the trapping thread.
   **LANDED 2026-08-26 — SEE §0.11′, which governs.**  The direction
   held; the supply channel had to be designed (the premise cannot be
   a new hypothesis on the trap engine — 425 files state
   `sie_cap_gpr`), and `intr_res` is context-indexed as a result.

**What the REAL cutover still needs after all the above is green:**
(i) add the real construction's ghost state — one mono_nat per context
plus a ghost_map for dirty (t,addr) pairs — to the Σ assumptions
(TsoCtxTwin2.v carries its own typeclass; threading it is a Context
sweep); (ii) replace the sealed `_def` bodies with TsoCtxTwin2's
definitions and re-prove TsoCtx's exported law surface (each law names
its already-proven twin lemma beside it); (iii) re-prove the load/store
WP leaves against a store-buffer machine (TsoMem.v) instead of
gen_heap — exactly the sites now marked by shim conversions, so
`grep -l TsoCtxShim iris/*.v` is that worklist, honest again;
(iv) the two design problems above (they are prerequisites: their
fixes remove the last is_lock-handle crossings).

### 0.11′ DESIGN PROBLEM 2 IS LANDED — THE TRAP HANDLER'S CAPS ARE TRAPPER-SUPPLIED (2026-08-26)

**Status: green.** After this change the full tree is red at
`UtResFits.v:169` ONLY (design problem 1, the deliberate `Abort`).
`ProofKernelvec.v:1681` is gone.

**The statement change, old vs new.**

```
  (* IntrDefs, before *)                  (* IntrDefs, after *)
  ires_of (S : CPU -d> iProp)             ires_of (T : caps_fam -d> CPU -d> mword 64 -d> iProp)
    : CPU -d> iProp                         : CtxId -d> CPU -d> iProp
  := λ c, ∃ h b, … ∗ ▷ S c h             := λ ξ c, ∃ h b (C : caps_fam),
                                                     … ∗ □ C ξ ∗ ▷ T C c h
  ihs_body_of kt R handler                ihs_body_of kt R C handler
  := □ ∀ XIb m av p pc0 sc tv,            := □ ∀ XIb m av p pc0 sc tv,
       ihs_trap_of (XI:=XIb) kt R …            □ C XIb -∗
                                               ihs_trap_of (XI:=XIb) kt (R XIb) …
  intr_handler_spec kt handler            intr_handler_spec kt C handler
  intr_res kt   (ξ-FREE)                  intr_res kt   (arity unchanged, ξ-INDEXED:
                                            ∃ C, … ∗ □ C cur_ctx ∗ ▷ ihs kt C h)
  kernelvec_handler_spec_body:            kernelvec_handler_spec_body:
    … -∗ devintr_caps γ… -∗                 … -∗
    intr_handler_spec KT1 kernelvec         intr_handler_spec KT1
                                              (devintr_caps_fam γ…) kernelvec
```

`caps_fam := CtxId -d> iPropO Σ`, and `SpecDevintr.devintr_caps_fam
γu γv γdk γtl γs pd pav pu := λ ξ, devintr_caps (XI := ξ) …` is the
NAMED persistent family (with `devintr_caps_fam_at`, the
member-at-a-named-context bridge).  Named deliberately: the park
protocol's resumer-supplied bundle wants the same shape.

**Why the obvious readings of the fix do not work, and what does.**
- `intr_handler_spec` lives in `IntrDefs`, at leaf altitude; it CANNOT
  name `devintr_caps` (SpecDevintr sits above it, through WpLock /
  SchedCtx / DiskInv / SpecClockintr / SpecConsoleintr).  So the caps
  premise had to become an ABSTRACT family parameter.
- "the trapping thread supplies it at each trap" cannot be read as a
  new premise on the trap engine: `WpIntrInv.wp_exec_step_intr` is
  what `WpSmodeIntr.wp_instr_s_sconf` runs, and **425 files** state
  `sie_cap_gpr`.  A premise there is the whole tree.
- THE CHANNEL THAT COSTS NOTHING is `intr_res` itself.  It is the
  trapping thread's own resource (it rides `trap_csrs` inside the
  enabled arm), so it is already stated at the holder's ambient
  context in every file.  Binding the family EXISTENTIALLY inside it
  (`∃ C, □ C cur_ctx ∗ ▷ ihs kt C h`) keeps `intr_res` / `trap_csrs` /
  `sie_arm` / `sie_cap` / `sie_cap_gpr` at their current ARITIES — so
  the 425 files are untouched — while making the resource re-supply
  the credentials at whatever context is holding it when the trap
  fires.  Only `intr_handler_spec` names the family, because only
  kernelvec's producer and the engine have to agree on WHICH
  credentials a given installed handler wants.

**Two things §0.10′ got wrong.**
1. It described the fix as local ("the caps premise moves inside
   `intr_handler_spec`'s ∀, supplied by the trapping thread").  The
   premise move is right, but the SUPPLY had to be designed: there is
   no channel from a trapping thread to the handler except
   `ihs_entry_of`/`intr_res`, both at IntrDefs altitude.
2. It implied `intr_res` could stay context-free.  It cannot: the
   supply is what makes it context-indexed.  The old header comment
   ("`ihs`/`intr_res`/`trap_csrs` therefore do NOT depend on the
   ambient XI") is now false for the last two and is corrected in
   place.  **`ihs` itself IS still context-generic** — which is why
   `ires_of` had to take ξ as an EXPLICIT argument rather than reading
   the ambient: reading the ambient captures the INSTALLER's context
   inside the fixpoint and re-creates the bug one level down (caught
   by `sie_cap_gpr_of_eq` failing to rewrite at `XIc`).

**MEASURED, and worth keeping:** of `devintr_caps`' seven conjuncts,
only `dev_inv` and `timer_cap` cross two context variables; the other
five (`console_caps`, `disk_geom`, the disk `is_lock`, `tick_keeper`,
`procs_inv`) fail an `iExact` under the hermetic seal.  All five fail
for ONE reason: `is_lock γ lk s R` is ξ-free GIVEN `R`, and the tree
spells its payloads `<{ P }>` (`const_pay`, i.e. `P` at the ambient).
So the ξ-dependence of every handle in the tree is an artifact of the
constant embedding, not of the semantics — and the alternative fix
(λ-convert those payloads, kmem recipe, so the handles become closed
terms) is blocked only by `CtxMorph proc_lock_res`, i.e. by exactly
the ▷/fixpoint-capable transport design problem 1 needs.  **The two
design problems have the same root; this one was routed around it,
design problem 1 still faces it.**

**What the change did NOT disturb, which was the risk:** `trap_csrs`
rides the swtch payload (`SchedCtx.p_sched`, both directions), so
making it context-indexed could have broken the park/resume chain.  It
did not — the whole scheduler cone (`SchedCtx`, `ProofSched`,
`ProofScheduler`, `ProofSwtch`, `ProofYield`, `ProofSleep`) compiled
UNCHANGED, because each proof is internally at one ambient context.
The only mechanical fallout was: `∃`-binder + one `_` at the six
`rewrite /intr_res` destructuring sites (`WpSconfSret`, `WpSconfCsr`
×3, `ProofPrepareReturn`, `ProofKernelvec` ×2, `WpIntrInv`), a caps
slot on `intr_res_intro`'s five callers, a `C` parameter on
`WpIntrInv.intr_psi` and on `UsertrapRes.ut_trap_csrs_fold` /
`ut_csrs_raw_fold` / `ProofUsertrap.ud_hold`.  12 files, 4 build
rounds.

**Two gotchas, both worth the hour they cost:**
- `solve_contractive` no longer discharges `ires_of_contractive`: the
  recursive occurrence is applied THREE deep (`T C c h`), and the
  tactic's `f_equiv` will not walk a three-fold discrete-fun
  application down to the hypothesis.  Naming it in the fallback chain
  (`solve_proper_core ltac:(fun _ => first [ (f_contractive; simpl) |
  apply HT | f_equiv ])`) is the whole fix.
- `(XI := …)` must be SPELLED at every site that touches a fact at the
  trap context — `ProofKernelvec`'s two `_of_eq` bridges need
  `(XI := XIc)`, and the caps family must be PINNED at
  `intr_res_intro` in `ProofMain`/`ProofMainSecondary` (leaving `_`
  makes the goal `?C cur_ctx` against a seven-conjunct bundle:
  higher-order, fails).  §0.8′ rule 3's hazard, exactly.

### 0.12′ DESIGN PROBLEM 1 — THE PARK PROTOCOL, SPLIT THREE WAYS (2026-08-26)

Implements `tso-park-protocol-memo.md`'s option (b).  The two lemmas the
memo names as the whole problem — `UsertrapRes.ut_res_bare_park` and
`UtResFits.usertrap_res_bare_park` — are **PROVED**.

**THE RULE THE SPLIT IS BUILT ON, and it is worth stating once because it
governs every future record in this port:** a parked record is read at the
context of whichever thread RESUMES it.  Since the M1 flip an
`is_lock`/`inv` handle over a `<{ P }>` payload is a *different
proposition* at a different ξ, and invariant bodies are not updatable, so
no transport exists and none can be written.  Therefore:

| what | where it rides | why |
|---|---|---|
| pure facts (`fclose_ties`, `un_pr = fsc_printk`, `un_dqi = DfracDiscarded`) | the record | pure |
| context-FREE resources (wait lock, ticks lock, nextpid lock, `procs_avail`, `wire_inv`, `kmap_at`) | the record | MEASURED to cross: their payloads are closed terms, so `is_lock γ lk s R` is ξ-free |
| ξ-DEPENDENT resources (`procs_inv`, `is_ftable`, `console_ready`, `console_caps`, the `initproc` share) | **the resumer**, inside the ∀, as `UsertrapRes.park_globals Xc γs γft γf` | cannot cross |
| everything the file system carries | `first_done` ⇒ `fs_ready`, at `Xc` | already per-resume |
| three ξ-INDEXED DISCARDED CELLS (`is_kstack`, `disk_geom` at the record's pages, `initproc ↦₈□`) | the record — **but only to be consumed into pure equations** | `TsoCtx.ctx_word_pointsto_agree` is stated over two FREE contexts and needs no `ctx_dom`; it is the only law in the sealed surface that relates two contexts for nothing |

`ut_caps_of_park` is now a TWO-CONTEXT lemma and is the join:
`ut_wf N → ut_park_caps N -∗ park_globals Xc (un_s N) (un_ft N) (un_f N) -∗
fs_ready (XI := Xc) -∗ ut_caps (XI := Xc) N`.  The only thing that crosses
between the parker's ξ and `Xc` inside it is `⌜pd = pd'⌝`-shaped.

**THE FOUR RULINGS (revisit welcome).**

1. **`W` STAYS AN `iProp`; the PARKER's ξ is ∀-quantified instead** (the
   memo's alternative to `W : CurCtx → iProp`, and it won).
   `ParkCap.park_cap`/`park_chan`/`park_token_F`/`park_token` now name **no
   context at all**: `park_cap` is `□ ∀ (ξp : CtxId) …` and `park_chan` is
   `□ ∀ (ξp : CtxId) (N : ut_names) (av : nat) …`.  A context-free token
   instantiates at every `Xc` for nothing, which is exactly what
   `UtResFits` needed.  Three reasons it is strictly better than the main
   line: (i) it makes TRUE again the two standing header claims the M1
   flip had falsified (`ParkCap.v`'s "ξ-FREE" note and `SpecSyscall.v:265`
   "HART-FREE, AND THAT IS PART OF THE CONTRACT"); (ii)
   `SpecForkretParkPaid.FORKRET_PARK_PAID`'s `park_token_intro` Parameter
   is written with NO `CurCtx` binder and has silently assumed this since
   before the flip — under the main line it would have needed one; (iii)
   `park_token_F_contractive` closes with `solve_contractive` unchanged, so
   the `CurCtx -d> iPropO` OFE the memo budgeted an hour for is not needed.
   `ProofForkretPark.park_token_intro` already discharged the cap at an
   ARBITRARY `(XI := MkCtxId inhabitant inhabitant)` — the ∀ is what that
   proof was morally doing, and it now says so.
2. **Console rows: NOT moved into `fs_ready`.**  The memo asked to reverse
   `ConsoleInv.v:255–262` and add `console_ready`/`console_caps fsc_uart`
   as `fs_ready` rows.  Once `park_globals` exists they are simply two more
   of its rows, which costs two conjuncts instead of two `fs_ready` rows +
   two projections + a builder edit + a reversed ruling.  **`ConsoleInv`'s
   ruling stands.**  (If a later consumer needs the console from
   `first_done` alone, revisit.)
3. **`park_own` DROPS THE `initproc` SHARE** — as ruled.  Both parkers pass
   `DfracDiscarded`, `ut_park_caps` now pins that as
   `⌜un_dqi N = DfracDiscarded⌝`, and the resumer's `park_globals` carries
   `∃ ip, initproc ↦₈□ ip`; the record's own copy is spent on the agreement
   that pins the VALUE.  `park_own N = bslots 3` — context-FREE, which
   removes the last exclusive ξ-crossing from the park.
4. **§0.4 item 6 re-worded** (below), per the memo: "immutable bytes are
   context-free" is true of **timestamp-0** (boot-image) bytes only.

**`park_globals` DOES NOT SHARE A PREDICATE WITH `devintr_caps_fam`** (the
memo's last section asked for 30 minutes on this; here is the answer).  The
sketch was "`devintr_caps_any` minus `procs_inv` minus `disk_geom`".  It
does not work, and the reason is instructive: the two bundles have
DIFFERENT SUPPLY CHANNELS.  The park's resumer is forkret, which holds
`first_done` and can therefore derive `dev_inv`, the disk lock and geometry
(∃-witnessed), `printk_env` and the kmem lock for free — so `park_globals`
is only what `fs_ready` does NOT reach.  The trap handler's supplier is the
TRAPPING THREAD, at leaf altitude, which has no `fs_ready` at all and must
carry the whole `devintr_caps` in its `intr_res`.  Their intersection is
`procs_inv` and nothing else.  One predicate cannot serve both; two small
named ones do.

**MEMO CORRECTIONS (all measured, all worth keeping).**
- **`ut_tfk` is CONTEXT-FREE.**  §1.2 names it as the first failure under
  the hermetic seal ("`kpt_inv` = `inv kptN (kpt_body root)` and
  `KptShare` imports `TsoCtx`, so the invariant body is ξ-indexed").  It is
  not: `ut_tfk` crosses two context variables by `iExact`.  It needs no
  index in any of the new statements.
- **The `ftable_res` λ-conversion is BLOCKED, not bounded.**  §3 option (b)
  calls it a "plain resource -- no ▷, no fixpoint, no WP -- so `CtxMorph`
  follows from the existing structural instances".  It does not:
  `ftable_res → fslot → file_pay → file_payload → off_hold` ends in
  `cinv (offN .@ k) γx (off_content γ k armed)`, and `off_content` unfolds
  to `off_raw`/`off_body`, both of which hold `a_fip k ↦₈` — an INVARIANT
  over a ξ-indexed body, which `CtxMorph` cannot cross for exactly the
  reason `proc_lock_res` cannot.  `file_core`'s `is_pipe` is a second
  instance of the same thing.  **So `is_ftable` is resumer-supplied
  (`park_globals`), and the 10 `<{ ftable_res }>` sites are untouched.**
  The M3 λ-payload sweep is therefore blocked on TWO payloads, not one.
- **The minimal restatement is not enough, and it fails by CRAWLING.**
  Keeping the bundle record-carried and repairing only `Rsys`/the
  derive-wand (memo §1.3) leaves `ut_caps_of_park (XI := Xc)` against a
  ξ-indexed `ut_park_caps`, which runs past ten minutes rather than failing.
  A crawl IS the signature of an unprovable crossing here — the hermetic
  seal fails FAST only when the two sides differ at the head symbol, and
  these differ deep inside a 64-element big-op of invariants.  Budget
  accordingly: never leave such a goal running.

**THE PARK'S SECOND CROSSING — STILL OPEN, AND IT IS NOT A PARK PROBLEM.**
`ProofForkretPark.forkret_park_paid` — the park's CAP, not its channel — has
a second context crossing the memo does not mention and §0.12′'s split does
not touch.  That proof MINTS the child's own thread identity
(`TsoCtx.ctx_parked_alloc`, `XIc`) and `SwtchCtx.valid_context_pre`'s resume
wand hands the resumed bundle at THAT identity, so forkret runs at `XIc` —
while every ξ-dependent premise it needs (`procs_inv`, `park_globals`,
`trap_csrs`, `proc_lock_res`, `is_kstack`, `proc_priv`) reaches the proof
from the PARKER, at the parker's ξ.  **A freshly minted context cannot hold
an `is_lock`/`inv` handle**: the payload is embedded at a ξ by `<{ P }>`,
invariant bodies are not updatable, and the twin's own transport
(`ctx_dom` / `twin_share`) is DATA-only by construction.  Measured: the
`iApply` crawls past twenty-three minutes.

**RULING (i) WAS IMPLEMENTED AND MEASURED, AND IT DOES NOT CLOSE IT.**  The
resume wand was changed to quantify the resumed context instead of naming
the parked one, in all three places that have to agree:

```coq
(* SwtchCtx.valid_context_pre, and SpecSwtch's caller-continuation premise *)
  OLD  ∀ (h : CPU)              (m : regfile) (eb' : bool), …
         sie_cap_gpr KT1 (CID := h) (XI := XIp) m av false p -∗ …
  NEW  ∀ (h : CPU) (Xr : CtxId) (m : regfile) (eb' : bool), …
         sie_cap_gpr KT1 (CID := h) (XI := Xr)  m av false p -∗ …
```

WHAT IT BOUGHT: `SwtchCtx` (including `valid_context_pre_contractive`, the
extra ∀ being structural) and `ProofSwtch` both close, and the two
parking-side call sites need one binder each
(`ProofSched.v:1390`, `ProofScheduler.v:1568`).

WHAT IT DID NOT BUY, measured on a full round: `ProofSched.v:1515` and
`ProofScheduler.v:1625` then fail on the RESUMED BUNDLE, because a parked
continuation captures its own facts at its own ξ and now receives
`sie_cap_gpr` at a ∀-bound `Xr` (the yielder's six saved frame words, its
`proc_held` / `trap_csrs` / `own_ctx`).  And the reframing that would fix
that — put EVERY ξ-dependent fact in the wand's premise list at `Xr`, so the
producer serves every `Xr` trivially and the RESUME SITE supplies them —
moves the wall exactly one tier down rather than removing it: the resume
site's deposit is `SchedCtx.p_sched`, and `p_sched` carries `trap_csrs`
(which since §0.11′ carries the trap handler's caps bundle) and
`proc_held` → `proc_ctx`, i.e. handles again.  No site anywhere holds an
`inv`-based handle at a context it did not already have it at, and the two
context-motion laws are `ctx_park : own_context ξ ==∗ ∃T, ctx_parked ξ T`
and `ctx_resume : ctx_parked ξ T ==∗ own_context ξ` — both ξ-PRESERVING, by
design (identity is the ghost name `ctx_bound_name ξ`).

**So the swtch-tier change was reverted** (`SwtchCtx`, `SpecSwtch`,
`ProofSwtch`, `ProofSched`, `ProofScheduler` are back at their committed
text) and `forkret_park_paid` is left at `Abort` with the crossing step kept
in a comment — the tree's convention for an M2 worklist entry, and it keeps
the failure fast.  **Keep the ∀-`Xr` shape in mind: it is right, and it is
free once the handles are ξ-free.  It is just not sufficient on its own.**

**THE TWO WAYS OUT, ranked.**
1. **Restate `wp_forkret` with its GLOBAL premises at an explicit context.**
   `wp_forkret_gen_body` gains `(ξg : CtxId)`; `procs_inv`, `park_globals`,
   `proc_lock_res` and `is_kstack` move to `ξg` while the thread-local rows
   (`sie_cap_gpr`, `trap_csrs`, `cpu_own`, `proc_priv`, `pc_is`) stay at the
   ambient.  `forkret_park_paid` then supplies the globals from its own ξ
   and the thread-local rows from the wand.  **This needs NO new law** — it
   is sound because `is_lock γ lk s R` is ξ-free in shape and its resource
   `proc_lock_res (XI := ξg)` is produced and consumed at the same `ξg`
   throughout.  The cost is entirely inside `ProofForkret`'s ~1900 lines
   (its acquire/release of p->lock is already consistent at one ξ; the risk
   is the boot arm, where kexec/fsinit mix the two).  EFFORT, not machinery.
2. **The M3 λ-payload sweep** (option (ii)), which makes the handles closed
   terms so a fresh context can hold them.  Measured-blocked on
   `CtxMorph proc_lock_res` (a `▷` over `valid_context`) and — this port's
   own finding — on `CtxMorph ftable_res` (a `cinv` over `off_content`, an
   `is_pipe` over `pipe_res`).

**Red list:** `ProofForkretPark.v` and its 7-file cone
(`LinkForkretParkPaid`, `LinkMain`, `LinkUserinit`, `BootChain`,
`BootShared`, `FsAdequacyImg`, `SystemAdequacy`).  Everything else is green,
including `UsertrapRes`, `ParkCap`, `UtResFits`, `ProofUsertrap`,
`ProofForkret`, `ProofUserinit`, `ProofKforkB5`, `ProofSwtch`, `ProofSched`
and `ProofScheduler`.

**THE STALE CONE, AND WHAT IT WAS HIDING.**  `UtResFits.vo`'s 21-file
downstream cone (`ProofUsertrap`, `ProofForkret`, `ProofForkretPark`,
`ProofUserinit`, `SystemAdequacy`, the Link* files, …) had not been
rebuilt since before the hermetic seal, because the aborted lemma stopped
`make` at the root.  Stubbing the abort and forcing the cone through found
SIX real breakages, all mechanical and all now fixed:
`SpecForkretParkPaid.forkret_park_pkg` had no `CurCtx` binder; four
`usertrap_res_bare_park` pass-through echoes
(`ProofUserretClosed`/`ProofUservec`/`ProofForkret`/`ProofUsertrap`) had an
implicitly generalized `XI` in the WRONG SIGNATURE POSITION (Coq inserts it
at the first `` `{…} `` group, the module type wanted it last — the
`ProofProcMapstacks` lesson again, and the reason every one of them now
spells `` `{XI : CurCtx} `` explicitly);
`ProofUserinit`'s `word_pointsto_persist` → `ctx_word_pointsto_persist`
(replay class (a)); and one leftover from §0.11′ (`ProofUsertrap`'s
`ut_csrs_raw_fold` needed the caps family PINNED — `?C cur_ctx` against a
seven-conjunct bundle is higher-order).  **LESSON: an `Abort` at a root
hides its whole cone from the build.  When one is left deliberately, stub
it once per sweep and run the cone.**

### 0.13′ WAY OUT 1 IS REFUTED, AND THE REFUTATION IS A RULE

§0.12′ ranked "restate `wp_forkret` with its GLOBAL premises at an explicit
context" as EFFORT, not machinery.  **It is machinery, and the reason is
structural rather than a matter of how many rows move.**  The statement
change was implemented and measured (`wp_forkret_gen_body` gained
`(ξg : CtxId)`; `procs_inv` / `park_globals` / `proc_lock_res` /
`is_kstack` moved to it; `fkr_tail` and `fkr_boot` threaded it), and
`ProofForkret` fails TWICE, neither failure in the boot arm the ruling
flagged as the risk:

1. **`fkr_tail`, at prepare_return** — `iSpecialize: cannot instantiate
   (is_kstack p ks -∗ … ) with (is_kstack ξg p ks)`.  Every callee takes
   its rows at ITS ambient, and a callee's ambient is fixed by the
   `sie_cap_gpr` it also takes, so a caller cannot hand one row at another
   context.  `is_kstack` is a discarded `↦₈` cell and does not cross
   (MEASURED: `NOTCONV`; only `ut_tfk` of the park's rows is `CONV`).
2. **`fkr_tail`, at the residue closer** — `cannot instantiate
   (park_globals XI γs γft γf -∗ …) with (park_globals ξg γs γft γf)`.
   This one is the rule:

> **A thread's AMBIENT context is its identity** — `own_context cur_ctx`
> is a conjunct of `IntrDefs.sie_cap`, beside the stack — **and the trap
> loop's residue is stated at that ambient** — `SpecUserretClosed`'s
> `URes : CpuId -> uptd -> mword 64 -> iProp` has no context argument, so
> `wp_userret_closed` consumes `usertrap_res_bare` at the ambient and
> forkret must therefore instantiate its closer at `Xc := XI`
> (`ProofForkret.v:669`).  Since §0.12′ made the residue's handle rows
> RESUMER-SUPPLIED (`park_globals Xc`), **the resumer must HOLD the
> system's handles at its own running context.**  A freshly minted context
> has none, and none can be given to it: no law transports an
> `is_lock`/`inv` handle, and `TsoCtx.ctx_deposit` — the one law written
> for exactly this hand-over ("a fork's hand-me-downs") — transports only
> `CtxMorph` payloads, i.e. DATA.

So `forkret` cannot run at the child's fresh `XIc`, and no redistribution
of its premises changes that: the ξ that must serve `park_globals` is the
one the WP conclusion runs at.  The corollary kills the tree-wide
generalisation too: pinning EVERY handle at one explicit `ξg` would leave
the data under those handles at `ξg` while the thread writes at its own
ambient, and `WpSconfMem.wp_sd_s_sconf` binds the `↦₈` and the
`sie_cap_gpr` at ONE ambient — so the first `p->chan ↦₈` store by any
thread at another context fails.  **Handles and the data they protect are
one context; a thread is one context; therefore a thread's handles are its
own.**

**WHAT THIS LEAVES.**  Way out 2 — the M3 λ-payload sweep, so a handle is a
CLOSED term and the acquire re-indexes the payload to the acquirer
(`ctx_dom` + `CtxMorph`) — is now the ONLY way out, and it is the honest
TSO story rather than a workaround: at TSO a lock acquire is exactly where
a payload changes context.  It is blocked where §0.12′ measured it, on
`CtxMorph proc_lock_res` (a `▷` over `valid_context`, a guarded fixpoint)
and `CtxMorph ftable_res` (a `cinv` over `off_content`, an `is_pipe` over
`pipe_res`) — i.e. on a ▷/fixpoint/invariant-capable transport, which is
real machinery and is the next design problem to solve, not an errand.
`ProofForkretPark.forkret_park_paid` stays at `Abort` until it lands; the
red list is unchanged (that file plus its 7-file cone).

**MEASUREMENT KIT, worth keeping.**  Two probes answer "is this predicate
ξ-dependent, and does it cross?" in one cheap file, with no crawl risk:
`Check @f` (a `TsoCtx.CurCtx` in the printed type = ξ-indexed) and
`Goal (f (XI := xi) … : iProp Σ) = f (XI := xj) …;
tryif reflexivity then idtac "CONV f" else idtac "NOTCONV f"` — the
hermetic seal makes the non-crossing case fail FAST under `reflexivity`,
where `iExact` is what crawls.  Results for the park's rows:
`cpu_own`, `trap_csrs`, `intr_res`, `proc_priv`, `is_kstack`, `procs_inv`,
`proc_lock_res`, `proc_held`, `ctx_cells`, `stack_own`, `first_done`,
`sie_cap_gpr`, `ut_trap_parked` all `NOTCONV`; `ut_tfk` `CONV`.
`cpu_claim`, `locked` and `pc_is` take no `CurCtx` at all.

---

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
   forever and `ctx_pointsto_persist` fights transport.
   **RE-WORDED 2026-08-26 (§0.12′ ruling 4; the audit this item asked for,
   done).**  "Immutable bytes are CONTEXT-FREE" holds for **timestamp-0**
   bytes ONLY — the boot image, `TsoCtxTwin2.own_context_lb0` /
   `ctx_pointsto_intro_zero`, "the twin image of kernel text is
   context-free".  That is `kernel_data`'s ∀-context form (§0.8′ ruling 1)
   and it is sound.  A byte discarded at RUNTIME (`t > 0`) — `p->kstack`,
   the virtio ring-page pointers, `devsw[]`, the `initproc` cell, all
   written at WP time by `procinit`/`virtio_disk_init`/`consoleinit`/
   `userinit` — needs `mono_nat_lb_own (tc_bnd ξ') t` at the reader's
   context, i.e. re-indexing along `ctx_dom` (`twin_share`), and `ctx_dom`
   is deliberately NOT persistent and is minted only at release/acquire and
   park/resume.  **So a runtime-discarded fact CANNOT ride a parked record
   by fiat.**  It must be re-supplied by the resumer or reduced to a pure
   equation through the cross-context agreement laws — which is exactly
   what §0.12′'s three pins do.  A fix built on the stronger reading would
   look green at SC and fail at cutover.

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
