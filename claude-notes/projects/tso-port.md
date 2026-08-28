# TSO port — plan of record

## 0. CHECKPOINT — READ THIS FIRST

**THE TREE IS FULLY GREEN (2026-08-27).  RED SET EMPTY.  READ §0.22′,
§0.20′, §0.19′, §0.17′ AND §0.18′ FIRST** — §0.22′ is M1 STAGE 3 (`↦ₛ`
flipped context-relative at arbitrary timestamps, its `ctx_string_all`
derived form in the lock handles, and the array→string accessor; §0.21′
is the ruling it implements); — §0.20′ is the CUTOVER BACK-PORTS (three
flip-workspace shapes landed on main below the Σ seam: the virtio
inside-out, the `HartMStore`/`HartMLoad` obligation pass-throughs, and
`WpSconfMem`'s store-side engine-bracket re-parking — with two measured
SKIPS and the `own_context`-is-CpuId-indexed finding the flip tree still
carries unfound); — §0.19′ is M1 STAGE 2 (`↦₂`/`↦₄` flipped; M1
closes) and is where the current shim ledger, the six λ-converted payloads,
the four re-closed invariant bodies and the deliberately-raw tiers are
recorded; — §0.17′ is the landing note for the last blocker class (the
two `inv`s over ξ-indexed bodies), for `ProofForkretPark.forkret_park_paid`
(now `Qed`), and for the second half of the eight-hart adequacy trap that
only a green park could reveal; §0.18′ is the LOCK KIT's convergence on the
same parked-record idiom (release = `ctx_deposit`, acquire = `ctx_absorb`,
`ctx_dom` off the lock's transport path, zero client files).
§0.10′–§0.16′ below are the road to them and are history where they
conflict; §0.19′ amends §0.12′'s park table and §0.14′'s payload
measurements where the flip moved them.

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
never flip; `↦₂`/`↦₄` are stage 2 (§0.19′), `↦ₛ` is stage 3 (§0.22′),
`↦ₚ` stays raw.

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
   mention sites are textually unchanged.  (`kernel_data_string` used to
   spend that ∀ on a junk `MkCtxId inhabitant inhabitant` and cross to the
   raw string tower through the shim — the tree's one "flip ↦ₛ" marker.
   §0.22′ retires it: `kernel_data_string_all` keeps the ∀, and it is the
   producer of the derived context-free string fact.)
2. **Lock metadata stays CONTEXT-FREE; lock-internal cells go ∃-context.**
   `lock_name`/`sl_name`'s name FIELD is spelled raw `word_pointsto` and
   its STRING is `ctx_string_all` (§0.22′'s ∀-context derived form) — a
   context in the persistent HANDLE would make a boot-minted `is_lock`
   unstatable elsewhere.  `lk_cpu_res`'s owner
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

### 0.14′ M3 STEP 1 IS LANDED; STEP 2 IS REFUTED (2026-08-26)

Implements `tso-transport-memo.md` §4 steps 1–2 and its ruling 3.  Two
of the three are landed and green; the third does not close, and the
refutation is measured rather than argued.

**RULING 3 — `CtxMorph` IS AN ENTAILMENT.  Landed.**  `TsoCtx.v:490`
now reads `ctx_dom ξ ξ' -∗ R ξ -∗ ctx_dom ξ ξ' ∗ R ξ'`.  The memo's
count was right to the site: `ProofAcquire.v:666` and
`ProofRelease.v:576` (`iMod` → `iDestruct`), `KallocInv.v`'s six
instance proofs, `TsoCtx.ctx_deposit`'s internal use.  `ctx_deposit`
stays `==∗` (its update is `ctx_dom_to_parked`, not the morph).  Every
structural instance lost its `iModIntro`; nothing else moved.
**Consequence worth recording:** a payload can no longer re-mint its
own ghost names on transport, so any future "the payload asserts its
own ξ and updates a names ghost to move" design is foreclosed by this
ruling — which is the right trade, but name it if it is ever revisited.

**STEP 1 — THE LEAF PAYLOADS.  THE MEMO'S LIST WAS FIVE-EIGHTHS WRONG,
AND THE ERROR WAS IN THE SAFE DIRECTION.**  Measured with §0.13′'s
`Check @f` kit against the built tree, not read off the sources:

| payload | memo said | MEASURED |
|---|---|---|
| `cons_res` (8 sites/3 files) | convert | ξ-INDEXED — converted |
| `pipe_res` (19/5) | convert | ξ-INDEXED — converted |
| `disk_res` (173/86) | convert | ξ-INDEXED — converted |
| `tx_res` (10/5) | convert | **already ξ-FREE** (`∃ l, ghost_var`) |
| `bcache_res` (14/6) | convert | **already ξ-FREE** (`bio_slot_res` is all `↦₄`) |
| `itable_res` (17/6), `itable_res2` (16/5) | convert | **already ξ-FREE** (`inode_ident` is `↦₄`) |
| `sl_res_gen`/`sl_res` (16+18) | convert | **already ξ-FREE** (`slk ↦₄` + ghost; its `R` is a plain `iProp` PARAMETER, so converting it would mean `R : CtxId → iProp` — a sleeplock-surface change, not a leaf conversion) |
| `log_res` (20/6) | convert | **already ξ-FREE** |

So §0.12′'s "already ξ-free and need nothing" row (`wait_res`,
`nextpid_res`, `ticks_res`, `<{ emp }>`) is much longer than recorded:
**five more payloads, ~111 more sites, are already closed terms and
`<{ }>` is already the correct spelling for them.**  The rule the
measurement teaches: *a payload is ξ-dependent iff it holds a `↦ₘ`/`↦₈`
cell; `↦₄`/`↦₂` rows, the phys tier and every ghost row are ξ-constant
at stage 1.*  Read the payload's LEAVES, not its size.

> **SUPERSEDED AT STAGE 2 (§0.19′).**  The "already ξ-free" verdicts above
> are all *"at stage 1"*, and stage 2 flipped `↦₄`/`↦₂`.  SIX of these
> payloads went ξ-INDEXED and were λ-converted then: `ticks_res`,
> `nextpid_res`, `sl_res_gen`/`sl_res`, `bcache_res`, `log_res`,
> `itable_res`/`itable_res2`.  Only `wait_res`, `tx_res` and `<{ emp }>`
> are still closed terms on their own.  The park rows are UNAFFECTED —
> a λ-converted payload makes the `is_lock` HANDLE closed again, so
> `ut_park_caps` still carries `wait` / `ticks` / `nextpid` and not one
> line of `UsertrapRes` / `UtResFits` / `ParkCap` changed.  The rule
> restated for the finished surface: *a payload is ξ-dependent iff it
> holds ANY memory cell outside the deliberately-raw tiers
> (`↦ₓ`/`↦ᵣ`/`↦ₚ`/`↦ₛ`); only ghost rows are ξ-constant.*

Conversions followed §0.7′ verbatim (payload λ names its ξ; `CtxMorph`
instances export beside the sealed definition, structural instances
applied AS TERMS; call sites keep the payload EXPLICIT).  Two mechanical
notes: (i) the lock HANDLE definition has to move below the section that
binds the ambient (`is_conslock`, `is_pipe` — `cons_res (XI := ξ)` is
not spellable inside the section that fixes `XI`), which is the
`KallocInv` `is_kmem` move again; (ii) `Typeclasses Opaque` on the
big-op seams must be `Global` for the same reason (`PipeInvDefs`'s
`pipe_data`/`pipe_slack` were local and are now global).

**ONE NEW STRUCTURAL INSTANCE:** `TsoCtx.ctx_morph_big_sepM`.
`disk_res`'s in-flight and parked windows are `big_sepM`s over
ξ-indexed members and the list instance does not reach them.  Same
induction (`map_ind`), derivable from `ctx_morph` alone — **kit
obligation: `TsoCtxTwin2`'s block needs the same instance at the
swap.**  (`TsoCtxTwin2.v`'s own `CtxMorph` still says `==∗`; flipping it
to `-∗` is a two-line follow-up the memo §1.1 already measured as free.)

**WHAT STEP 1 BOUGHT, AND WHAT IT DID NOT.**  `is_conslock` and
`is_pipe` are now CLOSED TERMS (`Check` prints no `CurCtx`), and so is
the disk `is_lock` (spelled inline at all 173 sites; there is no named
handle).  **`disk_geom` is NOT**, contra memo §4 step 1: its
ξ-dependence is its own three `d_desc_ptr`/`d_avail_ptr`/`d_used_ptr`
`↦₈□` cells, not `disk_res`, and no payload conversion touches them —
they are the M1 flip's discarded-cell problem, whose answer is §0.8′
ruling 1's ∀-context/timestamp-0 form or §5's
`∃ C, □ (∀ ξ, C ξ)` restatement.  `console_caps` is now ξ-free in its
BODY but still carries an unused `` `{XI : CurCtx} `` binder (hence
convertible across ξ, but still printing one); dropping that binder is
a one-line cleanup.  `trap_csrs` therefore stays `NOTCONV`: **the §4
gate did NOT flip after step 1**, and the two rows still holding it are
`disk_geom` and `procs_inv` (step 3).

**STEP 2 — THE `off_hold` FIX IS REFUTED.  There is no cross-context
JOIN, and ruling 2 needs one.**  Ruling 2 does make `off_hold` a closed
term.  It then fails at the one site where the two halves of `a_fip`
must become a whole cell again:

> `ProofSysOpenParts.so_open_slot` cancels the UNARMED off-cinv, gets
> that invariant's `a_fip k ↦₈{1/2}` half at the MINTER's context, and
> joins it with the reference's half at ITS OWN — `so_word_half_join`,
> i.e. `TsoCtx.ctx_word_pointsto_frac_split`, which is SINGLE-ξ.

The memo's answer to the recombination worry (§2(c): "`fpay_tok_agree`
forces the two shares' `pn`, hence their ξ, to agree") is about two
shares of `file_pay` — the dup/split axis.  It does not reach this
join, which is between the cinv's half and the reference's half, and
those are at two contexts by construction: the reference re-indexes at
every ftable acquire, the cinv body is frozen at whatever context
minted it.  It is reachable on the FIRST open after boot
(`FileInv.ftable_res_boot` mints at the boot context).  Moving the half
to the other side (untyped slot keeps the whole cell in `file_fields`)
does not help — it relocates the same join to `FileInv.off_hold_cancel`
at fileclose's last-reference arm.  **Exactly one join exists and it is
cross-context whichever way the halves are arranged.**

MEASURED, under the hermetic seal, in one probe file (kept at
`…/scratchpad/ZZJoinProbe.v`):

```
NOTCONV ctx_pointsto        (* two contexts are not convertible        *)
JOIN-DOES-NOT-CROSS         (* frac_split at xj, halves at xi and xj   *)
CONTROL-JOIN-OK             (* the same tactic, both halves at xj      *)
```

The sealed surface's only cross-context laws are the AGREE family
(`ctx_pointsto_agree`, `ctx_bytes_agree`, `ctx_word_pointsto_agree`);
a JOIN would need a `ctx_dom`, and no party at that site holds one over
the minter's context (the ftable acquire's `ctx_dom` is over the
PAYLOAD's parked ξ, which is not the cinv's).

**RECOMMENDED RULING (owner decision, and it is a design change the
memo did not rule):** the off-borrow cinv must stop holding a points-to
FRACTION of a flipped cell.  Replace the parked `a_fip k ↦₈{1/2}` with
ghost state — an agreement pinning `ip`, beside the existing exclusive
borrow marker `off_mark` — so `off_content` is ξ-free outright, the
whole `a_fip` cell rides the reference and re-indexes at every ftable
acquire, and no join is ever cross-context.  **That shape also survives
STAGE 2**, which the memo demanded of any stage-1 fix: `a_foff k ↦₄` is
genuinely read AND written by the borrower, so pinning it to an
`fp_ctx` would break the borrower the same way `a_fip` breaks the
publisher; under the ghost shape both cells live in the reference and
stage 2 costs nothing at the fd table.  Blast radius: `FileInvDefs`'s
`off_*` block, `FileOff`'s checkout/return, `so_open_slot`/`so_publish`,
`ProofFileclose`'s last-reference arm, `FileInv.ftable_res_boot`.  The
finding is recorded in `FileInvDefs.v`'s header, where the next
implementer will look.

`inode_pay` is NOT a second obstruction inside `ftable_res` (MEASURED
ξ-free: `inode_held_short` is ghost plus `↦₄`), so `off_hold` is the
whole of it — the memo was right about that.

**Red set unchanged:** `ProofForkretPark.v` (the deliberate `Abort`) and
its 7-file cone.  Three consecutive full VM rounds; the 173-site
`disk_res` sweep produced exactly ONE fallout site in the tree
(`ProofFilewrite.v:1542`, a MODULE-QUALIFIED `<{ DiskInv.disk_res … }>`
the unqualified grep missed — worth remembering for the next sweep).

### 0.15′ THE `XIp` RESHAPE IS LANDED, AND THE PARK'S LAST BLOCKER IS ONE PAYLOAD (2026-08-26)

Implements `tso-transport-memo.md` §4 steps 3–5.  Steps 3 and 4 are
landed and green; step 5 is **refuted by measurement**, on one row, and
that row is `tso-port.md` §0.14′'s own unfinished business.

**A PARKED RECORD'S ROWS ARE THE PARKED THREAD'S OWN.**
`SwtchCtx.valid_context_pre`'s six ambient rows now read the record's own
existential identity `XIp`, and `P` takes it as a leading argument.
`valid_context` — hence `SchedCtx.proc_ctx` / `sched_vc_at` / `p_sched`
— is a **CLOSED TERM** (`Check` prints no `CurCtx`), so `▷ proc_ctx` and
`▷ sched_vc_at` are `ctx_morph_const` and **no `▷`-capable transport is
invoked anywhere**.  Contractiveness closes with the tree's own tactic
unchanged, exactly as the memo's Probe A predicted.

**THE M3 SWEEP'S STEP 3 IS LANDED.** `proc_lock_res` is a CONVERTED
payload (`procs_inv` spells `(λ ξ, proc_lock_res (XI := ξ) …)`, 41 sites
in 17 files), so the per-proc `is_lock` HANDLE is a closed term and the
acquirer re-indexes the payload along `ctx_dom` — the honest TSO reading
of an acquire.  `procs_inv` is **transportable, not context-free**, and
cannot be either: it also carries the per-slot `is_kstack`.

**THE SWTCH DEPOSIT IS PROVED** (`ProofSwtch.v`).  `wp_swtch_sconf` gains
one instance-implicit premise, `CtxMorph (λ ξ, P ξ cpu_id Ao newc oldc …)`,
resolved by `SchedCtx.p_sched_morph` at both call sites; the proof
deposits the target's post-block save area, `cpu_own`, the chain payload
and (at `back = false`) the old context's raw cells into the record's
`XIt` with `TsoCtx.ctx_deposit`, then exchanges the tokens.

#### THE MEMO'S §5 FALLBACK IS UNSOUND, AND THE RIGHT SHAPE IS A GATED CERTIFICATE

`tso-transport-memo.md` §5 pre-approves restating `intr_res` as
`∃ C, □ (∀ ξ, C ξ) ∗ ▷ ihs kt C h` if the "§4 gate" (`trap_csrs`
`NOTCONV → CONV`) does not flip.  **Do not take it.**  `devintr_caps`
holds two rows of cells that are DISCARDED AT RUNTIME — `disk_geom`'s
three ring-page pointers and `procs_inv`'s per-slot `is_kstack` — and a
∀-context form over a `t > 0` discarded fact is precisely what §0.4 item
6 forbids: it would look green at SC and be false at the flip.

What the deposit actually needs is not context-FREEDOM but
TRANSPORTABILITY, and that is `CtxMorph`.  So `IntrDefs` now carries

```coq
Definition caps_morph (C : caps_fam) : iProp Σ :=
  (□ ∀ ξ ξ' : CtxId, ctx_dom ξ ξ' -∗ □ C ξ -∗ ctx_dom ξ ξ' ∗ □ C ξ')%I.
```

— `CtxMorph (λ ξ, □ C ξ)` internalised, `ctx_dom`-GATED — as a row of
`ires_of` / `intr_res` beside `□ C ξ`.  It is discharged once, by
`caps_morph_intro` (from the structural instances alone, consuming
nothing, hence sittable under the `□`) at
`SpecDevintr.devintr_caps_fam_morph`.  Cost: one row, the
`intr_res_intro` callers, the `rewrite /intr_res` destructuring sites, and
`ut_trap_csrs_fold` / `ut_csrs_raw_fold` (which take the certificate as a
premise and get it from `devintr_caps_fam_morph` at `ProofUsertrap`) — the
same fallout list §0.11′ recorded, again.

> **THE RULE.  When an ∃-bound abstract payload has to change context,
> give the resource the TRANSPORT, not the uniformity.  A ∀-context form
> is only sound for timestamp-0 (boot-image) facts; everything written at
> WP time transports along a `ctx_dom` and nothing else.**
>
> Corollary, and it retires a measurement: §4's gate is the WRONG TEST.
> `trap_csrs` stays `NOTCONV` and always will (it carries the whole
> device bundle); `CtxMorph (λ ξ, trap_csrs (XI := ξ) kt)` is what the
> deposit wanted, and it holds.  §0.14′'s "the §4 gate did NOT flip …
> and the two rows still holding it are `disk_geom` and `procs_inv`" is
> answered by making both TRANSPORT, not by making either disappear.

#### STEP 5 IS REFUTED, AND IT IS ONE ROW

`ProofForkretPark.forkret_park_paid` stays at `Abort`.  With the reshape
the record's rows are all at the freshly minted `XIc`, so the proof must
hand its six ξ-dependent rows over with `ctx_deposit` — `procs_inv`,
`park_globals`, `is_kstack`, `proc_priv`, the save area and the stack —
whose obligation is `CtxMorph` on each.  MEASURED with §0.13′'s kit on
this tree:

```
MORPH procs_inv OK          MORPH console_caps OK
MORPH console_ready OK      (the initproc cell: ctx_morph_word)
NOTCONV is_ftable           NO-INSTANCE CtxMorph is_ftable
NOTCONV ftable_res
```

`UsertrapRes.park_globals`' `FileInv.is_ftable` is
`is_lock γl ftable_addr "ftable" <{ ftable_res γ }>` — a CONSTANT
embedding of a payload that is still ξ-INDEXED, so two handles are `inv`s
over DIFFERENT bodies and no law relates them.  `ftable_res`'s
ξ-dependence is `FileInvDefs.off_hold`'s `cinv` over `off_content`, i.e.
the borrowed `a_fip k ↦₈{1/2}` half — **the one payload the M3 sweep has
not converted, and the one §0.14′ leaves with a recommended ruling.**
(`proc_priv`'s own chain — `first_tok` → `first_done` → `fs_ready` — is
NOT measured; every handle it carries whose payload the sweep converted or
measured ξ-free is a closed term, so it is expected to go through, but it
is the next thing to check, not something to assume.)

**So the order is forced, and it is short.**  (i) Land §0.14′'s
off-borrow ruling (the parked half becomes ghost state pinning `ip`), so
`ftable_res` converts and `is_ftable` is a closed term.  (ii) Thread the
parker's `own_context` through `ParkCap.park_cap` and
`forkret_park_paid_body` — `ctx_deposit`'s first premise, which no
persistent surrogate can replace (the depositor's authority over its own
context is what bounds the deposited facts' timestamps).  Both parkers
hold one inside their `sie_cap_gpr`; quantify the HART beside the context
in `park_cap` so the token stays hart-free (ruling 1).  (iii) Deposit the
six rows into `XIc` and finish with the body kept in
`ProofForkretPark.v`'s trailing comment.

#### MECHANICS WORTH KEEPING

- **A section variable cannot be instantiated inside the section that
  binds it, and that is what shapes both files.**  `valid_context_pre`
  must spell `ctx_cells (XI := XIp)`, so it moved below the section that
  defines `ctx_cells`; `p_sched` must spell `proc_held (XI := ξ)`, so
  `SchedCtx.v` is now FOUR sections (payload halves → chain → lock
  invariant → `procs_inv`, the last one split off only so its payload
  could be λ-converted).  **The sections that must not capture an ambient
  declare no `XI` at all** — with none in scope a forgotten annotation is
  an elaboration error instead of a silent capture (§0.8′ rule 3).
- **`Global Typeclasses Transparent cur_ctx` does NOT help** (measured).
  `↦₈`/`↦ₘ` put the index under the class projection `cur_ctx`, and
  instance search will not take that delta step, so `ctx_morph_word` /
  `ctx_morph_pointsto` must be **applied AS TERMS** for every payload
  written with the notations — the `KallocInv` recipe's rule 3 is a
  requirement, not a style.
- **Two new structural instances**, `TsoCtx.ctx_morph_if_then` /
  `ctx_morph_if_else`: a payload guarded by a boolean with `emp` on the
  other arm (`proc_slots`' five arms) transports arm by arm.  Kit
  obligation: derivable from `ctx_morph` alone, like `ctx_morph_big_sepL`.
- **ξ-profile, measured, worth not re-deriving:** `proc_pt` is ξ-FREE (it
  is entirely physical tier), and so are `tf_page`, `pstate_lock`,
  `hart_at`, `hart_at_any`, `pslot_used_at`, `proc_pub`, `hart_full`,
  `cpu_locks_lvl`, `hart_csrs`, `wire_inv`, `kmap_at`, `kernel_text`,
  `cwd_ref`.  `cpu_own`'s ONLY context-indexed row is `ProcGeom.cur_proc`
  (one word cell).  `SpecConsoleintr.console_caps` carried a PHANTOM
  `CurCtx` binder its body never mentioned; dropped, and it is now a
  closed term.
- **The swtch seam has exactly one shim use, and the reshape moved it.**
  `StackOwn.stack_own_reindex` is GONE ENTIRELY — the record's stack is
  already at `XIt`, `ProofSwtch` was its only caller, and one piece of
  cutover debt goes with it; `ctx_cells_reindex XIt cur_ctx` takes its
  place on
  the INBOUND leg, because the machine block reads the target's save area
  at the RUNNING hart's index and the sealed surface has no
  parked→running law (a resumer is entitled to those cells by its
  p->lock acquire's `ctx_dom`, which is not threaded to that proof yet —
  the same M2 seam `SchedCtx.cpu_ctx_free`'s ∃-context records).  The
  OUTBOUND leg is honest `ctx_deposit`.
- `SchedCtx.proc_ctx_cells` / `proc_ctx_own_ctx` were dead tree-wide and
  are deleted; they were the only ξ-crossing the reshape would have made
  unprovable.

#### THE CONE SWEEP, AND WHAT IT STILL HIDES

Swept per §0.12′'s lesson (stub the deliberate `Abort` once, force the
7-file cone, restore).  Two real breakages found and fixed:
`ProofForkretPark.usertrap_res_bare_park`'s implicitly generalized
`CurCtx` landed at the FIRST `` `{…} `` group while the module type wants
it LAST (the `ProofProcMapstacks` lesson, fifth occurrence — spell it),
and `park_token_intro`'s package hand-over needs the row-by-row
`iSplitR`/`iExact` spelling rather than one `iFrame`, because the globals
row is an ∃ over a discarded cell (`ParkCap.park_token_park` already
carries that note).

**The third is not repaired and is not this tranche's:** `BootShared.v`'s
`.bss` carve has been stale since the M1 flip.  `Section BootBss` /
`Section BootBssChain` bind no `CurCtx` while `cpu_slot_raw` and
`boot_hart_bss` hold `↦₈` cells and an `own_ctx`; and because `BootCarve`
sits BELOW the seam (its `↦₈` is the RAW `word_pointsto`) while
`BootShared` imports `TsoCtx`, every cell the carve hands to a ξ-indexed
consumer needs the phys→ctx mint `TsoCtxShim.ctx_word_of_mem` —
`BootCarveMain.v` already does exactly this at ~60 sites and is the
template.  Scope: two section binders plus ~25 mint insertions across
`BootShared`'s 35 `boot_ran_cell8*` sites (the `↦₄`/`↦₂` ones need
nothing — stage 1 does not flip them), then whatever the five files above
it hide in turn.  **Nothing above it can be checked until the park's
`Abort` goes, so budget this WITH the off-borrow ruling, not after it.**

**Red set unchanged:** `ProofForkretPark.v` (the deliberate `Abort`) and
its 7-file cone.

### 0.16′ THE OFF-BORROW RULING IS LANDED; THE PARK'S LAST ROW IS THE BCACHE ESCROW (2026-08-26)

Executes §0.15′'s forced order.  Step (i) is **landed and green**; step (ii)
was built, measured and **reverted**; step (iii) is **REFUTED by
measurement**, on one row, and that row is not in the park at all -- it is in
the buffer cache.

#### STEP (i) -- THE OFF-BORROW REDESIGN.  LANDED.

**The statement, old vs new.**

```coq
(* FileInvDefs, before *)                  (* FileInvDefs, after *)
off_body γ k                               off_body γ k ip
:= ∃ ip, a_fip k ↦₈{DfracOwn (1/2)} ip     := off_resident k
        ∗ (off_resident k                        ∨ (off_mark ip ∗ flive_tok γ k)
           ∨ (off_mark ip ∗ flive_tok γ k))

off_raw k                                  off_raw k
:= ∃ ip v, a_fip k ↦₈{DfracOwn (1/2)} ip   := ∃ v, a_foff k ↦₄ v ∗ ⌜off_wf v⌝
        ∗ a_foff k ↦₄ v ∗ ⌜off_wf v⌝

off_content γ k armed                      off_content γ k armed ip
off_hold γ k γx armed q                    off_hold γ k γx armed ip q

file_fields … a_fip k ↦₈{DfracOwn (q/2)}   file_fields … a_fip k ↦₈{DfracOwn q}
file_payload := file_core q pn C           file_payload := file_core q pn C
   ∗ off_hold γ k (fp_ocv pn) (file_armed C) q   ∗ off_hold γ k (fp_ocv pn)
                                                     (file_armed C) (fc_ip C) q
```

**THE GHOST CHOSEN FOR THE `ip` AGREEMENT IS THE ONE THE SLOT ALREADY HAD.**
The ruling said "replace the parked half with ghost state -- an agreement
pinning `ip`".  No NEW ghost was minted, and the reason is worth the
sentence: `off_hold` already takes two other C-derived arguments -- the cinv
NAME `fp_ocv pn` and the ARMED bit `file_armed C` -- and every site that must
reconcile two shares of one slot (`file_pay_split`, `file_rest_absorb`,
`file_rest_join`, fileclose's last-reference arm) ALREADY runs the two
agreements that pin them: `fpay_tok_agree` on `pn` and `FileInv.file_fields_agree`
on `C`.  Adding `fc_ip C` as a third rides those and creates **zero new proof
obligations anywhere**.  And `file_fields_agree` is a POINTS-TO agreement on
the very `a_fip` cell, so the tie between the invariant's `ip` and the
memory's is if anything tighter than the parked half was -- it is just paid
at the reference instead of inside the invariant.  The alternatives were both
worse: a fresh `own γ (to_agree ip)` needs a new `inG` in Σ (an adequacy-wide
change), and a slot-keyed `agree` map under the existing `fileUR` cannot be
RE-minted when a slot is republished.

**MEASURED, and it is the whole point.**  With §0.13′'s `Check` kit on this
tree:

```
@off_body, @off_content, @off_hold      -- no CurCtx  (CLOSED TERMS)
@file_core, @file_payload, @file_pay    -- no CurCtx  (CLOSED TERMS)
@file_fields, @fslot, @ftable_res       -- CurCtx     (ξ-INDEXED, as they should be)
MORPH ftable_res OK
```

`file_core` came out closed for free (`is_pipe` was λ-converted a tranche
earlier, `inode_pay` was measured ξ-free), so after the ruling **the whole
ξ-dependence of an ftable slot is `file_fields`' four flipped cells.**
`FileInv.ftable_res_morph` is then three structural instances applied AS
TERMS, `is_ftable` moved below the section that binds the ambient and became
`is_lock γl ftable_addr "ftable" (λ ξ, ftable_res (XI := ξ) γ)` -- a **CLOSED
TERM** -- and §0.15′'s blocker (`NOTCONV is_ftable`, `NO-INSTANCE CtxMorph
is_ftable`) is gone.

**Blast radius, as landed** (9 files): `FileInvDefs` (the `off_*` block, the
`file_fields` fraction, three new `CtxMorph` instances at the end),
`FileInv` (`file_fields_ip`, `file_fields_frac_split`, `off_hold_cancel`,
`ftable_res_boot`, the new `FileLock` section), `FileOff` (both borrow
lemmas), `ProofSysOpenParts` (`so_open_slot`, `so_publish` -- and
`so_word_half_join` is DELETED), `ProofSysOpen` (`so_ip_split` deleted, the
`a_fip` half premise dropped from `so_tail_pub`), `ProofFileclose` (the
last-reference arm), `SpecFileread` (`fileread_pay_carve`),
`ProofFileread` / `ProofFilewrite` (five `DfracOwn (q/2)` → `DfracOwn q`),
plus the 9 `<{ ftable_res γ }>` → `(λ ξ, ftable_res (XI := ξ) γ)` sites in
`ProofMain` / `ProofFilealloc` / `ProofFileclose` / `ProofFiledup`.

**THE `a_fip` PREMISE STAYS ON `off_checkout`/`off_checkin` AS A PASSENGER.**
It is dead in the proof now, and it was kept deliberately: it is what ties
`off_hold`'s `ip` argument to the borrower's own reference at the five call
sites, and dropping it would have churned two 2500-line proofs for nothing.

**STAGE 2 COSTS NOTHING AT THE FD TABLE, and the memo demanded this be said.**
When `↦₄` flips, `off_resident`'s `a_foff k ↦₄ v` becomes ξ-dependent -- and
that cell is genuinely READ AND WRITTEN by the borrower, so pinning it to an
`fp_ctx` would break the borrower exactly the way pinning `a_fip` broke the
publisher.  Under THIS shape the borrower takes the cell out and puts it back
inside one borrow window under `ip->lock`, so the `ctx_dom` it needs is the
one that sleeplock acquire already gives it; `a_fip`, the cell the PUBLISHER
writes, is not in the invariant at all any more.  The stage-2 work is
`FileOff.v`'s two lemmas and a `ctx_dom` premise, and NOTHING in
`FileInvDefs` / `FileInv` / `ProofSysOpenParts` / `ProofFileclose`.  Recorded
in `FileInvDefs.v`'s header, where the next implementer will look.

**ONE MEASURED GOTCHA, worth keeping.**  `Global Typeclasses Opaque
ftable_res` -- which §0.14′'s `PipeInvDefs` note would have you add to seal
the big-op seam -- **breaks three files**: `IntoExist` IS a typeclass, so
sealing an ∃-shaped definition breaks `iDestruct "H" as (M) "…"` at every
consumer (`ProofFilealloc`, `ProofFileclose`, `ProofFiledup`).  The seal is
not needed: the big-op inside `ftable_res` is reached only through
`ftable_res_morph`, which applies `ctx_morph_big_sepL` AS A TERM and never
searches there.  **Seal a big-op SEAM, not an ∃.**

#### STEP (ii) -- BUILT, MEASURED, AND REVERTED

Threading the parker's `own_context` through `ParkCap.park_cap` /
`SpecForkretParkPaid.forkret_park_paid_body` was implemented as §0.15′ says
(hart ∀-quantified beside the context, token handed straight back), together
with the one thing §0.15′ did not foresee and which is the note worth
keeping:

> **THE PACKAGE'S `▷` HAS TO MOVE ONTO ITS CLOSER ROW ALONE.**  `park_cap`
> takes `▷ park_pkg`, and the park must DEPOSIT three of that package's rows
> (`procs_inv`, `park_globals`, `stack_own`) into the child's freshly minted
> context.  `TsoCtx.ctx_deposit` is an update and `CtxMorph` needs its
> `ctx_dom` AT THE TOP LEVEL, so nothing under a `▷` can be deposited --
> `ctx_dom`'s non-persistence is exactly the obstruction
> (`tso-transport-memo.md` §1.2), and there is no `▷`-crossing to be had.
> Only the CLOSER row needs the later, and for the fixpoint's sake rather
> than the proof's: it is the only row that names `W`.  With the `▷` inside
> `park_pkg` on that row, `park_token_F_contractive` closes unchanged.

It is **reverted** (`ParkCap.v`, `SpecForkretParkPaid.v` back at their
committed text), because it buys nothing while step (iii) is refuted and it
moves an exported shape.  The shape above is the whole of it; re-derive it
when the escrow lands.  `IntrDefs.sie_cap`'s thread-of-control conjunct is
where both parkers get the token from, and the peel is
`sie_cap_gpr_split` / `sie_cap_gpr_join` around a six-way destructuring of
`sie_cap` -- twelve lines, and it belongs in `ParkCap.v` rather than
`IntrDefs.v` (425 files sit on the latter).

#### STEP (iii) IS REFUTED, AND THE ROW IS `BioInv.buf_escrow`

`ProofForkretPark.forkret_park_paid` stays at `Abort`.  **Five of the six
rows the deposit must move are payable, and are now PROVED so** -- three of
them by instances that did not exist before this tranche:

```
MORPH ftable_res OK      MORPH procs_inv OK       MORPH is_kstack OK
MORPH ctx_cells OK       MORPH stack_own OK       MORPH console_ready OK
MORPH park_globals OK    (UsertrapRes.park_globals_morph, landed)
MORPH cwd_ref OK         MORPH file_ref OK        MORPH disk_geom OK
```

The sixth is `ProcInv.proc_priv`, and it does not close:

```
proc_priv -> proc_priv_core -> FirstTok.first_tok
  -> (steady arm) FsReady.fs_ready            -> BioInv.bio_ctx
  -> (boot arm)   FirstTok.first_boot_persist -> BioInv.bio_ctx
  -> BioInv.buf_escrow = inv bioN (buf_escrow_body bn V k)

@buf_escrow      : … → CurCtx → bio_names → bio_view Σ → nat → iProp Σ
@buf_escrow_body : … → CurCtx → bio_names → bio_view Σ → nat → iProp Σ
NOTCONV buf_escrow                 NOTCONV buf_escrow_body
NO-INSTANCE CtxMorph buf_escrow    NO-INSTANCE CtxMorph bio_ctx
```

**An `inv` over a ξ-INDEXED body is the ONE shape `CtxMorph` cannot cross**
(§0.12′'s rule: invariant bodies are not updatable, so no transport exists
and none can be written).  It is the same shape the off-borrow ruling had to
remove from `off_hold` -- **and the ruling's technique does not replay.**
`off_content`'s ξ-dependence was a REDUNDANT COPY of a pointer, kept only so
the invariant could name an inode, and a pinned argument replaced it for
nothing.  `buf_escrow_body`'s is **the buffer's DATA**: `buf_parked` and
`buf_mid` hold `buf_own (bpa k) …`, the cached block's bytes, parked there
between bread and brelse.  That is what the escrow is FOR; it cannot be
pinned away.

**AND THE ROW CANNOT BE ROUTED AROUND.**  `first_tok` is a conjunct of
`proc_priv_core` and BOTH its arms reach `bio_ctx`, so the boot arm -- which
is exactly what userinit parks -- is no cheaper than the steady one.  Making
it resumer-supplied the way `park_globals` and `first_done` already are is
not available either: the FIRST resumer runs BEFORE `first_done` exists
(forkret's own boot arm is the one instruction in the kernel that mints it),
which is precisely why `proc_priv` carries `first_tok` and not `first_done`.

**SO THE NEXT TRANCHE IS THE BCACHE ESCROW, AND IT NEEDS AN OWNER RULING.**
The shape that would work is `WpLock.lock_inv`'s own: ∃-close the context
INSIDE the escrow body (`inv bioN (∃ ξ, buf_escrow_body (XI := ξ) bn V k)`),
which makes `buf_escrow` a closed term -- and then every OPENER (bget, bread,
brelse, the recycler) needs a `ctx_dom` from the ∃-bound ξ to its own before
it may read or write the block.  It is entitled to one by the bcache lock or
the buffer sleeplock it is holding; that `ctx_dom` is not threaded to those
proofs today.  Same seam as `SchedCtx.cpu_ctx_free`'s ∃-context records
(§0.15′), one layer down.

#### STEP (iv) -- THE `.bss` CARVE, AND THE EIGHT-HART TRAP IT WAS HIDING

`BootShared.v` had been stale since the M1 flip because the deliberate `Abort`
hid its whole cone from `make` (§0.12′'s lesson, third occurrence).  Repaired
as §0.15′ prescribed, and then some:

- `Section BootBss` / `Section BootBssChain` gained their `CurCtx` binder.
- **~28 crossings**, all `TsoCtxShim.ctx_word_of_mem`, `BootCarveMain.v`'s
  pattern verbatim: the 18 zeroed `devsw` slots, its two live ones, `kmem+24`,
  `kernel_pagetable`, `initproc`, the three `disk` ring pointers.
- **Three crossings that are NOT one cell each**, and each is worth naming:
  the `p->chan` family (a `big_sepL_mono` under the big-op, because
  `BootCarveMain.boot_procs_raw` is below the seam while `SchedCtx`'s p->lock
  resource reads `p->chan` at the LOCK HOLDER's context); the two byte RUNS
  (`sb`'s 32 and `disk.free`'s 8), for which `BootShared` now carries one
  local `boot_bytes_ctx`; and `SchedCtx.cpu_ctx_free`, which ∃-QUANTIFIES the
  save area's context (the cells belong to no thread while the slot is free)
  and which the carve therefore WITNESSES rather than frames.
- Two `iFrame`s became row-by-row `iExact`s, for the reason
  `ParkCap.park_token_park` already records: **an ∃ does not frame against an
  ∃**, and since the flip `own_ctx` is one.

**AND THEN THE FILE ABOVE IT CRAWLED, WHICH IS THE REAL FINDING.**  With
`BootShared` green the cone went green to `SystemAdequacy.v`, which then ran
**23 minutes 34 seconds** (2 GB RSS) against a normal cost of ~100 s
(durable-notes.md's measurement) before it was killed under §0.13′'s rule.
`rocq compile -time` localises it exactly: the last command that completes is
the `iModIntro` after `iMod (own_context_boot (CID := 0%fin))`, so the crawl
is the `iApply (boot_hart_primary (XI := ξ0) …)` that follows.

**THE EIGHT-HART ADEQUACY TRAP, stated once.**  The `.bss` carve runs ONCE,
inside one fupd, before any hart has a thread of control; the eight harts then
run at eight DISTINCT `own_context_boot` identities.  A bundle handed out at
the carve's single ξ can serve at most one of them -- and
`BootChain.boot_entry_bridge`'s own header had already asserted the intent
("`boot_shared_alloc` hands its per-hart bundle out under one ambient `XI` …
Keeping [`own_context`] a separate premise lets `SystemAdequacy` mint one
token per hart and instantiate THIS lemma at that hart's ξ") without the
statement being able to honour it.

**MEASURED: `BootChain.boot_hart_res` had exactly ONE ξ-indexed row** --
`ProcGeom.cur_proc`, the `cpus[h].proc` cell.  Everything else is registers,
ghosts, the physical tier, or `cpu_ctx_free`, which already ∃-closes its own
context.  So the fix is one row:

```coq
(* BootChain.boot_hart_res, before *)      (* after *)
   cur_proc zero_reg ∗                        (∀ ξ : CtxId, cur_proc (XI := ξ) zero_reg) ∗
```

and `boot_hart_res` is a **CLOSED TERM** (`Check` prints no `CurCtx`).  The
carve keeps the cell RAW (`RiscvPtsto.word_pointsto`, so `cpu_slot_raw` and
`boot_hart_bss` spell it explicitly) and does the phys→ctx mint UNDER the ∀ in
`boot_hart_pre`; `boot_entry_bridge` takes it at its own ambient with one
`iSpecialize ("Hproc" $! cur_ctx)`.

> **THE ∀-CONTEXT FORM IS SOUND EXACTLY HERE, and the two conditions are
> worth spelling out because §0.15′'s rule reads as an outright ban.**  The
> ban is on `□ (∀ ξ, C ξ)` over facts written at WP time: a PERSISTENT
> ∀-context form hands the fact out at every ξ, and for a `t > 0` discarded
> cell that is false at the flip.  This row is neither: the cell is
> EXCLUSIVE, so the ∀ is a *choose-your-ξ wand* and cannot be instantiated
> twice, and it is a TIMESTAMP-0 boot-image cell -- §0.4 item 6's one
> sanctioned case.  `TsoCtxShim.ctx_word_of_mem` quantifies its ξ, which is
> exactly what makes the ∀ provable from ONE raw cell.

**AND THE FILE STILL DOES NOT CLOSE, ON A SECOND MULTI-CONTEXT INVARIANT.**
With the trap answered, `SystemAdequacy` gets past `boot_hart_primary`'s
first four premises and dies on the fifth.  MEASURED, in 0.75 s (see the
performance note below):

```
@main_deposit : ... -> GenId -> CurCtx -> uart_names -> disk_names -> iProp
@started_inv  : ... -> iProp -> iProp            (* a PLAIN payload *)
@procs_inv    : ... -> GenId -> CurCtx -> list gname -> iProp

iSpecialize: cannot instantiate (started_inv (main_deposit gd gv) -* ...)
             with (started_inv (main_deposit gd gv))
```

The two sides print identically and differ in the implicit `CurCtx`.
`StartedInv.started_inv` takes a PLAIN `iProp` and is handed
`SpecMainSecondary.main_deposit`, which is ξ-INDEXED through
`SchedCtx.procs_inv` -- so it is an **`inv` over a ξ-indexed body that ALL
EIGHT harts need, each at its own `own_context_boot` identity.**  That is
`BioInv.buf_escrow`'s refutation again, one layer up, and it wants the same
ruling: ∃-close the context inside the invariant and give the opener a
`ctx_dom` (here, out of the deposit's own hand-over).  It cannot be answered
the way `cur_proc` was: `main_deposit` is PERSISTENT, so a ∀-context form
over it would be `□`-duplicable across ξ, and `procs_inv` carries the
per-slot `is_kstack` -- a `t > 0` discarded cell, §0.4 item 6's forbidden
case exactly.

**SO THE M1 FLIP LEFT EXACTLY TWO `inv`s OVER ξ-INDEXED BODIES THAT MUST
SERVE MORE THAN ONE CONTEXT**, and they are the whole of what stands between
here and a green tree: `BioInv.buf_escrow` (the park's row six) and
`StartedInv.started_inv (main_deposit ...)` (the eight harts).  ONE RULING
COVERS BOTH.

**THE PERFORMANCE LESSON, and it is the one to carry forward.**  Until it was
localised, that mismatch was a **23-minute, 2 GB crawl** inside
`iApply (boot_hart_primary ... with "H1 ... H30")` -- `make` simply never
finished, and the file's normal cost is seconds.  Rewritten as
`iPoseProof ... as "HP"` plus thirty `iSpecialize ("HP" with "Hi")`, the same
mismatch is reported **in 0.75 s, by name**.  The rewrite is in the tree.

> **A 30-PREMISE `iApply ... with "..."` IS A PERFORMANCE BUG WAITING FOR A
> MISMATCH.**  It builds the whole application and unifies it against the
> goal in one go, so a bad premise deep in the list has nowhere to fail
> fast; specialising one premise at a time gives the unifier a head symbol
> to differ at.  §0.13′'s "a crawl IS the signature of an unprovable
> crossing" applies to TACTICS as well as to goals -- and it is the same
> lesson the tree already carries as "row by row, not one `iFrame`"
> (`ParkCap.park_token_park`, and twice more in `BootShared` this tranche).
> Spell long premise lists out.

#### MEASUREMENT, AND ONE THING THAT DOES NOT WORK

- **The `Check`/`reflexivity`/`apply _` kit is still the right instrument**,
  and `tryif (apply _) then idtac "MORPH f OK" else idtac "MORPH f NO"` is the
  third probe to keep beside §0.13′'s two: it answers "does this row's
  transport obligation discharge?" in one cheap file with no crawl risk.
- **`Hint Extern` DOES NOT RESCUE THE HIGHER-ORDER UNIFICATION** (measured).
  §0.15′'s "structural instances must be applied AS TERMS" was recorded as a
  mechanic; the natural workaround --
  `Hint Extern 4 (CtxMorph (λ _, big_opL _ _ _)) => eapply ctx_morph_big_sepL`
  and the same for `bi_exist`, so that `eapply`'s more aggressive unifier runs
  instead of instance search's -- leaves `devsw_table`, `bio_ctx`,
  `first_fsinit`, `fs_ready`, `first_tok`, `ofile_slot`, `proc_ofiles` and
  `proc_priv` ALL still unresolved.  **The rule is a requirement; stop looking
  for a way around it.**
- **ξ-profile, measured, worth not re-deriving.**  Of `fs_ready`'s twenty
  conjuncts exactly ONE is ξ-indexed: `bio_ctx`.  `kernel_text`,
  `kernel_data`, `printk_env`, `log_ctx`, `fs_crash_seam`, `gen_cert`,
  `dev_inv`, `is_itable2`, `itable_inv`, `ic_escrows`, `ic_sleeplocks`,
  `ireg_inv`, `ireg_open`, `kalloc_avail`, `fs_sb_cells`, `bitmap_inv` all
  print with no `CurCtx`, and `disk_geom` -- which does -- has an instance.
  Inside `bio_ctx`: `bcache_res` and `bown` are ξ-FREE, `is_sleeplock` takes
  its resource as a plain `iProp`; only `buf_escrow` carries the index.

#### STEP (v) -- THE CONE, AND THE VERDICT

Swept per §0.12′'s lesson: the deliberate `Abort` was stubbed once, the
7-file cone forced, and the stub removed.  **Six of the seven are green**
(`LinkForkretParkPaid`, `LinkMain`, `LinkUserinit`, `BootChain`,
`BootShared`, `FsAdequacyImg`); the seventh, `SystemAdequacy`, is red on the
second multi-context invariant above and is now red FAST rather than after
23 minutes.

**THE TREE IS NOT FULLY GREEN, and the red set is exactly the one this
tranche inherited:** `ProofForkretPark.v`'s deliberate `Abort` and its
7-file cone.  `make` stops at that file and never reaches the cone, so no
build crawls and nothing above it is attempted; two consecutive full VM
rounds report that ONE error and nothing else.  What changed underneath is
that the cone is no longer HIDING anything: five of its files are proved
green, and the two remaining obstructions are named, measured, and share one
ruling.

#### MEMO CORRECTIONS

- **`tso-transport-memo.md` §2(c) ruling 2 ("add an `fp_ctx : CtxId` field to
  `fpnames` and state `off_content` at `fp_ctx pn`")** -- refuted at §0.14′,
  and its replacement is now LANDED.  The memo's own summary of the fix
  ("Cost: `a_fip` has 32 occurrences in 9 files … This is the smallest of the
  three fixes") is right about the size and wrong about the shape: the landed
  fix touches the SAME files and is smaller still, because it DELETES two
  half-cell lemmas (`ProofSysOpenParts.so_word_half_join`,
  `ProofSysOpen.so_ip_split`) and one `Qp.div_add_distr` rather than adding a
  record field.
- **`tso-port.md` §0.14′'s recommended ruling ("replace the parked
  `a_fip k ↦₈{1/2}` with ghost state -- an agreement pinning `ip`")** -- landed
  IN SUBSTANCE, but **no ghost was minted**.  The agreement that pins `ip` is
  the one the slot already ran (`file_fields_agree` on `C`, beside
  `fpay_tok_agree` on `pn`), because `off_hold` is applied at `fc_ip C` and
  its two other C-derived arguments were already reconciled by exactly those
  two agreements at exactly the sites that need it.  A new ghost would have
  cost a new `inG` in Σ and could not be re-minted at republication.
- **`tso-port.md` §0.15′: "`proc_priv`'s own chain -- `first_tok` →
  `first_done` → `fs_ready` -- is NOT measured … it is expected to go
  through, but it is the next thing to check."**  CHECKED.  It does not go
  through, and the obstruction is one row: `BioInv.buf_escrow`, an `inv` over
  a ξ-indexed body.  §0.15′'s forced order was right as far as it went and one
  item short: the bcache escrow comes BEFORE (ii) and (iii).
- **`tso-transport-memo.md` §4 step 2** ("`off_hold`/`ftable_res` … After this
  `is_ftable` is a closed term") -- **done, and true.**  §4 **step 5**
  ("`ProofForkretPark.forkret_park_paid` closes") is still refuted, but no
  longer on `is_ftable`: on `proc_priv`.  The memo's §8 correction ("its
  replacement … is what unblocks the park, and it is now the ONLY thing that
  does") is **wrong on the last clause** -- it unblocked one of two rows.
- **`tso-park-protocol-memo.md` §2's "the ξ-dependence of every handle in the
  tree is an artifact of the constant embedding, not of the semantics"**
  (quoted from §0.11′) -- true of handles, and it is worth naming the
  exception the park keeps running into: an `inv` that is not a lock handle
  has no acquire to re-index at, so its body's ξ-dependence is NOT an
  artifact.  `off_hold` was one such (fixed by removing the dependence);
  `buf_escrow` is the other (not fixable that way).

### 0.17′ THE TREE IS FULLY GREEN.  BOTH BARE-INV MEMBERS ARE PARKED RECORDS,
### AND THE PARK'S SECOND CROSSING IS PROVED (2026-08-26)

Executes `tso-absorb-memo.md` in full, plus §0.16′ step (ii) re-derived.
**Two consecutive full VM rounds, ZERO errors; no `Admitted`, no `Abort`,
nothing stubbed.**  `ProofForkretPark.forkret_park_paid` is `Qed`.

#### THE LAW, AND THE ONE INSTANCE THAT WAS MISSING

`TsoCtx.ctx_absorb` — `ctx_deposit`'s dual — is on the sealed surface, with
the twin image the memo proved (`ZZAbsorbProbe.twin_absorb`).  Five lines at
SC, and the ONE structural fact worth restating is why the premise is the
right one: it is HART-LOCAL (`hart_view_lb K ∗ ⌜T ≤ K⌝`, the stable pair
`ctx_resume` already consumes) and says nothing about the source context, so
an opener that knows nothing about the record can supply it — which is
exactly why a bare `inv`, having no acquire and hence no honest `ctx_dom`
producer, can host ξ-indexed data under THIS law and could not under a
`ctx_dom` premise.  The token comes back at the SAME stamp, which is what
makes the claim repeatable (an escrow is opened on every bread/brelse; a
persistent boot deposit is read once per hart).

`TsoCtx.ctx_morph_or` joins `const`/`pointsto`/`word`/`sep`/`exist`/
`big_sepL`/`big_sepM`/`if_then`/`if_else`.  Three disjunctions sit on the
park's critical path (`buf_escrow_body`'s three arms, `first_tok`'s two,
`ofile_slot`'s two) and the kit had none.

**Two new files, both small and both for the reason `IntrDefs.v` cannot hold
them (425 files sit on it):**

- `SieCapCtx.v` — `sie_cap_gpr_own_ctx_acc`, borrow-and-return of the
  thread-of-control token out of `sie_cap`'s fourth conjunct.  SIX call
  sites: the two escrow opens that move bytes, `bio_init_at` at
  main+0x8e, the started deposit at main+0xa2, and the two parkers.
- `CtxRecord.v` — `ctx_parked_inv`, the one-line persistent invariant that
  publishes a NAMED record's parked token.  Member 2 only; member 1
  ∃-closes instead.

#### MEMBER 1 — THE BCACHE ESCROW IS A PARKED RECORD, AND FOUR OF ITS SIX
#### OPENS DO NOT ABSORB AT ALL

```coq
Definition buf_escrow_rec bn V k := (∃ ξ T, ctx_parked ξ T ∗ buf_escrow_body (XI := ξ) bn V k)%I.
Definition buf_escrow     bn V k := inv bioN (buf_escrow_rec bn V k).
```

`buf_escrow` and `bio_ctx` moved below `End BioInv` into a section that
binds NO `CurCtx` (§0.8′ rule 3, sixth occurrence), and both print with no
`CurCtx`: **CLOSED TERMS.**  The six arm-swap lemmas are UNCHANGED — they
are stated on the BODY, and since the body is section-generalized over `XI`
they instantiate at the record's own ξ for nothing.

> **THE MEMO'S SIX-SITE COUNT IS CORRECTED BY MEASUREMENT, and the
> correction halves the work.  Only TWO of the six opens absorb.**  What
> decides it is not which lock is held but WHAT CROSSES THE BOUNDARY.  The
> escrow body's ONLY ξ-indexed rows are `BufOwn.buf_own`'s 1024 `↦ₘ` data
> bytes; every other cell it holds — `b_valid`, `b_dev`, `b_blockno`,
> `b_disk` — is `↦₄`, and **stage 1 does not flip `↦₄`**.  The three
> recycler stores (`escrow_recyc_dev` / `_bno` / `_valid`) and the
> mid-window peek borrow only `↦₄` cells, so they run AT the record's
> ∃-bound ξ with `(XI := ξe)` and hand the token back at the SAME stamp —
> nothing was written at ξ.  Only `bread_tail`'s CHECKOUT and `brelse`'s
> PARK move `buf_own`, and those two absorb and deposit.  At stage 2, when
> `↦₄` flips, the other four become absorb sites too; the two that exist
> are the template, and `ProofBreadParts.buf_escrow_inv`'s header says so.

**AND ONE OPEN HAD TO MOVE, WHICH IS THE TRANCHE'S SECOND SHAPE LESSON.**
`brelse`'s park was bundled into the `+0x02 sd ra,24(sp)` store's ATOMIC
UPDATE — and it cannot stay there:

> **NO DEPOSIT AND NO ABSORB CAN RUN INSIDE A `wp_..._au_...`.**  Both laws
> want the thread's own `own_context`, that token rides inside
> `sie_cap_gpr`, and by the time the atomic-update obligation is proved the
> WP leaf has already consumed the bundle.  There is nowhere to get it
> from.  The fix is not machinery: the escrow swap is a self-contained
> ghost step (open, swap, close, one fupd) and the store it was bundled
> with is to the thread's PRIVATE stack frame, so hoisting the swap to the
> ghost step before the instruction is the SAME program point.  With it
> hoisted the store is the plain `wp_csdsp_s_sconf` its three successors at
> +0x04/+0x06/+0x08 already use, and `escrow_swap_park_now` (which existed
> only to strip the AU's later cheaply) has no caller left.

`bio_init` / `BioInitAt.bio_init_at` **borrow an `own_context`** — the
memo's §3.4 asked this to be checked and neither had one.  Their escrows'
initial content has to be `ctx_deposit`ed into the freshly minted record
context, and a deposit runs at the depositor's authority.  The fold is
`BioInv.escrow_alloc_seq`, an explicit induction rather than a
`big_sepL_mono`: **the running token is EXCLUSIVE and has to be handed from
one buffer to the next**, which a `big_sepL_mono` cannot do.  Callers:
`ProofMain` at main+0x8e (peels it out of `sie_cap_gpr`) and
`FsBoot.fs_boot_bundle` (which has no consumer).

**Cascade, as landed (8 files):** `BioInv` (the two moves, four `CtxMorph`
instances, `escrow_absorb`/`escrow_deposit`/`escrow_alloc_seq`, `bio_init`),
`BioInitAt`, `FsBoot`, `ProofBreadParts` (`buf_escrow_inv` re-typed),
`ProofBread` (five opens), `ProofBrelse` (one open, hoisted), `ProofMain`
(the `bio_init_at` call).  `bio_ctx`/`fs_ready`/`first_tok`/`proc_priv`
arities do not change, so their ~1165 mentions across ~290 files are pure
echo.

#### THE PROBE VERDICTS (memo §10(a)/(b)), RUN FIRST AND CHEAP

```
@buf_escrow      : ... -> bio_names -> bio_view Σ -> nat -> iProp Σ     (no CurCtx)
@bio_ctx         : ... -> bio_names -> bio_view Σ -> iProp Σ            (no CurCtx)
@buf_escrow_body : ... -> CurCtx -> ...      (ξ-indexed, as it should be)
MORPH bio_ctx OK (closed term)
```

`fs_ready` / `first_tok` / `proc_priv` still PRINT a `CurCtx`, and they
should: each has ξ-indexed rows of its own.  What matters is that all three
now carry `CtxMorph` INSTANCES, and they are **proved, not searched** —
`FsReady.fs_ready_morph`, `FirstTok.first_boot_persist_morph` /
`first_fsinit_morph` / `first_tok_morph`, `ProcInv.file_ref_morph` /
`ofile_slot_morph` / `proc_ofiles_morph` / `proc_priv_core_morph` /
`proc_priv_morph`.  **`apply _` cannot find them and that is not a
regression**: `fs_ready` and `first_tok` are `Typeclasses Opaque` (for
correctness, not speed — `FirstTok.v`'s note), and the ∃/big-op rows are
unreachable by search anyway (§0.16′, measured).

> **ξ-PROFILE, MEASURED, WORTH NOT RE-DERIVING.**  With the escrow closed,
> `fs_ready`'s twenty-one conjuncts have EXACTLY ONE ξ-indexed row left: the
> `∃ pd pav pu` carrying `DiskInv.disk_geom`'s three ring-page pointers (its
> `is_lock` beside it is closed, the payload being λ-converted).
> `first_boot_persist` has the same one row; `first_fsinit` has three (the
> 32 raw superblock BYTES and the log spinlock's two `↦₈` words).
> `proc_priv`'s are `proc_fields`, `proc_pt_at`, `first_tok`,
> `ofile_slot`'s `p_ofile ↦₈` and its `file_ref` arm — and
> `ProcInv.cwd_ref` is a CLOSED TERM (`InodeInv.inode_held`), so it frames.
> The memo §9 residual — "`proc_ofiles → ofile_slot` is a reading, not a
> measurement" — is now measured, and it goes through.

#### MEMBER 2 — `started_inv`'s CONTEXT IS NAMED, AND `StartedInv.v` IS
#### UNCHANGED

`BootShared.boot_shared_alloc` mints `ξd` with the pure
`TsoCtx.ctx_parked_alloc`, publishes `CtxRecord.ctx_parked_inv ξd`, and
returns BOTH (one more existential, one more persistent row).

**WHICH OF §5's TWO OPTIONS WON: its own one-line `inv`, carried as a
CONJUNCT of `main_deposit` — not a new row of `started_body`.**  The reason
is the memo's own constraint: `StartedInv.v` must not change, and a new row
of `started_body` IS a change to it.  Riding inside `main_deposit` costs
nothing — `ctx_parked_inv` is persistent, so the package is still
`Persistent`, still rides the one-shot escrow, and still reaches all eight
harts — and it keeps the token's namespace out of `StartedInv`'s.  Landed:

```coq
Definition main_deposit_rows (ξd : CtxId) γd γv : iProp Σ := (∃ ..., ... at (XI := ξd) ...)%I
Definition main_deposit      (ξd : CtxId) γd γv : iProp Σ := (ctx_parked_inv ξd ∗ main_deposit_rows ξd γd γv)%I
```

in a section binding NO `CurCtx`.  Three of the nine rows are ξ-indexed
(`procs_inv`, `disk_geom`, the `kernel_pagetable ↦₈□` word) and
`main_deposit_rows_morph` transports exactly those.  **`StartedInv.v` is
byte-for-byte unchanged**, its `P : iProp Σ` parameter and `{!Persistent P}`
discipline intact.

**THE PRIMARY'S DEPOSIT MOVED OUT OF THE `□`-WAND**, as §5 said it must, and
the sharpest way to state why is the general rule this tranche keeps hitting:
`ctx_deposit` CONSUMES an `own_context`, and **nothing under a `□` can
consume anything**.  So `SpecMain`'s wand is now PURE PACKING with its rows
already at `ξd`, and the deposit happens at the wand's APPLICATION site,
`ProofMain.mn_grp_started` — the last point on main's boot arm that still
holds its `sie_cap_gpr`.  One `ctx_deposit` of the three rows as a `∗`, with
the `CtxMorph` composed AS A TERM (search does not reach through the `∗` to
rows named at an explicit ξ).

**THE SECONDARY ABSORBS AFTER THE FENCE**, at a second open, exactly as §5
predicted: `ProofMainSecondary.ms_spin`'s fall-through opens
`ctx_parked_inv ξd` (the token strips its `▷` by timelessness), absorbs
`main_deposit_rows` into the hart's own context, closes, and hands the rows
to its continuation.  Nothing downstream of `ms_spin` changed: the rows
arrive at the ambient, which is what `ms_inithart_sched` and the scheduler
always wanted.

**Cascade, as landed (8 files):** `SpecMainSecondary`, `SpecMain`,
`ProofMain`, `ProofMainSecondary`, `BootShared`, `BootChain`,
`SystemAdequacy`, plus `CtxRecord.v` new.  `FsCfg` / `FsCfgBoot` / `FsReady`
needed nothing (their mentions are comments).

#### STEP (ii), RE-DERIVED — AND THE SHAPE §0.16′ RECORDED IS EXACTLY RIGHT

`ParkCap.park_cap` gains `∀ (hp : CpuId)` beside its `∀ (ξp : CtxId)` and
takes `own_context (CID := hp) ξp`, borrowed and returned; `park_token` /
`park_chan` / `SpecSyscall.syscall_env` stay hart-free and ξ-free, which is
the whole point of quantifying the hart rather than letting the ambient in.
`park_pkg`'s and `forkret_park_pkg`'s `▷` moved onto their CLOSER ROW ALONE
— the only row that names `W`, hence the only one
`park_token_F_contractive` needs guarded — and `solve_contractive` closes
unchanged.  `ParkCap.park_token_park` and both parkers (`ProofUserinit`,
`ProofKforkB5`) thread the token; each peel is three lines.

#### THE PARK CLOSES: SIX ROWS, ONE DEPOSIT

`forkret_park_paid` hands `procs_inv`, `park_globals`, `is_kstack`,
`proc_priv`, `ctx_cells` and `stack_own` into the child's freshly minted
`XIc` in ONE `ctx_deposit`, with the six-way `CtxMorph` composed as a term,
and the raised stamp `Tc` becomes the record's.  Two mechanics were needed
and both are already-recorded lessons, met again:

- **an ∃ does not frame against an ∃** — the `park_globals` row is an ∃ over
  a discarded cell, so the deposit's payload is built with row-by-row
  `iSplitR`/`iExact`, never one `iFrame` (`ParkCap.park_token_park`'s note,
  fourth occurrence);
- **the resume wand's body must spell `(XI := XIc)`** — with the parker's
  ambient still in scope, `iAssert (own_ctx (p_context …))` silently
  captured it.  §0.15′'s kept body had this latent since the `XIp` reshape;
  it was invisible because the proof was `Abort`ed.

#### AND THE EIGHT-HART ADEQUACY TRAP HAD A SECOND HALF, WHICH ONLY A GREEN
#### PARK COULD REVEAL

§0.16′ answered the trap for `BootChain.boot_hart_res`'s one row and stopped
at `started_inv`.  With both members ruled, `SystemAdequacy` got past
`Hstarted` — and died on `main_locks_raw`, **the sixth premise, which no
build had ever reached.**

> **THE BOOT SUPPLY MUST BE CARVED AT THE BOOT HART'S OWN CONTEXT.**
> `boot_shared_alloc` runs ONCE, inside one fupd, before any hart has a
> thread of control, and everything it hands the BOOT hart —
> `main_locks_raw`, `main_globals_raw`, `main_data_raw`, the dormant proc
> rows, the disk's and kpt's raw cells — is ξ-INDEXED and EXCLUSIVE.  A
> bundle carved at one ξ can serve at most one identity.  The fix is one
> line and no machinery: mint `ξ0` with `own_context_boot (CID := 0%fin)`
> BEFORE the carve and run the carve at `(XI := ξ0)`.  The seven SECONDARIES
> need nothing ξ-indexed from it — `kernel_text`, `kernel_data`,
> `boot_hart_res` and `started_inv` are all closed terms — so one ambient
> serves all eight.  Contrast §0.16′ step (iv)'s ∀-context form, which is
> sound only for a single EXCLUSIVE timestamp-0 cell: pinning the carve is
> cheaper and equally honest, and it scales to a bundle.

#### THE M2 DEBT, AND IT IS SMALLER THAN THE MEMO BUDGETED

**THREE new `TsoCtxShim.hart_view_lb_any` sites, not seven** — the escrow's
checkout (`ProofBread`), the escrow's park (`ProofBrelse`), and the
secondary's absorb (`ProofMainSecondary`) — joining `ProofSwtch`'s and
`ProofAcquire`'s.  The four recycler opens need none, because they absorb
nothing.  **`TsoCtxShim.ctx_dom_sc` is NOT used at any of them**, which is
the point of choosing absorb over the cheaper ∃-close: a `ctx_dom` at a bare
`inv` would have no honest producer and would be a permanent lie, while
absorb's premise is hart-local and an acquire that knows nothing about the
escrow can still supply it.  The M2 sweep that makes `K` real is ONE item
serving swtch-resume, both escrow sites and the started absorb alike, and
`SpecAcquire` already exports `(∃ K, hart_view_lb K)` to every lock winner.

#### MEMO CORRECTIONS

- **`tso-absorb-memo.md` §3.3 and §3.4's "the 6 open sites bracketed
  absorb→work→deposit"** — **corrected by measurement: FOUR of the six need
  neither.**  §3.3 is right that the six opens are not under one lock and
  right that the escrow bridges two lock disciplines; what it did not check
  is that the recycler's three stores and the mid-window peek move only
  `↦₄` cells, which stage 1 leaves unflipped.  They run at the record's own
  ξ with `(XI := ξe)` and nothing else.  The memo's own §3.1 measurement
  ("the ONLY ξ-indexed row is `buf_own`") is what implies this; §3.3 did not
  draw the consequence.
- **`tso-absorb-memo.md` §3.4's "check this one: `bio_init_at` … must hold
  an `own_context` … if it does not, its parked context has to be threaded
  in from its caller."**  CHECKED: neither `bio_init` nor `bio_init_at` had
  one.  The landed answer is neither of the memo's two — the *token* is
  borrowed, not the *context* threaded: both allocators take
  `own_context cur_ctx` and hand it straight back, and mint one fresh parked
  context PER BUFFER inside `escrow_alloc_seq`.  Threading a single parked
  context in from the caller would not have worked: thirty escrows are
  thirty invariants and `ctx_parked` is exclusive.
- **`tso-absorb-memo.md` §6's "used at the 6 escrow opens, the 1 started
  claim, and the park's step (ii)"** — the accessor has SIX call sites, but
  not those six: two escrow opens, `bio_init_at`, the started deposit, the
  started absorb, and the two parkers.  The count is right by accident.
- **`tso-absorb-memo.md` §5's two options for the parked token ("a new row
  of `started_body` outside its disjunction, or its own one-line `inv`")** —
  the second won, and the first is REFUTED by the memo's own constraint: a
  new row of `started_body` is a change to `StartedInv.v`, which §5 and the
  §11 ruling both require to stay unchanged.
- **`tso-absorb-memo.md` §7's "Seven new sites"** — THREE.  See the M2
  section above.
- **`tso-port.md` §0.16′ step (iii)'s recommended shape ("∃-close the
  context INSIDE the escrow body … and then every OPENER needs a `ctx_dom`
  from the ∃-bound ξ to its own")** — the ∃-close is right and landed; the
  `ctx_dom` is not, and the memo's §7 says why (a bare `inv` has no acquire).
  What the openers get instead is `ctx_absorb` against their own hart's
  view.  And *most* openers need neither.
- **`tso-port.md` §0.16′ step (iv)'s "THE EIGHT-HART ADEQUACY TRAP, stated
  once"** — stated once, but it had TWO halves, and only the first was
  visible while the park was red.  The second is the boot supply, above.

**RED SET: EMPTY.**  `make -f CoqMakefile -j180 -k` exits 0 twice
consecutively.  The remaining distance to the REAL `TsoCtxTwin2` swap is
unchanged and is §0.10′'s four items: the `tsoG` ghost-class threading,
replacing the `_def` bodies and re-proving the law surface (every law now has
a named twin image, `ctx_absorb` included), the kit re-proofs where
`TsoCtxShim` bridges sit, and the M2 protocol sweep — whose worklist is
exactly the five `hart_view_lb_any` sites and the `ctx_dom_sc` uses.

---

### 0.18′ THE LOCK KIT CONVERGES ON THE PARKED-RECORD IDIOM (2026-08-26)

Executes `tso-absorb-memo.md` §12 (owner-ratified).  **The lock's two
transports are now the same two laws the escrow and the boot deposit run on:
release is `ctx_deposit`, acquire is `ctx_absorb`, and `ctx_dom` has left the
lock's transport path entirely.**  Eight files, ZERO client files; a CLEAN
1331-file VM round at exit 0 and two consecutive rounds after it.

#### THE STATEMENT CHANGES, OLD vs NEW

```coq
(* WpLock.v -- the free arm *)
-  ... ∗ lock_frag γ None ∗ (∃ ξ : CtxId, R ξ)          ∨ ⌜st ≠ None⌝ ∗ ...
+  ... ∗ lock_frag γ None ∗ lock_pay R                  ∨ ⌜st ≠ None⌝ ∗ ...
+  Definition lock_pay R := (∃ (ξ : CtxId) (T : nat), ctx_parked ξ T ∗ R ξ)%I.

(* WpLock.v -- the finisher, and the destroyer's return trip *)
-  ... -∗ (∃ ξ : CtxId, R ξ) -∗ |={E ∖ ↑lockN, E}=> Out
+  ... -∗ lock_pay R          -∗ |={E ∖ ↑lockN, E}=> Out
-  lock_finisher_destroy : (lock_frag γ None -∗ (∃ ξ, R ξ) ==∗ D ∗ Out) -∗ ...
+  lock_finisher_destroy : (lock_frag γ None -∗ lock_pay R ==∗ D ∗ Out) -∗ ...

(* WpLock.v -- the creators.  [newlock] / [lock_inv_alloc] / [WpLockAt.newlock_at]
   gain an IMPLICIT class binder (free at every call site, exactly as
   SpecAcquire's did in §0.6′); the two DELAYED forms, whose R is chosen
   inside the iProp, carry it as a ⌜⌝ premise (3 call sites). *)
-  Lemma newlock E lk s (R : CtxId → iProp Σ) : ...
+  Lemma newlock E lk s (R : CtxId → iProp Σ) `{!CtxMorph R} : ...
-  ... ==∗ ∃ γ, ∀ R,             R cur_ctx ={E}=∗ is_lock γ lk s R.
+  ... ==∗ ∃ γ, ∀ R, ⌜CtxMorph R⌝ -∗ R cur_ctx ={E}=∗ is_lock γ lk s R.
+  Lemma lock_pay_intro (R) `{!CtxMorph R} : R cur_ctx ==∗ lock_pay R.
```

**`SpecAcquire` and `SpecRelease` DID NOT MOVE — not one character.**
`is_lock`, `locked`, `lock_openable`, `lock_state`, the two acquire tiers,
the three release forms, `lock_finisher_close`: all unchanged.  Only
`WpSconfLock`'s five internal `(∃ ξ : CtxId, R ξ)` occurrences and
`ProofAcquire`'s private loop lemma re-spell the payload as `lock_pay R`,
and their PROOFS are untouched (the leaves carry the payload opaquely).

The two transport sites:

```coq
(* ProofRelease.wp_release_gen_sconf -- was one iAssert, is now the deposit *)
-  iAssert (∃ ξ : CtxId, R ξ)%I with "[HR]" as "HR"; first by iExists cur_ctx.
+  iDestruct (sie_cap_gpr_own_ctx_acc with "Hcg") as "[Hrun Hcgb]".
+  iMod ctx_parked_alloc as (ξc) "Hpk".
+  iMod (ctx_deposit R cur_ctx ξc 0%nat with "Hrun Hpk HR") as "(Hrun & Hdep)".
+  iDestruct "Hdep" as (T') "(_ & Hpk & HR)".
+  iDestruct ("Hcgb" with "Hrun") as "Hcg".
+  iAssert (lock_pay R) with "[Hpk HR]" as "HR". { iExists ξc, T'. iFrame. }

(* ProofAcquire.wp_acquire_gen_fresh_sconf -- was the ctx_dom_sc morph *)
-  iDestruct "HRes" as (ξ0) "HRes".
-  iPoseProof (ctx_dom_sc ξ0 cur_ctx) as "Hdom".
-  iDestruct (ctx_morph ξ0 cur_ctx with "Hdom HRes") as "[_ HRes]".
-  iAssert (∃ K, hart_view_lb (CID := CIDpo) K)%I as "Hlb". { iExists 0%nat. ... }
+  iDestruct "HRes" as (ξ0 T0) "[Hpk0 HRes]".
+  iAssert (hart_view_lb (CID := CIDpo) T0)%I as "#HK0";
+    [ iApply hart_view_lb_any | ].
+  iAssert (∃ K : nat, hart_view_lb (CID := CIDpo) K)%I as "Hlb";
+    [ iExists T0; iExact "HK0" | ].
+  iDestruct (sie_cap_gpr_own_ctx_acc (CID := CIDpo) with "Hcg") as "[Hrun Hcgb]".
+  iMod (ctx_absorb (CID := CIDpo) R ξ0 cur_ctx T0 T0 ltac:(lia)
+          with "Hrun HK0 Hpk0 HRes") as "(Hrun & _ & HRes)".
+  iDestruct ("Hcgb" with "Hrun") as "Hcg".
```

Acquire uses the SAME receipt it hands the client: `Hlb` is minted at
`K := T0`, the record's own stamp, so the absorb's pure tie is reflexivity
and there is exactly ONE receipt object on the path.  Both the running token
and the receipt are at `CIDpo`, the hart that won the AMO — the entry hart's
would be the wrong one, since the prologue may have migrated.

#### THE TOKEN-TRAVEL CHOICE: NEITHER OF §12's TWO, AND THE MEASUREMENT SAYS WHY

§12 offered "the token travels with the holder" or "it sits in the held arm".
**Both are refuted, and the same wall refutes them: `ctx_absorb` needs the
token, the payload AND an `own_context` IN ONE HAND, and `own_context` is
only ever in hand OUTSIDE a WP leaf.**  Written out:

- *Held arm.*  If the token stays in the invariant, the acquirer has nothing
  to absorb WITH.  Putting the absorb inside the AMO leaf instead would then
  force release's `ctx_deposit` inside the word-clear store's ATOMIC UPDATE
  (`WpSconfLock.wp_sw_zero_lockfin_s_sconf`), and §0.17′'s measured rule —
  NO DEPOSIT AND NO ABSORB CAN RUN INSIDE A `wp_..._au_...`, because the
  bundle carrying `own_context` has already gone to the leaf — kills it.
  Rescuing it needs a state-INDEXED held arm (the token present only at
  `Some (i, true)`) plus two more lock leaves re-plumbed.
- *Travels with the holder.*  The holder between acquire and release is
  arbitrary client code, so the token would have to ride inside `locked`
  (the acquire postcondition itself is an exported statement).  That is a
  resource change under the 83 files that name `locked`, and it re-plumbs
  the same two cpu-word leaves anyway (`lock_setcpu` would have to consume a
  token, `lock_clrcpu` to yield one).

**WHAT LANDED: a record is minted PER PUBLICATION — at release — and
abandoned by the winner that claims it.**  `ctx_parked_alloc` is pure and
`ctx_deposit` raises the fresh record's stamp to cover exactly the facts
this release publishes, which is the honest per-generation tie; nothing
needs a stamp that ratchets across generations, because a later acquire's
receipt dominates a later release's store.  Cost: zero change to `locked`,
zero change to the cpu-word leaves, zero client files.

#### THE STAMP TIE, RECORDED BECAUSE IT IS LOAD-BEARING AT CUTOVER

`ctx_deposit` returns some `T'`; what makes the record claimable is
`T' ≤ t_release` (the log position of release's word clear) — **≤, not =**:
every fact deposited was written before that store.  Today it is stronger
than needed, because acquire's AMO drains to the top of the log and its
receipt dominates every stamp, so the SC proof picks the trivially valid
pair (`K := T`, reflexivity).  It becomes load-bearing exactly when an
acquire path does NOT drain to top — a plain-load test-and-test-and-set spin
before the AMO, or any acquire-like pattern built from plain loads plus the
message-passing argument.  Same shape as the boot `started` flag and the
kernel-page-table publication: **the lock bit IS the flag.**  The comment
lives at `WpLock.lock_pay` and at both transport sites.

#### THE SHIM LEDGER: ONE DIES, TWO SURVIVE, ONE IS NEW

- **`ProofAcquire`'s `ctx_dom_sc` — DEAD.**  The acquire-side transport is
  now `ctx_absorb` against a hart-local receipt.  This was the whole point:
  `ctx_dom_of_parked`, the one lock-leaf step that reaches into the state
  interpretation for at-the-top evidence, collapses into "receipt + absorb".
- **`ProofAcquire`'s `hart_view_lb_any` — SURVIVES**, and is the SAME M2
  item `SpecAcquire` already owed.  It is now instantiated at the record's
  stamp rather than at 0.
- **`ProofRelease`'s `ctx_dom_sc` — SURVIVES, at the CANCELLING instance
  only**, and the reason is §0.17′'s rule met again: the destroyer's
  completion wand is cashed INSIDE the word-clear store's atomic update,
  where no `own_context` is in scope, so its return trip (`lock_pay R` back
  to `R cur_ctx`) cannot be an absorb.  The record's token is dropped there
  — the lock is being DESTROYED, so nothing will ever claim it.  The
  ORDINARY release path has no shim at all.
- **`WpLock.lock_pay_intro` — NEW, and it is the one this tranche adds.**  A
  `newlock` caller holds its payload at its own context and has no
  `own_context` to run `ctx_deposit` with; giving the creators one means
  borrowing the running token through **19 direct call sites** (12 in the
  `newlock` / `newlock_d` / `newlock_delayed` family, 7 more at
  `WpLockAt.newlock_at`) and every creator wrapper above them
  (`new_sleeplock*`, `new_tickslock`,
  `delayed_locks_alloc`, `pipe_alloc`, `bcache_alloc`, …), exactly the way
  `BioInv.bio_init` already does.  That cascade is priced and DEFERRED: the
  creator transport is `ctx_dom_sc`, quarantined at ONE named lemma, and
  when the shim burns that lemma is the single compile error naming the
  whole cascade.  Net ledger: 2 `ctx_dom_sc` uses before, 2 after, but the
  surviving pair is at a DESTROY path and a CREATE path — never on the
  running acquire/release transport, which is now honest end to end.

#### THE RECEIPT-THREADING ITEM IS REFUTED, AND THE REFUTATION IS THE RULE

The tranche was also asked to retire `hart_view_lb_any` at `ProofBread`,
`ProofBrelse` and `ProofMainSecondary` "where an HONEST receipt is in scope".
**Measured: at none of the three is one in scope, and — the sharper half —
even if one were, it could not be used.**

> **A RECEIPT AND A RECORD'S STAMP CANNOT BE TIED AT SC.**  `ctx_absorb`'s
> premise is `hart_view_lb K ∗ ⌜T ≤ K⌝` where `T` is EXISTENTIALLY BOUND BY
> THE RECORD (`iDestruct "Hrec" as (xie Te) "…"`).  An honest receipt fixes
> `K` independently, at the acquire that minted it; nothing at SC relates
> the two, and the shim's value is precisely that it lets the site pick
> `K := T`.  The tie is what the M2 sweep must MANUFACTURE (at TSO: the
> record's stamp was set by a deposit that happens-before the release the
> acquirer synchronised with), not something threading can supply.

And the scope half, checked: `ProofBread.bd_tail` and
`ProofBrelse.wp_brelse_sconf` take no receipt premise and have no acquire in
their own instruction stream before the open (brelse's `acquire(&bcache.lock)`
is 300 lines LATER); `SpecAcquiresleep.v` contains no `hart_view_lb`,
`CtxMorph` or `cur_ctx` at all, so the sleeplock chain exports nothing —
threading it would be a sleeplock-surface change on top of an unprovable
tie.  `ProofMainSecondary`'s secondary hart has no acquire whatsoever.
**All five `hart_view_lb_any` sites therefore stay, and they are ONE M2
worklist item, not five.**

#### CASCADE, AS LANDED (8 files, ZERO client files)

`WpLock` (the free arm, `lock_pay`, `lock_pay_intro`, the finisher, four
creators), `WpLockAt` (`newlock_at`), `WpSconfLock` (five payload
re-spellings, no proof changes), `ProofAcquire` (the absorb + the private
loop lemma's payload), `ProofRelease` (the deposit + the cancel bridge),
and three CREATOR sites for the delayed forms' new `⌜CtxMorph R⌝` slot:
`BioInv` (bcache), `PipeInv` (pipe), `SpecProcinit` (`delayed_locks_alloc`
and `procs_inv_alloc`).  Every one of the three discharges it with
`apply _`.

**SLEEPLOCKS INHERIT WITH NO EDIT — verified, not assumed.**
`SleepLock.is_sleeplock_gen` is `is_lock γl (sl_lk slk) "sleep lock"
<{ sl_res_gen γ slk R H }>`, and a `<{ }>` payload's `CtxMorph` is
`ctx_morph_const_pay`, found by search.  `SleepLock.v`, `SleepLockAt.v` and
every sleeplock proof are byte-for-byte unchanged.

**Rounds: the incremental round rebuilt the whole `WpLock` cone (672 files)
at EXIT 0; a CLEAN round (`rm -f iris/*.vo` first) rebuilt all 1331 at
EXIT 0; two further consecutive rounds after the receipt tidy-up, EXIT 0.
No `Admitted`, no `Abort`, no `Axiom`.**

#### MEMO CORRECTIONS

- **`tso-absorb-memo.md` §12's "the token travels with the holder (or sits
  in the held arm — implementer's pick, record which)"** — **BOTH REFUTED
  by measurement, and the landed shape is a third one: a record per
  PUBLICATION, minted at release and abandoned at acquire.**  The reason
  both fail is one wall — `ctx_absorb` wants token + payload + `own_context`
  in one hand, and `own_context` is only in hand outside a WP leaf
  (§0.17′'s rule) — so a token that survives the held phase forces either a
  deposit inside the word-clear store's atomic update or a resource change
  to `locked`.  §12's own stamp analysis is what makes the third shape
  correct: the tie is `T' ≤ t_release`, a PER-PUBLICATION fact, so nothing
  needs a stamp that ratchets across generations.
- **`tso-absorb-memo.md` §12's "Exported statements (`is_lock`,
  `SpecAcquire`/`SpecRelease` shapes) should not move — the ~180 client
  files are expected untouched."** — CONFIRMED exactly, and the count is
  ZERO client files.  What §12 did not foresee is that the CREATORS move:
  a parked record has to be minted from the payload, and `newlock` has no
  `own_context`.  That is the `lock_pay_intro` entry above.
- **`tso-absorb-memo.md` §12's "acquire = `ctx_absorb`, its premise
  discharged from the AMO receipt (`SpecAcquire` already exports
  `∃ K, hart_view_lb K`)"** — right, and sharper than stated: the exported
  receipt and the absorb's receipt are the SAME object, minted once at
  `K := T`.  There is no second mint and no `hart_view_lb_le` step.
- **The tranche brief's "three sites use `hart_view_lb_any` where an HONEST
  receipt is in scope — ProofBread …, ProofBrelse …, ProofMainSecondary"** —
  **REFUTED on both halves**: no receipt is in scope at any of the three,
  and the pure tie `T ≤ K` between a record's ∃-bound stamp and an acquire's
  fixed `K` is not SC-provable in any case.  See the block above; this is
  an M2-sweep obligation, not a threading one.
- **`tso-port.md` §0.6′'s "The two shim steps in `ProofAcquire`
  (`ctx_dom_sc` for the ∃ξ→cur_ctx morph at the win, `hart_view_lb_any` for
  the receipt) are exactly where the cutover kit's direct proof puts the
  AMO's honest evidence."** — half of it is now HISTORY: the `ctx_dom_sc`
  step is gone, and what the cutover kit has to supply at the AMO is only
  the receipt.  `TsoCtxTwin2.ctx_dom_of_parked` is no longer on the lock's
  critical path at all.

**RED SET: EMPTY.**  The distance to the real `TsoCtxTwin2` swap is
§0.10′'s four items, with the fourth (the M2 protocol sweep) now a strictly
smaller and better-defined job: FIVE `hart_view_lb_any` sites, all wanting
the same thing (tie a record's stamp to the claiming hart's view), and TWO
`ctx_dom_sc` uses, neither on a running transport.

### 0.19′ M1 STAGE 2 IS LANDED — ↦₂/↦₄ ARE CONTEXT-INDEXED, AND M1 CLOSES (2026-08-27)

Replays `tso-machine-flip.md`'s A6.15 on THIS tree.  The tower and the
notation flip are A6.15's verbatim; **the FALLOUT is not, and the difference
is the whole content of this section**: A6.15 was measured in the flip
workspace, a copy of the tree from BEFORE §0.11′–§0.18′, so it never met the
park protocol, the λ-payload sweep, or §0.16′'s closed-term rulings.  On this
tree the same flip walks straight into them.

#### THE TOWERS AND THE NOTATIONS

`TsoCtx.v` gained `ctx_word2_pointsto` and `ctx_word4_pointsto`, each
character-for-character the in-tree 8-byte tower at width 2/4, with
`_unfold` / `_aligned_p` / `_bytes` / `_intro` / `Timeless` (+ the `ktier`-typed
`_timeless'`) / discarded-`Persistent` (+ `_discarded_persistent'`) /
`_frac_split` / `_half` / `_half_split` / `_half_join` / `_persist` /
`_agree` (cross-context) / `_ktier_mono`, plus `ctx_morph_word2` /
`ctx_morph_word4` beside `ctx_morph_word`, and one new byte law the two
`ktier_mono`s run on: **`ctx_ktier_mono`** (`mem_ktier_mono`'s image, a LAW of
the surface, not a shim).  All four dfrac spellings of `↦₂` and `↦₄` are
re-declared at the towers, bracket form and `dq custom dfrac at level 1`
included.  Neither tower is sealed, for the 8-byte one's reason.

`TsoCtxShim.v` gained `ctx_word{2,4}_shim` / `_of_mem` / `_to_mem` (the
gen_heap bridges) and **`ctx_word{2,4}_reindex`** — the SC-only ξ→ξ' re-index,
new in this stage; the SHIM LEDGER below says where its twenty uses are and why
each is an M4 entry.

**`↦ₛ` did not flip AT THIS STAGE, and the reasons recorded here are
REFUTED by §0.21′/§0.22′** (both read the tier off its rodata instances
only, and the kernel writes `p->name` at runtime).  It flips in stage 3;
after THAT stage the deliberately-raw tiers are exactly **`↦ₓ` (text),
`↦ᵣ` (registers) and `↦ₚ` (the physical/image tier)**.

#### THE WAVE: 31 ROUNDS, NOT A6.15's 14

A6.15 measured 14 rounds with ONE new error file per round.  Here it took
**31 full VM rounds**, with peaks of 22 red files.  The extra classes are all
CONSEQUENCES OF WORK THAT LANDED AFTER THE FLIP WORKSPACE WAS COPIED:

| class | A6.15 | here |
|---|---|---|
| `word{2,4}_pointsto_<law>` → the `ctx_` twin (+ a leading ξ `_`) | yes | yes, ~25 files |
| `?XI : CurCtx` binders on decls/sections | yes | yes, ~40 decls |
| genuine gen_heap seams (leaf/boot) → shim | yes | yes, and MORE (below) |
| crossings DELETED, not converted | yes (PageFields, ByteBuf, InodeInv) | yes, plus DinodeSlot, DiskBoot, ProofArgraw, ProofDirlookupParts, ProofFilestatParts, ProofFsinit, ProofKexecSeam, ProofKexecTail, ProofDirlink, ProofKwait, ProofSysUnlink, ProofSysPipe |
| **λ-CONVERTED PAYLOADS** | none | SIX (below) |
| **closed terms that had to be re-closed** | flagged as an open question | FOUR `inv` bodies + `boot_hart_res`; one cost a 33-minute crawl |
| **`CtxMorph` chains that had to be built** | none | ~30 instances across 8 files |

#### THE PAYLOAD CONSEQUENCE, AND THE PARK ROWS

§0.12′ classified `wait_res` / `ticks_res` / `nextpid_res` as record-carried
*because* `is_lock γ lk s R` was a closed term for them.  The flip moves that
ground.  MEASURED, per payload:

| payload | before | after the flip | what was done |
|---|---|---|---|
| `WaitInv.wait_res` | ξ-free (`↦₈` under a file that does NOT import TsoCtx) | **still ξ-free** | nothing |
| `TicksInv.ticks_res` | ξ-free (`a_ticks ↦₄`) | ξ-INDEXED | λ-converted; `is_tickslock` moved below the section |
| `SpecAllocpid.nextpid_res` | ξ-free (`alp_nextpid ↦₄`) | ξ-INDEXED | λ-converted at all 9 `<{ }>` sites; section gained the binder |
| `SleepLock.sl_res_gen` | ξ-free | ξ-INDEXED (the `locked` word and the `pid` cell) | λ-converted; the file SPLIT into `SleepLock` / `SleepLockHandle` (no ambient) / `SleepLockRes` |
| `BioInv.bcache_res` | ξ-free (§0.14′'s measurement) | ξ-INDEXED (`bio_slot_res` is all `↦₄`) | λ-converted, 15 sites |
| `LogInv.log_res` | ξ-free | ξ-INDEXED (three counters + the header cells) | λ-converted via a new `log_pay`; the section SPLIT so the λ is spellable |
| `IcacheInv.itable_res`, `IcacheEscrow.itable_res2` | ξ-free | ξ-INDEXED (the `inode_ident` halves) | λ-converted via `itable_pay` / `itable_pay2`; both sections split |

**THE PARK ROWS SURVIVE, AND THE EXPECTED OUTCOME IS THE ONE THAT HAPPENED.**
`ut_park_caps`'s three lock handles (`wait`, `ticks`, `nextpid`) are still
CLOSED TERMS and still ride in the record: the wait lock never moved, and the
other two are closed again *because* their payloads were λ-converted.  Not one
line of `UsertrapRes.v`, `UtResFits.v` or `ParkCap.v` changed, and
`ut_res_bare_park` / `usertrap_res_bare_park` are green untouched.  §0.12′'s
table needs one edit and no re-ruling: the reason those three rows cross is
now "their payloads are λ-converted", the same sentence the console, pipe,
disk and ftable rows already carry.

**AND ONE RULING THE FLIP FORCED AT THE LOCK ITSELF.**  `WpLock.lock_word` —
the 4-byte `lk->locked` cell inside `lock_inv` — would have become
AMBIENT-indexed, which drags a context into the persistent `is_lock` handle
and would have falsified the park rows outright, with no payload conversion
able to repair it.  It is now **∃-CONTEXT**, exactly like `lk_cpu_res`'s owner
cell and for §0.8′ ruling 2's reason, with `lock_word_acc` as the bridge; every
client-facing spelling (`lk ↦₄ 0` in and out of the creators/destroyers) is
unchanged.  RAW was considered and REJECTED on a cutover argument worth
keeping: the lock word is only ever READ exclusively (both `amoswap`s take the
machine's exclusive arm, which reads flat memory at the top of the log), but
release's word clear is a STORE, and a store owes `Wobl_ram`, whose γts update
needs the cell's timestamp element — a cell with no ledger residue cannot be
stored to (`tso-machine-flip.md` A6.16).

#### FOUR BARE `inv` BODIES HAD TO BE RE-CLOSED, AND ONE COST 33 MINUTES

A6.15 flagged "ctx facts inside a bare `inv`" as a STANDING QUESTION it did
not have to answer.  On this tree it is not a question, it is the blocker
class, because `FsReady.fs_ready` and `FirstTok.first_boot_persist` carry
those handles and owe `CtxMorph`.  The rule that came out of it, and it is the
same rule three times over: **an `inv`/`cinv` body must be a CLOSED TERM, so
its cells go ∃-CONTEXT with a named `_acc` equation, and the ∃-ELIMINATION is
the SC-only step.**

- `IcacheInv.itable_body` — `iref_cells` became `[∗ list] k, iref_cell k …`
  with `iref_cell_acc`; every accessor keeps its old statement through
  `iref_cells_acc_eq`.
- `FileInvDefs.off_content` — `off_cell` and `off_mark` are ∃ now, with
  `off_cell_acc` / `off_resident_acc` / `off_raw_acc` / `off_mark_acc`.  This
  is EXACTLY the stage-2 work `FileInvDefs.v`'s own header predicted
  (§0.16′ step (i)), landing where it said it would — `FileOff`'s two borrow
  lemmas — except that the header's "their `ctx_dom` premise" is, for now, the
  shim's re-index: `ctx_dom`'s honest producer left the lock's transport path
  at §0.18′, so the honest form is the borrow window's `ctx_absorb`, an M4
  entry.
- `IcacheEscrow.ic_escrow_body` — NOT re-closed, and this is the one place a
  different answer was cheaper and is also honest: the body keeps its ambient
  index and the HANDLE is transported by **Iris's `inv_iff`** against a
  two-way `ic_escrow_body_reindex`, which is `TsoCtxShim.ctx_dom_sc` applied to
  the body's own (new) `CtxMorph`.  That buys `ic_escrows_morph` for
  `fs_ready` and `first_boot_persist` at the cost of ZERO changes at the ~27
  opener sites.  Each use of the equivalence is an M4 entry; the honest form
  is the escrow-as-parked-record idiom `BioInv.buf_escrow` already runs.
- `StartedInv.started_body` — **the 33-minute crawl.**  `started_inv` is a
  bare `inv` and the ADEQUACY proof hands the SAME persistent handle to every
  hart at its OWN freshly-minted identity (`SystemAdequacy`'s per-secondary
  `own_context_boot`).  With an ambient index in the body that hand-off is a
  FALSE goal, and it failed the way §0.8′'s landmine says: by CRAWLING.
  `SystemAdequacy.v` went from **3.6 s** (optimization.md's measured number,
  without `Print Assumptions`) to **33 minutes and still running** on one
  `iApply (boot_hart_secondary …)`.  `started_cell` + `started_cell_acc` closes
  the body; `ProofMain` / `ProofMainSecondary` pay `started_cell_acc` at their
  two peek-opens of the invariant.

**AND THE SAME SENTENCE HID A SECOND CROSSING — THE EIGHT-HART ADEQUACY TRAP,
A THIRD TIME.**  Closing `started_body` did not fix the crawl, it only moved
the failure: `BootChain.boot_hart_res` carries `cpus[cid].noff` and
`cpus[cid].intena`, and those are `↦₄`.  §0.16′ step (iv) had already made
that bundle a CLOSED TERM (the `proc` row is `∀ ξ, cur_proc (XI := ξ)`,
minted under the ∀ by `BootShared.boot_hart_pre`) precisely because
`boot_shared_alloc` carves all eight bundles under ONE ambient while the harts
run at eight distinct `own_context_boot` identities — and stage 2's flip
silently un-closed it.  Fixed by the ruling that was already there: both cells
stay RAW in `BootShared.cpu_slot_raw` / `boot_hart_bss` and cross **under the
∀**, beside `proc`, in `boot_hart_pre`; `boot_entry_bridge` instantiates all
three at `cur_ctx`.  Sound for `proc`'s two reasons — exclusive (so the ∀ is
not duplicable, it is not under a `□`) and timestamp-0 boot-image cells,
§0.4 item 6's one sanctioned case.  `SystemAdequacy.v` is back at seconds.
**THE STANDING LESSON:** every `∀ ξ`-quantified or ∃-context row that an
earlier stage introduced is a row a LATER tier flip can silently re-index —
when a family flips, re-read the closed-term bundles that mention its width,
not only the files that fail.
  **THE DIAGNOSTIC RULE, restated because it earned it:** a build round whose
  only remaining worker has been alive for tens of minutes is not a slow file,
  it is a false ξ-crossing; `ps -o pid,etime,rss -C rocqworker --sort=-etime`
  finds it and `coqc -time` names the sentence — and if the sentence is one
  big `iApply`, split it into `iPoseProof` + one `iSpecialize` per premise:
  the crawl becomes an ordinary "cannot instantiate" error naming the row.

Also re-closed, though not an `inv`: **`IcacheRef.inode_held_short_any`**, the
∃-context wrapper for `FileInvDefs.inode_pay`'s `cinv` body.  §0.16′'s whole
point is that `inode_pay` / `file_core` / `file_payload` / `file_pay` are
closed terms; after the icache flip the CINV BODY had to be closed by an ∃
while the four wrappers stayed ξ-indexed-but-TRANSPORTABLE (a `CtxMorph` chain
`inode_ident → inode_shr_gen → inode_shr_held_gen → inode_pay → file_core →
file_payload → file_pay`, all new).

#### THE ICACHE CLUSTER: A6.15's RULING HOLDS, ITS COST DOES NOT

A6.15's decision — flip `IcacheRef`, the file that OWNS `inode_ident`'s two
`↦₄` cells, rather than re-declare `↦₄` raw per file — is RE-DERIVED and
TAKEN here for the same reason (a `Local Notation` only moves the
disagreement, and a non-`Local` one silently un-flips importers).  Eleven
files follow it, as A6.15 said.  What A6.15 could not see is the CASCADE
above: on this tree the same ruling drags in `inode_held_short_any`, the
`file_pay` morph chain, `itable_pay`/`itable_pay2`, and `ic_escrows_morph`.
The ruling still looks right — the alternative is the whole fs-invariant
cluster raw, and then every leaf that reads an inode cell is a seam — but the
price is an order of magnitude larger than A6.15 records, and a re-run should
budget for it.

**`BreadLru` IS GENUINELY MIXED, exactly as A6.15 says.**  It takes the flip
(the import, plus a binder on `Section BreadSlots` for `bio_slot_res`'s `↦₄`
cells) and its SIX `bcache_lru` link words — `BcacheInv`'s, which stays raw —
now spell `word_pointsto` explicitly.  Re-derived, not assumed: the six are in
`Section BreadLru`, at `bnext`/`bprev`, and they are `↦₈`, not `↦₄`.

`BitmapInv` is a file A6.15 does not mention and that this tree needs: its
`bm_alloc_res` holds the two frozen superblock cells at `↦₄`, so it takes the
import and a section binder.

#### THE BOOT TIER STAYS RAW, AND THAT IS WHERE THE SHIM GREW

`BootCarve` / `BootCarveMain` / `BootShared` are boot tier and keep the raw
notations (the eight-hart adequacy trap; they talk through qualified
`TsoCtx.…` names).  Their `↦₈` cells already crossed through
`ctx_word_of_mem`; the `↦₄`/`↦₂` ones now cross the same way, ~50 sites.
**A route that looked cheaper was tried and REVERTED**: flipping
`BootCarve`'s five cell lemmas to yield the ctx form directly would have made
all 50 call sites work unchanged, but `BootCarveMain`'s own intermediate
definitions (`dinfo_raw`, `dops_raw`, `file_node_raw`, `bpay_raw`) are stated
with the RAW notation, so the mismatch just moves inside that file.  The
boundary belongs where the `↦₈` boundary already is.

#### SHIM LEDGER

| | before | after |
|---|---|---|
| files naming `TsoCtxShim` | 76 | 73 |
| `TsoCtxShim.<lemma>` uses | 275 | 399 |

The file count went DOWN and the use count went UP, and both numbers are the
story.  NINE files lost the shim entirely — `ByteBuf`, `DinodeSlot`,
`DiskBoot`, `InodeInv`, `PageFields`, `ProofArgraw`, `ProofDirlookupParts`,
`ProofFilestatParts`, `ProofFsinit` — because their crossings were
`↦₂`/`↦₄`-vs-`↦ₘ` seams that simply CEASED TO EXIST (A6.15's payoff, and it
reproduced).  SIX files gained it — `FileInvDefs`, `IcacheEscrow`,
`IcacheInv`, `IcacheRef`, `ProofAcquiresleep`, `StartedInv` — every one for an
∃-context elimination this stage introduced.  The +124 uses are almost entirely
the boot tier's new `↦₄`/`↦₂` crossings (75 `ctx_word4_of_mem`, 51
`ctx_word4_to_mem`, 6 `ctx_word2_of_mem`) plus 20 `ctx_word4_reindex`.  **The reindex uses ARE the new M4 worklist**, and they sit in six
files: `ProofBread` (14, across the three recycler `wp_…_au_…` windows — no
absorb can run inside one, §0.17′'s rule), `FileInvDefs` (2,
`off_cell_acc`/`off_mark_acc`), `IcacheRef` (2,
`inode_held_short_any_intro`/`_elim`), `IcacheInv` (1, `iref_cell_acc`) and
`StartedInv` (1, `started_cell_acc`).  `WpLock.lock_word_acc` needs none: its
∃ is eliminated inside the file that owns the cell.

#### WHAT M1 LEAVES BEHIND

M1 stage 2 is complete; **stage 3 (`↦ₛ`, §0.22′) is what actually closes
M1**.  Deliberately raw after it, with the reasons recorded at their
definitions: **`↦ₓ`** (kernel text — timestamp-0, context-free by the port's
ruling), **`↦ᵣ`** (registers — per-hart machine state) and **`↦ₚ`** (the
physical tier — image bytes, the pristine gate's tier, the DMA window's flat
half).

**RED SET: EMPTY.**  A CLEAN 1331-file VM round at exit 0 with zero errors,
and a green incremental round on either side of it.  No `Admitted`, no
`admit`, no new `Axiom`.  129 `.v` files changed; the only exported
client-visible statements that MOVED are the ones A6.15's rulings move (the
icache owner flip and its `file_pay` chain) plus the five ∃-context cells
(`lock_word`, `iref_cell`, `off_cell`/`off_mark`, `started_cell`,
`inode_held_short_any`), each of which keeps its old spelling available
through a named `_acc` equation.

### 0.20′ THE CUTOVER BACK-PORTS: THREE FLIP-WORKSPACE SHAPES LAND ON MAIN (2026-08-27)

M-leg work, and a different KIND of M-leg work from §0.8′–§0.19′: those
sweeps added an AXIS (the ambient ξ, the notation towers).  This one adds
no axis at all.  It takes three STATEMENT SHAPES that the flip workspace
developed below the Σ seam, checks which of them are SC-provable as they
stand, and lands those on main — so that the eventual `TsoCtxTwin2` swap
changes MEANINGS and not STRUCTURE.  Every shape here is stated at its
SC-degenerate spelling (the flat obligation main already uses); what
transfers is the accessor form, the premise threading and the
parameterization, never the TSO vocabulary.

**Rule of engagement, applied throughout, and it disposed of two items:**
a back-port earns its place only if it reduces the cutover EDIT.  A shape
whose SC-degenerate form is vacuous — nothing to pay, nothing to thread —
is mimicry, and mimicry that carries a measured compile hazard is worse
than nothing.  Both skips below are of that kind and both are recorded
with the measurement that decided them.

#### ITEM 1 — THE VIRTIO INSIDE-OUT (A6.48 ruling 4).  LANDED.

`VirtioProto.virtio_proto_step` no longer performs the DMA completion's
byte update.  It hands the write set's OLD bytes OUT and takes the NEW
ones back through the close-wand; `gen_heap_interp m` goes in for
`dma_agree`'s pure fact and comes straight back UNTOUCHED.  The store is
performed by the ONE caller that holds both authorities — `WpUart`'s
`wp_disk_loop`.

| | before | after |
|---|---|---|
| `WpVirtio.dma_update` | the updater (`gen_heap_interp (w ∪ m)` out) | kept, but as the SC store gate's engine only |
| — | — | **`WpVirtio.dma_acc`** — the ACCESSOR: `old` out at `dom old = dom w`, `⌜old ⊆ dma⌝`, and a wand taking `w` back |
| — | — | **`WpVirtio.phys_map_store`** — the SC store gate (`TsoCtx.ledger_store_ok`'s stand-in), stated over the bare big-op the accessor hands across |
| `WpVirtio.virtio_lease_step` | `gen_heap_interp m ==∗ gen_heap_interp (w ∪ m) ∗ virtio_lease v'` | **`virtio_lease_acc`** — `gen_heap_interp m` in and back, `∃ old`, wand to `virtio_lease v'` |
| `VirtioProto.virtio_proto_step` | `∃ kq wr`, wand yields `gen_heap_interp (w ∪ m) ∗ auth ∗ proto` | **`∃ kq wr old`**, `⌜dom old = dom w⌝ ∗ `gen_heap_interp m` ∗ old-bytes out; wand takes `perm_done` AND the new bytes, yields `auth ∗ proto` |
| `WpUart.wp_disk_loop` | frames the updated heap out of `Hback` | performs the store itself (`phys_map_store w old m`) before closing |

**The device-conformance tier did not move**, exactly as A6.48 predicted:
`virtio_req_step`, `virtio_queue_ok_step`, `vproto_step_det` and every
model-side statement are untouched, and so is `dma_own`'s tier (`↦ₚ`
stays raw on main — `phys_ledger` is the flip's tier and is not
statable here).

**Why this is the highest-value item of the three.**  It is the only one
whose SC-degenerate form is not degenerate at all: the accessor/gate split
is a REAL restructuring that SC can carry in full, and it is forced by a
fact that has nothing to do with SC-vs-TSO — that a value-changing law may
not split two authorities that the interpretation ties together.  At
cutover, `VirtioProto.v` and `WpVirtio.v` need only their TIER renamed
(`phys_pointsto` → `phys_ledger`) and `phys_map_store`/`dma_update`
deleted; not one accessor statement moves.

#### ITEM 2 — THE OBLIGATION PASS-THROUGHS (A6.2 / A6.14 / A6.30 / A6.55).

**(a) `HartMStore`'s TWELVE and `HartMLoad`'s FIVE.  LANDED.**

Both chains are PASS-THROUGHS: nothing in either file owns a points-to, so
no lemma in them discharges the memory obligation — each takes it and
hands it down.  That is exactly the property that makes them cheap to
cut over, and it was invisible because the obligation was INLINED at every
statement.  It is now named, in two definitions per file:

```coq
  (* HartMStore *)
  wobl_ram (σ : mstate) (n : N) (req : Interface.WriteReq.t n) : iProp Σ
    := mstate_interp (MState σ.(sregs) (write_bytes σ.(mem)
         (Interface.WriteReq.pa req) n (Interface.WriteReq.value req))
         σ.(mdev)).
  wobl_prem (n : N) (req : Interface.WriteReq.t n) (R : iProp Σ) : iProp Σ
    := (∀ σ, mstate_interp σ ={⊤,∅}=∗ ▷ (|={∅,⊤}=> wobl_ram σ n req ∗ R))%I.

  (* HartMLoad *)
  robl_ram (mm : gmap Arch.pa (bv 8)) (pa : Arch.pa) (w : bv 64) : Prop
    := read_bytes mm pa 8 = Some w.
  robl_prem (pa : Arch.pa) (bytes : bv 64) (R : iProp Σ) : iProp Σ
    := (∀ σ, mstate_interp σ ={⊤,∅}=∗ ⌜robl_ram σ.(mem) pa bytes⌝ ∗
              ▷ (|={∅,⊤}=> mstate_interp σ ∗ R))%I).
```

The twelve store statements now read `wobl_prem 4 (mwrite_req pa v) R -∗`
(and the width-8 / `execute_STORE` variants), the five load statements
`robl_prem pa bytes R -∗`.  **Seventeen five-line premises became
seventeen one-line ones**, and the cutover's edit at these two files is
now FOUR definition bodies instead of seventeen statements.

TWO measurements worth keeping:

- **the abbreviation is transparent to the proof mode almost everywhere.**
  `iMod ("Hmem" $! σ with "Hσ")` sees through a plain `Definition`, so the
  five load proofs and ten of the twelve store proofs needed NO change at
  all — only the two innermost consumers
  (`swp_checked_mem_write`/`_write8`, which actually open the callback)
  carry a `rewrite /wobl_prem /wobl_ram`, and it is written there
  deliberately rather than relied on.
- **exactly one external caller noticed**, and it is the honest one:
  `WpMmodeStore.v`'s two `swp_vmem_write_gen8` sites PROVE the obligation
  and end at `rewrite st_write_value`, which cannot see a folded head; one
  `rewrite /wobl_ram` each.  No other file in the tree consumes these
  seventeen premises — `PtTreeAdue`, `HartSMem`, `HartMRun`, `WpMmodeLoad`
  all mention the chain's lemmas but not its obligation slot.

**(b) THE A6.30/A6.55 PAYER SITES.  MEASURED, AND SKIPPED — WITH THE
REASON, WHICH IS A6.30's OWN RULE RUNNING IN MAIN's FAVOUR.**

A6.30's ruling is NEGATIVE: *before threading a payer upward, compute the
closure and check that something up there HOLDS the bundle; if nothing
does, the obligation belongs on the lane where the bundle is handed DOWN
as a callback — the `swp` lane, never the `exec` one.*  Checked on main,
at the two lanes it names:

- **the `exec` lane DOES perform its own update on main.**
  `KptTree.ptree_translateAddr_own` / `_upd` (`:1069`, `:1199`) and
  `KptShare.tlb_res_pt_translateAddr` (`:270`) take `gen_heap_interp
  σ.(mem)` and return `gen_heap_interp σ'.(mem)`, doing the Svadu A/D
  write-back inside (`ptree_own_path_upd` +
  `PtTreeAdue.phys_word_pointsto_write`).  This is the site the question
  asks about.  **But there is no SC-degenerate payer premise to add**: at
  SC the payment IS the `gen_heap` update these lemmas already perform, and
  A6.30 measured that threading a payer up this lane is paid by nobody
  (`mstate_interp` does not carry the bundle, and it is the widest thing
  the chain holds).  A back-port here would be a premise with no content
  and no payee — mimicry by the rule of engagement above.  Recorded, not
  landed.
- **the `swp` lane is ALREADY the shape A6.30 endorses.**
  `HartSKpt.kpt_leaf_write_node` (`:507`) concludes in a callback that is
  HANDED `mstate_interp` and returns it written —
  `PtTreeAdue.wpte_obl_at`'s SC-degenerate form, spelled inline — and
  `PtTreeAdue`'s seven PTE read/write nodes take the same callback as a
  premise.  Nothing structural is missing; the only delta left is that the
  callbacks are inlined rather than named, which is item 2(a)'s treatment
  applied to a file whose cone is the widest in the S-mode tier
  (`HartSTrans`, `Pt2WalkPt`, `SmodeCorePt`, `UserPtTree`, `KptTree`).
  **Deliberately deferred**, not refused: it is the same mechanical change
  and it will pay off, but it is a whole-tier round of its own and it is
  not what A6.30/A6.55 are about.

A6.55's `pte_wb_ok` / `pte_slot_set` family is **not statable on main at
all** — it is the pinned-byte-set vocabulary (`TsoMemPa.byteset`,
`phys_ledger_pin`), which is TSO machinery by construction.  Skipped by
the standing rule.

#### ITEM 3 — `WpSconfMem`'s ENGINE-BRACKET RE-PARKING (A6.18 / A6.33).

**THE STORE HALF: LANDED, AND EVERY EXPORTED STATEMENT IS TEXTUALLY
UNCHANGED** — which is A6.18's own acceptance test, and it held here too.

A6.33's finding was that `wp_store_s_sconf_au` already OWNS `own_context`
(it is a conjunct of `IntrDefs.sie_cap`, so it arrives with the
`sie_cap_gpr` the leaf already takes) but parks it on the `swp_mono` POST
bracket, where the write node cannot reach it.  Re-routed:

| | before | after |
|---|---|---|
| `swp_mono`'s post bracket | `[… Hstk Harm Hctx Hclose]` | `[… Hstk Harm Hclose]` |
| the leaf's `R` | `Ψ` | `(own_context (CID := CID) cur_ctx ∗ Ψ)%I` |
| the write node | `iIntros (sigma) "Hsi"`, then `wordw_pointsto_write_c … "Hk Hmem Hbw"` | `… "Hk Hmem Hctx Hbw"` as `"(Hmem & Hctx & Hbw)"`, and `iFrame "… Hctx HPsi"` |
| the post | `(… & HPsi & Hfrag)` | `(… & [Hctx HPsi] & Hfrag)` |
| `wordw_pointsto_write_c` (a `Local Lemma`) | `gen_heap_interp mm -∗ wordw_pointsto … ==∗ …` | `… -∗ own_context (CID := CIDw) cur_ctx -∗ wordw_pointsto … ==∗ … ∗ own_context (CID := CIDw) cur_ctx ∗ …` |

**AND THE ONE THING THAT WAS NOT IN A6.33's PLAN, which is the finding to
carry back to the flip: `own_context` IS CpuId-INDEXED, AND THE WRITE NODE
RUNS AT A DIFFERENT `CpuId` THAN THE SECTION.**  `wp_store_s_sconf_au`'s
proof does `rename CID into CID0; iIntros (CID Hs)` — the instruction
obligation binds a FRESH `CpuId`, and the capability (hence the token) is
at that one, while typeclass resolution inside the proof still finds the
SECTION instance.  So both the leaf's `R` and the helper had to name the
CpuId explicitly: `own_context (CID := CID) cur_ctx` at the `iApply`, and a
new `{CIDw : CpuId}` binder on `wordw_pointsto_write_c` (a section variable
cannot be instantiated from inside its own section — `(CID := …)` is
rejected with "Wrong argument name CID").  It failed the way this class
always fails: `iExact` refusing two terms that PRINT IDENTICALLY, and only
`Local Set Printing All` names the difference (`@own_context Σ _ CID …`
vs `… CID0 …`).  **The flip's `WpSconfMem` has the same re-parking with an
AMBIENT index and has never compiled past its load half (A6.61), so it
carries this bug unfound**; and post-flip the same parameter is needed
twice over, because it also names the append's author (`hart_agent
cpu_id`).

**THE LOAD HALF: NOT ATTEMPTED, AND THE MEASUREMENT SAYS DO NOT.**
A6.61 measured the flip's load-side re-park as a NON-TERMINATING
elaboration — 35 min on the first attempt, 60 min with the partial `set`
fix, at 1.34–1.39 GB RSS, against 4.57 s for the 195 sentences before it —
because the leaf's `R` is a value-indexed LAMBDA occurring twice inside a
forty-argument application (once alone, once under `Mobl_ram_ex`).  Main's
load leaf has exactly that shape and would reproduce it.  Against that:
main's SC read obligation is `s_mem_chunk` against `sigma.(mem)`, which
needs NO token, so the SC-degenerate re-park has zero content — it is pure
shape, and pure shape is not worth a measured 60-minute hazard.  A6.61's
rigid-head recipe (`set` + `assert` + `clearbody`) remains the thing to
try, and it should be tried where the goal is real.

**`WpSconfLock` (A6.33's second "no new premise" site): SAME VERDICT,
SAME REASON.**  `wp_amoswap_lockopen_s_sconf` parks `Hctx` on its post
bracket at `:1027` and its engine payload is `(fun bytes => Tc ∗ …)` — the
value-indexed lambda again, and its write node would additionally need
`SmodeCorePt.word4_pointsto_write_c` to grow the token.  Recorded for the
same lane as the load half.

#### THE CUTOVER-DIFF REDUCTION, MEASURED

Comment-stripped, whitespace-normalised line diffs of each main file
against its flip-workspace twin (`/shared/xv6iris-3-fliptree-backup`),
before and after this session:

| file | before | after |
|---|---|---|
| `VirtioProto.v` | 55 | **39** |
| `WpVirtio.v` | 79 | **55** |
| `WpUart.v` | 88 | **82** |
| `HartMLoad.v` | 86 | 84 |
| `WpSconfMem.v` | 253 | 252 |
| `HartMStore.v` | 386 | 435 |

**READ THAT TABLE WITH ITS CAVEAT, because two of its rows are honest and
misleading at the same time.**  Item 1 is a straight win and the number
says so (222 → 176 across the three virtio files, −21%).  Items 2 and 3 are
NOT measured by this metric and it is worth saying why:

- `HartMStore` GREW because the flip file still spells its twelve premises
  INLINE while main now names them.  The claim being made is not "the
  textual diff against today's flip tree shrank"; it is that the cutover's
  EDIT at this file drops from twelve statements to two definition bodies
  — which requires the flip file to adopt `wobl_prem` too, and that is a
  one-time mechanical change on the flip side.  (Most of the 386-line
  baseline is the flip's ~358 lines of `wobl_ram_ledger*` payer lemmas,
  which are TSO-only and unportable in either direction.)
- `WpSconfMem` is flat because the file's biggest flip-side delta is the
  `wordw_pointsto` DATUM going ctx-tier (A6.18's three lines) plus the
  deletion of the `wordw{2,4}_ctx` adapters, none of which is statable
  here.  The re-parking itself did converge exactly: the `swp_mono`
  bracket at the store leaf is now CHARACTER-FOR-CHARACTER the flip's, and
  the write-node block went 18 → 14 differing lines, with the 14 being
  precisely the `img/log/tv/V` binders and `Htso` — i.e. all that is left
  at that site is TSO vocabulary.

#### THE TWO-ROUND VERDICT

**ROUND 1** (full VM `make -f CoqMakefile -j180 -k` from the repo root):
**814 files recompiled — the whole cone above the M-mode load/store chain —
ZERO errors.**  No crawl: the worker table never showed a worker past ~90 s,
and the tail was `SystemAdequacy.v` at seconds, as §0.19′ left it.

**ROUND 2** (the same command, immediately after): `Nothing to be done for
'real-all'`, `MAKE_EXIT=0`, **1331 `.v` / 1331 `.vo`** (the 1332nd source is
`SystemAssumptions.v`, which `iris/_CoqProject` deliberately does not list —
durable-notes.md's `make audit` note).  Zero errors, zero compiles.
`make audit` re-run on top of it, and **the adequacy print is the baseline,
unchanged**: exactly `functional_extensionality_dep`,
`xv6iris_extras.resv_matches`, `xv6iris_extras.resv_is_valid` — nothing else,
no `Link*` entry.

Files changed: **7** — `VirtioProto.v`, `WpVirtio.v`, `WpUart.v`,
`HartMStore.v`, `HartMLoad.v`, `WpSconfMem.v`, `WpMmodeStore.v`.
No `Admitted`, no `admit`, no new `Axiom`.  No exported statement above
the kit changed: the virtio device-conformance tier is untouched, the
seventeen `HartMStore`/`HartMLoad` premises are the SAME PROPOSITION under
a name, and `WpSconfMem`'s ~20 S-mode load/store leaf statements are
textually identical.

#### WHAT THIS LEAVES FOR THE NEXT LANE, RANKED

1. **`WpSconfMem`'s LOAD half and `WpSconfLock`'s AMOSWAP engine** — both
   blocked on A6.61's lambda-payload elaboration, not on any design
   question.  Whoever tries the `clearbody` rigid-head recipe should do it
   where the payload is real (the flip tree), and budget one 30-minute
   compile per attempt.
2. **`PtTreeAdue`'s obligation naming** (item 2(b)'s deferred half) — the
   same `wobl_prem`/`robl_prem` treatment for the seven PTE read/write
   nodes and `HartSKpt.kpt_leaf_write_node`'s conclusion.  Mechanical, but
   the widest cone in the S-mode tier, so it wants its own round.
3. **The flip side of item 2(a)** — `HartMStore`/`HartMLoad` in the flip
   workspace should adopt `wobl_prem`/`robl_prem` so the cutover's edit at
   those two files really is four definition bodies.  Until it does, the
   naive `diff` against main GROWS there, which is the table's caveat.

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

### 0.21′ OWNER RULING (2026-08-27): ↦ₛ is redefined CONTEXT-RELATIVE at
arbitrary timestamps; pristine/t=0 is a DERIVED special case, never the
definition

> **LANDED — the implementation and its measurements are §0.22′.**

The pristine-tier spelling floated for ↦ₛ (flip-note A6.69's item 2)
is OVERRULED as the definition: it hardcodes timestamp 0, and the
kernel has dynamically-generated strings — safestrcpy at proc.c:290
(kfork: np->name) and exec.c:132 (p->name) — whose proofs today
bypass the string tower entirely via the ad-hoc pname_cells byte
big-op (ProcDefs.v:52).  The ruled shape: ↦ₛ flips to a ctx string
tower (ctx_string_pointsto ξ a dq s, the full law set, notation at
cur_ctx per the M1 mechanism), covering arbitrary-timestamp string
data uniformly; the lock handles' persistent string facts
(lock_name/sl_name — A6.15's objection (a)) use the DERIVED
context-free form instead: on main the ∀-context spelling (the
kernel_data precedent, trivially mintable at SC), discharged at
cutover via the twin's ⌜t = 0⌝ arm — i.e. the pristine content
enters as the justification of the derived fact for rodata literals,
not as ↦ₛ's meaning.  Optional follow-up in the same lane if cheap:
unify pname_cells with the new tower (it IS a string fact carrying
pname_wf).  This lane runs PARALLEL to the fliptree critical path,
on the green main tree; the fliptree keeps ↦ₛ raw with its three
named bridges until this lands and ports at cutover with the rest
of M1.

0.21′ AMENDMENT (owner, same day): pname_cells is NOT unified into ↦ₛ
— it is a different kind of string (a fixed-size array with an
embedded null-terminated string; pname_wf carries the terminator).
The ruled relationship is a DERIVATION AT CALL BOUNDARIES: an
accessor/split-join pair from the array-with-a-string resource to the
callee-facing ↦ₛ fact — borrow the prefix-up-to-the-null as the
string view (the tail bytes stay behind), hand it to the function
that expects a string, reassemble on return.  Both resources keep
their own definitions; the bridge is positional (a prefix/suffix
split of the byte list), so it is split + reassemble, not a
conversion.  The lane builds: the ctx string tower (the 0.21′ ruling),
the derived context-free form for the handles, and this
array→string accessor family with safestrcpy's spec as the acceptance
test (its source argument consumes the borrowed string view; kfork's
and kexec's call sites are the worked instances).

### 0.22′ M1 STAGE 3 IS LANDED — `↦ₛ` IS CONTEXT-RELATIVE AT ARBITRARY
TIMESTAMPS, AND THE ARRAY→STRING ACCESSOR IS ITS BRIDGE (2026-08-27)

Implements §0.21′ and its amendment on the green main tree, PARALLEL to the
fliptree critical path.  §0.19′'s "`↦ₛ` DOES NOT FLIP" and its "WHAT M1
LEAVES BEHIND" list are SUPERSEDED for the string tier by this section; the
deliberately-raw tiers are now exactly **`↦ₓ` (text), `↦ᵣ` (registers) and
`↦ₚ` (the physical/image tier)**.

#### THE STRUCTURE QUESTION, ANSWERED BY THE M1 MECHANISM

The fliptree lane's aborted evaluation (A6.70) flagged that
`string_pointsto` lives in `RiscvPtsto.v`, BELOW `TsoCtx`, and that the flip
therefore had to either MOVE the definition and its four-notation family
(34 files) or split declaration from definition.  Neither: the answer is the
one stage 1 and stage 2 already used, and it needed no new decision.
`TsoCtx.v` declares a SECOND tower (`ctx_string_pointsto`) over its own
sealed byte and RE-DECLARES the four `↦ₛ` spellings at it; `RiscvPtsto`'s
raw tower stays put as the kit-tier fact, exactly as `word4_pointsto` does.
Import order decides, the spellings are character-identical, and NOTHING
moved.  **The general rule, since this is the third time it has come up:** a
tier flip never relocates the raw definition — the raw one is the below-Σ
fact and the flipped one is a new tower with the same spelling.

#### THE TOWER

`ctx_string_pointsto ξ a dq s` = `[∗ list] j ↦ b ∈ cstring_bytes s,
ctx_pointsto ξ (pa_add a j) dq b` — the raw tower's shape over the ctx byte,
no alignment side condition.  Laws, mirroring the stage-2 word towers
adapted to strings: `_unfold` / `_bytes` / `_intro` / `Timeless` (+ the
`ktier`-typed `_timeless'`) / discarded-`Persistent` (+
`_discarded_persistent'`) / `_frac_split` / `_half` / `_persist` /
`ctx_string_ktier_mono`, plus `ctx_morph_string` beside `ctx_morph_word4`.
Not sealed, for the word towers' reason.

**One law is DELIBERATELY WEAKER than the word towers', and the difference
is a real fact about strings.**  `ctx_word4_pointsto_agree` concludes
`⌜w1 = w2⌝`; the string tower's `ctx_string_pointsto_bytes_agree` concludes
only that the two byte lists agree where both reach.  Two string facts at
one address need NOT name the same string: `s1` may be a proper prefix of
`s2` when `s2` has an EMBEDDED NUL character, which Coq's `string` permits
and only `PrintkFmt.nonul` rules out — and `nonul` lives far above `TsoCtx`.
State the byte-level law here and let a `nonul`-holding consumer sharpen it.

#### THE DERIVED CONTEXT-FREE FORM, AND WHERE ITS SUPPLY COMES FROM

`ctx_string_all a dq s := ∀ ξ : CtxId, ctx_string_pointsto ξ a dq s`, with
`_unfold` / `_elim` / `_intro` / `Persistent` (+ the `ktier` twin) /
`_ktier_mono`.  The `kernel_data` precedent, and the pristine/t=0 story
enters HERE — as the justification of a derived fact, never as the meaning
of `↦ₛ`.

`WpLock.lock_name` and `SleepLock.sl_name` carry it.  Each is still
`∃ p, word_pointsto (name_field lk) □ p ∗ <the string>`; only the string
half moved, the field stays RAW per §0.8′ ruling 2.  **`is_lock` and
`is_sleeplock` are character-identical and still CLOSED TERMS** — the park
rows (`ut_park_caps`'s three handles) did not move, `UsertrapRes.v` /
`UtResFits.v` / `ParkCap.v` are untouched and green, and `SystemAdequacy.v`
is at seconds.

**The supply was already minted and was being thrown away, exactly as
A6.70 measured.**  `kernel_data` is ∀-context (§0.8′ ruling 1), and
`kernel_data_string` used to instantiate that ∀ at a JUNK
`MkCtxId inhabitant inhabitant` and cross to the raw tower through the
shim — because its conclusion had to be context-free and the raw tower was
the only context-free string there was.  Now `kernel_data_string_all` keeps
the ∀ and hands it straight through (zero shim), and `kernel_data_string`
is that lemma instantiated at `cur_ctx`, its statement unchanged.  **The
lesson worth keeping: a lemma that instantiates a ∀ at a junk witness is a
lemma whose conclusion is in the wrong tier — the junk witness is the
diagnostic.**  `KernelDataInv.v` was the tree's one "flip `↦ₛ`" seam marker
and it is gone.

`SpecInitlock` / `SpecInitlockWrapper` / `SpecInitsleeplock` take the ∀ form
as their name-string premise (the one sanctioned client-visible shape
change), and their twelve callers mint it with `kernel_data_string_all`
instead of `kernel_data_string` — one call, used twice, since it is
persistent.  The chain rodata → `kernel_data_string_all` → `lock_name_intro`
→ `is_lock` has NO seam anywhere in it.

#### WHY THE SINGLE TOWER SUPERSEDES THE DISCARDED/OWNED SPLIT

The fliptree lane independently converged on SPLITTING `↦ₛ` into a
discarded (rodata, context-free) and an owned (runtime, context-indexed)
form before the countermand.  It is refuted by the ruling and by this
landing: the split hardcodes the rodata/runtime distinction INTO THE
NOTATION, so every consumer must know statically which kind of string it
holds, and the two forms cannot meet — `printk("%s", …)` takes a format
literal and a `p->name` in the SAME `descs` list at the SAME
`pk_desc_res`, and under a split that list cannot be typed without a
disjunction in the resource.  The single arbitrary-timestamp tower gives
one `pk_desc_res`, and the rodata case comes back as `ctx_string_all` — a
DERIVED fact that lives only where a persistent handle needs it (two
definitions, three spec premises, twelve mint sites), not as a second tier
with its own law set.  The general shape: **when two cases differ in what
you can PROVE about them, that is a derived lemma; only when they differ in
what they MEAN is it a second definition.**

#### THE ARRAY→STRING ACCESSOR (`ProcDefs.v`)

`pname_cells` stays its own resource (§0.21′ amendment): `p->name` is a
FIXED-SIZE sixteen-byte array — all sixteen always owned, the length is part
of `proc_fields` — with a C string embedded in it, and `ProcGeom.pname_wf`
is the terminator's existence.  `↦ₛ` owns `|s|+1` bytes and stops.  The
bridge is a POSITIONAL split, not a conversion:

| | |
|---|---|
| `pname_pad pa dq nm pad` | the bytes past the string's NUL, addressed from the FIELD's base so the halves rejoin positionally |
| `pname_addr pa i` | `pa_add (p_name pa 0) i = p_name pa i` — the cursor/element re-index |
| `pname_bytes_split` | `pname_bytes pa dq (cstring_bytes nm ++ pad) ⊣⊢ p_name pa 0 ↦ₛ{dq} nm ∗ pname_pad pa dq nm pad` — both directions at once |
| `pname_wf_cstring` | a buffer that BEGINS with a C string is well-formed |
| `pname_cells_borrow` | `pname_cells pa dq bs -∗ ∃ nm pad, ⌜bs = cstring_bytes nm ++ pad⌝ ∗ ⌜nonul nm⌝ ∗ p_name pa 0 ↦ₛ{dq} nm ∗ pname_pad pa dq nm pad` |
| `pname_cells_return` | `p_name pa 0 ↦ₛ{dq} nm -∗ pname_pad pa dq nm pad -∗ pname_cells pa dq (cstring_bytes nm ++ pad)` |

The string is DETERMINED, not assumed (`pname_wf` gives the NUL,
`CstringInv.bytes_string_split` gives the split), and the RETURN takes an
ARBITRARY string because the callee may have written it — `pname_wf` is
re-derived, never carried across.  `ProofSyscall`'s hand-rolled
`sysc_name_addr` / `sysc_pname_app` (the latter a shim crossing) are
retired into it.

**WORKED INSTANCES.**

1. `ProofSyscall`'s `printk("%d %s: unknown sys call %d\n", p->pid,
   p->name, num)` — seven lines of hand-rolled split/rejoin became
   `pname_cells_borrow` … `pname_cells_return`, with `nonul` riding out of
   the accessor.
2. **kfork's `safestrcpy(np->name, p->name, 16)`** — the SOURCE argument now
   comes out of the borrow.  `ProofKforkParts.kfk_src_of_string` re-indexes
   the borrowed `↦ₛ` view plus the retained tail into the byte window
   safestrcpy's contract states its source over, and
   `kfk_src_ok_of_string` discharges `ssc_src_ok` from **the string's own
   NUL — the second disjunct** — rather than from kfork happening to own all
   sixteen bytes (`ssc_src_ok_full` is gone from that call).  That is the
   honest reason the copy is safe, and it is the same reason exec's is.

**safestrcpy'S SPEC IS NOT RE-SPECED, and why.**  Its source is stated as a
byte window over a naming function `f` because its POSTCONDITION has to
speak about the destination byte by byte (`ssc_post`'s `s j = f j` for
`j < k`), which a `↦ₛ` fact cannot say; and `SpecStrncpy` / `ProofUserinit`
share the `f`-shaped source.  The re-spec, recorded at
`ProofKforkParts.kfk_src_of_string` for whoever wants it: replace the source
premise and `ssc_src_ok f n ns` by `t ↦ₛ{dq} src` alone, dropping `ns` and
`f` from the source side; `ssc_stop` then reads
`k = min (String.length src) (n-1)` and `ssc_post`'s copied bytes read off
`cstring_bytes src`.  Strictly smaller, but it is a RE-PROOF of the copy
loop, not a re-statement.

**WHERE THE ACCESSOR DOES *NOT* APPLY, measured at kexec.**  exec's
`safestrcpy(p->name, last, PNAMELEN)` has its array at the DESTINATION and
its source at `last`, a pointer INTO `char path[MAXPATH]` — a `ByteBuf`
window with `bb_cstr`, not an array-with-an-embedded-string, so the accessor
has no purchase on the source.  At the destination the callee reports BYTES
(`h`), so `pname_wf` + `pname_cells_intro` is the closer and the accessor's
return half would be a no-op round trip; the return half is for a callee
that reports a STRING, which is exactly what the re-spec above would make
safestrcpy.  The general shape the amendment gestures at (a fixed-size
buffer + terminator evidence) would generalize to `ByteBuf`'s `bb_cstr` if a
second instance ever wants it; there is one today, and one instance is not a
generalization.

#### FALLOUT LEDGER

**FOUR full VM rounds, 44 files changed** — an order of magnitude smaller
than stage 2's 31 rounds, and the reason is worth recording: the string tier
has almost no INTERIOR.  It is produced in one place (`kernel_data`) and
consumed in one (`printk`), so the flip's honest seams were three files, not
thirty.  Error classes, in the order the build produced them:

| class | files | fix |
|---|---|---|
| `Could not find an instance for "CurCtx"` on a `<msg>_str : kernel_data -∗ a ↦ₛ□ msg` lemma in a binder-less `*Msg`/`*Data` section | 11 | one `Context \`{XI : CurCtx}.` per section; every statement text unchanged |
| initlock/initsleeplock callers feeding the spec's string premise | 12 | `kernel_data_string` → `kernel_data_string_all` |
| genuine ctx↔mem seams that CEASED TO EXIST | 3 (`KernelDataInv`, `ProofSyscall`, `ProofPrintk`) | delete the crossing |
| the `↦ₛ`-vs-`pname_cells` split done by hand | 1 (`ProofSyscall`) | the accessor |

Two intermediate loop-invariant lemmas (`ProofIinit`, `ProofProcinit`) took
the ∀ form on their name premises, since they carry the string across the
per-lock loop.  `PrintkArgs.pk_desc_res` gained the ambient binder — it is
the one definition BELOW `TsoCtx` that spoke `↦ₛ`, and leaving it raw would
have made every printk caller a seam.

SHIM LEDGER: files naming `TsoCtxShim` **73 → 71**, uses **401 → 396**.
`KernelDataInv` and `ProofSyscall` lost it entirely; `ProofPrintk` lost
three uses (`pk_str_byte`'s two and `pk_digits_data`'s one) and keeps its
stack-frame crossings.  **No shim use was ADDED** — the derived ∀ form is
minted from `kernel_data`'s own ∀, so stage 3 is the first tier flip that
pays nothing for what it buys.

VERDICT: two consecutive full 1331-file VM rounds at exit 0, zero errors, no
`Admitted`, no `admit`, no new `Axiom`.  Exported client-visible statements
are unchanged except the three spec premises and the two handle definitions
the ruling moves.

#### PORT OBLIGATION FOR THE FLIP WORKSPACE

The fliptree keeps `↦ₛ` raw with three named rodata bridges.  At cutover it
ports THIS shape, not a re-derivation: the tower and `ctx_string_all` in
`TsoCtx.v`, `kernel_data_string_all` as the ∀'s producer (its three bridges
collapse into that one lemma), the two handle definitions, and
`ProcDefs`'s accessor family.  The twin's job is one arm: `ctx_string_all`
at `⌜t = 0⌝` for the rodata literals — which is where the pristine receipts
`BootCarve.kernel_data_intro` already holds finally get spent instead of
discarded.

### 0.23′ OWNER RULING (2026-08-27): main moves ONCE, after leg C
validates on the tso branch

The M-leg's merge/replay onto `main` WAITS until leg C has landed and
validated on the `tso` branch — the below-Σ kit swapped in from the
flip workspace, the full build green, `make audit` at baseline, the
adequacy statement carrying its carve conjunct.  Rationale (owner):
the Σ-surface statements added on the M-leg are exactly the things a
cutover surprise would force back open, and main must not churn
twice.  Consequences: (i) the C-leg cutover is performed ON THE TSO
BRANCH first — `tso` remains the certificate tree; (ii) the
merge-vs-replay choice for main is also deferred to that moment
(post-cutover, a plain merge/rebase of `tso` is likely to dominate
the runbook replay, but decide with the validated tree in hand;
`tso-flip-replay.md` stays as the fallback recipe); (iii) nothing in
the current lane plan touches `main` — this ruling changes no
in-flight work, only pins the ordering.

### 0.24′ OWNER RULING (2026-08-27): the specific-binary U-mode tier is
DEFERRED from the port; the generic user-mode safety proof stays

For the T-leg (and hence the C-leg cutover), the port keeps the
GENERIC user-mode safety tier — arbitrary-user-code safety
(SpecUser/ProofUser and whatever user-translation/fetch machinery it
and the kernel's own copyin/copyout/exec lanes consume) — and DEFERS
the specific-binary proof tier (the init/sync/sh/echo certificates:
UProof*/user-verified and any machinery consumed ONLY by them).
Process: the implementing lane MEASURES the split first (which of the
U-mode frontier files — UmodeFetch, UptWalkPt, UserMemPt, the ~18-site
payer threading — sit in the generic tier's cone vs only the
binary tier's), ports the generic-serving ones, and descopes the
binary-only ones per the Aug-19 precedent (rows commented out of the
flip workspace's _CoqProject with the ruling recorded in place and a
reverse-dependency check that every consumer of a commented file is
itself commented).  The deferred tier is re-ported after the cutover
lands, as its own effort.

### 0.25′ OWNER RULING (2026-08-27): the THREE-CASE CONFIDENCE GATE, and
what it unlocks

The goal, stated by the owner: confidence that the context formulation
works for the three tricky synchronization cases — (1) the spinlock's
racy internals (the M4 window/floor kit: the notheld exclusion read,
the holder's own-write reads, the lock word), (2) the boot barrier
variables (started, and first via the park protocol), (3) lock-free
page-table sharing with concurrent A/D write-back.  ONCE ALL THREE
ARE PROVEN UNDER TSO in the flip workspace, partial replay of the
M-leg conversion onto `main` MAY BEGIN — this refines 0.23′: the
three-case gate unlocks *starting* the main replay (the Σ statements
those cases exercise are the ones a cutover surprise would reopen,
and the gate is exactly the evidence they will not); the full
main-moves-once discipline of 0.23′ still governs the remainder.
Status at ruling time: (3) is proven in its concurrency core (walker
+ A/D + the secondaries' sharing chain green; hart 0's publication
site is mechanical wiring behind M4); (1) is one in-flight tranche
from done (the atomic unit; all kit proven); (2)'s consumer half is
green and its producer half + the park port are the remaining real
work.

### 0.26′ OWNER RULING (2026-08-27): free-page ownership is
VISIBILITY-FREE — ∃x,↦x is subtly too strong for kfree under TSO

The owner's observation, verbatim in spirit: kfree's classical
precondition ∃x, a ↦ x asserts the freer holds a value DETERMINATE
AT ITS OWN CPU'S VIEW, and under TSO that is surplus — a page whose
lock another CPU just released has no value well-known to the freer,
and freeing must not require one.  What kfree needs is only the
FUTURE half of ownership: exclusivity plus the per-byte timestamp
element any future write must pay.  Determinacy re-mints itself at
the next write with no evidence (stores do not read; one's own write
is visible by forwarding), and xv6's kfree/kalloc memset immediately,
so the allocator path never reads before writing.  Consequences:
(i) the allocator's free-page bodies restate at the visibility-free
tier (physical fraction + element, no justification bit — the tier
already exists in the kit); (ii) the lock-cell reclamation at
pipeclose→kfree becomes EVIDENCE-FREE — a ghost reset of the history
payload at full element ownership (removing a history claim only
weakens the interpretation's obligations) plus the tier weakening;
the acquire remains protocol-relevant (no-other-references), not
per-byte-relevant; (iii) drain-evidence reclamation survives only
where a taker READS before writing — the context-switch stamp, which
is designed separately; (iv) a kalloc client that reads a fresh page
before writing it now owes a visibility justification, which is the
model being honest about allocator junk.  This supersedes the
drain-evidence reclaim-gate design for the free path.

0.26′ ADDENDA (owner, same day): (a) THE INVARIANT PRINCIPLE, stated
as the standing rule it has become — invariants speak in STAMPS AND
BOUND-RELATIONS, never ambient identities: an invariant stores data
beside a stamp/floor and states claimability as "any context whose
bound can be raised past this stamp, given view evidence, may take
these facts"; a context appears in an invariant body only as the
parked-record idiom (the token as authority over a bound).  Every
capture bug in the port's history violated this; every fix restored
it.  (b) READ-BEFORE-WRITE KALLOC CLIENTS ARE KERNEL BUGS: the 0.26′
sweep FLAGS any such client rather than proving around it — none are
expected to exist.

### 0.27′ OWNER RULING (2026-08-27): resume freshness comes from
p->lock — the lock invariant ties the parked stamp to the release
write's timestamp

The owner's design, verbatim in spirit: when a thread calls sched(),
the scheduler's RELEASE of p->lock lands after the park's
publication, so the release write's timestamp t_rel dominates the
suspended context's stamp T — and the LOCK INVARIANT states that tie
(⌜T ≤ t_rel⌝, with t_rel available as the lock word's own ledger
element timestamp under the M4 contract).  Any CPU's scheduler that
later acquires p->lock drains to view ≥ t_rel, opens the invariant,
and manufactures the resume premise T ≤ K INSIDE the acquire, where
both halves are in hand — exporting the parked token RESUME-READY
(parked T ∗ view ≥ K ∗ ⌜T ≤ K⌝) as one bundle the switch consumes.
Refinement: the process record publishes RELATIONALLY — a parameter
U ("every stamp parked here ≤ U"), instantiated by the free arm at
the lock element's timestamp — keeping the internal stamps
existential/migratable and the published fact monotone, per the
0.26′ invariant principle (bound-relations, never identities or
absolute positions).  This SUPERSEDES A6.90's characterized
"valid_context publishes its stamp + wp_swtch takes a receipt" as
separate travelers; the 0.18′ stamp-tie comment (T ≤ t_release,
"load-bearing at cutover for non-draining paths") becomes invariant
content with the scheduler's resume as its second and primary
customer.  Implementation: fliptree, lock/scheduler tier, after the
M4 flip re-application (same files).

### 0.28′ OWNER RULING (2026-08-27): the trap-handler capability
"problem" dissolves — invariants are context-free; finish making them
invariants

The owner's correction, upheld on measurement: an inv is a
context-free persistent proposition, and every WP is proven with the
context as a section variable — the handler's ∀-context contract was
never special.  The bundle's context-sensitivity was two removable
artifacts: (1) the constant-embedding payload spelling (each mention
site elaborating the payload at ITS ambient, making the "same"
is_lock two different propositions) — fixed by finishing the M3
λ-conversion on the straggler payloads (console/uart/ticks); (2) a
few NAKED discarded points-tos that were mis-homed per the 0.26′
invariant principle: the virtio ring-pointer cells are read only
under vdisk_lock and MOVE INTO THAT LOCK'S PAYLOAD (claimable at
acquire, standard); the devsw entries' lock-free readers all thread
the fs-initialization token, so they move BEHIND THAT TOKEN's
invariant as data-beside-a-stamp, claims discharged by the
bound-domination the token already implies.  No ancestry induction,
no new machinery.  CONSEQUENCE: the internalized transport
certificate (caps_morph) RETIRES — with handles closed and cells
re-homed, the bundle holds nothing context-indexed to transport.
The stvec framing is also corrected for the record: the register
flips at every mode crossing (uservec/kernelvec); "installed once"
refers to the per-CPU interrupt resource carrying the handler's
spec.  What remains is mechanical: the straggler λ-conversions, the
two re-homings, the certificate's removal.

0.28′ ADDENDUM (owner, same day): AN INTERRUPT IS NOT A CONTEXT
CROSSING.  The preempted thread keeps its identity; kernelvec runs on
the same hart, same stack, same context; its exclusive resources
(stack_own, the GPR/interrupt capability) arrive in the PRECONDITION
at that ambient and are BORROWED from the interrupted frame and
returned at sret — the degenerate, evidence-free case of the
algebra, unchanged by TSO (same context = same bound-view chain).
The trap path's complete story: persistent needs are context-free
invariants (0.28′); exclusive needs are precondition borrows (this
addendum); the one true crossing — a timer-driven yield that parks —
departs through sched() under p->lock, which is exactly 0.27′'s
machinery.  The install-time framing was the red herring: what is
installed is only the ∀-quantified spec; the resources always come
from the trapping site.
