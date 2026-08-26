# DECISION MEMO — TSO port, the ▷/fixpoint/invariant-capable context transport

Read-only analysis on branch `tso` @ `33ee1360` (2026-08-26); no files edited,
no build run; every claim is static reading of the sources named plus the
notes' own measurements.  Produced as the owner-decision record for the
transport question that tso-port.md §0.13′ leaves as "the next design problem
to solve" — the last red root of the tree and the gate on the M3 λ-payload
sweep.  **The ask is §3's four owner rulings.**  Line numbers are from that
tree.

---

## 0. Verdict, up front

**The transport does not need to be built. The two blocked payloads are blocked by two *statement* defects, each of which has a precedent already landed in this port, and neither of which needs a new law on the sealed surface.**

- `CtxMorph proc_lock_res` is blocked by `▷ proc_ctx` / `▷ sched_vc_at`, i.e. by `SwtchCtx.valid_context`. `valid_context` is ξ-dependent **only because six rows of `valid_context_pre` read the *ambient* context instead of the record's own `XIp` — which the record already binds (`SwtchCtx.v:245`, `∃ … (XIp : CtxId) (Tp : nat)`), and which that definition's own header already says is the intended index.** This is §0.11′'s `ires_of` bug, one file over: *reading the ambient captures the installer's context inside the fixpoint and re-creates the bug one level down.* Fix it and `valid_context` becomes a **closed term**; the `▷` stops mattering because there is nothing left to transport under it; `CtxMorph proc_lock_res` follows from the existing structural instances.
- `CtxMorph ftable_res` is blocked by `off_hold`'s `cinv` over a ξ-indexed body and by `file_core`'s `is_pipe`. **`is_pipe` is not a separate obstruction** — it is `inv lockN (lock_inv γl pi "pipe" <{ pipe_res }>)` (`PipeInvDefs.v:601`), i.e. an ordinary M3 λ-conversion one level deeper, and `pipe_res` (`PipeInvDefs.v:512`) is ▷-free, `inv`-free, and structurally morphable. **Only `off_hold` is real**, and its fix is the same move a third time: index the cinv body by the *slot's* own context, carried in `fpnames` (which `file_pay` already ∃-closes and `fpay_tok` already forces to agree between shares).
- Candidate (a) — a step-taking `CtxMorphStep` — is **sound but unnecessary, and would not compose**. I give the refutation in §2(a) because it is worth having on the record: the composition failure is structural, not tactical.
- Candidate (d) — restating `CtxMorph` as a plain entailment — is **provable at the twin and at the REAL kit** (measured below) and is worth doing on its own merits, but it does **not** by itself buy the `▷` crossing. §2(d).

**The one thing that must be validated before committing** is not any of the four candidates: it is the *swtch deposit* that the `XIp` reshape creates, because `p_sched` carries `trap_csrs → intr_res`, which since §0.11′ holds an ∃-bound persistent caps *family* at ξ and a `▷ ihs`. §4 gives the ordering that makes that obligation trivially dischargeable and §5 the ten-minute experiment that confirms it.

---

## 1. Three measurements that change the picture

### 1.1 The transport is already an ENTAILMENT at the twin — and at the REAL kit

`TsoCtx.v:479` and `TsoCtxTwin2.v:566` both state

```coq
Class CtxMorph (R : CtxId → iProp Σ) :=
  ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ==∗ ctx_dom ξ ξ' ∗ R ξ'.
```

The `==∗` is **not used**. `TsoCtxTwin2.ctx_morph_pointsto` (`:569–592`) contains no `iMod`: it derives `⌜t ≤ B'⌝` by `mono_nat_lb_own_valid` / `ghost_map_lookup` (both entailments), does `iClear "Hbit"`, `iModIntro`, and rebuilds the clean arm from `ctx_dom`'s persistent `mono_nat_lb_own (tc_bnd ξ') B'`. Same in the **REAL kit at TSO**: `/shared/xv6iris-3-fliptree-backup/iris/TsoCtx.v:763–786` — the twin bodies, hermetic — is likewise `iMod`-free.

So the bare update in the class is decoration. That matters twice: it is candidate (d)'s soundness argument, and it is why candidate (a) is over-engineered.

### 1.2 `ctx_dom`'s non-persistence is the *real* obstruction to any ▷-crossing, and it is by design

At the twin (`TsoCtxTwin2.v:349`):

```coq
Definition ctx_dom (ξ ξ' : CtxId) : iProp Σ :=
  (∃ (B W B' : nat) (D : gmap (nat * Z) unit),
    ctx_at ξ (1/2) B D ∗ ⌜∀ k, k ∈ dom D → (k.1 ≤ W)%nat⌝ ∗
    ⌜(B ≤ B')%nat⌝ ∗ ⌜(W ≤ B')%nat⌝ ∗ mono_nat_lb_own (tc_bnd ξ') B')%I.
```

Transporting one fact needs the **non-persistent half `ctx_at ξ (1/2) B D`** to bound the fact's own timestamp `t` against `B'`; comparing two `mono_nat_lb_own`s is impossible, so no persistent surrogate exists. `TsoCtx.v:460–467` forbids marking it persistent ("a persistent domination would license registering later facts — the unsound step"). Therefore:

> **To move a fact across contexts *under a `▷`* you must be able to bring a non-duplicable authority under that `▷` and get it back out. That is exactly what a step buys and nothing else does.**

This is why every "just make it work under later" shape fails, and why the right answer is to remove the ▷-guarded ξ-dependence rather than to cross it.

### 1.3 There are exactly TWO ▷-guarded ξ-dependent rows in `proc_lock_res`, and they are the same predicate

`SchedCtx.v:441` `(if needs_ctx st then ▷ proc_ctx pa else emp)` and `SchedCtx.v:426` `▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) pa` inside `run_slot`. Both are `SwtchCtx.valid_context p_sched _ _ _`. Everything else in `proc_lock_res` (`SchedCtx.v:447`) is ▷-free: `p_state ↦₄`, `pstate_lock`, `p_chan ↦₈`, `proc_pub` (three `↦₄`), `own_ctx` (a 14-cell `↦₈` run), `proc_dormant` (`ProcDefs.v:302` — `↦₄`/`↦₈`/ghost/big-ops only, verified ▷-free, `inv`-free), `hart_at_any`, `pslot_used_at`. Every one of those is covered by `ctx_morph_word` / `ctx_morph_big_sepL` / `ctx_morph_const` **today**.

`valid_context_pre` is destructed at only **four** sites tree-wide: `SchedCtx.v:585`, `ProofForkretPark.v:196`, `ProofSwtch.v:146`, `ProofSwtch.v:247`.

---

## 2. The candidates

### (e) — THE FRONT-RUNNER (not in the brief; it is what (a)+(b) were reaching for)

**"A parked record's rows are the parked thread's own."** Move the six ambient-reading rows of `SwtchCtx.valid_context_pre` to the record's own existential identity `XIp`, and drop the ambient index from `valid_context` entirely.

Current (`SwtchCtx.v:245–261`), verbatim, with the offending rows marked:

```coq
    (∃ (vs : list (mword 64)) (av : nat) (XIp : CtxId) (Tp : nat),
      ⌜length vs = 14%nat⌝ ∗
      ⌜eq_vec (access_vec_dec (ret_pc (nth 0 vs (mword_of_int 0))) 0) ('b"0") = true⌝ ∗
      ctx_cells c vs ∗                                        (* [1] ambient *)
      stack_own (KTR := KT1) (nth 1 vs (mword_of_int 0)) av ∗ (* [2] ambient *)
      ctx_parked XIp Tp ∗
      (∀ (h : CPU) (m : regfile) (eb' : bool),
         ⌜adm A h⌝ -∗ ⌜callee_img m = vs⌝ -∗
         sie_cap_gpr KT1 (CID := h) (XI := XIp) m av false p -∗   (* already XIp *)
         cpu_own (CID := h) 1 eb' p false {["proc"]} -∗          (* [3] ambient *)
         pc_is (CID := h) (ret_pc (m !!! Regidx (mword_of_int 1))) -∗
         ctx_cells c vs -∗                                       (* [4] ambient *)
         (∃ (A' : ctx_adm) (cret : mword 64) (back : bool),
            (if back then ▷ rec A' cret p else own_ctx cret) ∗   (* [5] ambient *)
            P h A' c cret (rget (CID := h) m (mword_of_int 4 : mword 5)) p back) -∗ (* [6] *)
         WP (LoopE gen_id h : expr riscv_lang)))%I.
```

Proposed: rows [1]–[5] gain `(XI := XIp)`; `P` gains a leading `CtxId -d>` and is applied at `XIp`; `rec` loses its context index (the fixpoint is now over the closed family). Result:

```coq
  Definition valid_context_pre
      (P : CtxId -d> CPU -d> ctx_adm -d> mword 64 -d> mword 64 -d>
           mword 64 -d> mword 64 -d> bool -d> iPropO Σ)
      (rec : ctx_adm -d> mword 64 -d> mword 64 -d> iPropO Σ)
      : ctx_adm -d> mword 64 -d> mword 64 -d> iPropO Σ := …   (* NO CurCtx anywhere *)
```

**Why it is right, not a trick.** `SwtchCtx.v:227–244`'s own header already asserts it: *"`XIp` is ITS identity, held here while it is not running, and its resume wand asks for the bundle at THAT identity — so the facts its closure captured (all indexed by `XIp`) are the facts it wakes up holding."* The implementation left five of the seven rows at the ambient. `TsoCtx.v:82–88` records that `Inhabited CtxId` is load-bearing precisely so a resumer can push `▷` inside this `∃ XIp` — i.e. the design already anticipates the record being read at `XIp`.

**Parking side is FREE.** A parking thread's own identity *is* `XIp` (it does `ctx_park ξ` → `ctx_parked ξ T`, `TsoCtx.v:253`), so every row it stows is already at `XIp`. No transport.

**Soundness at the twin.** No new law. The only motion is `TsoCtx.ctx_park` / `ctx_resume` / `ctx_exchange` (twins `twin_park`/`twin_resume`/`twin_exchange`, `TsoCtxTwin2.v:734/750/797`), all ξ-preserving and all already exported.

**Fixpoint/contractiveness.** Unchanged in shape: `rec` still occurs exactly once, under `▷`, inside one arm of the `back` `if`. `valid_context_pre_contractive` (`SwtchCtx.v:263–278`) closes with the same `solve_proper_prepare; repeat (f_contractive || f_equiv); all: try apply H` — the ∃-bound `XIp` is structural and `P`'s extra leading argument is a discrete-fun argument, not a recursive occurrence. (Watch for §0.11′'s gotcha: if `f_equiv` stalls on the now-four-deep application of `P`, name the hypothesis in the fallback chain, exactly as `ires_of_contractive` had to.)

**What `CtxMorph proc_lock_res` then looks like.** By `ctx_morph_sep` over: `↦₄` rows (`const`, `↦₄` is unflipped — stage 1 flips only `↦ₘ`/`↦₈`, `TsoCtx.v:653–684`), `p_chan ↦₈` (`ctx_morph_word`), `own_ctx` (`ctx_morph_big_sepL` over `ctx_cells_at`), `proc_dormant` (structural), `▷ proc_ctx` and `▷ sched_vc_at` (**now `ctx_morph_const`** — a `▷` over a closed term is a closed term). **No `▷`-transport is invoked anywhere.**

**Cascade, counted.** Statement: `SwtchCtx.v` (one definition, 6 rows, + the contractive proof + `valid_context`/`valid_context_unfold` types), `SchedCtx.v` (`p_sched` gains its `CtxId` argument — 32 occurrences in 13 files, mostly type-level echo; `proc_ctx`/`sched_vc_at`/`run_slot`/`proc_slots` lose their index). Proof: the four `valid_context_pre` destruct sites (`SchedCtx.v:585`, `ProofForkretPark.v:196`, `ProofSwtch.v:146`, `:247`). Downstream type-level echo: `valid_context` 35 occurrences / 11 files; `proc_ctx` 36 / 11; `sched_vc` 17 / 11; `proc_lock_res` 121 / 34; `procs_inv` 379 / 169 (arity unchanged — pure echo, and only if a mention pins `(XI := …)`).

**THE ONE NEW OBLIGATION, and it is where the risk lives.** The *resumer* must now supply the wand's premises at `XIp` while it holds them at its own ξ. It has exactly the premises of `TsoCtx.ctx_deposit` (`:569`) — `own_context ξ` (a conjunct of `sie_cap_gpr` by ruling 2) and `ctx_parked XIp Tp` (out of the record) — and `ctx_deposit`'s twin is the **interp-free, free** `ctx_dom_to_parked` (`TsoCtxTwin2.v:644`). So the law exists and the site is **one** (`ProofSwtch.v`). The obligation is `CtxMorph` on the deposited rows: `cpu_own`, `ctx_cells cret`, and `p_sched` — and `p_sched` (`SchedCtx.v:216`) carries `trap_csrs KT1 (CID := h)`, which since §0.11′ is `∃ C, □ C ξ ∗ ▷ ihs kt C h`. **`□ C ξ → □ C ξ'` is not derivable for an abstract `C`.** That is the "wall one tier down" §0.12′ measured, and it is real. §4 gives the ordering that removes it before (e) lands; §5 is the experiment.

**Risks.** (i) *Silent capture* (§0.8′ rule 3): every one of the six moved rows must spell `(XI := XIp)` explicitly — `XIp` is a `CtxId`-typed binder in scope, and `Global Typeclasses Transparent CurCtx` (`TsoCtx.v:651`) means an unannotated ambient row inside the `∃` may or may not pick it up per site. This is the highest-probability lost day, exactly as §0.11′ found for `ires_of`. (ii) *Crawl*: never leave a failing `iExact` across two ξ inside the 14-cell `ctx_cells` big-op running — use `Goal … = …; tryif reflexivity` (§0.13′'s kit), which fails fast under the hermetic seal. (iii) *Performance*: `Global Typeclasses Opaque` on `proc_ctx`/`sched_vc_at` before touching `SchedCtx`, per the `page_rest` 4088-conjunct lesson.

### (a) — the step-taking transport: SOUND, UNNECESSARY, AND IT DOES NOT COMPOSE

Statement as briefed:

```coq
Class CtxMorphStep (R : CtxId → iProp Σ) :=
  ctx_morph_step : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ ={E}▷=∗^n ctx_dom ξ ξ' ∗ R ξ'.
```

**The ▷ rule holds** at `n = 1`: given `ctx_dom` and `▷ R ξ`, `|={E}▷=∗ X` unfolds to `|={E}=> ▷ |={E}=> X`; take the outer `fupd` trivially, `iNext` (which strips `▷ R ξ` and leaves the un-latered `ctx_dom` in place), apply the existing bare `CtxMorph R`, weaken `R ξ'` to `▷ R ξ'`. Both `ctx_dom` and the payload come back *inside* the step-fupd, which is exactly what makes it work where the bare `==∗` cannot. Twin image: nothing new — it is `TsoCtxTwin2.ctx_morph_pointsto` under `bi.later_mono` plus `ctx_dom_timeless` (`TsoCtxTwin2.v:386`).

**But `ctx_morph_sep` costs a step per conjunct.** `|={E}▷=>^{n₁}` then `|={E}▷=>^{n₂}` is `|={E}▷=>^{n₁+n₂}`; the parallel rule `(|={E}▷=>^n A) ∗ (|={E}▷=>^n B) ⊢ |={E}▷=>^n (A ∗ B)` is unavailable because the two conjuncts must share the single non-duplicable `ctx_dom` (§1.2). `proc_lock_res` has ten conjuncts. Two escapes, both real work:

- **(a1) fractional `ctx_dom`.** `ctx_dom ξ ξ' q`, with `ctx_dom_split : ctx_dom ξ ξ' (q₁+q₂) ⊢ ctx_dom ξ ξ' q₁ ∗ ctx_dom ξ ξ' q₂`. Twin image exists and is easy: `ctx_at` is literally `mono_nat_auth_own (tc_bnd ξ) q B ∗ ghost_map_auth (tc_dirty ξ) q D` (`TsoCtxTwin2.v:270`), already halved by `ctx_at_halves` (`:274`) and re-agreed by `ctx_at_agree` (`:283`); the rest of `ctx_dom` is pure plus a persistent lb. Cost: an arity change on a sealed constant, both mints (`ctx_dom_to_parked`, `ctx_dom_of_parked`) and both give-back wands.
- **(a2) `n`-indexed class.** `CtxMorphN n R`, sep at `n₁+n₂`. `proc_lock_res` would need `n ≥ 2` (the two `▷` rows) and the acquirer must have `n` laters in hand.

**And the acquirer does not have them.** Measured: `ProofAcquire.v:664–668` does the transport *after* the whole instruction sequence, and every leaf on acquire's path burns its own step-later internally — `WpSconfBtype.v:767` `wp_cbnez_fall_s_sconf` states its continuation as `wp_next b p (fun CID => … -∗ WP Loop)` with **no `▷`**, and closes with `- iNext. iExact "Hcont".` at `:799`. Only the *backward-branch* leaf (`:904`, `▷ wp_next …`) exposes one, and that one is spent on the Löb. At the AMO itself (`WpSconfLock.v:906`) the single step-later is already spent stripping `▷ lock_inv`: the payload is produced as `▷ (∃ ξ : CtxId, R ξ)` at `:1110` and un-latered by `iModIntro. iNext. iMod "Hclm" as "_". iModIntro.` at `:1135`. `RiscvPtsto.v:2121` sets `num_laters_per_step _ := 0`, and there are no later credits anywhere in the tree (`grep` for `£`/`lc_supply`: zero hits). **So candidate (a) additionally requires restating one leaf per unit of `n` in a `▷`-exposing form.** Acquire executes ~8 instructions after the AMO, so the laters exist physically; they are not exposed.

**Verdict on (a): refuted as the plan, kept as the fallback.** If (e) fails the §5 experiment, (a1) — fractional `ctx_dom` plus one `▷`-exposing leaf variant — is the sound machine-honest alternative, and it is genuinely "the honest TSO story" §0.13′ describes. It costs a sealed-surface arity change plus a leaf restatement; (e) costs neither.

### (b) — the ∀-`Xr` reshaping: RIGHT INSTINCT, WRONG QUANTIFIER

§0.12′ measured the ∀-`Xr` reshape as "right, and free once the handles are ξ-free — just not sufficient on its own", and reverted it. The static reading says why, precisely: **`Xr` is the wrong binder.** The resumed party does not keep running as `Xr` — `SwtchCtx.v:240–244` and `TsoCtx.v:277` fix the protocol: *"swtch is the one place the token is exchanged: the parker's token parks INTO the record it builds, the target's is resumed OUT of the record it consumes."* After the exchange the hart runs as `XIp`. So rows handed in at a ∀-bound `Xr` are stale one ghost step later — which is exactly the failure §0.12′ observed at `ProofSched.v:1515` / `ProofScheduler.v:1625` ("a parked continuation captures its own facts at its own ξ and now receives `sie_cap_gpr` at a ∀-bound `Xr`").

**(b) is (e) with the quantifier fixed: `∃ XIp` instead of `∀ Xr`.** The record already binds `XIp`; the `∀ Xr` adds a second, unrelated context and forces the two to be reconciled at every resume. Does the WP-inside-the-wand problem dissolve? **Yes, and for a reason worth stating:** the WP conclusion (`WP (LoopE gen_id h)`) is ξ-free, so once every *premise* row of the wand names `XIp` rather than the ambient, the whole wand is ξ-constant and the contravariance disappears — no transport ever has to run backwards. That is the real content of "right shape, not sufficient alone".

### (c) — context-generic invariant bodies, for `off_hold` (and `off_hold` only)

The measured claim in §0.12′ — *"`ftable_res → fslot → file_pay → file_payload → off_hold` ends in `cinv (offN .@ k) γx (off_content γ k armed)` … `file_core`'s `is_pipe` is a second instance of the same thing"* — is **half right**.

- **`is_pipe` is not a second instance.** `PipeInvDefs.v:601`: `is_pipe γl γp pi := ⌜page_valid pi⌝ ∗ (inv lockN (lock_inv γl pi "pipe" <{ pipe_res γp pi }>) ∨ pipe_dead γl γp)`. It is a `const_pay` lock payload — the ordinary M3 case — and `WpLock.lock_inv` (`:336–344`) **already ∃-closes the payload's context** (`∃ ξ : CtxId, R ξ`). λ-convert `pipe_res` and `is_pipe` becomes a closed term. `pipe_res` (`PipeInvDefs.v:512`) is 11 rows of `↦₈`/`↦₄`/ghost/`pipe_data` big-op, **no `▷`, no `inv`, no `cinv`, no WP** — the `KallocInv.v:389–441` template applies line for line. 19 `<{ pipe_res }>` sites in 5 files; 25 `is_pipe` mentions in 10 files, arity unchanged. Same for `SleepLock.sl_res`, the only other payload with a nested `is_lock`.
- **`off_hold` is the real one.** `FileInvDefs.v:1042`: `off_hold γ k γx armed q := cinv (offN .@ k) γx (off_content γ k armed) ∗ cinv_own γx q`; `off_content` (`:1037`) is `off_body`/`off_raw`, whose **only** ξ-dependent row today is `a_fip k ↦₈{DfracOwn (1/2)} ip` (`:965`, `:988`) — everything else is `↦₄` (unflipped).

**Recommended shape (c-XIp), not (c-∃).** ∃-closing the context inside the cinv body (`∃ ξ, a_fip k ↦₈{1/2}(XI:=ξ) ip ∗ …`) makes the handle closed but breaks the *cancel*: `off_hold_cancel` (`FileInv.v:325`) and `off_hold_cancel_raw` (`FileInvDefs.v:1078`) recombine the borrowed half against `file_fields`' half, and `ctx_pointsto_frac_split` (`TsoCtx.v:336`) is single-ξ. Instead, **add a `fp_ctx : CtxId` field to `fpnames`** and state `off_content` at `fp_ctx pn`. Then:
- the body is a closed term *given `pn`*, so `off_hold` is ξ-free;
- `file_pay` (`FileInvDefs.v:1194`) **already** ∃-closes `pn` and `fpay_tok_agree` (used at `file_pay_split`, `:1200`) already forces the two shares' `pn` — hence their ξ — to agree, so the fraction recombination stays single-ξ. **The problem (c-∃) creates is the problem the existing names-ghost already solves.**
- the *mint* picks `fp_ctx := cur_ctx` (`off_hold_alloc`, `FileInvDefs.v:1057`; `ftable_res_boot`, `FileInv.v:709`; sys_open's and pipealloc's publication).
- at *use*, the borrower reads `a_fip` for agreement only, and `TsoCtx.ctx_word_pointsto_agree` (`:447`) is stated over **two free contexts and needs no `ctx_dom`** — the memo's mechanism (C), the only law in the sealed surface that relates two contexts for free.

**Cost:** `a_fip` has 32 occurrences in 9 files; `off_hold` 24 in 5; `off_body`/`off_raw` are referenced outside `FileInvDefs.v` at only two places (`FileInv.v:330`, `:738`). This is the smallest of the three fixes.

**Owner ruling required (and it is a real one):** at **stage 2** (`↦₄`/`↦₂` flip) `a_foff k ↦₄` becomes ξ-dependent too, and *that* cell is genuinely read and written by the borrower, not merely agreed upon. At that point `fp_ctx` alone will not do and the borrower will need a `ctx_dom` from whatever lock synchronises it (the inode sleeplock / the exclusive reference). **Do not build the stage-1 fix in a way that pretends stage 2 is free.** The pristine/timestamp-0 machinery (`own_context_lb0`, `ctx_pointsto_intro_zero`, `TsoCtxTwin2.v:982–998`) does **not** rescue any of this: these cells are written at WP time by `sys_open`/`pipealloc`, i.e. at `t > 0` — §0.12′ ruling 4 / the park memo's ruling item 4, which is the single most important correction in that memo and applies verbatim here.

### (d) — the honest weakening of the sealed surface: `CtxMorph` as an entailment

```coq
Class CtxMorph (R : CtxId → iProp Σ) :=
  ctx_morph : ∀ ξ ξ', ctx_dom ξ ξ' -∗ R ξ -∗ ctx_dom ξ ξ' ∗ R ξ'.     (* -∗, not ==∗ *)
```

**Twin image: `TsoCtxTwin2.ctx_morph_pointsto` (`:569`) with `iModIntro` deleted, and the REAL kit's `/shared/xv6iris-3-fliptree-backup/iris/TsoCtx.v:763` likewise.** Measured in §1.1: neither proof contains an `iMod`. Every derived instance (`_sep`, `_exist`, `_big_sepL`, `_word`, `_const`, `_const_pay`) is `iMod`-free once the base is. This is a **strengthening** of the exported surface, provable at both instantiations, and it is the honest statement of what the construction does.

**What it buys.** `▷` is monotone, so `CtxMorph R → (▷ R ξ ⊢ ▷ R ξ')` *modulo* the `ctx_dom` (which is consumed under the `▷` and returns under it — §1.2). It is therefore **not** a `▷`-crossing on its own; it is a cheap correctness/clarity win and it removes a modality from the fixpoint story wherever a payload does end up under a `▷`. **Do it, but do not sell it as the fix.**

**Cascade, counted:** two consumption sites in the whole tree — `ProofAcquire.v:666` and `ProofRelease.v:576`, both `iMod (ctx_morph ξ0 cur_ctx with "Hdom HRes") as "[_ HRes]"` → `iDestruct`; six instance proofs in `KallocInv.v:389–441` (`iMod` → `iDestruct` throughout); `TsoCtx.ctx_deposit` (`:569`, its own `iMod (ctx_morph …)` becomes `iDestruct`; the lemma stays `==∗` because `ctx_dom_to_parked` is a genuine update). **Nine call sites, three files.**

**No other weakening is worth proposing.** I considered and reject: (i) persistent `ctx_dom` — refuted by design (`TsoCtx.v:460–467`) and unsound at the twin; (ii) a `ctx_pointsto ξ ⊣⊢ ctx_pointsto ξ'` escape — forbidden by ruling 3 (`TsoCtx.v:45–50`) and false at TSO; (iii) a persistent transport certificate `□(R ξ -∗ R ξ')` — refuted in §1.2: the derivation of `t ≤ B'` needs `ctx_at ξ (1/2)`, which cannot go under `□`.

---

## 3. Ranked recommendation

### Owner rulings (four)

1. **`SwtchCtx.valid_context_pre`'s six ambient rows move to the record's own `XIp`, and `valid_context` becomes context-free.** This is the load-bearing ruling. It ratifies as *implementation* what `SwtchCtx.v:227–244`'s header already asserts as *intent*, and it is §0.11′'s ruling applied to the scheduler tier. Falsifies nothing in the notes; **corrects** §0.12′'s "way out 2 is blocked on a ▷/fixpoint-capable transport" to "blocked on a statement defect with the same shape as design problem 2's".
2. **`ftable_res`'s cinv bodies are indexed by the slot, via a new `fp_ctx : CtxId` field on `fpnames`** — not ∃-closed. Ratify with the stage-2 caveat above stated in the header.
3. **`CtxMorph` becomes an entailment.** Cheap, provable at both instantiations, nine call sites.
4. **The M3 sweep runs leaves-first** (§4). This is an ordering ruling, not a design one, but it is what keeps the swtch deposit from being circular, and getting it wrong costs a full round-trip.

### Mechanical (in dependency order)

- λ-convert the leaf payloads: `disk_res` (173 sites / 86 files), `log_res` (20/…), `pipe_res` (19/5), `sl_res_gen`+`sl_res` (18/…), `itable_res2`+`itable_res` (17/…), `bcache_res` (14/…), `tx_res` (10/…), `cons_res` (9/4). All measured ▷-free / `inv`-free / WP-free at the top level; `KallocInv.v:389–441` is the template. `wait_res` (37 sites), `nextpid_res` (18), `ticks_res` (13), `<{ emp }>` (12) are **already ξ-free and need nothing** (§0.12′'s measured row). Total sweep surface: **450 `<{ }>` sites in 165 files**, of which ~80 are provably no-ops.
- The `(XI := XIp)` annotations in `valid_context_pre` (6 rows) and the `p_sched` argument (32 occurrences / 13 files, type-level).
- The four `valid_context_pre` destruct sites.
- `fpnames` + `off_hold`/`off_content` (24 + 32 occurrences, 9 files).
- `iMod (ctx_morph …)` → `iDestruct` (9 sites, 3 files).

---

## 4. The ordering that makes the swtch deposit non-circular

`p_sched` carries `trap_csrs → intr_res = ∃ C, □ C ξ ∗ ▷ ihs kt C h` (§0.11′). For (e)'s swtch deposit, `□ C ξ → □ C XIp` must hold. `C := devintr_caps_fam` and §0.11′ **measured** that of `devintr_caps`' seven conjuncts, five (`console_caps`, `disk_geom`, the disk `is_lock`, `tick_keeper`, `procs_inv`) are ξ-dependent *only because of the constant embedding* — "the ξ-dependence of every handle in the tree is an artifact of the constant embedding, not of the semantics". Therefore:

1. **Sweep the leaf payloads first** (`disk_res`, `cons_res`, `log_res`, `bcache_res`, `itable*`, `sl_res*`, `tx_res`, `pipe_res`). None is blocked. After this, `console_caps`, `disk_geom` and the disk `is_lock` are closed terms.
2. **`off_hold`/`ftable_res`** (ruling 2). Independent of everything above. After this `is_ftable` is a closed term.
3. **(e) at `SwtchCtx`/`SchedCtx`** → `CtxMorph proc_lock_res` → λ-convert `proc_lock_res` (40 sites / 17 files) → **`procs_inv` is a closed term**.
4. `devintr_caps` is now ξ-free in all seven conjuncts → `devintr_caps_fam` is constant in ξ → `□ C ξ ⊣⊢ □ C ξ'` → **`intr_res`/`trap_csrs` are trivially morphable** → the `ProofSwtch` deposit is data-only.
5. `ProofForkretPark.forkret_park_paid` closes: `procs_inv`/`park_globals`/`proc_lock_res` are ξ-free persistent handles the parker can simply hand over; `is_kstack` and the `initproc ↦₈□` share are `ctx_morph_word` payloads deposited by `TsoCtx.ctx_deposit` (`:569`) into the freshly-minted `XIc` — which is precisely what `ctx_deposit`'s header says it is for ("a fork's hand-me-downs"). **§0.13′'s "a freshly minted context has none, and none can be given to it" becomes false the moment the handles are closed terms — which is what §0.13′ itself predicted ("way out 2 … is now the ONLY way out").**

Step 3 is the only step whose ordering is forced; steps 1 and 2 are independent and parallelisable.

---

## 5. The cheapest experiment (≈30 minutes, no full build)

Two probes, in `/tmp`, using §0.13′'s measurement kit — `Check @f` (a `TsoCtx.CurCtx` in the printed type = ξ-indexed) and `Goal (f (XI := xi) … : iProp Σ) = f (XI := xj) …; tryif reflexivity then idtac "CONV" else idtac "NOTCONV"`, which fails **fast** under the hermetic seal where `iExact` crawls.

**Probe A — does (e) actually close it?** Import `SchedCtx`. In a section with two `CtxId`s `xi xj`, state by hand the *reshaped* `valid_context_pre` (the six rows at `XIp`, `P` at `XIp`) as a local definition `vcp'`, take its fixpoint, and check
```coq
Goal (valid_context' p_sched' None c p : iProp Σ) = valid_context' p_sched' None c p.  (* no CurCtx to differ *)
Check @valid_context'.   (* PASS iff no TsoCtx.CurCtx appears in the printed type *)
```
`Check` alone answers it: if the reshaped `valid_context'` prints without a `CurCtx`, `▷ proc_ctx` is `ctx_morph_const` and the whole ▷/fixpoint problem is gone. **This is the single measurement that validates or refutes the front-runner**, and it needs no proof, only elaboration.

**Probe B — is the swtch deposit payable, and when?** Same file:
```coq
Check @IntrDefs.trap_csrs.   (* confirms the CurCtx *)
Goal (trap_csrs KT1 (CID := h) (XI := xi) : iProp Σ) = trap_csrs KT1 (CID := h) (XI := xj);
  tryif reflexivity then idtac "CONV trap_csrs" else idtac "NOTCONV trap_csrs".
```
Expect `NOTCONV` today (it is `intr_res`'s `□ C ξ`). Re-run it **after** step 1 of §4's ordering; the transition `NOTCONV → CONV` is the gate that says (e) may land. If it does not flip after step 1, the caps family needs `intr_res` restated as `∃ C, □ (∀ ξ, C ξ) ∗ ▷ ihs kt C h` — a one-line change at `IntrDefs`, six destructuring sites (`WpSconfSret`, `WpSconfCsr` ×3, `ProofPrepareReturn`, `ProofKernelvec` ×2, `WpIntrInv`) per §0.11′'s own fallout list, and *not* a new law.

**Do not** attempt an `iApply` of `forkret_park_paid` or an `iExact` across two ξ inside `procs_inv`'s 64-element big-op as a probe: §0.12′ measured 23 minutes and §0.12′'s memo-correction records that a **crawl is the signature of an unprovable crossing** here, because the seal fails fast only at the head symbol.

### MEASURED (2026-08-26, both probes run)

**How they were run, and the one caveat.** The tree's `.vo` state is **stale** —
330 sources are newer than their objects, and `RiscvLang.vo` (07:53) predates
the `TsoMemPa.vo` (07:56) it depends on, so `coqc` refuses the library with
*"makes inconsistent assumptions over library xv6iris.TsoMemPa"*.  Nothing
above `RiscvLang` can be loaded without a full rebuild, which is not a probe.
Both probes were therefore run **self-contained** against the matching switch
(`opam exec --switch=/shared/xv6rocq -- coqc`, Rocq 9.0.1): `CtxId`/`CurCtx`
mirror `TsoCtx.v:77–99` verbatim (record identity, transparent class, no
default instance), and each row is an abstract parameter carrying **exactly**
the tree's ξ-profile.  Probes at
`…/scratchpad/probe/{ProbeA,ProbeB}.v`; both exit 0.
*This tests the SHAPE of the reshape, which is the load-bearing question; it
does not re-measure the tree's own constants.*

**PROBE A — PASS, on all three counts.**

```
@vc_old  : ∀ Σ, … → (CtxId → nat → iProp Σ) → (nat → nat → iProp Σ)
                  → (nat → iProp Σ)
                    → CurCtx                        <-- THE AMBIENT INDEX
                      → (nat -d> ctx_adm -d> …) → ctx_adm -d> nat -d> nat -d> iPropO Σ

@vc_new  : ∀ Σ, … → (CtxId → nat → iProp Σ) → (nat → nat → iProp Σ)
                  → (nat → iProp Σ)
                    → (CtxId -d> nat -d> ctx_adm -d> …)   <-- P gains its CtxId
                      → ctx_adm -d> nat -d> nat -d> iPropO Σ
                                                    <-- NO CurCtx ANYWHERE
```

1. **`CurCtx` disappears.**  With rows [1]–[5] at the record's own `XIp` and
   `P` at `XIp`, the fixpoint elaborates with **no `CurCtx` instance in scope
   at all** — not merely absent from the printed type, but not required for
   elaboration.  `valid_context` becomes a closed term, as §0/§2(e) claim.
2. **Contractiveness survives, with the tree's own tactic verbatim.**  Both
   `vcp_old_contractive` and `vcp_new_contractive` close under
   `solve_proper_prepare. repeat (f_contractive || f_equiv). all: try apply H.`
   — `SwtchCtx.v:274–278` unchanged.  §0.11′'s `ires_of_contractive` fallback
   chain is **not** needed: the extra leading `CtxId` on `P` is a discrete-fun
   argument, not a recursive occurrence.
3. **The blocking obligation discharges by instance search alone.**
   `CtxMorph (λ _ : CtxId, ▷ vc_new P A c p)` closes with `apply _.`, resolving
   through `ctx_morph_const` — i.e. once `valid_context` is closed, `▷ proc_ctx`
   and `▷ sched_vc_at` are constant payloads and **no `▷`-capable transport is
   invoked**.  This is the exact obligation that has gated M3 since the flip.

**PROBE B — baseline confirmed, and the obstruction localised to one row.**

Against the `intr_res` shape §0.11′ landed
(`∃ h C, □ C ξ ∗ ▷ ihs C c h`, with `ihs` ξ-generic):

```
NOTCONV ires_now
NOT-TRANSPORTABLE ires_now (the [box C xi] row)
@ires_now      : ∀ Σ, (…) → CtxId → nat → iProp Σ     (ξ-INDEXED)
@ires_uniform  : ∀ Σ, (…) →          nat → iProp Σ     (ξ-FREE)
@ires_uniform_member : … ires_uniform ihs c ⊢ ires_now ihs ξ c
```

- `NOTCONV` — the expected baseline.  §0.13′'s recorded kit result already
  lists `trap_csrs` (and `intr_res`) as `NOTCONV` against the real tree; this
  probe reproduces it at the shape level and says **why**: the `▷ ihs C c h`
  row transports for free (`ihs` is ξ-generic, §0.11′), and the failure is
  isolated to the credential row `□ C ξ`.  The second goal frames everything
  except that row and then fails precisely at `□ C xj` from `□ C xi` — abstract
  `C`, higher-order, no instance.  **The swtch deposit under (e) is blocked by
  one conjunct, not by `trap_csrs` as a whole.**
- The fallback restatement **works**: `ires_uniform` (`∃ h C, □ (∀ ξ, C ξ) ∗ ▷ ihs C c h`)
  takes **no `CtxId`**, and `ires_uniform_member` is proved — the uniform form
  yields the member at every ξ, so no consumer loses anything.

**What this settles.**  Ruling 1 is validated: (e) removes the ambient index,
keeps the fixpoint contractive, and hands the M3 obligation to
`ctx_morph_const`.  §4's ordering gate is validated as *stated but not yet
cleared*: the deposit needs `□ C ξ → □ C XIp`, which step 1 of §4 delivers by
making `devintr_caps_fam` constant — and if it does not, §5's one-line
`∃ C, □ (∀ ξ, C ξ) ∗ ▷ ihs` restatement provably does, at six destructuring
sites and no new law.

**Still to measure against the real tree** (needs a rebuild, not a probe):
re-run §0.13′'s `Check`/`reflexivity` kit on `IntrDefs.trap_csrs` after §4 step
1, and confirm the `NOTCONV → CONV` flip.  That is the gate that says (e) may
land.

---

## 6. Should this land in the fliptree first?

**No for (e), (c) and (d); yes for the one law that (a1) would need, if (a1) is ever taken.**

The fliptree's `TsoCtx.v` carries the REAL bodies (`ctx_pointsto_def` over the store-buffer heap, `ctx_dom_def` over the borrowed halves) behind the same hermetic seal, with kit-facing gates (`ctx_load_ok`, `twin_passed_get`, `ctx_dom_of_parked` at the live interp). I checked the one thing that could differ: **`ctx_morph_pointsto` at the REAL kit (`fliptree/iris/TsoCtx.v:763–786`) is `iMod`-free**, exactly as at SC — so (d) is provable there unchanged, and (e)/(c) are *statement* changes above the seal that the kit never sees. Landing them on `tso` first is right: they are the changes whose failure mode is a fast compile error under the hermetic seal, which is the whole reason the seal was made hermetic (§0.10′ item 2).

The exception is **(a1)'s fractional `ctx_dom`**: an arity change on a sealed constant, whose twin obligations (`ctx_at_halves`/`ctx_at_agree` at general fractions, the two mints, the two give-back wands) are all *kit-side*. If the §5 probe refutes (e), prove `ctx_dom_split` in the fliptree first and back-propagate the arity — do not guess it above the seal.

---

## 7. Corrections to the notes, for the record

- **`tso-park-protocol-memo.md` §3 option (λ)**: *"`CtxMorph`'s bare `==∗` cannot cross the `▷` … needs a `▷`-capable/step-taking transport, a genuine new law on the sealed surface"* — the diagnosis is right, the conclusion is not. The `▷` is over `valid_context`, and `valid_context`'s ξ-dependence is six mis-indexed rows, not semantics. **No new law is needed.**
- **`tso-port.md` §0.12′ memo-correction**: *"`file_core`'s `is_pipe` is a second instance of the same thing"* — it is not. `is_pipe` is `inv lockN (lock_inv … <{ pipe_res }>)`, an ordinary `const_pay` payload over a ▷-free, `inv`-free `pipe_res`. **The M3 sweep is blocked on ONE payload (`off_hold`), not two.**
- **`tso-port.md` §0.12′ ruling on ∀-`Xr`**: *"right, and free once the handles are ξ-free. It is just not sufficient on its own."* — the quantifier is wrong, not insufficient. The record binds `∃ XIp` and the protocol makes the resumer *become* `XIp`; a second `∀ Xr` is stale one ghost step after the exchange.
- **`TsoCtx.v:479` / `TsoCtxTwin2.v:566`**: the `==∗` is unused in every twin proof, at SC and at the REAL kit. The class is an entailment.

---

## 8. CORRECTIONS FROM THE LANDING (2026-08-26; see tso-port.md §0.15′)

Ruling 1 landed and is confirmed on the real tree: `valid_context`,
`SchedCtx.p_sched`, `proc_ctx` and `sched_vc_at` all print with no
`CurCtx`, contractiveness closes with the tree's own tactic, and `▷
proc_ctx` / `▷ sched_vc_at` are `ctx_morph_const`. Three things the memo
got wrong:

- **§5's `ires_uniform` fallback (`∃ C, □ (∀ ξ, C ξ) ∗ ▷ ihs kt C h`) is
  UNSOUND and must not be taken.** `devintr_caps` holds two rows of cells
  discarded at RUNTIME — `disk_geom`'s three ring-page pointers and
  `procs_inv`'s per-slot `is_kstack` — and a ∀-context form over a `t > 0`
  discarded fact is exactly what §2(c)'s own stage-2 caveat (tso-port.md
  §0.4 item 6) forbids. What the swtch deposit needs is not context
  freedom but TRANSPORTABILITY: `IntrDefs.caps_morph C :=
  □ ∀ ξ ξ', ctx_dom ξ ξ' -∗ □ C ξ -∗ ctx_dom ξ ξ' ∗ □ C ξ'`, carried by
  `intr_res` beside `□ C ξ` and discharged once from the structural
  instances. **§4's gate (`trap_csrs` `NOTCONV → CONV`) is therefore the
  wrong test and never had to flip**; `trap_csrs` stays `NOTCONV` and is
  `CtxMorph`, which is all the deposit wanted.
- **§2(e)'s cascade count omitted the section surgery.** A section
  variable cannot be instantiated inside the section that binds it, so
  `valid_context_pre` (which must spell `ctx_cells (XI := XIp)`) and
  `p_sched` (which must spell `proc_held (XI := ξ)`) have to sit BELOW the
  sections that define those. `SwtchCtx.v` is two sections above its shim,
  `SchedCtx.v` four. The sections that must not capture an ambient declare no `XI` at
  all, so a forgotten annotation is an elaboration error rather than a
  silent capture.
- **§4 step 5 is REFUTED, on one row.** With every other row transporting,
  `forkret_park_paid`'s deposit into the fresh `XIc` fails at
  `park_globals`' `FileInv.is_ftable` — `is_lock γl ftable_addr "ftable"
  <{ ftable_res γ }>`, a constant embedding of a still-ξ-indexed payload,
  hence two `inv`s over different bodies. Measured: `NOTCONV is_ftable`,
  `NOTCONV ftable_res`, `NO-INSTANCE CtxMorph is_ftable`, against `MORPH
  procs_inv OK` / `MORPH console_caps OK` / `MORPH console_ready OK`. The
  memo's ruling 2 (the `fp_ctx` field) was already refuted at §0.14′; its
  replacement (the off-borrow cinv stops holding a points-to fraction) is
  what unblocks the park, and it is now the ONLY thing that does.
