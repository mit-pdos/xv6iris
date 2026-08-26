# DECISION MEMO — TSO port, design problem 1 (sleep/swtch parking)

Read-only analysis on branch `tso` @ `b6a2a496` (2026-08-26); no files
edited, no build run; every claim is static reading of the sources plus
the notes' own measurements.  Produced for the owner decision that
tso-port.md §0.10′ requests before implementing the park-protocol fix.
Line numbers are from that tree.

---

## 1. The exact current statement, and where it dies

### 1.1 `UsertrapRes.ut_res_bare_park` (`iris/UsertrapRes.v:1732–1768`), verbatim

```coq
Lemma ut_res_bare_park `{XI : CurCtx}
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
      !irefslotG Σ, !pavG Σ} `{GEN : GenId}
    (Rsys : gname -> mword 64 -> bio_names -> fclose_names -> iProp Σ)
    (W : iProp Σ) (N : ut_names) (av : nat) :
  ut_wf N -> (K_usertrap <= av)%nat ->
  ut_park_caps N -∗
  (FirstTok.first_done -∗ W -∗ Rsys (un_f N) (un_pj N) (un_bn N) (un_fn N)) -∗
  park_own N -∗
  (∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (V' : pprivate),
     ⌜pv_upt V' = pt'⌝ -∗
     ut_tfk (CID := h) (add_vec (un_ks N) (mword_of_int 4096)) V' -∗
     FirstTok.first_done -∗
     W -∗
     timer_cap (CID := h) -∗
     ut_trap_parked (CID := h) (XI := Xc) (un_pj N)
       (add_vec (un_ks N) (mword_of_int 4096)) av ∅ -∗
     proc_priv_nopt (un_f N) (un_pj N) (un_pid N) V' -∗
     fd_slots FDSPARE -∗ iref_slots IREFSPARE -∗
     ut_res_bare (CID := h) (XI := Xc) Rsys pt'
       (add_vec (un_ks N) (mword_of_int 4096))).
```

**The single structural defect, stated exactly:** every premise except
`ut_trap_parked` elaborates at the *section-ambient* `XI` — the parker's
ξ — while the conclusion is `ut_res_bare (XI := Xc)` at the ∀-bound
resumer's ξ.  `Rsys` is worse than ξ-mismatched: it is a *parameter
bound outside the ∀*, so a single `Rsys` must serve every `Xc`.  It
cannot, because `ut_res_bare (XI:=Xc)`'s `ut_own_nopt` row is
`Rsys (un_f N) …` and the caller's `Rsys` is `SY.syscall_env`, which is
itself ξ-indexed.

### 1.2 First failure point

The proof body is two intro steps and then `Abort` (`:1764–1768`); the
`Abort` is deliberate, so there is no *recorded* failing tactic.  The
failing steps are in the kept body (`:1772–1789`), against the goal
`ut_res_bare (CID:=h) (XI:=Xc) Rsys pt' ksp`:

| kept-body step | status | why |
|---|---|---|
| `iDestruct ("Hderive" with "Hdone HW") as "Hsys"` | succeeds | all three at ξ |
| `iDestruct (ut_caps_of_park with "Hpark Hrdy") as "#Hcaps"` | succeeds, **produces the wrong fact**: `ut_caps (XI:=ξ) N` | `ut_caps_of_park` (`:718`) is stated wholly at the ambient |
| four pure `iSplitR`s | succeed | |
| `iSplitR; [iExact "Htfk" \| ]` | **FIRST FAILURE under the hermetic seal** | goal `ut_tfk (XI:=Xc)`, hyp at ξ. `ut_tfk` (`:913`) = `∃ kroot, kpt_inv kroot ∗ ⌜…⌝`; `kpt_inv` = `inv kptN (kpt_body root)` (`KptShare.v:79`) and `KptShare` imports `TsoCtx`, so the invariant *body* is ξ-indexed and the two `inv`s are different propositions. |
| …later, the `ut_caps` row after `rewrite /ut_env_nopt` | the **pre-hermetic** failure | the measured 35-minute `iExact "Hcaps"`: `ut_caps (XI:=Xc) N` vs `ut_caps (XI:=ξ) N`, the unifier exhausting itself on an unprovable goal (§0.8′). |

This matches §0.9′ ("under the hermetic seal the park lemma fails at
`first_done`/`W`, not just at the caps"): `first_done` =
`first_addr ↦₄□ 0 ∗ fs_ready`, and `ut_caps` carries `FsReady.fs_ready`
as a conjunct, so the `first_done` the closer is handed at ξ can never
discharge the `fs_ready` the conclusion needs at `Xc`.

### 1.3 `UtResFits.v:169` — a *statement*-level failure, not a proof one

```coq
iApply (ut_res_bare_park (SY.syscall_env) (park_token (un_s N)) N av Hwf Hav
        with "Hcaps [] Hown").
```

Today this fails trivially (the lemma is Aborted, so the name does not
exist).  But **even if the lemma were proved as stated it would not
apply here**, and this is the load-bearing observation for the
redesign: `UtResFits.usertrap_res_bare` is
`Definition usertrap_res_bare `{… XI : CurCtx} := ut_res_bare (SY.syscall_env)`.
One binder `XI` serves *both* occurrences, so instantiating at `Xc`
re-indexes the environment too:

    usertrap_res_bare (XI := Xc)  ≡  ut_res_bare (XI := Xc) (SY.syscall_env (XI := Xc))

The goal (`UtResFits.v:160`) quantifies `Xc`, so it needs a *different*
`Rsys` per `Xc`; `ut_res_bare_park` offers one fixed `Rsys`.  **`Rsys`
must move inside the ∀ (i.e. become per-`Xc`) regardless of which
option below is chosen.**  So must the derive-wand at `:1740`, since it
produces `Rsys` and consumes `first_done`.

---

## 2. Anatomy of the ξ-dependence — the evidence the options turn on

`park_env N` (`UsertrapRes.v:1653`) = `ut_park_caps N ∗
sysc_park_extra (un_tk N)`.  Row by row:

| # | row | ξ-dep? | source of the dependence |
|---|---|---|---|
| 1 | `⌜fclose_ties (un_fn N)⌝` | **no** | pure; pins 18 `un_*` fields to `fsc_*`/`icfg_*` |
| 2 | `⌜un_pr N = fsc_printk⌝` | **no** | pure |
| 3 | `procs_inv (un_s N)` | **YES** | `<{ proc_lock_res γl pa }>` — `p_chan ↦₈`, `proc_pub`, `proc_slots` → `▷ proc_ctx` → `valid_context` → `stack_own` + `p_sched` (`SchedCtx.v:447,711`) |
| 4 | `is_kstack (un_pj N) (un_ks N)` | YES | `p_kstack pa ↦₈□ ks` (`ProcDefs.v:89`) — *discarded* |
| 5 | `devintr_caps_any …` | YES | only via `disk_geom` (discarded cells) and `procs_inv`; `dev_inv` is ξ-free (`WpUart.v` does not import `TsoCtx`), `is_tickslock` is ξ-free today (`ticks_res` is `↦₄`, unflipped) |
| 6 | `is_lock (un_w N) … <{ wait_res }>` | **no, today** | `WaitInv.v` does not import `TsoCtx`, so `p_parent ↦₈ v` is the raw fact.  Becomes ξ-dep at the stage-2 flip. |
| 7 | `is_ftable (un_ft N) (un_f N)` | YES | `<{ ftable_res γ }>` → `fslot` → `file_fields` (`↦ₘ`, `↦₈`) |
| 8 | `disk_geom (un_v N) (un_pd N) (un_pav N) (un_pu N)` | YES | three `↦₈□` pointer cells |
| 9 | `park_world (un_s N)` | YES | only via `procs_inv`, `disk_geom`, and the `initproc ↦₈□` share |
| 10 | `sysc_park_extra (un_tk N)` | YES | only via `console_ready` (`devsw_table` = `↦₈□` big-op, `is_conslock` → `<{ cons_res }>`) |

Plus `park_own N` (`:1107`) = `bslots 3 ∗ initproc ↦₈{un_dqi N} (un_ip N)`
— ghost + one discarded share; and `proc_priv_nopt`, `ut_tfk`,
`first_done`, `W = park_token …` inside the ∀, all at ξ.

Three separate mechanisms, needing three different answers:

* **(A) `<{ P }>` const_pay lock payloads.**  The *handle*
  `is_lock γ lk s R` is ξ-free in shape; `R : CtxId → iProp` is a
  parameter and `lock_inv` already `∃`-closes it (`WpLock.v:336,385`).
  It is ξ-dependent only because `const_pay P` elaborates `P` at the
  outer ambient.  λ-converting `R` to `(λ ξ, P (XI:=ξ))` makes the
  handle a **closed term** with zero transport cost *at the handle*;
  the cost lands as the `CtxMorph R` obligation at acquire/release
  (`SpecAcquire.v:255–267`, `SpecRelease.v:210–222`).
* **(B) discarded (`↦₈□`, `↦ₘ□`) cells.**  `is_kstack`, `disk_geom`,
  `devsw_table`, the `initproc` share.  §0.4 item 6 flags "immutable
  bytes are CONTEXT-FREE, audit before M1's flip"; **the audit was
  never done, and `TsoCtxTwin2` says the ruling is only half true.**
  In Twin2, `ctx_pointsto ξ a dq v = ∃ t, a ↪[γheap]{dq} (t,v) ∗
  (mono_nat_lb_own (tc_bnd ξ) t ∨ (t,a) ↪[tc_dirty ξ]{dq} ())`
  (`TsoCtxTwin2.v:337`).  A **timestamp-0** discarded byte *is*
  context-free (`own_context_lb0`, `ctx_pointsto_intro_zero`,
  `:982–998` — "the twin image of kernel text is context-free").  A
  byte discarded at `t > 0` — which `p->kstack`, the ring-page pointers
  and `devsw[]` all are, written by `procinit`/`virtio_disk_init`/
  `consoleinit` at WP time — needs `mono_nat_lb_own (tc_bnd ξ') t`,
  i.e. re-indexing along `ctx_dom` (`twin_share`, `:961`).  `ctx_dom`
  is deliberately **not persistent** and is minted only at
  release/acquire and park/resume.  **Conclusion: a discarded fact
  cannot ride the parked record across the park by fiat.**  It must
  either be re-supplied by the resumer or reduced to a pure equation.
* **(C) the escape hatch nobody is using.**  `TsoCtx.ctx_pointsto_agree`
  (`:326`) and `ctx_word_pointsto_agree` (`:447`) are stated over **two
  free contexts** `ξ1 ξ2` and require no `ctx_dom`.  They are the only
  laws in the sealed surface that relate two contexts for free, and
  they yield exactly what a name-pinning argument needs: `⌜w1 = w2⌝`.

---

## 3. The options, costed

Common to all three: `Rsys` and the derive-wand move inside the ∀
(§1.3), and `first_done`, `ut_tfk`, `proc_priv_nopt` gain `(XI := Xc)`.
That part is not optional and not in dispute.

**A fact that makes all of this cheaper than it looks:** at the *one
and only* application site of the closer — `ProofForkret.v:667`,
`iDestruct ("Hyield" $! CIDf XI pt (upd_upt V' pt) …)` — forkret
instantiates **`Xc := XI`, its own ambient context**.  So every premise
re-indexed to `Xc` is discharged by whatever forkret already holds at
its own ξ, with no conversion.  The redesign is expensive to *state*
and nearly free to *apply*.

### Option (a) — pin the remaining `un_*` fields as pure ties

**Verdict: partially impossible, and the impossible part is decisive.**

* 20 of the 24 relevant fields are **already pinned** by `fclose_ties`,
  `ut_wf`, `⌜un_s N = γs⌝`, and row 2 — nothing to add.
* `un_pd`/`un_pav`/`un_pu` **have no global constant to be tied to.**
  `fsc_desc`/`fsc_avail`/`fsc_used` were deliberately removed from
  `fscfg` (`FsReady.v:305–318`, `FsCfg.v`'s note: `virtio_disk_init`
  `kalloc`s the pages at WP time, so no boot-era `fupd` can give the
  record a value).  `fs_ready` quantifies them existentially.  **There
  is no pure tie to write.**
* `un_w`/`un_ft`/`un_f`/`un_tk` are gnames with no global constant
  either, and no cells to agree on.

Cascade if pursued anyway: `ParkCap.v` whole file, `UsertrapRes.v`,
`UtResFits.v`, plus a new obligation at both parkers
(`ProofKforkB5.v:240–255`, `ProofUserinit.v:711–735`) per added tie.
**Rank: rejected on soundness of statement, not cost.**

### Option (b) — split the bundle: global part resumer-supplied, N-specific pure facts record-carried

**Statement change.**  `park_chan`'s arity unchanged.  `park_env N`
splits:

```coq
(* record-carried, at the parker's ξ — must be ξ-FREE *)
Definition park_pure (N : ut_names) : Prop :=
  fclose_ties (un_fn N) /\ un_pr N = fsc_printk.

(* resumer-supplied, inside the ∀, at Xc, at the RESUMER's own names *)
Definition park_globals `{XI : CurCtx} (γs : list gname) : iProp Σ := …
```

and the channel becomes

```coq
Definition park_chan `{XI : CurCtx} URB (W : CurCtx -> iProp Σ) (γs : list gname) : iProp Σ :=
  (□ ∀ (N : ut_names) (av : nat),
     ⌜un_s N = γs⌝ -∗ ⌜ut_wf N⌝ -∗ ⌜park_pure N⌝ -∗ ⌜(K_usertrap <= av)%nat⌝ -∗
     ▷ (park_own N -∗
        ∀ (h : CpuId) (Xc : CurCtx) (pt' : uptd) (V' : pprivate),
          procs_inv (XI := Xc) γs -∗          (* pinned by ⌜un_s N = γs⌝ *)
          park_globals (XI := Xc) γs -∗
          … first_done (XI:=Xc), W Xc, ut_tfk (XI:=Xc), proc_priv_nopt (XI:=Xc) … -∗
          URB h Xc pt' …))%I.
```

**What the resumer can actually supply at `Xc = XI`** (checked against
`wp_forkret_gen_body`, `SpecForkret.v:278–334`): `procs_inv γs`,
`wire_inv`, the trampoline `kmap_at`, `kernel_text`, `is_kstack p ks`
(with `p`/`ksp` definitionally `un_pj N`/`add_vec (un_ks N) 4096` at
the `park_token_park` instantiation), everything reachable from
`first_done ⇒ fs_ready` (dev_inv, printk_env, the disk lock + an
∃-witnessed `disk_geom`, kmem lock, kalloc_avail, bitmap_inv,
itable/ireg), and `W = park_token γs` — all already premises.  NOT
supplied: `disk_geom` at `un_pd/un_pav/un_pu` specifically (vs the
∃-witness), `is_ftable (un_ft N) (un_f N)`, `console_ready`/
`console_caps fsc_uart`.  The four ξ-free rows (`is_tickslock`, the
wait lock, `procs_avail`, nextpid) stay record-carried at zero cost.

**The bridge for the disk row exists.**  `ctx_word_pointsto_agree`
(`TsoCtx.v:447`) is cross-context.  Restate `disk_geom_agree` over two
contexts — the record's `disk_geom (XI:=ξ)` is carried *only* to be
consumed into `⌜un_pd N = pd⌝ ∧ …` against the resumer's `fs_ready`
witness at `Xc`; the real row is the resumer's.  This is exactly the
recovery `ut_park_caps`'s own header already describes; the only change
is that the agreement now spans two contexts, which the sealed law
already permits.  **One lemma, `DiskInv.v`.**  The identical move
covers `is_kstack` (against `procs_inv`'s `∃ ks, is_kstack …`) and the
`initproc` share.

**Residual, after the bridge — two bounded sub-fixes:**
* `is_ftable`: λ-convert `ftable_res`.  Plain resource — no `▷`, no
  fixpoint, no WP — so `CtxMorph (λ ξ, ftable_res (XI:=ξ) γ)` follows
  from the existing structural instances; `KallocInv.v:389–441` is the
  line-for-line template.  Sites: **10** `<{ ftable_res }>` occurrences
  in 5 files (`FileInv.v:54`, `ProofFilealloc.v:334,898,1003`,
  `ProofFiledup.v:281,457`, `ProofFileclose.v:326,553,972`,
  `ProofMain.v:1585`); the 52 `is_ftable` mentions in 32 files are
  unchanged (the handle's type does not move).
* console: add `console_ready` (and `console_caps fsc_uart`) as rows of
  `FsReady.fs_ready` — 2 rows + 2 projection lemmas + the one builder.
  Reverses the small ruling at `ConsoleInv.v:255–262` (owner nod
  wanted; nothing structural at stake).

**Full cascade:** `UsertrapRes.v` (park_env split; `ut_park_intro_body`;
`ut_res_bare_park` restated + reproved ~60/~30 lines; a two-context
`ut_caps_of_park`; `park_own` loses the `initproc` share), `ParkCap.v`
(effectively the whole 244-line file, incl. `park_token_F` +
contractive proof), `UtResFits.v` (both module types + the fit proof),
`SpecForkret.v`, `SpecForkretParkPaid.v`, `SpecForkretPark.v`,
`ProofForkretPark.v` (2 theorems; the two
`(XI := MkCtxId inhabitant inhabitant)` pins go away),
`ProofForkret.v` (closer premise + threading; the application at :667
stays a one-liner), the pass-through `Definition`s in
`ProofUserretClosed.v:225`/`ProofUsertrap.v:1194`/`ProofUservec.v:80`/
`ProofForkret.v:144`, the two parkers (`ProofKforkB5.v:240` and
`ProofUserinit.v:711` — their `iAssert (park_env N)` blocks DELETE,
~45 lines net removal), `park_token` type-level threading in ~17 files,
one agreement lemma each in `DiskInv.v` and `ProcDefs.v`, the
`ftable_res` λ-conversion (5 files), and the 2 `FsReady.v` rows.

**New obligations, all discharged by existing law:** cross-ξ agreement
(`ctx_pointsto_agree`/`ctx_word_pointsto_agree` as written); the
`ftable_res` CtxMorph (structural instances, kmem precedent);
`procs_inv γs` at `Xc` (already a `wp_forkret` premise).  Transporting
an `is_lock` handle between contexts is needed NOWHERE (no law exists
and none can — invariant bodies are not updatable; the design avoids
it).

**Risks:**
* *Contractiveness of `park_chan`.*  The token stays under the same
  `▷`; `solve_contractive` handles ∀ structurally — low.  But `W`
  becomes `CurCtx → iProp Σ`, so `park_token_F` needs the OFE on
  `CurCtx -d> iPropO Σ` (`CtxId` is a discrete two-gname record, so it
  is available) — medium; budget an hour.
* *Silent capture* (§0.8′ rule 3): the new `∀ Xc` (and any `∀ ξp`) is a
  TC candidate inside its body.  **Every** re-indexed premise must be
  spelled with an explicit `(XI := Xc)`; none left ambient.  The
  highest-probability source of a lost day.
* *Performance*: `Global Typeclasses Opaque` on any big-op crossing the
  new seams (`ftable_res`'s `seq 0 NFILE` run; the `page_rest`
  4088-conjunct lesson).  `Set Printing Depth 40.` before touching
  `UsertrapRes.v`/`UtResFits.v`.  Never re-attempt an `iExact` across
  two ξ without first checking the goal is provable.

### Option (λ) — λ-convert the proc-lock payload so `procs_inv` is a closed term

Would erase row 3 with no channel change; the notes name it first.
Cascade: 43 `<{ proc_lock_res }>` occurrences across 18 files, plus
the `CtxMorph` instance.  **Blocked, structurally:**
`proc_lock_res ⊇ proc_slots ⊇ if needs_ctx st then ▷ proc_ctx pa` — a
`▷` over `SwtchCtx.valid_context`, a guarded fixpoint whose unfolding
contains a resume wand ending in `WP (LoopE gen_id h)`.
`CtxMorph`'s bare `==∗` cannot cross the `▷`
(`▷ |==> P ⊬ |==> ▷ P` — needs a `▷`-capable/step-taking transport, a
genuine new law on the sealed surface), and the WP's premises would
have to transport *contravariantly* — no story exists in the
bare-update shape.  §0.8′ ruling 3 records the attempt + revert; the
obstruction is structural, not a missing lemma.  For the *other*
payloads λ-conversion is genuinely mechanical.

## 4. Recommendation, ranked

1. **Option (b) with the agreement bridge** — cheapest sound path.
   The sub-question resolves as: *neither (a) nor (b) alone; (b) plus
   cross-context agreement for the fields (a) cannot pin.*  Four
   classes of `un_*` field, four answers, all already available:
   already-pinned (20 fields, cost 0); ξ-free-today rows stay
   record-carried (cost 0 now, revisit at stage-2 flip); ξ-indexed
   discarded cells ride the record *only to yield a pure equation* via
   `ctx_word_pointsto_agree` (2 small lemmas); `procs_inv` moves inside
   the ∀, resumer-supplied (free at the one call site).
2. **Option (λ) for the non-proc payloads only, as a follow-on** —
   `ftable_res` under (b) is the first step of the M3 sweep and
   validates the recipe on an NFILE-sized big-op.  Do not let it grow
   into the full sweep during this fix.
3. **Option (a) alone: reject.**  Unprovable for the three ring pages
   (no global name exists, by the deliberate `FsCfg` design).
4. **Option (λ) for `proc_lock_res`: reject for M2.**  Two structural
   obstructions (`▷`-transport; WP under a bare update).  Revisit only
   if a ▷-capable transport is added to the sealed surface — a Σ-shape
   question, not a park question.

### What needs an owner ruling (4 items)

1. **`W` becomes `CurCtx → iProp Σ`** (forced by §1.3).  Falsifies two
   standing header claims to correct in the same change:
   `ParkCap.v:88–99` ("ξ-FREE") and `SpecSyscall.v:265` ("HART-FREE,
   AND THAT IS PART OF THE CONTRACT").  *Alternative worth one hour
   before committing:* ∀-quantify the **parker's** ξ inside
   `park_cap`/`park_chan`
   (`□ ∀ ξp, … ▷ park_pkg (XI:=ξp) … -∗ |==> ▷ proc_ctx (XI:=ξp) γs pa`),
   keeping `park_token` ξ-free and `W : iProp Σ`.
   `ProofForkretPark.park_token_intro` already applies
   `forkret_park_paid` at an arbitrary `(XI := MkCtxId inhabitant
   inhabitant)` (`:317`) precisely because nothing pins it — the ∀ form
   is what that proof is morally doing, and the arbitrary witness is an
   artefact the hermetic seal would break anyway.  If it works it is
   strictly better; if not, fall back to `W : CurCtx → iProp Σ`.
2. **Console rows into `fs_ready`**, reversing `ConsoleInv.v:255–262`.
3. **`park_own` loses its `initproc ↦₈□` share** (redundant: both
   parkers pass `DfracDiscarded`, and `park_world` already carries
   `∃ ip, initproc ↦₈□ ip`).  Leaves `park_own = bslots 3`, ξ-free —
   removing the *last* exclusive ξ-crossing from the park.
4. **tso-port.md §0.4 item 6 must be re-worded**: "immutable bytes are
   context-free" holds for **timestamp-0** (boot-image) bytes only
   (`own_context_lb0`/`ctx_pointsto_intro_zero`).  A byte discarded at
   runtime re-indexes along `ctx_dom` (`twin_share`), which a parked
   record cannot carry.  **The single most important correction in this
   memo** — a fix built on the stronger reading of item 6 would look
   green at SC and fail at cutover.

### What is mechanical

Explicit `(XI := Xc)` on every re-indexed premise; deleting the two
parker `iAssert (park_env N)` blocks; the pass-through `Definition`
echoes; the two agreement lemmas; the `ftable_res` λ-conversion
(KallocInv template); `ProofForkret.v:667` stays a one-liner.

### Estimate

Statement work ~4 files deep, ~450 lines of Definition/Parameter text
(`UsertrapRes`, `ParkCap`, `SpecForkret`, `SpecForkretParkPaid`,
`UtResFits`); proof work concentrated in `ProofForkretPark.v`
(2 theorems) and `UtResFits.v` (1); the 17-file `park_token` threading
is type-level echo.  Two-thirds of the risk is in ruling item (1) and
the capture hazard; budget the `park_token_F_contractive` re-proof
separately.

### One thing to check before starting

`ProofKernelvec.v:1681` (design problem 2) is the same shape with
`devintr_caps` in place of `park_env`, and `devintr_caps_any` is
*already* the ξ-free-by-construction bundle this memo recommends
building for the park.  If `park_globals` is defined as
"`devintr_caps_any` minus `procs_inv` minus `disk_geom`", **the same
predicate serves both fixes** and problem 2 collapses into "the
trapping thread supplies `park_globals` at its own ξ".  Worth 30
minutes of confirmation before the shape of `park_globals` is frozen —
the difference between one M2 change and two.
