# Proof performance & build optimization

## RULE ZERO: run `-time` FIRST, before believing any theory

The section below ("`Qed` time is term size") is true and was the answer for a
whole class of files.  It is not the answer for every slow proof, and reaching
for it first cost real time once already.  **`coqc -time` prints a line per
command; look at that before profiling `Qed` at all.**  If the slow line is a
tactic, no amount of term-size work will help.

### The trap it found: `ltac:(set_solver)` in a large proof context

`ProofSysDup.wp_sys_dup_sconf` took **9 min 10 s**.  `-time` put 467 s of it on
three lines, all of the same shape — a set-membership side condition passed
positionally to a lemma:

```coq
iDestruct (proc_ofiles_repay γf p (pv_ofile V) ∅ fd0 k q Cf
             ltac:(set_solver) Hlk0 Hklt with "Hof Href") as "Hof".
```

Those goals are `fd0 ∉ ∅` and `fd1 ∉ {[fd0]}` — trivial.  They cost **106 s,
180 s and 180 s**.  `set_solver` ends in `naive_solver`, which searches over
*every hypothesis in scope*; at those points the context held ~200 hypotheses
of large mword terms (a whole-function proof's register-chain facts), and the
search is superlinear in that.  The goal's own size is irrelevant.

Replacing them with the one lemma that actually applies:

```coq
ltac:(apply not_elem_of_empty)
ltac:(apply not_elem_of_singleton_2; exact Hne01)
```

**9 min 10 s → 25.6 s (21x).**  Afterwards the slowest single item in the file
is the final `Qed` at 3.3 s, i.e. entirely ordinary.

**The rule: never `set_solver` (or `naive_solver`, `lia` on a big context,
`done` with a wide hint database) inside a whole-function proof.**  Discharge
set side conditions with the named lemma — `not_elem_of_empty`,
`not_elem_of_singleton_2`, `elem_of_union_l`, `elem_of_singleton_2` — or hoist
the obligation into a `Local Lemma` at the top of the file, where the context is
two hypotheses wide.  `set_solver` is fine *inside* the small definitional
lemmas (`ProcInv.v`'s own uses cost nothing); it is the call site that matters,
not the tactic.

Corollary for the sweep: any `ltac:(set_solver)` / `ltac:(lia)` appearing as a
positional argument in a `Proof<F>.v` capstone is a suspect, because that is
exactly where the context is widest.

## WHERE `Qed` TIME ACTUALLY GOES: proof-term TREE size, not typechecking

Measured 2026-08-05 with `rocq compile -profile`, which breaks a `Qed` down by
kernel phase.  On `UserClassify.active_step_branch` (a 10.9 s `Qed`):

```
10.884s Qed
   1.896s close_proof
   8.987s interp-delayed-qed
       3.913s HConstr.of_constr            <- 36 %
       2.715s Typeops.execute (+Conversion) <- 25 %  the only REAL typechecking
       0.950s sort_and_universes_of_constr <-  9 %  (4 calls)
```

**Only a quarter of `Qed` is conversion.**  The rest — `HConstr.of_constr`
(Rocq 9's sharing-aware pre-pass, `kernel/hConstr.ml`, unconditional in
`Constant_typing.check_delayed`, no user flag), `close_proof`, and
`sort_and_universes_of_constr` (a naive `Constr.fold`, `kernel/vars.ml:532`) —
are all **linear in the proof term's TREE size**, i.e. they re-walk every
occurrence of a shared subterm.  So the lever on `Qed` is *term size*, and the
question to ask is never "what is the kernel converting?" but "how big is the
tree?".

**The diagnostic: `Set Debug "hconstr".`**  It prints, per `Qed`, `tree size`
(the unfolded tree) and `bindings` (distinct subterms, i.e. the DAG).  A high
**tree/bindings ratio is the tell** — the proof is small, its tree is not:

| proof | tree | bindings | ratio |
|---|---|---|---|
| `WpUmodeStep.uv_interrupt_branch` | 15,255,420 | 3,045 | **5010x** |
| `UserClassify.active_step_branch` | 24,508,005 | 11,511 | **2130x** |
| `ProofUservec.wp_uservec_pt` | 39,174,545 | 53,702 | 729x |
| `ProofPiperead.wp_piperead_sconf` | 34,808,397 | 149,033 | 234x |

To localise the blow-up inside one lemma, bisect with an axiom stub —
`Axiom cheat_ : forall (A : Type), A.` and replace one branch's tactics with
`exact (cheat_ _).`  Unlike `Admitted` this still runs `Qed`, so each variant
reports its own tree size.  That pinned 23.7M of `active_step_branch`'s 24.5M
onto three of its five branches in one parallel batch.

### The cause found this way: `unfold set_reg` is a 3^N tree bomb

`set_reg s r v := MState (register_set r v s.(sregs)) s.(mem) s.(mdev)`
mentions `s` **three times**, so `unfold set_reg` over an N-deep state chain
writes out a `3^N` tree; `utrap_state` alone is a 12-deep chain (`3^12` = 531k)
and every subsequent `rewrite` copies that into an `eq_ind_r` motive.  The
goal after `cbn` is small, so nothing looks wrong — the cost is invisible to
tactic profiling and lands entirely in `Qed`.

**Peel with the projection lemmas in `RiscvLang.v`, never with `unfold`:**

| old | new |
|---|---|
| `unfold X, set_reg; cbn [sregs]` | `unfold X; rewrite ?sregs_set_reg` |
| `unfold set_reg; cbn [sregs mem mdev]` | `rewrite ?sregs_set_reg ?mem_set_reg ?mdev_set_reg` |

They are **goal-identical** drop-ins (`mstate_interp s` is literally
`reg_interp s.(sregs) * gen_heap_interp s.(mem) * dev_interp s.(mdev)`, so
every site is pure projection peeling), so whatever tactic followed —
`irrelevant_register_set`, `register_lookup_set`, `iFrame`, `iExact` — still
applies.  `UserClassify` went **24,508,005 -> 1,062,390 tree nodes for the same
11.3k-node DAG (23x), 23.4 s -> 8.7 s, 1832 MB -> 722 MB RSS** (isolated,
min of two interleaved).

**Swept tree-wide 2026-08-05: 437 sites over 53 files**, one clean rebuild,
zero errors, `lemma_diff.py` clean.  Whole build **ΣCPU 10364 s -> 9728 s
(−6.1 %)**, clean-build wall ~635 s -> 495 s, `Qed` 1546 s -> 1377 s.  Biggest
per-file CPU wins: `WpUmodeStep` −63 %, `UserClassify` −61 %, `ProofVirtioDiskRwB`
−42 %, `ProofVirtioDiskRwF` −27 %, `ProofVirtioDiskInit` −24 %, `ProofBread`
−24 %, `ProofPiperead` −21 %, `ProofSysPipe` −19 %.  (`ProofScheduler` +20 s and
`ProofPipealloc` +15 s in the same pair of builds are **untouched files** — pure
`-j32` contention noise, the ±10 s-in-both-directions effect this file warns
about below.  The one touched "regression", `ProofKvminithart` +7 s in-build, is
18.20 s vs 18.00 s CPU isolated, i.e. unchanged.)

**Four sites must keep the `unfold` spelling** — do not "finish the sweep" by
converting them:

- `WpGprCsrwA.set_reg_pmpcfg_n_overwrite` states an equation between **whole
  states** (`set_reg (set_reg s r a) r b = set_reg s r b`), not between
  projections, so `f_equal` needs the `MState` constructor exposed.  There is no
  projection in the goal for the rewrites to fire on.
- Three `{ unfold set_reg; cbn [sregs mem mdev]. rewrite Hmdevtr. ... }` sites
  (`WpSmodePtLeaves`, `UserretPt`, `WpSmodePtMem`, `WpSconfLock`, `WpSconfMem`).
  **ssr's `rewrite ?L` deltas through let-bound locals while matching**, so
  after producing `mdev s_tr` it keeps going into `s_tr`'s body and yields
  `mdev s_pc` — and the next line's `rewrite Hmdevtr` then fails with *"The LHS
  of Hmdevtr (mdev s_tr) does not match any subterm of the goal"*.  `cbn [mdev]`
  does not delta local definitions and so stops where the hypothesis wants.
  **The general rule: do not put `rewrite ?<proj>_set_reg` immediately before a
  `rewrite H` whose LHS is a projection of a `set`-bound state.**  Sites where
  the `rewrite H` comes FIRST on the line are fine and were converted.

**THE SWEEP IS COMPLETE — do not go looking for more.**  An earlier draft of
this note claimed "282 remaining sites"; that was a bad grep (`unfold
([^.]*?set_reg[^.]*?)[.;]` matches greedily across the `;` into the *converted*
`rewrite ?sregs_set_reg`, so it counted the fix as a miss).  Counting only
`set_reg` appearing in an `unfold`'s comma-separated NAME LIST, **24 sites
remain and all 24 are legitimate**:

- **11 are `unfold set_reg at 1`** — a SINGLE-occurrence unfold, already linear
  (3 copies of one level, not `3^N`).  Nothing to fix.
- **7 are the `rewrite Hmdevtr` / whole-state-`f_equal` sites** documented above.
- **6 are whole-state equations** (`MinstretInv`, `SmodePte`, `WpPushOffCsr`)
  of the form `set_reg s r v = s`, which need the `MState` constructor exposed
  for `f_equal`/`register_set_*_id` to apply.

## The OTHER shape: a setoid rewrite whose cost is in the PREDICATE, not the context

`BootShared`'s `rewrite !big_sepL_sep` — zipping four per-hart families before
`iFrame` — measured **12.7 s of that file's 27 s**, and `BootShared` is on the
build's critical-path **TAIL** (`BootChain -> BootShared -> SystemAdequacy`, all
at 1x parallelism), so it was wall time.

The instructive part is that **the usual fix did not work.**  `big_sepL_sep` is
a `⊣⊢`, so rewriting with it is setoid rewriting over `envs_entails Δ Q`, and
the reflex (see the `set_solver` and `wp_next_off` rules) is "the context is too
big — hoist it into a small-context lemma".  Hoisting it into a top-level lemma
with an EMPTY proofmode context changed nothing: **11.76 s there vs 12.7 s at
the use site.**  The size is in the *predicates* the rewrite must build `Proper`
proofs over (`boot_reg_res` / `hart_sie` / `boot_hart_bss` at eight harts), not
in the goal around them.

**The fix is to leave the setoid machinery entirely: use the WAND form.**  Iris
ships `big_sepL_sep_2` (`iris/bi/big_op.v`) next to `big_sepL_sep`; `iApply`
matches it by head and never enters setoid rewriting.  Three `iApply
(big_sepL_sep_2 with ...)` in place of one `rewrite !big_sepL_sep` took
**BootShared 28.3 s -> 15.3 s CPU (1.85x)**, isolated, min of two interleaved.

**Do NOT sweep this one.**  The tree has six other `rewrite big_sepL_sep` sites
and every one is cheap — `BootCarveMain` 0.12 s, `DiskBoot` 0.40 s / 0.17 s,
`ProcInv` 0.05 s, `ProofFreewalk`/`BioInv` sub-second — precisely because their
predicates are small.  Look up a candidate's per-sentence cost in the
`*.v.timing` files before touching it; the site count tells you nothing.

## Boot-chain audit (2026-08-05): two non-bugs and one real fix

Tree sizes say the boot chain looks pathological (`ColdBoot` 5,482,721/3,698 =
**1483x**, `BootReset` 4,539,073/6,151 = **738x**), but `-profile` says the time
is NOT in `Qed` there:

- **`ColdBoot`** — 8.85 s in `let x := eval vm_compute in ...` plus 2.72 s in the
  following `Defined.`, i.e. the 5.5M-node term IS the cold-boot state computed
  once into its own `Definition`.  That is the documented fix from
  durable-notes, not a bug; leave it alone.
- **`BootReset`** — 14.85 s in one `peel` on `exec_config_is_valid`, of which
  **98 % is `phnf`** (`let P' := eval hnf in P in change P with P'`), 7.54 s in a
  single call.  The cost is the `eval hnf` over the Sail `config_is_valid`
  program, NOT the `change`'s conversion check: swapping in `change_no_check`
  was measured at **28.7 s -> 27.3 s**, i.e. noise, and was rejected (no reason
  to weaken a check for that).  Shortening this needs a real refactor — prove
  the twelve config checks by a dedicated lemma instead of peeling the monad —
  and `BootReset` is OFF the critical path, so it is CPU only.

## Where the pipe/printk proofs' cost is: nowhere in particular

`ProofPrintk` / `ProofPipealloc` / `ProofPiperead` / `ProofPipewrite` carry the
tree's biggest proof terms (26–45 M nodes) but at **224–298x** over DAGs of
87k–149k distinct subterms — an ordinary ratio for an Iris proof that large, not
a duplication bug.  Their per-sentence profiles are flat: 1600–6700 sentences
each, the single largest item is the `Qed` itself (14–35 s) and the rest is a
long tail of 2–9 s `iApply`/`iFrame`.  There is no `unfold`-style bomb to
remove; shrinking them means the structural remedy already in this file (split
into `Qed`-sealed chunk lemmas of ~5–6 instructions), which is a design change,
not a tactic swap.  Do not go hunting for a hot statement there — it was looked
for, twice, and there is not one.

**Amended 2026-08-05 (see the next section): that verdict holds for the
straight-line body, but it MISSED a 5 s-per-site outlier hiding in the block
`iIntros`, because an `iIntros` of eighteen wands is exactly the sentence a
reader skips.  The general lesson is the one already at the top of this file
under "`done` / bare `cbn` / bare `reflexivity`": to find these, list every
sentence ≥ 5 s from a `.timing` file — do not read the proof.**

## `ProofEndOp` / `ProofPiperead` (2026-08-05): a `#`-intro can cost 5 s, and the rest is the proofmode

Measured with isolated `coqc -async-proofs off -time-file` on a quiet machine.
**Do the isolation first**: inside a `-j32` build these same two files read
414 s / 350 s — a 3–4x inflation that also *reorders* the per-sentence ranking
(the block `iIntros` below reads 41 s in-build and 5.4 s isolated, because a
5 GB-heap process pays GC on every allocating tactic).

| | before | after | |
|---|---|---|---|
| `ProofEndOp` (4255 lines, six `Qed`-sealed blocks) | 92.5 s / 1.83 GB | **~68 s / 1.72 GB** | −26 % |
| `ProofPiperead` (2618 lines, ONE monolithic `Qed`) | 113.1 s / 2.74 GB | **~97 s / 2.50 GB** | −19 % |

(Per-cent figures are ratios taken *inside one batch*, which is the only
comparison that survives a shared machine — the absolute seconds above come
from different batches and drift ±15 % with whatever else is running.  RSS does
not drift, and it moved the same way, which is the corroboration.  Piperead's
−19 % is −13 % from the tactic edits plus −6.5 % from the `is_pipe` seal.)

**The command that answers "why":** `Set Ltac Profiling.` after the imports,
`Show Ltac Profile.` at the end, and read the *local* (self) column — the total
column just re-reports `iApply`.  Both files said the same thing:

```
                              ProofEndOp   ProofPiperead
typeclasses eauto (self)         22.2 %         6.4 %   <- ONE tactic; see below
iSpecializePat_go (self)         19.5 %        22.9 %  \
notypeclasses refine (self)      13.6 %        21.3 %   |  the proofmode itself
pm_reduce / pm_eval              14.1 %        14.4 %  /
rewrite (ssr, self)               7.1 %        10.3 %
```

### The outlier: `iIntros "#Hdlock"` on an `is_lock` was 5.1 s

`ProofEndOp`'s three block-entry `iIntros "Hcg Hcnt #Htext … #Hdlock …"` were
its three most expensive sentences.  **Split the pattern one name per sentence**
— that is the whole diagnostic — and it is `iIntros "#Hdlock"` **alone**, 5.11 s
of 5.4 s, where `Hdlock : is_lock γk d_lock "virtio_disk" (disk_res …)`.
`is_lock` had a `Persistent` instance but was **not** `Typeclasses Opaque`, so
resolution unfolded the definition and descended through `lock_inv γ lk R` into
`R` — and `disk_res` carries 4096-entry descriptor big-ops.  `Global Typeclasses
Opaque is_lock` (WpLock.v) takes it to 0.14 s.  `is_pipe` (PipeInv.v) is a
separate definition with the same hole: sealing it is another −6.5 % on
`ProofPiperead` (104 s → 97 s).

Two controls, so nobody repeats them: sealing the *resource* instead
(`Typeclasses Opaque disk_res`) changes **nothing** (11.64 s vs 11.43 s), and
dropping the `#` so the lock enters spatially wins the same 5 s as the seal —
which is what proves the cost is the persistence search, not the hypothesis.

The seal costs one `rewrite /is_lock` inside each of `is_lock_name` /
`is_lock_inv` / `is_lock_intro` (and the `is_pipe` twins).  That is the point:
with it, nothing else can `iDestruct` a lock apart, so the projection lemmas
become the only interface.  **Look for this shape wherever a big-resource
abstraction has a `Persistent`/`Timeless` instance but no `Typeclasses Opaque`.**
Tree-wide the one line is worth far more than the two files it was found in:
`ProofBread` −45 s CPU, `ProofMain` −45 s, `ProofWriteHead` −32 s, `SleepLock`
−22 s, `ProofInstallTrans` −23 s, `ProofBrelse` −14 s.

**The candidate list, and why it was NOT swept.**  98 `Definition`s in the tree
carry a `Persistent`/`Timeless` instance with no `Typeclasses Opaque` (find them
with: collect every `Typeclasses Opaque` name tree-wide, then grep
`Instance … : (Persistent|Timeless) (X`).  The ones over a big resource are
`bio_ctx`, `log_ctx`, `procs_inv`/`scheds_inv`, `dev_inv`/`disk_inv`/`uart_inv`,
`is_sleeplock`, `is_ftable`, `is_kmem`, `is_txlock`, `is_tickslock`,
`kalloc_avail`, `kpt_inv`, `intr_inv`.  Sealing each costs a `rewrite /X` in its
projection lemmas and risks breaking any consumer that `iDestruct`s it, so seal
one at a time with a measurement — **and measure BEFORE you seal**: the
one-name-per-sentence `iIntros` split on `ProofEndOp` says every other `#`-intro
in that file is already under 0.15 s (`#Hbio` 0.14 s, `#Htext`/`#Hprocs`/
`#Hscheds`/`#Hlctx` below 0.1 s), i.e. the lock was the *only* one worth
sealing there.  Cost tracks the size of the resource under the abstraction, not
the number of sites.

### Everything else is the proofmode, and it is diffuse

After the seal there is no hot statement left in either file: `iApply` is
0.07–0.20 s a call over ~210 calls, `Qed` is 13 s (EndOp, six blocks) / 16.8 s
(Piperead, one monolith), and the remaining ~50 % is a flat tail of `iEval` /
`iPoseProof` / `assert` / `rewrite` / `set`.  Four cheap edits that DID pay,
each measured as a ratio **inside one batch** (never across batches):

- **Drop the redundant `[-]` from a leaf `iApply`'s spec pattern** — 110 / 107
  sites, **EndOp −13 %**, Piperead −2 %.  `iApply (wp_X … with "Hcg Hpc Hi [-]")`
  and `… with "Hcg Hpc Hi")` leave the *same* goal, but `[-]` forces an explicit
  `envs_split` of the whole spatial context at every instruction, while omitting
  it lets `iApplyHyp` hand the residual context over untouched.  Safe exactly
  when the omitted premise is the LAST one (which for these leaves — the
  `wp_next` continuation — it always is).  Textual drop-in: `s/ \[-\]"/"/`.
- **`set (Mk := <[Regidx …]> …)` → `pose`** (the rule already in this file, just
  never applied here) — 72 sites, **EndOp −11 %**.  It bought ~0 in
  `ProofPiperead`, and the reason is worth knowing: **`set (x := e)` with
  parentheses is vanilla Coq's `set`, not ssr's `set x := e`**, so it does not
  fail when it finds no occurrence — and every one of Piperead's 58 sites is
  followed by a `change e with Fk` that does the real fold.  Those 64 `change`s
  total under 0.5 s for the whole file; the `set`s they follow cost 4.3 s.
- **`clear` a single-use `assert`ed fact right after its one `iEval`** — the
  per-instruction pc-bump `Hpp*` and value `Hwv*` equations, 129 / 131 sites:
  **Piperead −5 %**, EndOp ~0.
- **Pose an `instr` fact immediately before the `iApply` that consumes it**,
  not in a batch of 24 at the top of a block — **EndOp −2.7 %** (`eo_loop` posed
  24 facts at L2082–2105 for uses spread to L3126; median gap 121 lines, max
  993).  `ProofPiperead` already did this and measured 0.  **That pair is the
  useful result: spatial-context LENGTH is not the driver** — 12 fewer entries
  out of ~40 bought 2.7 % — so do NOT go bundling live resources into folded
  definitions expecting a win from the entry count alone.  Gotcha when
  automating the move: a fact used TWICE is used once per *arm* of a branch and
  must stay put (`iSpecialize: "Hi100" not found` is what you get otherwise).

### What did NOT work

- `Local Strategy opaque [rget] / [tp_pin] / [rf_upd]` — the `ProofVirtioDiskInit`
  2.2x seal.  **Neutral in both files** once the lock seal is in (EndOp 80.0 s
  vs 79.7 s; Piperead 113.9 s vs 114.4 s).  Consistent with the existing rule:
  it pays only where a 20+-link `pose` chain and a large Iris context both hold,
  and these proofs keep the goal one insert deep.
- Sealing `disk_res` — 0 %, see above.
- **A `-j` build log is NOT evidence of a regression.**  The build after the
  lock seal showed `ProofVirtioDiskRwF` +53 s and `PipeInv` +32 s CPU.  Both are
  noise: `PipeInv` does not mention `is_lock` *at all*, and isolated A/B gives
  `PipeInv` 45.6 s sealed vs 45.7 s transparent, `ProofVirtioDiskRwF` 80.5 s vs
  85.3 s (sealed is faster).  This is the ±-in-both-directions effect the
  measurement-discipline rule below warns about, at a magnitude that looks
  convincing.

### What is left, and what it would cost

`ProofPiperead` is now ~97 s for ~100 instructions in one `Qed`, spread evenly
(4–15 s per 200 lines, growing gently with chain depth) plus that 16.8 s `Qed`.
In descending value, the remaining levers are:

1. Chunking into `Qed`-sealed ~5–6-instruction lemmas — the documented remedy,
   deliberately not done here.
2. Give the S-mode leaves an explicit successor-pc parameter
   (`add_vec_int pc n = pc' -> … pc_is pc'`), so the per-instruction
   `assert (Hpp…)` + `iEval (rewrite Hpp) in "Hpc"` pair disappears: ~110
   sentences and ~6 s per whole-function proof, times ~50 such proofs.  It is a
   sweep over the whole `Wp*` leaf layer, so cost it before starting.
3. Nothing else.  The profile is the Iris proofmode executing 100 instruction
   steps, and no tactic swap changes that.

## Proof performance rules (apply proactively when writing new proofs)

- **Never `set_solver`** (or `naive_solver`) inside a large Iris WP context — it rescans the whole hypothesis context: **100–190 s per call** (and **272 s per call** measured 2026-07-28 in `ProofVirtioDiskRwF.wp_vdrw_p6_seam`, on a goal as trivial as `h ∈ tri_set (h,m2,t)`). Instead:
  - register-membership `mword_of_int N ∈ [concrete list]`: `ltac:(compute_done)` (context-free, instant).
  - domain `r ∈ dom (<[k:=v]> … M)` from `Hr : r ∈ dom M`: `rewrite !dom_insert_L. repeat apply elem_of_union_r. exact Hr.`
- **A slow `set_solver` does not look slow — it looks like a hanging `Qed`, and it HIDES COMPILE ERRORS.** Worked example (2026-07-28, `ProofVirtioDiskRwF.v`): the file "compiled for >60 minutes without finishing" across several runs; `ps` showed one `rocqworker` at 99 % CPU and ~2 GB RSS, and the redirected log stayed **0 bytes the whole time**, which reads exactly like a pathological async `Qed`. It was not. Four `set_solver` calls (three `h ∈ tri_set (h,m2,t)`, one `dom` identity) inside one phase proof were burning ~20 minutes of MAIN-process tactic time, and the file had a plain type error a few hundred lines further on whose message sat in unflushed stderr behind them. Diagnosis took one command — **`coqc -time -async-proofs off`**, which both attributes every `Qed` precisely (async workers are invisible to `-time`) and streams per-sentence timings live, naming the culprit sentence in the first minutes. Replacing the four calls with pure top-level lemmas proved in a three-variable context took the file from **>60 min (never finishing) to 36 s**, and it then reported four genuine errors in four 40–60 s iterations. Two rules follow: (a) when a proof file "hangs", run `-time -async-proofs off` FIRST — never wait; (b) `pgrep` for the compiler by the right name — in Rocq 9 `coqc` is a wrapper and the process actually doing the work is named **`rocqworker`**, so a `rocqworker` at 99 % CPU is usually the main elaborator, not an async `Qed`.
- **Never call `set_solver` from inside a phase/WP proof at all — state the set fact as a top-level `Lemma` over set VARIABLES and `exact` it.** `set_solver` on a `gset nat` is instant when the context is three variables and lethal when the context is forty Iris hypotheses; the fix is always the same and costs nothing (`ProofVirtioDiskRwF.vdrwf_tri_mem` / `vdrwf_dom_delete` are the pattern). The same reflex applies to `lia` (already noted below) and to any context-scanning solver.
  - **It recurs, and the cheapest detector is the per-file `.timing` roll-up, not reading the proof.** `ProofVirtioDiskRwD.v` shipped one `set_solver` on a `gset nat` goal as trivial as `{[np]} ∪ S = S ∪ {[np]}`, under the publish step's whole-function context: **417 s of the file's 455 s in ONE sentence**, and nothing about the source line looks expensive. Lifting it to `vdrwd_dom_fl_ins` (three variables, closed by `union_comm_L`) took the file to **33 s**. After any build that felt slow, group each `*.v.timing`'s sentences by tactic head and sort — a single-sentence outlier of this size is always one of the context-scanning solvers.
  - **`ProofLogWrite.v` (2026-08-08, CI's build-profile step summary): five `set_solver`s plus one `set_solver`-closed equality, all inside `wp_log_write_gen`'s ledger-update block, cost 250/114/85/84/82/55/51 s = 665 s of the file's 879 s.** All were `gset Z` facts over `Sb`/`LB`/`om'` (subset-of-union, union-monotonicity, membership-under-a-subset, and one `list_to_set (W ++ [x]) = list_to_set W ∪ {[x]}` equality) inside the whole-function ledger proof, i.e. exactly the shape this rule warns about. None needed a hoisted top-level lemma — each was one direct stdpp combinator applied inline (`union_subseteq_l'`, `union_least`, `union_mono_r`, `elem_of_weaken`, `subseteq_union_1_L` + `elem_of_subseteq_singleton` + `comm_L`, and `list_to_set_app_L` + `right_id_L`), verified against a throwaway three-line sandbox file before editing the real proof so the combinator choice was checked without paying an 879 s rebuild. **879 s → 43.7 s (20x)**, `Qed`-clean, no other file touched.

- **Name a whole-function proof's register chain with `pose`, not `set`.** The straight-line WP idiom is `iApply (wp_<insn> … Mk …)` at the ENTRY map by name, and the leaf hands back `<[rd := v]> Mk`, so the goal is never more than ONE insert deep: there is no deep term for `set`'s occurrence abstraction to collapse, and the next `iApply` recovers the name with one delta step either way. What `set` *does* cost is a whole-goal pattern search per instruction — and the goal of a whole-function proof is `envs_entails Δ Q` with the entire Iris context inside it. The cost therefore scales with the proof's CONTEXT, not with the chain: measured across the tree, a chain `set` is ~0.1–0.26 s in the lock/alloc proofs but **1.7 s** in `ProofVirtioDiskInit` (device invariant + disk resources + the whole-function continuation), i.e. 158 s of that file's 305 s. Swapping the 85 chain links to `pose` — nothing else — took it to **177 s**, `Qed`-clean. Keep `set` only where the abstraction is the point: a value that really does occur throughout the goal (`sp0`, a kalloc'd page address). `pose` binds a local definition exactly as `set` does, so `rewrite /Mk`, `unfold Mk` and the `peel`/`reg_lookup` discharges are unaffected.
- **SEALING A DEFINITION TOWER HALFWAY BUYS NOTHING — seal every layer down to the one that actually computes, or none.** The S-mode register resource is a three-layer tower: `rget m k := tp_pin m !!! Regidx k`, `tp_pin m := <[Regidx Rtp := …]> m`, and `<[…]>` on a `regfile` is `rf_upd`, the function that does the decidable-equality test. Over a whole-function proof's 20+-link `pose` chain, CONVERSION walks the whole tower, and sealing only the top constant just makes it start one layer lower. `ProofVirtioDiskInit` shipped with `Local Strategy opaque [rget]` alone for exactly this reason, and the A/B that justified stopping there (`rget` vs `rget tp_pin`, 482.5 s vs 487.8 s) was uninformative *because `tp_pin`'s only body is an `rf_upd`* — with `rf_upd` transparent, sealing `tp_pin` cannot change anything. Sealing **`rget` + `tp_pin` + `rf_upd` together** took that file from **575.6 s to 260.7 s**, and the `Qed` alone from **235.3 s to 34.9 s**. `reg_neq` / `peel` / `reg_lookup` / `upd_ne` are lemma-driven, not conversion-driven, and keep working with `rf_upd` sealed.
  - **The tell is that the cost is invisible to tactic profiling.** Conversion cost lands in the kernel at `Qed` and inside `iEval`/`pm_reduce`, not in a sentence you can point at: post-sweep this file read `Qed` 235 s + `iEval` 211 s spread over 224 sentences, none individually alarming. **The only reliable detector is an A/B against a known-good older commit** — build just that file's cone in a worktree (`make -f CoqMakefile ProofF.vo`) and profile both with `coqc -time -async-proofs off`. Here pre-sweep (459da64) was 149.8 s with a 30.1 s `Qed`; the 3.8× was real and had gone unnoticed because the sweep's own commit message measured only the one `iApply` it had already fixed.
  - **Do NOT sweep the seal tree-wide — it was measured and it does not pay.** Ten of the most expensive proofs were A/B'd with the same three `Strategy` lines (min of two interleaved runs each, per the measurement discipline below): `ProofUvmcopy` −7 %, `ProofAllocproc` −4 %, `ProofScheduler` −4 %, `ProofSysPipe` 0 %, `ProofMain` +1 %, `ProofPrintk` −6 % — all inside run-to-run noise — and `ProofCopyout` does not even compile (it `unfold`s `tp_pin` twice). `ProofVirtioDiskInit` is a genuine outlier: it is the only proof whose `pose` chains (20+ links) and Iris context (device invariant + disk resources + the whole-function continuation) are both large enough for conversion cost to dominate. Seal per file, with a measurement; never as a sweep.
    - Beware the first measurement. A 20-way-parallel batch reported `ProofAllocproc` −25 %, `ProofSysPipe` −13 % and `ProofMain` **+28 %**; re-run at min-of-two those became −4 %, 0 % and +1 %. Under that much contention the noise is bigger than every effect being measured, and it is signed randomly, so it reads as a convincing result in whichever direction it lands.
- **`rewrite wp_next_off` is a setoid rewrite over the WHOLE proofmode goal — use `iApply wp_next_off_intro` instead.** Every instruction step of a `b = false` whole-function proof discharges its `wp_next` obligation, and spelling that as `rewrite` on an `⊣⊢` re-traverses the entire Iris context once per instruction: **45 s across 115 sites** in `ProofVirtioDiskInit`, **12 s** after switching. The wand form (`WpNext.v`) leaves exactly the same continuation and only has to match the goal's head. It is a safe textual drop-in (`rewrite wp_next_off.` → `iApply wp_next_off_intro.`) — five files were swapped and recompiled with zero errors — but the payoff scales with the file's CONTEXT, not its site count, so outside `ProofVirtioDiskInit` it is small: `ProofHolding` −11 %, `ProofSched` −8 %, `ProofBread` −5 %, `ProofVirtioDiskIntr` −3 %, `ProofMain` −1 % (min of two interleaved). ~835 sites remain across the tree; worth sweeping for the CPU, but it is not a fix for anything and it will not move a critical path.
  - **SWEPT TREE-WIDE 2026-08-03 (1171 sites, 52 files), and the last sentence above was wrong — it DID move the critical path.** `sed -i 's/rewrite wp_next_off\./iApply wp_next_off_intro./g' *.v` over `iris/`, one clean rebuild, zero errors. The profiler's per-pattern roll-up had put **310 s of tactic time in that one spelling**, and the distribution is what made it a path fix rather than a CPU fix: the top two files were `ProofPiperead` **48.2 s (22 % of the file)** and `ProofPipewrite` **36.4 s (19 %)** — and `ProofPiperead` *was* the critical path's tail. Result over the whole build: **ΣCPU 9656 s → 9500 s, critical path 386 s → 342 s.** The lesson generalises: before dismissing a broad mechanical sweep as "CPU only", check where its sites CONCENTRATE — `python3 -c` over the `*.v.timing` files, grouping one regex's sentences per file, takes a minute and tells you whether the pattern happens to sit on the tail.
- A `b`-GENERIC whole-function proof cannot use any of this: `ProofPrintk` and friends thread `wp_next … b …` with `b` a variable and discharge it with `wp_next_chain`, so they have no `wp_next_off` sites at all. `ProofPrintk`'s ~195 s is its own shape (147 chain links, the format/digit fuel inductions) and is unrelated to the explicit-cpuid regression.
- **Order `repeat (first [ … ])` rewrite loops** so cheap structural rewrites come first and broad whole-goal normalisation (e.g. boolean-identity cleanup) comes LAST — the loop re-tries its first branch after every success, so a broad first branch re-scans the whole goal every iteration. Profile hot branches with `Set Ltac Profiling. … Show Ltac Profile.`.
- **The build is critical-path-bound, not core-bound.** Measured 2026-07-29 on a clean `make -C iris -f CoqMakefile -j32 TIMED=1 TIMING=1` (550 files): **wall 448 s, ΣCPU 7296 s, critical path 352 s, avg parallelism 16.6×.** The tree has outgrown the regime where wall ≈ critical path exactly (it was 238.7 s wall ≈ 236.7 s path over 282 files on 2026-07-21): the middle of the build now saturates the cores, so ~100 s of the wall is scheduling slack above the path and ΣCPU reduction buys wall too. The path itself is one long common prefix (~147 s: `RiscvPtsto → … → InstrBytes → SmodeCore → KptTree → IntrDefs → WpIntrInv → WpSmodeIntr → WpSconfBtype`) plus ONE whole-function proof — whichever is slowest that day. So the lever is the single most expensive whole-function proof, then the prefix; the per-phase `ProofVirtioDiskRw{,B,C,D,E,F}` files are the one genuinely SERIAL cone (~205 s, each phase consuming the previous phase's exit lemma from inside its functor) and would need their seams lifted into a shared definitions file to run in parallel. Reconstruct the path from `coqdep` × per-file TIMED `real` (or from `.vo` mtimes: a file's start ≈ mtime − its `real`), NOT from per-file time sums — the sums mislead because big files run in parallel. **The binding tail is the user-mode classification chain**, not the kernel lock/alloc cone the spec-module migration dissolved: `WpGprCsrwB(16) → SmodePte → PtTree(8) → PtTreeAdue → KptTree(6) → UptTree → UserPtTree → UserExec → UserTrap(19) → UserClassify(21) → UserClassifyAsm → UserTotalU(33) → UserMemClassify(80) → ProofUser`. The **second tail sits at 201 s** (`ProofWalk`/`ProofMappages → LinkMappages/LinkKvmmap`), so that chain is the floor: ~36 s of the user-classify cone is worth attacking and no more.
  - **RE-MEASURED 2026-08-03 at 669 files: wall 479 s, ΣCPU 9364 s, critical path 356 s, avg parallelism 19.9× (peak 33× of -j32).** The shape is unchanged but the ratio has shifted again: the wall is now ~125 s ABOVE the path, and that gap is NOT recoverable by scheduling (see the two negative results below). Where the ΣCPU goes, tree-wide, by leading tactic (sum the `*.v.timing` sentences and group by head — the one command that answers "why is the build slow" without reading any proof): **`iApply` 16.3 %, `Qed` 15.2 %, `Require`/`From` 16.9 %, `iIntros` 7.6 %, `iDestruct` 4.4 %, `mk_rvc` 4.4 %, `rewrite` 3.5 %, `iEval` 3.4 %, `set` 3.0 %, `iNext` 2.9 %.** The import line is the one to internalise: **~1.9 s per file × 669 files ≈ 1280 s of pure module loading**, and it is a floor, not a bug — measured incrementally in one `coqc` each, an empty file costs 0.36 s for Stdlib, +0.47 s for stdpp, **+1.12 s for `iris.proofmode`+algebra+base_logic+program_logic**, +0.35 s for the whole Sail model (`rv64d_types.vo` is 22.7 MB and costs almost nothing — .vo loading is lazy, so do NOT go hunting there). It also sets the price of every file SPLIT: ~2 s of ΣCPU per new file, worth paying only when the split takes something off the path.
  - **NEGATIVE RESULT — `_CoqProject` order does not matter; do not try to schedule the build by reordering it.** The theory is attractive (GNU make dispatches a rule's prerequisites left to right, and `coq_makefile` emits `all: $(VOFILES)` in `_CoqProject` order, so the serial `ProofVirtioDiskRw*` cone sitting at positions 595–603 of 669 "obviously" explains why it starts 116 s after its last dependency is ready and then runs alone for the final 60 s). Measured, three orders over the identical tree: original **487 s**, sorted by descending critical-path level (longest chain from the file to a sink) **496 s**, sorted by descending upstream serial depth (longest chain ending at the file — the right key for a depth-first dispatcher) **487 s**. Level-order *did* visibly change the schedule — the big proofs started at ~200 s instead of ~250–340 s — and the wall did not move, because make refilled the freed slots with other work either way. Reverted; the file is back in its hand-maintained dependency-ish order.
  - **NEGATIVE RESULT — oversubscribing `-j` does not help either.** `-j48` on 32 cores: wall **484 s** vs 487 s at `-j32`. It DOES fix the queueing gap (`VirtioDiskRwDefs` starts at 200 s instead of 326 s, i.e. immediately when ready), which is the cleanest proof that the gap was slot starvation and not a dependency — but the cure costs exactly what it buys: **Σwall 9410 s → 13180 s (+40 %) and ΣCPU 9269 s → 9792 s (+5.6 %)**, so every file on the serial cone runs proportionally slower and the cone still ends at ~482 s. The machine is saturated in the middle of the build; there is no free parallelism to find. **The wall is pinned by the `virtio_disk_rw` cone in every configuration** (it is the last thing to finish in all five builds measured that day), and it has no hot statement to fix — 66 s of `ProofVirtioDiskRwF` is diffuse `iApply`/`rewrite`/`destruct`. Shortening it means splitting more of its seams (the recipe below), not tuning the build.
  - **Measurement discipline: never compare an isolated `rocqc` run against a file's time inside a `-j32` build.** Under 12 concurrent `rocqworker`s (1–2 GB RSS each) memory-bus contention inflates per-file `real` by tens of percent, and run-to-run variance on a 30 s file is ±10 s in BOTH directions — untouched files "improve" by 10 s between two builds. `UserretAllPt` reads 81–84 s in-build but 59 s isolated; that gap is contention, not a change. So: judge a code change by an isolated A/B in ONE process each (or by the computed critical path across two full builds), never by diffing per-file times between two parallel builds.
  - No `-j` helps this chain — only shrinking a file ON it, or removing a Require edge that needlessly serializes it (e.g. a bits-/offset-keyed fact misfiled in a heavy proof — see design/code-organization.md). **The call-graph edges are removed structurally**: a whole-function proof is a sealed functor over its callees' `Module Type` specs, so it depends on `SpecF.v` (~2 s) instead of `ProofF.v` — see design/spec-modules.md and completed/spec-module-migration.md. A file OFF the tail (e.g. the largest, `WpUserretAll`) costs CPU, not wall. Before chasing a "hot" file, confirm it is actually on the tail.
- **CSR nested-if dispatch** (`read_CSR`/`write_CSR`, ~90 clauses): use the batched peel lemmas from the start — `skip_csr_false_clauses` (writes) / `drive_csr` (reads, WpGprCsrrCommon.v), built on `exec_if_false_g16`/`_g4` (ExecCommon.v). Do NOT peel one clause per `erewrite exec_if_false_g` — it's O(tail) retyping per clause and dominates whole files.
- **What makes a funnel `iApply` slow is register-file lookups, NOT the proofmode (measured).** A 5–7 s funnel `iApply` (`wp_walk_tail_sconf`/`wp_walk_alloc_sconf` in ProofWalk.v) profiled as: `rewrite` **80 %**, the lookup peel **67 %**, the whole iApply proofmode machinery only **17 %**, `pm_reduce` a mere **2.5 % (~0.005 s)**. So do NOT chase the proofmode: making addresses opaque `Definition`s buys ~2.5 % at most, and do NOT retry the "bare-name framing swap" `iEval (rewrite -Hacpu) in "Hcpu"` (it breaks on let-bound vars and chases that same 2.5 %). The `unshelve iApply …; all: first[…]` split makes the split visible (iApply 0.5 s, deferred lookup side-goals 6.2 s); inline-`ltac:` funnels just fuse the two into one sentence.
  - **The lever was the representation, and it has been taken: the register file is a total function `regfile := regidx → mword 64` (RegFile.v), not a `gmap`.** A lookup `M !!! Regidx j` over a deep update chain is one `vm_compute` over the concrete-key if-chain (`reg_lookup`) instead of O(depth) ssreflect `rewrite lookup_total_insert{,_ne}` — 9 lookups over a 20-deep chain: **1.22 s → 0.04 s (~30×)**, values stay abstract. Discharge every register lookup and `callee_saved` conjunct with `reg_lookup`, never `reflexivity`/`repeat split` (bare conversion over a transparent update tower blows up the async `Qed` — see completed/regfile-migration.md). Remaining levers on the funnels are per-call side-goal count and chain depth, not the tactic.
- **State a whole-function WP's post in the ∀-continuation form — never with a deep `let m1 := … in … let mN := … in` register-map chain in the STATEMENT.** A let-chain statement makes every caller re-pay a huge structural `iApply` cost: each `iApply (wp_F …)` zeta-traverses the whole chain, ×N call sites (worst when the `mK` are nested `<[…]>` gmap inserts — those blow up quadratically; flat address lets are cheap). Instead universally quantify the return map as an abstract `∀ m', … gpr_file m' … ⌜callee_saved m0 m' ∧ <return-value facts>⌝ … -∗ WP` (the form CalleeSaved.v documents and most call specs already use), and keep the concrete `m1..mN` chain alive *inside the Proof only* as `set (mk := …)` local defs (the body's `change … with mk` / `unfold mk` steps are then unaffected), closing with `iApply ("Hcont" $! mN with …)`. Callers change by one token: `iIntros "…"` → `iIntros (m') "…"`. `wp_mycpu` is the worked example. Gotcha: the `set` tactic here does NOT accept `set (x : T := v)` — put the ascription in the term: `set (x := (v : T))`.
- **A family of "field X is untouched" laws over one bit-level constructor should be N corollaries of ONE testbit reading, not N testbit chases.** `PtAdBits.v` proved `pte_set_ad_absorb` / `_ppn` / `_ext` each by `mw_prep` + `apply (bv_eq_testbit w); tbk` — i.e. each one re-unfolded `update_subrange_vec_dec` and re-chased the `bv_extract`/`bv_concat`/`bv_wrap` tower from scratch, at a different width. Stating the single bitwise reading (`pte_set_ad_testbit : 0 <= k < 64 -> Z.testbit (bv_unsigned (pte_set_ad z a d)) k = if k =? 6 then … else if k =? 7 then … else Z.testbit (bv_unsigned z) k`) once and deriving the three from it — each becomes `apply (bv_eq_testbit n); rewrite !<field>_testbit, pte_set_ad_testbit; …` over two tiny `Local` field-extraction lemmas — took the file from **27.6 s to 13.0 s** (2.1×, interleaved isolated `coqc`), with the extra lemma added. The chase cost is per-law and superlinear in the term it walks; the reading is paid once. PtAdBits is on the `SmodePte → PtTree → PtTreeAdue → KptTree → UptTree` tail, so this is wall time, not just CPU. Look for this shape wherever a file has several `apply (bv_eq_testbit _); tbk`-style proofs about the SAME constructor.

- **Mark big concrete literals `Global Typeclasses Opaque`** (e.g. `kernel_bytes`, `kernel_data`, `kernel_symbols`, `mem_pointsto`): otherwise typeclass search (Persistent instances, every `#`-intro) unfolds the 23K-entry gmap (~108 s each). `vm_compute`/`reflexivity` ignore `Typeclasses Opaque`, so lookups still reduce. Use `Typeclasses Opaque`, never `Opaque` (a tactic may need to `unfold`).
- **Never bury a `vm_compute`-heavy discharge in an inline `ltac:(…)`** term-arg to `iApply`/`iDestruct` over a big gmap — the proofmode re-elaborates the spliced term without the Qed vm-seal (~16–26 s/call). Prove it FIRST as a named hyp `assert (H : …) by (tac)`, then pass `H` (a named hyp's type is fixed, no re-elaboration). If several such args exist, use the **"unshelve hoist"**: replace the inline `ltac:(…)`s with bare `_`, prefix `unshelve iApply`, and discharge the resulting evar subgoals as standalone `{ … }` goals (they land after Iris's bracketed-resource subgoals and before the WP continuation).
  - **This rule applies to `iPoseProof` too, and the `kernel_data_string` string-literal witnesses were the worst offenders in the tree** (measured 2026-07-21): the byte-lookup premise `∀ j b, cstring_bytes s !! j = Some b → kernel_data !! (A + j) = Some b` passed as an inline `ltac:(intros j b Hj; do N (destruct j …); …)` cost **17–29 s per call site** — the single most expensive statement in the whole build. Hoisting it verbatim into `assert (Hs : ∀ j b, …). { … }` above the `iPoseProof` and passing `Hs` by name drops it to **under 0.2 s**: ProofFileinit 32 s→2 s, ProofTrapinit 26 s→2 s, ProofPrintkinit 20 s→2 s, ProofKinit 39 s→14 s, ProofUartinit 63 s→39 s (**−122 s ΣCPU, −5 %**). The tactic script is byte-identical; only its position changes. Write new `kernel_data_string` uses this way from the start.
  - **`kernel_data_window` is the same trap, and `ProofArgraw` was its last instance** (measured 2026-07-27, isolated `coqc`, fresh deps): **93.8 s / 2.49 GB → 21.0 s / 0.99 GB (4.5×)** by hoisting ONE premise. `ar_table_word` read the six-entry `.rodata` jump table with a six-way `destruct i` ON THE IRIS GOAL and six `iApply (kernel_data_window … ltac:(…) ltac:(intros j Hj; destruct j …; vm_compute; f_equal; apply bv_eq; reflexivity) …)`; that ONE sentence was **73.6 s of the file's 93.8 s** (~12 s per call site, the same order as the `kernel_data_string` figure). The fix: state the byte premise as a pure `Lemma ar_tbl_bytes (i : nat) : (i < NARG)%nat -> ∀ j, (j < 4)%nat -> KernelData.kernel_data !! (ar_tbl + 4 * Z.of_nat i + Z.of_nat j) = Some (nth_byte (ar_entry i) j)` over a SYMBOLIC `i`, `pose proof` it, and pass it by name — the `destruct i` on the Iris goal disappears entirely and one `iApply` at symbolic `i` replaces six at concrete indices. Region cost: **73.6 s → 0.2 s**. `ProofPrintint.digits_bytes` is the same fix at the `kernel_data_window` call for the 16-byte `digits` table: hoisting that one `ltac:(intros j Hj; do 16 (destruct j …))` argument into a named pure lemma was **66.7 s → ~0 s**, taking the file from 104 s to 21 s (isolated). Grep for `ltac:(intros` inside a `kernel_data_window`/`kernel_data_string` argument list — every remaining hit is this bug.
    - **The 18k-entry `list_to_map` is NOT the cost — do not "batch the `vm_compute`s".** The retired note in projects/proc-struct-resources.md blamed "24 map lookups ~67 s, each renormalising the 18k-entry `list_to_map`" and proposed fusing them into one `vm_compute`. Measured, that premise is false: the VM compiles `kernel_data` to bytecode ONCE per process, so the first lookup costs ~0.15 s and every later one ~2 ms — 24 separate `vm_compute`s total **0.152 s**, and a single fused `vm_compute` over all 24 is **0.111 s** (a 0.04 s difference, not 67 s). A/B'd in one `coqc` process each. When a `vm_compute`-over-a-big-map sentence is slow, suspect the inline-`ltac:` position, not the map.
- **Register lookups: `reg_lookup` by default; the lemma-based `peel_reg` only for a SYMBOLIC hit.** `reg_lookup` (RegFile.v) is one `vm_compute` and is the right default. Where the target value is symbolic (`M !!! csp = spr` with `spr = add_vec sp0 …`) `vm_compute` would try to reduce the `add_vec` and hang; use instead the local `peel_reg` (ProofWalk.v / ProofMappages.v), which peels via the `upd_eq`/`upd_ne` LEMMAS so values stay opaque: `repeat first [ rewrite upd_eq | rewrite upd_ne; [| reg_neq] | lazymatch goal with |- ?M !!! _ = _ => is_var M; progress unfold M end ]; reflexivity`. Two rules it encodes, both learned the hard way:
  - **Peel ONE layer at a time; never unfold the whole `set`-chain first.** A threading proof builds the loop-head register file as a 20–30-layer `set`-chain (`M9 := <[…]> M8`, …). Unfolding the whole chain (`rewrite /M9 /M8 … /W1`) makes one giant nested term and then peels it, so every peel re-traverses it — O(depth²), and worse if it re-elaborates inline in an `iApply`. Unfold one layer and peel it immediately, keeping the goal one update deep (O(depth)). Gotcha: this MUST be `first [peel | unfold-var]`, NOT a `lazymatch` with the var-branch first — the pattern `?M !!! _` also matches an exposed update, so `lazymatch` commits to `is_var` (which fails) and never reaches the peel branch, silently stalling after one unfold.
  - **Try the HIT lemma (`upd_eq`) BEFORE the miss lemma at every layer, and guard the disequality with `reg_neq`.** When the lookup key IS in the chain (sp/s1/s3 and every register the code reads back), the peel terminates at `<[k:=v]> m !!! k`. Miss-first order attempts `rewrite upd_ne` there, whose side goal `k <> k` is FALSE, and **`vm_compute; discriminate` fails CATASTROPHICALLY slowly (~4–8 s per call) trying to refute a true `mword`/`bv`-record equality** (`discriminate` exhaustively hunts a discriminating position in two equal records and finds none). Hit-first makes the terminating layer resolve instantly and never attempts a false disequality; miss layers pay only one cheap failed *unification* of `upd_eq` before falling through. The same pathology bites EVERY hand-written inline `repeat (rewrite upd_ne; [| vm_compute; discriminate])` (the `repeat`'s last, failing, iteration at the hit layer where it stops) — do NOT reorder each by hand, guard the disequality discharge ONCE and swap it in everywhere. `reg_neq` (ProofWalk.v / ProofMappages.v): `lazymatch goal with |- ?a <> ?b => tryif unify a b then fail else (vm_compute; discriminate) end`. `unify a b` settles convertible-or-not cheaply — a MISS fails on the syntactically-distinct index arg (`mword_of_int 15` vs `…18`) WITHOUT reducing the `mword`, so `discriminate` only ever runs on a genuine miss; a HIT makes `unify` succeed so `reg_neq` `fail`s FAST (no doomed `discriminate`), which is exactly what the enclosing `repeat`/`first` wants at a terminating hit. Sound: `reg_neq` can only *succeed* via the else-branch on a true miss.
  - **Auditing an existing file for the unfold-all-first anti-pattern: watch for a DELIBERATE partial peel that stops early to reuse an already-proven intermediate fact — blindly swapping in the interleaved `peel_reg`-style step breaks those.** ProofProcMapstacks.v had ~40 manual `rewrite /V_n /V_(n-1) … /V_1. repeat (rewrite upd_ne; …)` call sites; mechanically replacing ALL of them with one `peel_reg_step := repeat first [upd_eq | upd_ne;[|reg_neq] | is_var+unfold]` (no final `reflexivity`, so the caller's own closing tactic — `exact H`/`reflexivity`/`vm_compute`/`apply lemma` — still runs after) cut the file's isolated `coqc` wall time from **8m37s to ~35s (≈14.6×)**, `Qed`-clean, verified by a full incremental rebuild. But a handful of sites intentionally unfold only a PREFIX of the chain and then hand off to a named fact proven earlier for that exact intermediate layer (e.g. `rewrite /W10 /W9. repeat (…). exact HW8a1.`, where `HW8a1` is a fact about `W8` — an interior link, not the chain's true base). `peel_reg_step` doesn't know to stop at the prefix's end; it keeps peeling past it, so a trailing manual `rewrite /Wxx upd_eq` or `exact H<interior-var>` no longer matches (`Error: The LHS of upd_eq … does not match any subterm of the goal`, or a failed `exact`). **Detect these before substituting:** a site is SAFE to collapse to `peel_reg_step` when its explicit unfold list is EXHAUSTIVE all the way down to the chain's genuine non-`set` base (a lemma-bound parameter like `mm`/`Mf`/`mr0` that `unfold` cannot open further) — then `peel_reg_step`'s maximal peel lands on the exact same residual regardless of interleaving order, so vm_compute/reflexivity/`exact <fact-about-the-true-base>` closers all still apply. A site is UNSAFE (leave it as-is, or fix it by hand) when the unfold list stops short of that base AND the trailing tactic keys off that specific stopping point (another explicit `rewrite /Vk …`, or `exact` of a fact about an interior chain variable). Grep for the shape first (`rewrite(?: /\w+)+\.\s*repeat \(…\)`), then check each match's tail before swapping.
- **`congruence` as the fallback branch of a per-layer peel tactic is a 4 s-per-call trap — and it hides in the CALLEE-SAVED-AGREEMENT peel, which every whole-function proof has.** A "the registers this function never touches still agree" transport (`uu_thr` / `ua_thr` style: `∀ c, is_cs_idx c = true -> c ∉ {written} -> mj !!! c = mm !!! c`) peels the register-map `set`-chain with `rewrite upd_ne`, whose side goal is `Regidx c <> Regidx k` — **lookup key ≠ update key, in that order**, so a proof via `is_cs_idx_true_neq` needs `not_eq_sym`. When `k` is itself callee-saved that route does not apply and the natural fallback is `congruence`; in `ProofUvmalloc.v` that single fallback branch was **~120 s of a 168 s file**. Replace it with, in order,
  `refine (not_eq_sym (is_cs_idx_true_neq _ _ _ Hcs)); vm_compute; reflexivity`
  and then, after `subst`, an explicit
  `lazymatch goal with H : ?a <> ?a |- _ => exact (H eq_refl) end`.
  Measured **168 s → 46.5 s (3.6×)**. Same family as the `reg_neq` rule above: never let a general-purpose closer (`congruence`, `discriminate`, `set_solver`) run inside a `repeat`-driven peel. (Unfolding the whole `set`-chain before the peel — the documented O(depth²) anti-pattern — was worth only ~10 s of the same 168 s, so fix the closer FIRST.)
- **THE SAME RULE, ONE STEP UP: `done` / bare `cbn` / bare `reflexivity` as the LAST tactic of a step in a whole-function proof.** The `repeat`-driven peel is only the most obvious place a general-purpose closer meets a huge context. It also sits, invisibly, at the end of perfectly ordinary lines — and there the giveaway is that the tactic is *trivially* discharging a goal you can read at a glance, so nobody suspects it. Four instances found in one profiling pass (2026-08-03, isolated A/B, one `coqc` each) and all fixed by naming the proof instead of searching for it:
  - **`ProofPipeclose` 40.0 s → 23.8 s.** Five copies of `iFrame "Hnm … Hslack". done.` rebuilding `pipe_res`; the residual `done` was closing `⌜pipe_count_ok nr nw⌝ ∗ ⌜length bs = PIPESIZE⌝`, 4–8 s a time. `iPureIntro. exact (conj Hcnt Hbslen).` — the two facts were already in context under those names, from the `iDestruct` that opened `pipe_res`.
  - **`ProofScheduler` 71.9 s → 60.1 s.** `{ iPureIntro. done. }` on the goal `(0%nat = 0%nat ∧ true = true)` was **16.1 s**; `exact (conj eq_refl eq_refl)` is free. Two more at `iMod ("Hclose" …) as "[$ $]". done.` over `|={E}=> True` → `iModIntro. iPureIntro. exact I.`
  - **`ProofSwtch` 57.8 s → 10.2 s (5.7×), RSS 2.76 GB → 0.78 GB.** The whole file was one `assert`: `nth 1 (callee_img m) d = m !!! Regidx csp_rs1` closed by `unfold …; cbn; reflexivity` at the CONCRETE register file `vregs_den rho swtch_regs1`, so the bare `cbn` normalised the entire VC denotation (18.4 s) and `reflexivity` re-did it (23.4 s) and `Qed` re-checked the result (39.1 s) — **81 s of a 98 s file in one bullet**. Hoisted verbatim into a `Local Lemma` over an ABSTRACT `m` with `cbn [map nth]`, it is instant, and both call sites become one `rewrite`/`exact`. Note the tell: the file ALREADY had the identical fact proved cheaply a few hundred lines earlier at an abstract `m0` — when the same one-liner is cheap in one place and lethal in another, the difference is whether its subject is concrete.
  - **`BioInv` 37.9 s → 18.8 s (2.0×).** `iFrame "Hsf"` (10.5 s) and `iFrame "Hlock"` (14.7 s) — *named*, not bare, and still the two most expensive sentences in the file, because the GOAL side is `bio_ctx bn ∗ bslots bn BSLOTS` with an NBUF-long big-op of sleeplocks and escrows to search per name. `iSplitR "Hsf"; [| iExact "Hsf"]` then `iSplitL`/`iExact` down the structure searches nothing. **So the "name the hypotheses" rule below is not the whole story: naming fixes the CONTEXT-side scan, and a big goal still costs a GOAL-side one. When the goal's shape is known, split structurally and `iExact`.**
  - **How to find these:** they are exactly the sentences a reader skips. Don't read for them — take any TIMED+TIMING build and list every sentence ≥ 5 s (`Chars A-B [snip] T secs` in `*.v.timing`, offset → line number against the `.v`). There were 87 such sentences tree-wide totalling 874 s; most are honest `Qed`s, and what remains after you cross those off is this list.
- **The inline-`ltac:` rule bites PLAIN `apply` too, not just the proofmode.**
  `apply (lem w _ _ _ _ ltac:(vm_compute; reflexivity) …)` — where the `_`s are
  bitvector WIDTHS the unifier has not yet fixed — did not terminate at all
  (ProofWalkaddr's PTE2PA step): the spliced tactic runs against unresolved
  width evars. Pre-`assert` the premises and `apply lem; [exact H1|exact H2|…]`
  is instant. So the rule is positional, not proofmode-specific: **never splice
  a computing tactic into a term whose implicit arguments are still evars.**
- **`lia` cannot do a nested-division chain, even mword-free and iris-free.**
  `E mod 32 = 0 -> E/32 mod 4 = 0 -> E/128 mod 4 = 0 -> E/512 mod 2 = 0 -> E = 0`
  comes back "Cannot find witness" — this is not the `bitvector.tactics` zify
  hook (see durable-notes.md), it is plain `lia` having no theory of iterated
  division. Stage it by hand with `Z_div_exact_2` + `Z.div_div`.
- **Inline `ltac:(rewrite …)`/`ltac:(vm_compute; …)` premise args over an OPAQUE (∀-quantified) register map hang the whole `iApply`.** When you `iApply (big_lemma … ltac:(rewrite Hmap; …) … with "…")` and the lemma's map argument is a universally-quantified `Mr` (e.g. inside a loop-invariant continuation `∀ Mr, …`), the inline ltac elaborates against the iApply's UNRESOLVED EVARS — `rewrite`/`vm_compute` then chase the map lookups through evar-laden `let`-bindings and blow up (indistinguishable from a hang; the SAME tactic as a standalone `assert` runs in <1 s). The fix mirrors kfree's release call: **pre-establish every premise as a named `assert` BEFORE the iApply, then pass the hypotheses by name** (`… Hlka2 Hmine2 Hcoup Hpos Hal5 with "…"`). Concrete maps (kfree's straight-line register file) don't trigger this — only opaque ∀-bound ones (the wakeup-loop `Hrel`/`Htail` continuations). Diagnostic: bisect with `admit` right before vs. right after the `iApply`; if "before" is fast and "after" hangs, and pre-asserting the premises makes it fast, this is the cause.
  - **`Wakeup.wp_wakeup_sconf` is the worst instance in the tree, and it is worst because its SPEC has a `let`-chain statement.** `wp_wakeup_sconf_body` opens `let sp0 := … in let spF := … in let rettgt := … in` (the very shape the ∀-continuation rule above says never to write), so an inline ltac at a call site chases the map lookups through *those* lets on top of the evars. `ProofPipeclose` called it twice — once per `destruct w` arm — as `iApply (Wakeup.wp_wakeup_sconf … ltac:(lia) ltac:(intro r; apply rf_to_gmap_dom) Hlen HtpW2 ltac:(rewrite HtpW2; reflexivity) ltac:(rewrite HtpW2; exact Hcpune) ltac:(lia) with "…")` over `W2 = <[ra:=…]>(<[a0:=…]> M0)` where `M0` is acquire's ∀-bound return map. That **did not finish** (6.8 GB and climbing at 95 s, still inside the first arm). All five premises pre-asserted and passed by name: ~0.1 s. Any new `wp_wakeup_sconf` call site must be written this way; the durable fix is to restate the spec in ∀-continuation form.
- **SEAL A WHOLE-FUNCTION PROOF'S CONTINUATION — do not spell the postcondition inline in the spec body.** A whole-function WP carries its continuation as a spatial hypothesis across every instruction step, so its TYPE is re-traversed by every proofmode operation that splits or frames the context: `iApply … with "… [-]"`, `iIntros`, `iPoseProof`, all of them. Written out, `virtio_disk_init`'s was twenty wands over three `[∗ list] j ∈ seq 0 4096` big-ops, and it cost **more than half the file**. The fix is one `Definition` in the spec file plus `Global Typeclasses Opaque`, with the proof unfolding it exactly once at the return (`iEval (rewrite /vdi_post) in "Hcont"`). Measured on `ProofVirtioDiskInit`: the first thirty instructions went **24 s → 7.3 s** (and `iClear "Hcont"`, the diagnostic that proves it is the continuation, only reached 11.5 s — the seal beats deleting it, because it also stops instance search on the surrounding chain); the whole file went **176.7 s → 91.4 s isolated, RSS 5.4 GB → 2.6 GB**. Diagnose it in two minutes: truncate the proof after ~30 instructions with `Admitted`, then A/B that probe with and without `iClear` of the continuation.
  - **The seal is worth nothing if the continuation is ALREADY a named `Definition`** — measured, so do not repeat it. The six `ProofVirtioDiskRw` phase files state their seams as `vdrw_pN_exit`/`vdrw_pN_loop` definitions; adding `Typeclasses Opaque` to all seven bought **0 s** (166.5 s vs 166.3 s over the chain, two interleaved reps) and cost seven `iEval (rewrite /…)` lines at the apply sites. The cost was never instance search walking into the constant — it was the *size of the term* when there was no constant. Name the continuation; only reach for the seal when naming is not enough.

- **Do not let the BUILD serialize along a proof's phase structure.** A long function proved in phases (`P1 → … → P6`, each consuming the previous phase's exit lemma) turns into a strictly serial require chain, and that chain becomes the build's critical path — `ProofVirtioDiskRw{,B,C,D,E,F}` was **166 s of pure serial tail**. But the coupling is almost never the whole file: measure it. Splitting each file at its functor boundary showed the heavy phase proofs (P3, 19 s; P4, 32 s) sat ENTIRELY before the functor, needing nothing from their predecessor but shared vocabulary, and the actual seam module was **0.6 s and 1.1 s**. So hoist the vocabulary into one functor-free file (`VirtioDiskRwDefs.v`) and split each phase into `ProofVirtioDiskRwX.v` (heavy, depends on the vocabulary only) + `ProofVirtioDiskRwXSeam.v` (the glue, depends on the predecessor). P3 and P4 then compile alongside P1/P2 instead of behind them: the cone's chain went **166.5 s → 129.9 s**, for +15 s of ΣCPU (three new files' import preludes) — a good trade whenever the chain is the serial tail, which is exactly when you are looking at it.
  - **Finding the cut is mechanical, not a reading exercise.** `.glob`'s `R` lines give every reference with its defining library; filter them to the byte range before the functor and you get the exact list of cross-file names to hoist (here: five from P1, three from P2, eight from P3 — all tiny helpers). Then `coqdep` confirms the result: `ProofVirtioDiskRwD.vo` should list `VirtioDiskRwDefs.vo` and nothing else from the cone.

- **A `reflexivity`/`exact` that has to fold a `gset Arch.pa` back into its name normalises a 4096-element `list_to_set`.** `VirtioProto`'s `vinit_dma_disj` closed with `rewrite !range_map_dom. exact Hd.` where `Hd` was stated at `avail_idx_dom c ## used_page_pas c` and the goal at the `pa_range … 4096` those unfold to — one delta step apart, but left to conversion it cost **3.7 s**, with `vinit_dma_dom`'s `reflexivity` another 3.5 s and as much again at each `Qed`. `unfold`ing the two names first (in the hypothesis, or in the goal) makes the match syntactic: the file went **38 s → 27 s**. Same family as the `set_solver`-on-`gset Arch.pa` rule above — never leave an address-set identity to a general-purpose closer.

- **Strip only the GOAL's later with `iApply bi.later_intro`; reach for `iNext` only when a HYPOTHESIS's `▷` has to come off too.** `iNext` is `iModIntro` at `▷`, so it runs `MaybeIntoLaterN` over every hypothesis in both environments: its cost tracks the proof's CONTEXT, not the goal, and in a whole-function WP proof that is ~1.1 s per call — once per instruction whose leaf leaves a `▷` on the goal. `bi.later_intro : P ⊢ ▷ P` turns the goal `▷ Q` into `Q` and touches nothing else: ~0.06 s, a ~20× difference for the same effect. In practice the only steps that need the real `iNext` are the **Löb back edges**, where `IH` (and any `▷`-guarded exits bundle like `HEX`) must be stripped before it can be applied.
  - **The tell that a file has this backwards** is an `iNext` followed, a few lines later, by `iAssert (▷ X)%I with "[H]" as "H". { iNext. iExact "H". }` — that block is *repairing* a `▷` the `iNext` stripped and the proof still wanted, so BOTH tactics are the expensive one and the pair does no net work. `▷ sched_vc` (the scheduler valid-context every S-mode whole-function proof carries) is the usual victim; grep `{ iNext. iExact` to find them. Replacing the pair with a single `iApply bi.later_intro` — keeping a real `iNext` at the 1–3 back-edge sites per file — measured **ProofPiperead 144 s → 96 s (−33 %)**, **ProofPipewrite 97 s → 74 s (−24 %)**, and the same edit applies to `ProofSysPause`. The inner `{ iNext. iExact "H". }` alone is ALWAYS safe to swap (goal `▷ X`, hypothesis `X`); the outer one is not, so convert it and let the build tell you which sites are the back edges.
  - **A/B this one with `-async-proofs off`.** With the async `Qed` worker on, the two variants hide different amounts of kernel work where `-time-file` cannot see it, and the per-sentence sums ranked them BACKWARDS here (they made the slower variant look 3 % faster). With async off the same comparison, interleaved over three reps, was unambiguous in both files.
- **Give every big-resource abstraction with a `Persistent`/`Timeless` instance a `Typeclasses Opaque` right next to it** — otherwise each `#`-intro/`iDestruct` re-derives the instance by unfolding and descending into the resource. Measured at **5.1 s for one `iIntros "#Hdlock"`** on `is_lock … (disk_res …)`; see the `ProofEndOp`/`ProofPiperead` section above for the diagnostic (split the `iIntros` one name per sentence) and the candidate list.
- **Do not write `[-]` as the last element of a leaf `iApply`'s spec pattern.** `iApply (wp_X … with "Hcg Hpc Hi [-]")` and `… with "Hcg Hpc Hi")` leave the same goal, but `[-]` forces an explicit `envs_split` of the whole spatial context on every instruction. −13 % on `ProofEndOp` over 110 sites. Safe whenever the omitted premise is the last one, which for a `wp_next`-continuation leaf it always is.
- **Never bare `iFrame` in a large Iris context — name the hypotheses.** `iFrame` searches the WHOLE spatial context for something to match each conjunct of the goal, so its cost scales with (context size × #conjuncts). Rebuilding `pipe_res` (9 separating conjuncts) with a bare `iFrame` in `ProofPipeclose`'s arm — a context holding the three join wands (`EPI`/`JOIN`/`TAILS`), ~20 `instr` facts and the frame cells — **did not terminate** (RSS climbing through 2.6 GB while `coqc -time` sat on that one sentence). `iFrame "Hnm Hnr Hnw Hro Hwo Hst0 Hst1 Hdat Hslack"` — the same nine, by name — is instant. Diagnostic: `coqc -time` flushes per sentence as it goes, so a stalled build's *last printed* sentence is the one BEFORE the culprit; the culprit is the next one in the file.
- **Never `vm_compute` a goal containing a symbolic `mword` variable** (a ∀-quantified pointer `p`/`head`/`spr`) or a concrete built-up `mstate` (a tower of `set_reg`/`update_subrange`) — it tries to normalize 64-bit modular arithmetic symbolically and does not terminate (looks like a multi-minute hang). Compute only the CLOSED offset (`replace (<offset> : mword 64) with (mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity)`, then close `add_vec p 0 = p` with `avi0`/`kv_addv_zero`); or prove the pure fact against an ABSTRACT state and `apply` it. Diagnostic: two `coqc -time` runs dying at the exact same char = the next sentence hangs (not a wall-clock cap).
- **A guard fixed by `change`/plain cast pushes a slow non-VM conversion to `Qed`** (minutes). Close it with `replace g with v by (vm_compute; reflexivity)` so the kernel gets a vm-cast instead. For CSR/extension dispatch guards use `csr_dispatch_eq` (ExecCommon.v) — a positive `cbv delta [eq_vec get_word … bool_decide] iota zeta beta; reflexivity` that decides only the guard primitives and leaves `currentlyEnabled`/`hartSupports` folded (~1.7 s → ~0.02 s). NEVER `cbv -[…]` (negative delta) to collapse a Sail dispatch guard — it unfolds a def with a huge normal form and OOMs the box (125 GB).
- **A monolithic Iris WP threading proof grows super-linearly in #instructions** (17 chained iApply/iNext ≈ 22 min; 21 didn't finish in 58 min). Split long chains into `Qed`-sealed chunk lemmas of ~5–6 instructions, each stating the next chunk's precondition as its postcondition, then compose (each chunk is an opaque constant, so proof terms stay small). Also `clear -` irrelevant hyps before any `set_solver`/`vm_compute`/`assumption` over a big context.
- **Collapse a run of N consecutive same-register writes into ONE update with `upd_upd`, INLINE, right after the writes (shortens the whole downstream `set`-chain).** When a block writes the SAME register K times in a row (e.g. an srl/andi/slli/add slot-address computation all writing s2), the natural proof builds a K-deep `set`-chain of single-key updates all keyed on the same reg — and EVERY later peel that crosses the block pays those K layers. Right after the K-th write, collapse in place: keep the intermediate `set (M1..M3 := …)`, then
    ```
    set (M4 := <[rd := regval_into_reg final]> Base).                     (* the ONE-deep target *)
    assert (HM4c : <[rd := regval_into_reg (add_vec (M3!!!rd) (M3!!!s1))]> M3 = M4).
    { rewrite /M4 /M3 /M2 /M1 !upd_upd. do 2 f_equal.                     (* upd_upd: <[k:=x]><[k:=y]>f = <[k:=x]>f *)
      rewrite upd_eq. rewrite upd_ne; [| reg_neq].
      rewrite Hbase_s1; exact (walk_slot_addr_lemma …). }
    iEval (rewrite HM4c) in "Hfile".                                      (* Hfile : gpr_file (<[rd:=…]> Base), one insert deep *)
    ```
  Now `M4` is `<[rd:=final]> Base` (ONE insert over `Base`, not four). **The payoff: NO downstream cascade.** M1..M3 stay defined, so the pre-existing deep peels `rewrite /M8 … /M4 /M3 /M2 /M1` still parse — `/M4` unfolds straight to `Base` and the now-absent `/M3 /M2 /M1` are harmless no-ops (ssr `rewrite /Mk` on a def not in the goal does nothing, does not fail). So you change ONLY the block, never its readers. For a SINGLE-USE block prefer this over a `Qed`-sealed chunk lemma (the lemma's own `Qed` and body are overhead nothing amortizes, and it forces a real downstream `/M3 /M2 /M1`-removal cascade). Gotchas: (a) the value hyp for the collapsed base (`Base !!! s1 = …`) may need deriving from a deeper fact — `first [ exact H | (rewrite /Base; repeat (rewrite upd_ne; [| reg_neq]); exact H) ]` is robust; (b) if you DO drop the intermediate `set`s (lemma path), the `upd_ne` side goal is `lookup-key ≠ update-key`, so a `∀ r, r ≠ Regidx 18` hyp may need `not_eq_sym`.
  - **When the SAME multi-instruction body repeats across call sites** (unlike a single-use block), a `Qed`-sealed chunk lemma DOES pay off — its one-time `Qed`+body cost amortizes over the reuse. Walk's loop-body straight-line core `+0x26..+0x36` (srl/andi/slli/add slot-address compute → `ld` the PTE → `andi` the valid bit, single-exit at `+0x3a`) recurs at THREE level-1 sites (mapped-descend, mapped-terminal, unmapped-alloc); `wp_walk_probe` (ProofWalk.v) factors it once, stated generically over the entry map `M`, `va`, `shift`, `slotaddr`, `pte` (+`dq`/`dqm` fractions), consuming `pc_is +0x26`/`gpr_file M`/`slotaddr ↦₈ pte` and the persistent `kernel_text`, returning `pc_is +0x3a` with the concrete 3-insert output map `<[15:=…]>(<[9:=pte]>(<[18:=slotaddr]> M))` + the slot ownership back; each call site does the `upd_upd` collapse ONCE inside the lemma and re-folds the output with three `set (M4/M5/M6 := …)` (folding works inside the Iris context too). Gotcha when porting a downstream reader: if it referenced an assert that lived in the now-replaced inline block (e.g. walk's alloc arm uses `HM4s2 : M4!!!s2 = slotaddr`), re-provide that assert inside the lemma-call glue (harmless where unused).
  - **Forward-looking lever for walk:** the loop body is not the bottleneck — the dominant cost is the FUNNEL applications, the five `iApply (wp_walk_alloc …)` / `iApply (wp_walk_tail …)` at the level-1/0 termination arms, each discharging ~8 register-lookup `ltac:` side-goals over the loop-head map (they were ~18–22 s each before the register file became a function; the lookup component of that is now ~30× cheaper, so re-measure before optimizing). The remaining lever is shrinking those funnels' per-call side-goal count or the chain depth they peel, not more straight-line factoring.
- **Invert a symbolic-step executor over its ABSTRACT value parameters — never `cbn`/`unfold` it into a hypothesis and destruct the guards there.** A VC-step WP lemma (`wp_vc_step_caddi16sp_sconf`, the caddi sp-move case in WpSconfVc.v) proves `vc_step_sp_s st op = Some st1 -> … -∗ WP …`. The tempting proof `cbn [vc_step_sp_s …] in Hstep; unfold vc_step_sp_move in Hstep; cbn; set (d := zimm12 (caddi16sp_imm imm6)) in *; destruct (guard d) …; injection Hstep` reduces the executor INTO `Hstep`, so each `destruct` of a guard buried in that big reduced term **reverts `Hstep` into the match's dependent motive**; at `Qed` the kernel reconciles the reduced form against the original `vc_step_sp_s (VScaddi16sp imm6)` and must NORMALISE the immediate there. `caddi16sp_imm imm6 = sign_extend' 12 (concat_vec imm6 (Ox"0"))` — `concat_vec` uniquely carries an `autocast` (`Z.eq_dec` width-cast) plus an extra nested stdpp-`bv` wf-proof layer — is ~17× costlier to normalise than caddi's plain `sign_extend' 12 imm`. Result: **~30 s per lemma, 100% in `Typeops.execute`** (kernel conversion, NOT tactic time; `vm_conv` untouched; the proof term is even *smaller* than caddi's, so it's per-node conversion cost, not size).
  - **Not fixable by opacity.** `Strategy opaque`/`remember`+`clearbody`/module-seal either do nothing (the cost is the original-vs-reduced conversion of `vc_step_sp_s`, independent of `d`'s body) or make it *worse* — sealing `caddi16sp_imm` or its `concat_vec` sent WpSconfVc to 40 GB / 16 min, but at **TACTIC time** (a `cbn`/`reflexivity`/unification that relied on transparency diverges). The kernel never explodes from opacity; only the tactic engine does. So don't reach for sealing here.
  - **The fix: one inversion lemma over the ABSTRACT displacement.** `vc_step_sp_move` already takes `d : Z` abstractly, so `sp_move_inv : vc_step_sp_move st pc' d = Some st1 -> ∃ v, (vsb st).(vregs)!!csp_rs1 = Some v ∧ … ∧ (POP-case ∨ PUSH-case)` does the whole guard case-analysis with `d` OPAQUE — no immediate ever enters a motive (proves in 0.006 s). Every WP lemma then `set (d := <its immediate>) in *; apply sp_move_inv in Hstep; cbn [vsb…]; destruct Hstep as (v & … & [POP | PUSH])` and gets its facts with the concrete immediate merely *substituted* (never normalised). Measured: `wp_vc_step_caddi16sp_sconf` ~30 s → <1 s; WpSconfVc.v 47 s → ~15 s.
  - **Minimal repro (for regression testing):** `set (d := zimm12 (caddi16sp_imm imm6)) in *; destruct (Z.ltb d vsp_half)` on the reduced `Hstep` is 28 s; byte-identical with `sign_extend' 12 imm6` is 1.7 s.
  - **General rule:** this bites ANY "`cbn`/`unfold` a Sail/bv computation into a hypothesis, then destruct guards over it" proof. The `vc_store8_sp` store-step lemmas are latent instances (cheap today only because `zoff6`/`zimm12 imm` offsets are simple); refactor them the same way (a `store8_sp_inv`) if a store ever gets an autocast-heavy offset.

## `upd_ne`'s side goal when the written register IS callee-saved

The standard name-free peel branch (`apply not_eq_sym; apply
is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]`) does not apply
when the register being written is itself callee-saved — every frame register
of a `thr`-style transport. The tempting fallback is `congruence`, which is
the 3.6x trap above. The replacement that works, and stays name-free:

```coq
| let He := fresh "Hxx" in
  intro He; injection He as He; subst;
  lazymatch goal with H : ?a <> ?a |- _ => exact (H eq_refl) end
```

(`subst` turns the excluded-register hypothesis `c <> k` into `k <> k`.)
Needed in prologue and epilogue peels; a loop body whose writes are all
caller-saved is covered by the `is_cs_idx_true_neq` branch alone.

## The peel branch for a callee-saved *written* register, name-free

The `subst`-based variant recorded above still fails on a `thr`-style
transport that excludes NINE saved registers: any Ltac that *mentions* a
hypothesis introduced by its own `injection` dies at definition time ("The
reference Hx2 was not found") — the durable-notes trap. The robust form binds
everything in the match:

```coq
| lazymatch goal with
  | |- Regidx ?x <> Regidx ?y =>
      match goal with
      | H : x <> y |- _ => exact (fun Hq => H (regidx_inj x y Hq))
      end
  end ]
```

`match` (not `lazymatch`) over the hypotheses is what makes it pick the right
one of the nine disequalities. **`regidx_inj` (`Regidx x = Regidx y -> x = y`)
lives in `CalleeSaved.v`**, next to `is_cs_idx_true_neq` — it must be a named
top-level lemma, not an inline `injection`, precisely so the branch can stay
name-free.

## A missing bullet at the END of a `split_and!` block is invisible to every obvious probe

`callee_saved` has fourteen conjuncts; supply thirteen and `Qed` says
"Attempt to save an incomplete proof" — but the usual probes all lie, because
the leftover goal sits behind the bullet focus:

- `Show 1.` answers **"No such goal"**
- `all: match goal with |- ?G => idtac G end` prints **nothing**
- `all: idtac "X"` prints **once**

**`Unshelve. Show Existentials.`** is what names it, in one run. Reach for that
whenever "incomplete proof" is reported and the goal list looks empty — the
same family as the "a failing tactic looks like a hang" entry in
durable-notes.md: the diagnostic you would naturally try is the one that
misleads you.

## `u_pte_addr` (CommonWalk) and `pte_addr_at` (Pt4kWalk) are the same term, but only CONVERTIBLE

`rewrite pte_addr_at_unsigned` in a goal spelled with `u_pte_addr` reports "no
subterm matching" on a term you can see. Restate the fact you want at the `u_*`
spelling in one line closed by `exact` (conversion does the work), then rewrite
with the restatement. Same reflex for any Pt4kWalk fact reached from the `u_*`
side.
