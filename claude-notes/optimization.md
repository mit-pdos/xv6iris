# Proof performance & build optimization

Rules for writing proofs that compile in reasonable time, and the diagnostics
that find the cost when they do not. Apply the rules proactively; reach for the
diagnostics before believing any theory about why a file is slow.

## Diagnosis, in order

**RULE ZERO — run `coqc -time` first.** It prints a line per command as it goes,
so the last line in the log is the stalling sentence. If the slow line is a
*tactic*, no amount of proof-term work will help. Map `Chars A-B` to a line with
`head -c B <f>.v | wc -l`.

- **Isolate before measuring.** Inside a parallel build a file reads several
  times its real cost and the per-sentence *ranking* reorders (a multi-gigabyte
  heap pays GC on every allocating tactic). Judge a change by an isolated A/B,
  one `coqc` each, min of two interleaved runs — never by diffing per-file times
  between two parallel builds. Run-to-run variance is large in **both**
  directions, so untouched files routinely "improve".
- **"Isolated" MEANS CHECK `uptime` FIRST — this box is shared, and a busy one
  INVERTS an A/B, not merely widens it.** The same arm of the same file has read
  as a clean win on a loaded box and a clear regression on a quiet one, with the
  per-tactic breakdown agreeing both times. Min-of-N is the guard that survives
  this, because contention only ever ADDS — a single reading, or two readings
  taken hours apart, prove nothing at all.
- **Per-file wall from two DIFFERENT parallel builds is not a comparison
  either, and it will hand you a large fake win.** The same unchanged file reads
  very differently in a full build and in a narrow incremental one — GC pressure
  tracks the width of the build, so even the `user` column moves. Confirm any
  cross-build delta with an isolated A/B before believing it.
- **`iris/.lia.cache` MAKES A WARM MEASUREMENT LIE, BY A LARGE FACTOR.**
  micromega persists every `lia` certificate in a per-DIRECTORY `.lia.cache`
  (with `.nia.cache` beside it), both gitignored and both excluded from the VM
  push, so they survive everything. A file can read an order of magnitude faster
  warm than with the cache deleted. Two consequences for any A/B. (1) The FIRST
  compile after an edit re-derives every certificate the edit moved, so a change
  that improves a file reads as a REGRESSION on the run that introduces it.
  Always take the second reading. (2) Compare cold against cold when the number
  you want is what CI or a fresh worktree pays: `rm -f .lia.cache` before each
  arm. The gap is not noise, it is the whole certificate search.
- **`-async-proofs off`** when the question involves `Qed`: `coqc` offloads
  kernel-checking to a `rocqworker` that `-time` does not count, so `-time`'s
  sum can be tiny while the wall is minutes.
- **`Set Ltac Profiling.` … `Show Ltac Profile.`** — read the *local* (self)
  column; the total column just re-reports `iApply`.
- **`Set Debug "hconstr"`** prints each `Qed`'s `tree size` and `bindings` (the
  DAG). A high tree/bindings ratio means a small proof with an exponentially
  unfolded term. `rocq compile -profile <f>.json` breaks a `Qed` into its phases.
- **To localise a blow-up inside one lemma**, bisect with `Axiom cheat_ : forall
  (A : Type), A.` and `exact (cheat_ _).` — unlike `Admitted` this still runs
  `Qed`, so each variant reports its own tree size.
- **To find which hypothesis is big**, `iClear` it *before* the block you are
  measuring (clearing at the end measures nothing — the earlier steps already
  paid) and diff the tree size.
- **RANK BY ms PER SENTENCE BEFORE YOU OPEN THE FILE — it decides whether you
  are hunting a bug or looking at a floor.** One `awk` over every `.v.timing`
  (sum the `secs`, divide by the sentence count) separates the two kinds of
  expensive file. A file at or below its peers' rate has no hot statement to
  find; the tree's single most expensive file is routinely one of them, merely
  the biggest. See "ProofCreate IS THE FLOOR" below for what that verdict costs
  to reach the long way.
- **`.v.timing` roll-ups beat reading the proof.** After a build that felt slow,
  list every sentence over a few seconds across the tree and cross off the
  honest `Qed`s; what remains is the bug list. These sentences are exactly the
  ones a reader skips.
- **When a `clear -H..` needs a hypothesis grepping sibling call sites won't
  find, dump the goal and context instead of guessing.** A temporary
  `match goal with |- ?G => idtac G end. repeat match goal with H : ?T |- _
  => idtac H ":" T; fail end.` spliced in before the tactic (removed
  afterward) prints the goal and every hypothesis to stdout on a plain
  `coqc` run — no `-time`/`-async-proofs off`, no interactive `coqtop`. The
  `repeat … fail` is what makes `match goal` enumerate every hypothesis
  instead of stopping at the first.

## RULE ONE: the cost is `|Δ|`, the Iris context

`tree ≈ 2 × (#proofmode steps) × |Δ|`, because every proofmode step's term
mentions the whole context twice — the `tac_*` lemma's input and output
environment. Even a *trivial* `iPoseProof` costs tens of thousands of tree nodes
while the DAG grows by a handful. Two consequences: **`Qed` time is the size of
the context times the number of steps it survives**, and splitting a proof into
`Qed`-sealed chunks buys nothing by itself — each chunk carries its own context.

So a whole-function proof can be the slowest file in the tree **with no hot
sentence at all** — a flat tail at several times per sentence what a comparable
proof pays. That ratio *is* the diagnosis.

### Fold block continuations into named definitions

This tree hands control between basic blocks with nested `iAssert (□ wp_next …
(fun CIDs => <40–80 lines of ∀/wands>))`. Ten live at once is far more statement
than actual resources, and every step pays for all of it. **Before hunting a hot
statement, count the lines of `iAssert` statement live at the deepest point; if
they outweigh the resources, the file's cost is its own continuations.** Folding
is a drop-in — the proof script does not change — and is worth a solid double
-digit percentage on the proofs that have the shape:

```coq
  Definition nx_head_body (j : nat) (b : bool) (K plen : nat)
      (pfun : nat -> bv 8) (pv : mword 64) (CIDs : CpuId) : iProp Σ := (…)%I.
  …
  iAssert (□ wp_next (CID0 := CID) b (proc_addr j)
             (fun CIDs : CpuId => nx_head_body j b K plen pfun pv CIDs))%I
    with "[]" as "#Hhead".
```

1. **Keep the definition TRANSPARENT — do NOT `Typeclasses Opaque` it.**
   `iApply ("Hhead" $! off Ms with "…")` unifies through a transparent constant;
   through an opaque one it fails and forces an `iEval (rewrite /X)` per use
   site, which is itself context-proportional and measured as a clear
   regression even for a smaller term. `Typeclasses Opaque` is right for a post
   nobody applies inside the proof, wrong for a continuation applied everywhere.
2. **Fold only the INNER body** — the `∀ fuel` and the `wp_next`/`□` must stay
   syntactically visible for the call sites' `iSpecialize`.
3. **For a `∀ fuel, …` block, parameterize by `fuel` and keep the `∀` outside.**
   `iInduction` then leaves the IH **folded**, which is half the win: the IH is a
   second copy of the loop invariant living in `Δ` for the whole body.

Two limits: when `GEN`/`CID0` are LEMMA binders rather than section context the
body definitions must take them explicitly; and a continuation with no `wp_next`
wrapper (a pinned-hart stretch, index `false`) cannot be folded — the next
leaf's implicit process pointer stops unifying (`iSpecialize: cannot instantiate
… false ?p`), and making `p` an explicit parameter of the definition does not
rescue it. Confirmed thrice — ProofPiperead (WXP/CLOOP), ProofIget (both scan
blocks; the rule-3 `iApply ("IH" $! …)` fails the same way, so the fold's own
IH is subject to the limit), ProofFilealloc (the descriptor scan); each file's
header records the exact error. The limit is that pinned-`false` shape
specifically, NOT bare folds: ProofScheduler's four `□ (∀ …)` blocks have no
`wp_next` wrapper either and three folded clean (its leaves take the zero
process pointer literally, so nothing needs `?p` through the fold).

### Seal a whole-function proof's continuation

Do not spell the postcondition inline in the spec body: one `Definition` in the
spec file plus `Global Typeclasses Opaque`, with the proof unfolding it exactly
once at the return. A 20-wand continuation over three 4096-element big-ops was
**more than half** of `ProofVirtioDiskInit`. **But the seal is worth nothing if
the continuation is already a named `Definition`** — naming is the fix; the seal
is only for a spec body that spells it inline.

**THE SAME RULE APPLIES TO A PREMISE-SIDE CLOSER, and there it is easier to
miss** — a closer arrives as a hypothesis rather than as a goal, so it never
shows up as a hot sentence; it just sits in `Δ` making every step of the walk
dearer. `ProofForkret`'s residue closer (`∀ h pt' V', ⌜..⌝ -∗ ⌜..⌝ -∗ ⌜..⌝ -∗
ut_tfk -∗ first_done -∗ W -∗ timer_cap -∗ forkret_yield -∗ URes h pt' ksp`) was
spelled out in THREE statements — `wp_forkret_gen_body` and both of the proof's
two block lemmas — and was a double-digit percentage of the Iris context of
every step of a very long walk. One `Definition SpecForkret.forkret_closer`
naming it, used in all three, paid clearly and left a byte-identical assumption
set. Keep it TRANSPARENT for the reason the previous subsection gives: the tail
applies it with `iDestruct ("Hyield" $! …)`.

**How to find the entry worth sealing: dump `Δ` and rank it by printed size.**
`Unset Printing Notations. Set Printing Depth 200. Show.` on a line in the
middle of the walk, on a scratch copy, prints `environments.Envs` in full;
splitting it on the quoted hypothesis names gives a size per entry. On
`ProofForkret` at the `kexec` call the closer was the biggest single row by a
wide margin. This beats guessing — the entries that LOOK big (`big_opS`/`big_opL`
rows over the fs kit) are among the smallest.

**A closer that is a premise of a MODULE-TYPE contract has to be defined
outside the spec file's `Section`.** The closer quantifies over the hart `h`
and applies its rows at `(CID := h)`, and inside a `Section` whose `Context`
fixes `CID` those rows do not take a `CID` argument yet — the error is
*"Wrong argument name CID"* at the first such row. Give the `Definition` its
own `` `{!riscvGS Σ, …} `{GEN : GenId} `` binders at top level, exactly as the
contract body beside it already does.

### ProofSysUnlink: the two CONTINUATIONS were the bulk of Δ

`ProofSysUnlink.v` was the tree's most expensive file, and it is the worked
example for this whole section — the diagnosis, the two folds, and why it lands
on the opposite side of the ledger from `ProofIput` below.

**The profile says RULE ONE and nothing else.** Isolated `coqc -time` showed no
hot sentence at all: the cost was spread over `iApply`, `Qed`, `iDestruct` and
`iIntros`, all of which are priced by `|Δ|`, and together they were the great
majority of the file. **The hundreds of `assert`s, which look like the problem,
are a rounding error** — do not chase them.

**Δ, dumped and ranked** (`Unset Printing Notations. Set Printing Depth 250.
Show.` on a copy with the other blocks `Admitted`, then split on the quoted
names — the `Esnoc` scaffolding has to be stripped first or the last
intuitionistic row absorbs the whole spatial-env prefix and reads much too
big). Two entries dominated, both continuations, both spelled inline:

- **`Hcont`, the RETURN continuation** — fifteen rows, written out TEN times
  (the contract in `SpecSysUnlink.v` and nine block-lemma statements), and a
  further copy inside each block's own seam.
- **`Hseamk`, the block's fall-through seam** — one per block, dozens to
  low-hundreds of source lines each, inert in Δ for the whole walk and applied
  twice at the end.

Everything else is a flat tail of short rows: the two 20-row open-inode
bundles, the 15-row stack frame, the ambient fs fabric. **Do not fold those.**
The walk consumes them row by row, so a bundle would have to be taken apart at
every callee call and the cost would move rather than go — see "Extracting a
persistent fact out of a bundle" below.

Both folds are DROP-IN. `Definition sys_unlink_closer` in `SpecSysUnlink.v`
(outside the `Section`, because it is a premise of the module-type contract)
and one `Definition su_wN_seam` per block beside its lemma, all TRANSPARENT.
**Not one line of proof script changed** — `iApply ("Hcont" $! …)`,
`iApply ("Hseamk" $! …)` and the `iIntros` that discharges the seam goal in
`wp_sys_unlink_sconf` all unify straight through a transparent constant. The
closer alone was a modest win; the three seams on top of it took both the wall
and the `.vo` down substantially, with peak RSS following.

Min of three, arms interleaved. One outlying reading in the seam arm was the
shared box, not the arm: the other two agreed to a fraction of a percent, and
the closer arm's own pair straddled it the same way under load. Contention only
ADDS — take the min, never the mean.

**`su_w3_seam` is a 58-ARGUMENT constant and it pays, where `ProofIput`'s
28-argument closer was a regression.** Argument count is not the predictor.
What separates them is the SHARE of Δ removed against the number of steps that
carry it: `ProofIput`'s fold shrank Δ in a file whose per-step cost was already
modest, while here W3's Δ nearly halved under a walk with hundreds of `iApply`s
and dozens of `Qed`s. Rank Δ first; fold the row that is tens of percent of it,
and only that row.

**GET THE `Definition`'s TYPECLASS BINDER LIST EXACTLY RIGHT — the two ways
of getting it wrong fail in OPPOSITE directions, and only one of them
errors.** Folding a bundle out of a proof file into a shared `Definition`
means restating the `` `{!riscvGS Σ, …} `` list by hand, and:

- **Too MANY classes** (one no row mentions) is a clean, immediate failure:
  the extra binder is an argument every call site must supply, so any site
  whose section context does not fix it reports *"Could not find an instance
  for ProcAvail.pavG"* — or, on a whole statement, `UNDEFINED EVARS`.
- **Too FEW classes** (one a row does need) does NOT error. Instance
  resolution goes hunting through the `gFunctors` instances for the missing
  evar and **DIVERGES**, consuming hundreds of gigabytes until it is killed,
  against a second or two with the right list. There is no error message to
  read, and on a shared box it takes the machine with it.
  This is durable-notes.md's "NAMING AN AMBIENT CLASS FIELD OUTSIDE ITS
  CLASS'S SCOPE IS A MEMORY BOMB" reached from a second direction — same root
  cause, a class search with an unknown `Σ` — so if either bites you, read both.

So derive the list, do not guess it: for each row, open the module that
defines it and copy that section's `Context`. The one that catches people is
`ProcInv` — `proc_priv` needs `` `{!riscvGS, !fileG, !xv6G, !bioslotG,
!fdslotG, !irefslotG} ``, i.e. `fileG` and `fdslotG` even though nothing in
the row's spelling mentions a file or an fd. **And cap the memory while
experimenting**: `ulimit -v 25000000` before `coqc`/`make` is many times the
largest legitimate file in the tree, so it never bites a real build and turns
this failure into a fast one.

**THE PRIZE IS ABSOLUTE BYTES OFF Δ, NOT THE SHARE.** Below roughly a kilobyte
removed it is worth nothing however good the share looks: several folds with
excellent-looking shares came out flat or within noise even where the `.vo`
fell. `ProofPrintk`'s eleven `wp_printk_arm_*` exit continuations are
character-for-character identical and a third to a half of each statement,
which reads exactly like this section's shape — folding all eleven measured as
nothing. `|Δ| × steps` is per PROOF, and those eleven lemmas are individually
cheap, so a large share of a cheap proof's Δ is noise. `su_w3` is the
contrasting case: ONE expensive lemma with a single entry approaching half of
its Δ. **Rank candidates by the lemma's own `coqc -time` cost times its share,
never by the file's cost times the share** — the file-level metric is what put
ProofPrintk top of the list.

**Still on the table in this file, not done**: its seven `iNext`s cost several
times what `iApply bi.later_intro` costs — which the same file already uses at
thirteen other sites. See "Modalities and rewriting".

### Do not pose instruction facts AT ALL — close them as subgoals

**This supersedes "pose late" for `instr` facts, and it is a bigger win than
anything else of its size in this file.** A leaf lemma's `instr pc rvc ast`
premise does not have to arrive as a hypothesis. Leave it as a `[]` in the
specialisation pattern and close the subgoal on the spot from the persistent
`kernel_text`:

```coq
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.pipealloc + 0x02))
              (mword_of_int 5 : mword 6) Rra R1 (K - 6)%nat u40 b
              with "Hcg Hpc [] Hr40").
    { iApply (pai_02 with "Htext"). }
```

No `pai_*` fact ever enters Δ, so the whole file's per-step cost drops by the
size of the block that used to sit there. Purely mechanical: delete the
`iPoseProof (pai_<off> with "Htext") as "Hi<off>"` lines and rewrite each
`with "Hcg Hpc Hi<off> …"` into `with "Hcg Hpc [] …"` plus the brace.

**The whole tree now follows this discipline** — 226 proof files converted,
verified by a from-scratch rebuild (every `.vo` deleted): 1297/1297, zero
errors. Wall and `Qed` both improved solidly across the ~110 files where
before/after pairs were taken; `.vo` mostly shrank but is **not** a proxy and
occasionally grew.

On the reference file (`ProofPipealloc.v`, one whole-function proof, 58 posed
facts) the proof term shrank by roughly two thirds while the shared DAG barely
moved — the derivations are still there, sharing subterms, but no longer
re-embedded in every following step's environment. That is RULE ONE from the
`|Δ|` side, and it is why the saving is FLAT: no sentence gets dramatically
faster, the whole tail does.

**What predicts the size of the win** is `min(peak live block net of iClears,
poses per Qed)` — `tools/instr_subgoal.py --rank` computes it. Not the file's
site count: a 27-site single-block file beat a 92-site file spread over ~30
proofs, and a file with 127 poses that posed-and-cleared one at a time barely
moved. It sorts candidates; it sizes the win only roughly, and `ProofSysLink`
has the tree's largest block yet lands mid-pack because most of its time is not
proofmode work at all.

Four things measurement refuted, all of which looked true after the first file:
`Qed` does NOT always improve more than wall (fails on small blocks); `.vo` is
not a proxy and can grow; peak RSS is not a reliable benefit; and a
`Löb`/`iInduction` body is NOT a special case (in-loop and out-of-loop
discounts agree).

**Do not measure this on a loaded box.** The error is BIASED, not just noisy:
eight files measured concurrently reported seven apparent REGRESSIONS that were
all wins when re-measured serially. One `coqc` at a time, arms interleaved,
2–3 reps.

**The user tier (`UProof*.v`) is out of scope and should stay that way**: its
`uinstr` is a `Prop` over a pure process image, passed positionally as a Coq
term at each leaf (1016 sites, zero `iPoseProof`), so it never enters `Δ`.

`tools/instr_subgoal.py` does the edit; see
`claude-notes/completed/instr-subgoal-sweep.md` for the recipe and the traps.
The sweep itself is DONE — the rule applies to what you WRITE next.

The limit is the same as "pose late"'s: an `instr` used inside a Löb/induction
body is re-derived on every iteration. That is one extra `iApply` per iteration
against a persistent fact, and it is still the right trade — but do not expect
the retrofit to be free there.

### Pose late, clear early

For everything that is NOT an `instr` fact (and for an `instr` fact you have a
reason not to convert), a persistent hypothesis is still not free — it is
re-embedded in the term of every step that follows it. Pose it on the line above
the `iApply` that eats it, not in a block of 40 at the top. Write new proofs this
way; retrofitting only works on **straight-line** stretches (in a Löb/induction
body a textually single use runs every iteration, so an `iClear` after it kills
the back edge, and if the uses are spread over two arms, moving the pose into the
first starves the second).

**`iPoseProof (fkr_XX with "Htext") as "HiXX"` lands the fact in the
INTUITIONISTIC context, so the `iApply` that reads it does NOT consume it** —
`instr` is persistent, and the proofmode files a persistent hypothesis under
`□`. That is why the pose block costs what it costs, and why the retrofit needs
an explicit `iClear "HiXX"` after the last use, not just a later pose.

**And it is why a pose that is never used is invisible.** Nothing fails: a
persistent leftover does not trip the "spatial hypotheses remain" check at
`Qed`, so a copy-pasted block of 30 poses can carry 16 that the proof never
reads. `ProofForkret.wp_forkret` had exactly that (`fkr_64` … `fkr_8e`, which
its callee `fkr_tail` poses for itself). Grep for it with "a pose whose name
never appears again in the same `Proof.`…`Qed.`"; the name is reused across the
file's lemmas, so the search has to be scoped to one proof block or every pose
looks live. **That retrofit is superseded by the subsection above** —
converting the surviving poses to `[]` subgoals is the bigger win, and it makes
the dead ones vanish by construction.

### Hypothesis names are a measurable share of a whole-function proof term

Iris's `ident` is a Stdlib `string` — a cons-list of `Ascii` over eight
booleans, ~10 term nodes per character — and the environment is embedded once
per step, so the term grows by hundreds of nodes per character of hypothesis
name. The only lever here is shorter names, a bad trade for readability except
in the two or three longest monoliths. **Sealing the name does not help and
cannot**: opacity is a reduction control, not a representation change, and a
name behind a constant breaks `envs_lookup`, which must COMPARE names under
`pm_eval`'s delta whitelist. What would fix it is a primitive-string `ident`
upstream.

## Never let a general-purpose closer meet a large context

This is the single most productive rule in this file — instances of it have been
worth more than an order of magnitude on individual files.

- **`set_solver` IS FIXED — the tree overrides it, and the old prohibition no
  longer applies.** `iris/FastSetSolver.v` replaces stdpp's `set_solver` tree-wide
  (hooked in from `RiscvModelBytes.v`, a transitive dependency of nearly every
  file; `BitmapEnc.v` and `CrashProto.v` import it directly). Read that
  file's header for the details. The short version:
  - stdpp's `set_solver` spends **almost all of its time in three whole-context
    sweeps that have nothing to do with sets** — `setoid_subst`, `set_unfold`'s
    `csimpl in *`, and `naive_solver`'s `unfold … in *` / `simplify_eq/=`. The
    step that actually reasons about sets is a rounding error.
  - The override clears the hypotheses that cannot reach the goal (the
    connected component of the goal in the "hypothesis mentions variable"
    graph, plus every hypothesis mentioning a set operation) and then runs
    stdpp's own pipeline on what is left. Cost becomes **linear** in the
    context instead of quadratic-to-cubic: hundreds of hypotheses cost the
    same as dozens, where upstream is already unusable at eighty.
  - **Solving power is unchanged, and this was checked properly.** The whole
    stdpp 1.12.0 library was recompiled against the override with the fallback
    DELETED (`set_solver := set_solver_fast`): all 55 files build clean and all
    23 of stdpp's own test files produce output byte-identical to baseline, so
    the filtered path alone discharges all **373** `set_solver` call sites in
    stdpp. `iris/FastSetSolverTests.v` does the same for the 62 shapes this
    tree discharges or works around. In normal use `set_solver` additionally
    falls back to the unfiltered upstream tactic, so nothing that was provable
    stops being provable; `set_solver_fast` / `set_solver_slow` name the halves.
  - **If you change the filter, re-run it with the fallback deleted.** A green
    tree proves nothing on its own — with the fallback in place `set_solver`
    cannot fail, it can only get slow. Three of the four bugs found during
    development (a missing `Control.enter`, a dropped `False` hypothesis, and
    `@eq` missing from the walked connectives, which made every *set equation*
    invisible to the filter) were exactly the kind the fallback hides.
  - So **`set_solver` at capstone altitude is now fine**, and the hand-written
    blocks that exist only to dodge it (`bmset_*` in `ProofBmap.v`, `wiset_*`
    in `ProofWritei.v`, `cr_*` in `ProofCreate.v`, `gset_disj_*` in
    `VirtioQueue.v`, `ip_*`/`ig_*`/`it_*`/`nx_*`/`bm_used_*`, …) are
    retirable — they are correct, just no longer necessary. Retire them
    opportunistically when you are in the file anyway, not as a sweep.
  - **THE OVERRIDE NEEDS *IMPORT*, AND A LEAF CAN MISS IT.** It is a
    `Tactic Notation`, so it reaches a file only through an unbroken
    `Require Export` chain (`BitmapEnc` exports `FastSetSolver`; every
    intermediate that merely `Require Import`s it breaks the chain).
    `iris/FsInitPinBoot.v` — an `FsImgCheck`-consumer leaf — got stdpp's
    upstream one, and ONE `set_solver` closing `b ∉ ∅` with
    `b ∈ fs_home_set fsimg_cov …` in the context (`fsimg_cov` is a
    1,999-element `list_to_set` literal) took minutes in a file that is
    otherwise trivial. `Print Ltac set_solver.` answering *"set_solver is not
    a user defined tactic"* is the check: the override is not in scope. Then
    either `Require Import FastSetSolver` or close the goal by hand
    (`exact (not_elem_of_empty b)`) — in a deliberate leaf, prefer the
    second and leave the cone alone.
  - **Confirmed on a REAL site, not a synthetic:** `ProofSysDup.v:836`'s
    workaround (`ltac:(apply not_elem_of_empty)`, written because `set_solver`
    there was unusable) put back to `ltac:(set_solver)` is now free, against
    upstream's two-figure minutes for the same sentence. That one site took two
    further fixes, both worth knowing:
    - **A goal reached through `ltac:(…)` inside a term is an EVAR**, and an
      evar carries an instance listing every variable in scope. Walking into it
      made the goal "mention" the whole context, so the filter kept everything.
      `vars_of` now skips evar instances.
    - **`Std.clear` is ALL-OR-NOTHING.** One name Coq refuses — something
      outside the analysis still depends on it — fails the whole call, and then
      NOTHING is cleared and the filter silently degrades to upstream with no
      error anywhere. This is what kept that site slow even once the analysis
      was running correctly (instant to decide, then a full solve over the
      context it had failed to clear). `clear_greedily` now bisects on failure
      and keeps the halves that go.
    - The general lesson: **a filter that fails open is invisible.** Both bugs
      presented as "the tactic is just as slow as before", never as an error.
      If the override ever looks like it is doing nothing, check that
      `set_shrink` is in scope and that it is actually clearing, before
      believing anything about the goal.
  - **A SINGLE MEMBERSHIP IN A UNION OF TWO `gset register` VARIABLES IS STILL
    EXPENSIVE, override or not.** `assert ((tlb : register) ∈ Drw ∪ Dro) by
    set_solver` inside a `swp` translation proof costs many seconds per call —
    and adding `Require Import FastSetSolver` to the file changes nothing, so
    this is not a "the override is not in scope" case. Two of them dominated
    `Pt2WalkPt.v`; `by (apply elem_of_union_l; exact HWtlb)` is the fix. The
    rule the durable notes give for tower-carrying proofs (name the union
    lemma) is therefore still the rule whenever the sets are VARIABLES rather
    than literals — which is exactly the `Drw`/`Dro` frame idiom.
    `HartSKpt.swp_translate_kpt` carried the `set_solver` form and that one
    `assert` was most of the file; its premise `HWtlb : tlb ∈ Drw` was already
    in context, so `by (apply elem_of_union_l; exact HWtlb)` is the whole fix.
    Grep for `∈ .* ∪ .*) by set_solver` before believing a file is
    intrinsically slow.
    **`HartSTrans.v` carried TWO MORE of exactly that assert** (`swp_translate`
    and the update arm, 2.7 s and 2.1 s), with the same `HWtlb : tlb ∈ Drw`
    already in context; the same one-line replacement took the file 10.3 s →
    6.0 s, and it is on the critical path. The grep above now finds none left
    in the tree — every remaining `by set_solver` over a `∪` has a LITERAL
    carrier, which is the case the override handles.
  - **A HYPOTHESIS THAT IS A SET EQUATION IS KEPT BY THE FILTER BY
    CONSTRUCTION, SO `clear` IT ONCE THE REWRITE HAS USED IT.** The override
    keeps every hypothesis mentioning a set operation — that is its
    correctness condition — so a giant `assert (Hws : dom (write_bytes
    (write_bytes …)) = …)` that the proof has already rewritten away is still
    reified by the closer that follows. Measured on
    `VirtioProto.vslot_writes_dom_eq`: two `set_solver`s at 2.0 s each, both
    with their computed carriers already behind `set`/`clearbody`, went to
    nothing under one `clear Hws` on the line above. **That exhibit is gone**
    — the one-bus-transaction-per-step rewrite replaced the lemma with
    `vslot_write_dom_elem`, which reasons per byte and calls no closer — but
    the rule is not: the tell is that every ATOM in the goal is already a
    variable and the closer is still slow, and then it is not the goal, it is
    what the filter kept.
  - **A PURE UNION SHUFFLE BELONGS IN A LEMMA STATED AT VARIABLES.** The
    publish arm of `VirtioProto`'s lease-hole move closed
    `a ∪ r ∪ (p ∪ u) ∪ i ∪ d = (a ∪ r ∪ u ∪ i ∪ d) ∪ p` with
    `apply set_eq. intro x. rewrite !elem_of_union. tauto.`, where every
    letter stands for a COMPUTED carrier (`avail_idx_dom`, `ring_cells_dom`,
    `dom (pins_union …)`): 7.9 s in the `rewrite` and 5.7 s in the `tauto`,
    the tree's most expensive non-`Qed` pair. The same identity as a
    six-variable lemma closed by `set_solver` — where there is nothing to
    unfold and nothing to reify — plus `apply` at the site, took the file
    115.8 s → 99.4 s including its `Qed`. Same edit retired that file's
    `map_fold` commutation side condition (`intros. set_solver.` over two
    `slot_done_dom`s). This is "a side condition that is the SAME at every
    call site belongs in a lemma proved where the context is EMPTY" with the
    emphasis moved: what the lemma buys here is not sharing, it is that its
    ARGUMENTS ARE RIGID.
  - **Two things the override does NOT fix**, both goal-side rather than
    context-side, so the old workarounds stand: `gset (mword n)` still fails
    (instance divergence — see the durable notes), and `set_unfold` still
    unfolds a `list_to_set` over a literal-size list, so `gset Arch.pa` goals
    at concrete sizes still must not go near it.
  - Still true regardless: do not create the goal if you can avoid it.
    `dom_insert_lookup_L` (`is_Some (m !! i) → dom (<[i:=x]> m) = dom m`) closes
    a "the slot was already live" domain identity with no set reasoning at all.
  - **A slow tactic looks like a hanging `Qed` and HIDES COMPILE ERRORS** —
    the log stays 0 bytes while the main process burns tactic time, and a real
    type error further down sits in unflushed stderr behind it.
- **`done` ENDS IN A NO-ARGUMENT `discriminate`, WHICH HEAD-NORMALISES EVERY
  HYPOTHESIS TYPE WITH DELTA — so `by` is a general-purpose closer too, and one
  `⊆` between two gmaps is a large context all by itself.** `VirtioQueue.v`'s
  `by exists (vp_lo pr + k)%nat, sl` took minutes to close
  `vp_pend pr !! q = Some sl ∧ vs_hd sl = vs_hd sl` — a goal whose two halves
  are a hypothesis and `eq_refl`. `coqc -profile-ltac` put essentially all of it
  in a SINGLE `discriminate` call, and clearing the context down to one
  hypothesis at a time named the culprit exactly: `Hrsub : ring_bytes c
  (vp_ring pr) ⊆ vproto_ctl c pr`, on its own, was the whole cost. Nothing else
  in that 17-hypothesis context registered at all. The mechanism is that no-arg
  `discriminate` walks the local context looking for an equation between
  distinct constructors, and to decide that it `hnf`s each hypothesis's type
  WITH delta — so a `⊆`/`##ₘ` between two *computed* gmaps (here a `write_bytes`
  fold over eight ring cells, unioned into a lease) gets unfolded, and the
  goal's own triviality never gets a chance to matter.
  - **The fix is to say what the goal is**: `exists q, sl. exact (conj Hsl
    eq_refl)` in place of `by exists q, sl` took the sentence to nothing and
    the file with it. Same shape as the `iPureIntro. done.` bullet above, one
    level deeper: the giveaway is again that the goal is trivial to read, so
    nobody suspects the closer.
  - **Name the hypothesis whenever you do want `discriminate`.** The same file's
    remaining cost was a bare `discriminate` in a branch whose goal was a fat
    `⊆`: `discriminate H1`, where `H1 : None = Some _` is the equation meant all
    along, skips the walk. `discriminate Hreq` likewise.
    **AND THE BILL IS PER BRANCH, so a `destruct` over a wide inductive
    multiplies it.** `UserTotalU`'s two `destruct i; try (cbn in Hdi;
    discriminate)` over the decoded-instruction type run the context walk once
    per constructor; naming it (`discriminate Hdi`) fixes each sentence and the
    file. The tell is the same as ever — the equation being refuted is one you
    can read, and it is already named in the line above.
  - **This is not specific to `by`.** Every `done`, every `by tac`, and every
    bare `discriminate` in scope of a map-inclusion, map-disjointness or
    map-subset hypothesis carries the same bill. Before believing such a
    sentence is intrinsically slow, `clear` the fat hypothesis and re-time —
    it is one run and it is conclusive.
- **`naive_solver` on its own is still forbidden inside a whole-function
  proof** — it is the half of the old `set_solver` that the override does not
  reach when you call it directly. It ends in a search over *every* hypothesis
  in scope, and a capstone's context is ~200 register-chain facts over large
  mword terms.
- **Never `simplify_eq` inside a whole-function proof's Iris context** — like
  `congruence`, it scans every hypothesis in scope looking for equalities to
  substitute/discriminate, so cost tracks context size, not the one hypothesis
  you meant to consume. Fix: `injection H as pat…` names exactly the hypothesis
  and produces one pattern per NON-trivial component — a component syntactically
  equal on both sides (`Ep = Ep`) is dropped automatically, so a
  `(Ep, b') = (Ep, uint bno)` equality takes one pattern (`as ->`) where a
  `(e', b') = (Ep, uint bno)` one — both sides genuinely distinct — takes two
  (`as -> ->`); guess wrong and the error is *"Unexpected introduction pattern
  (at most N was expected)"*, which names the fix.
- **Never `congruence` anywhere but LAST** in a peel's side-goal alternation,
  and never `done` / bare `cbn` / bare `reflexivity` as the last tactic of a
  step. The giveaway is that the tactic is *trivially* discharging a goal you
  can read at a glance, so nobody suspects it: `iPureIntro. done.` on
  `(0%nat = 0%nat ∧ true = true)` is expensive where `exact (conj eq_refl
  eq_refl)` is free. When the same one-liner is cheap in one place and lethal in
  another, the difference is whether its subject is CONCRETE.
  **`by split` IS THE SAME TACTIC WEARING A HAT** — `split` then `done`, so the
  walk still happens. The tree's only two sites (`ProofPipealloc.v:1625,1647`,
  closing `fdstate_ok` at a literal `MkFContent` — three `eq_refl`s) were both
  expensive; `exact (conj eq_refl (conj eq_refl eq_refl))` took both out of the
  profile and the file with them.
- **`upd_ne`'s side goal has exactly one answer: `CalleeSaved.reg_ne_side`.**
  Write `Local Ltac regne := reg_ne_side.` and never hand-roll the alternation.
  Its branch order is the point: (1) the disequality already in context, via
  `regidx_inj` and a name-free inner `match goal` — the only branch that
  COMPUTES NOTHING, and what a save/restore frame's transport wants; (2)
  `is_cs_idx_true_neq`, either orientation; (3) both keys concrete
  (`vm_compute; discriminate`); (4) `congruence`, last, for completeness only.
  The name-free branch must use `match` (not `lazymatch`) over the hypotheses so
  it picks the right one of the six-to-nine disequalities a transport carries —
  an Ltac body cannot mention a hypothesis its own `injection` introduced.

### A BESPOKE SIDE-CONDITION TACTIC IS THE SAME BUG, AND IT HIDES BETTER: `wp_next_chain`

Everything above is about a STDLIB closer meeting a large context. This is the
same mechanism in a tactic this tree wrote itself, and it hid for much longer
because a hand-written tactic reads as "the thing that discharges this
obligation" rather than as a search. **Read every `Ltac` that a leaf's
`ltac:(…)` slot invokes as a closer, and price it by the context it runs in,
not by the goal it proves.** The tell is the same as ever: the goal is one
equation you can read.

`wp_next_chain` (`WpNext.v`) discharges a leaf's hart-crossing side condition —
`b = false ∨ p = zero_reg → (CIDb : CPU) = (CIDa : CPU)` — from the conditional
equalities a straight-line stretch accumulates, one per instruction. As landed
it was two `repeat match goal … specialize` loops over the WHOLE context, so it
proved a one-hop equation by specializing every link in scope. A whole-function
walk accumulates dozens of them by its deepest point, and ProofNamex calls it
127 times: thousands of `specialize`s and `destruct`s, a quarter of the file,
for goals that need a handful of links.

**The chain is a PATH, so follow it from the goal.** At `?x = ?z` the only link
that can matter is the one whose conclusion is `?x = _`; consume it with
`eq_trans`, land on `?y = ?z`, stop at `reflexivity`:

```coq
Ltac wp_next_link Hd :=
  match goal with
  | H : _ = false \/ _ = _ -> ?x = _ |- ?x = _ =>
      refine (eq_trans (H Hd) _); clear H
  end.
```

Three things make it drop-in and worth copying:

- **`refine (eq_trans …)`, never `rewrite`.** The equation lands in the proof
  TERM and the context is never touched. The `rewrite He` spelling of the very
  same walk is a **REGRESSION** — ssr `rewrite` becomes about half the file.
  Measured, so do not re-run it.
- **Keep the old loops as branches four and five.** The fast path fails
  cheaply (nothing is specialized, `first` rolls the state back), so no call
  site can regress and a shape the walk cannot follow still closes. Roughly a
  fifth of ProofNamex's calls still take a fallback.
- **`clear H` after the `refine`** is what makes `repeat` terminate against a
  cyclic pair; the already-built term keeps its own reference, so clearing it
  from the residual goal is sound.

240 files call this tactic; the whole-tree ΣCPU moved by a few percent and the
register-chain-heavy files by a fifth to a quarter each. ProofNamex's
`.lia.cache` cold reading agrees with its warm one, so none of this was
certificate work.

**`rdok_tpne`'s bare `congruence` is the second instance, and it is the
`discriminate` bullet above at 3673 call sites.** `IntrDefs.rdok` — the
`ltac:(rdok)` sitting positionally in nearly every gpr leaf's premise slot —
ends in `intro H1; injection H1 as H2; vm_compute in H2; congruence`, where
the goal at that point is `False` and `H2 : 9%positive = 4%positive`.
`congruence` head-normalises every hypothesis in scope to get there.
`first [ discriminate H2 | congruence ]` (the fallback for a site whose two
indices are not both concrete costs nothing, because a NAMED `discriminate`
fails immediately) took ProofCreate's 419 calls out of the profile. The same
edit is in `rgne`, whose side condition is the identical script.

### ProofCreate IS THE FLOOR, NOT A BUG

`ProofCreate.v` is the tree's most expensive file and it has **no pathology at
all** — this is the record of what was measured, so nobody re-runs it looking
for one.

- **Per SENTENCE it is CHEAPER than its peers.** It is the top file because it
  is the tree's biggest walk — five halves (`cr_found_half`, `cr_mkdir_half`,
  `cr_alloc_half`, and the two failure halves) of a straight-line-with-branches
  function. Compute this ratio from the `.v.timing` roll-up BEFORE opening a
  slow file; it decides whether you are looking for a bug or at a floor.
- **Δ is already flat and already folded.** Dumped mid-walk in `cr_mkdir_half`
  (the recipe in "Seal a whole-function proof's continuation"): 90 rows, no
  entry anywhere near dominant once the last intuitionistic row's absorbed
  spatial prefix is discounted — the artefact that section warns about, seen
  again. The parked bodies (`cr_alloc_body`, `cr_mkdir_body`, `cr_fail_body`,
  `cr_cont_body`, `cr_tail_body`) are already named `Definition`s, so the
  ProofSysUnlink lever was spent here before it was written down.
- **The tail is the majority of the file**: thousands of sentences well under a
  second. The few dozen above that are mostly honest `Qed`s.
- **The `.lia.cache` is not hiding anything**: cold and warm agree, and this
  file's contribution to the directory cache is small.
- **`Strategy opaque [rget] [tp_pin] [rf_upd]`** is already on in this file;
  adding the same three to `ProofNamex` — the obvious next candidate, a
  register-chain-heavy whole-function proof — is a **NULL**. That lever is
  still confined to `ProofVirtioDiskInit`'s shape.
- What is left is `|Δ| × steps` and nothing else: the Ltac profile is
  `iSpecializePat_go`, `notypeclasses refine`, `tc_solve` and `_iIntros_go`, in
  that order. **The only lever that could still move it is fewer RESOURCE
  ROWS per callee call** — ~30 names go out at each fs-callee `iApply` and
  ~20 come back at the `iIntros` — i.e. bundling the two 20-row open-inode
  bundles behind one abstraction with a constructor and an accessor. That is
  a spec-layer change across `SpecIlock`/`SpecDirlink`/… , and it is the same
  one ProofSysUnlink's case study declined ("the cost would move rather than
  go"); it has NOT been measured, and it should not be attempted as a perf
  edit alone.
- **It is not on the critical path**, so splitting the file buys nothing:
  `tools/proof_profile.py` puts the path elsewhere.

### ProofIput RESISTS ALL FOUR OF THIS FILE'S LEVERS

**Except the fold.** `ip_free_entry`'s two continuations (the largest inline one
in the tree) and `ip_free_locked`'s own both paid, in two steps — i.e. the very
continuation the regression below is about now measures NEGATIVE, folded as a
seam on the current tree. The two results are not reconciled (the file has
changed a great deal since, and the span that note describes is not obviously
the one folded later); take it as: **re-measure before trusting an old per-file
verdict, and never read "this file resists the lever" as "this continuation
does".**

`ProofIput.v` is well above the tree's median cost per sentence, so it reads
like a textbook RULE ONE file. It is not fixable by the rules above, and here
is what was tried so nobody re-runs it:

- **Naming the closer made it SLOWER.** `ip_free_locked`'s +0x30 continuation
  was 60 rows spelled inline and was the biggest entry in Δ by a wide margin —
  a bigger share than the `ProofForkret` case that paid. One `Definition` for it
  did exactly what it should to the context (Δ shrank by nearly a third, and
  that entry went from dominant to negligible) and made the file **slower**,
  confirmed on a second reading. The regression is inside `ip_free_locked`
  itself, spread UNIFORMLY across every tactic at identical call counts: the
  per-step delta-unfold of a **28-argument** constant costs more than the
  smaller Δ saves. Its CALLER improved, which is the tell — a fold helps
  whoever SUPPLIES the closer and hurts whoever USES it.
- **Sealing that constant does not rescue it, either way.** `Typeclasses
  Opaque` and `Strategy opaque` both fail identically at
  *"iSpecialize: cannot instantiate"*, and the `iEval (rewrite /X)` repair puts
  the expansion straight back into Δ, which is the thing being removed.
- **`Strategy opaque [rget] [tp_pin] [rf_upd]` is a REGRESSION here**, over two
  interleaved pairs, even though the mechanism is real elsewhere
  (`ProofPipewrite` keeps the same three lines and benefits).
- **Hoisting inline `ltac:` is not available**: the file's 247 splices are
  individually cheap, against the much dearer splices that made the same edit
  worth doing in `ProofSysUnlink`.

**AND THE FIRST THREE READINGS SAID THE OPPOSITE, because the box was loaded.**
The `Strategy` arm read as a clean win under load and reversed once the same
interleaved A/B ran on a quiet box. A single reading on a shared machine is
worth nothing here; take `uptime` before believing an A/B, and interleave.

### `lia` IS A GENERAL-PURPOSE CLOSER TOO, AND 180 HYPOTHESES IS A LARGE CONTEXT

**THE EXHIBITS ARE GONE, THE LESSON IS NOT.** `iris/FsEff*.v` and
`iris/FsOp*.v` were deleted — the whole-state pure preservation layer
`design/fs-state.md` §6 superseded, with no reader left. You cannot open the
files to re-read them. Every rule they produced applies unchanged to any
monolithic proof with a wide context.

The whole cost of the stage-F2 effect band (`iris/FsEff*.v`: eight PURE files,
no Iris, no `set_solver`, no `vm_compute`) was one tactic. `coqc -profile-ltac`
put the overwhelming majority of `FsEffCreateEntry.v` in `lia` — `xlia` the
bulk of it LOCAL, `Zify.zify` most of the rest — across 381 calls whose goals
are three atoms wide. What they cost is their CALL SITE: a monolithic
whole-transaction proof carries ~180 hypotheses, ~45 of them arithmetic, two of
those mentioning `Z.div`, and every call reifies the lot and re-eliminates the
divisions. Three fixes took the band from unusable to unremarkable:

1. **A side condition that is the SAME at every call site belongs in a lemma
   proved where the context is EMPTY.** Each effect proof case-splits
   `fs_dinode` through a local `Hdec` whose premise is the inode region's
   width, `0 <= z < 16 * (sb_ninodes sb / 16 + 1)`, and all 124 sites spelled
   it `ltac:(lia)`. `FsEffBase.v`'s six `iblk_*_range` / `inum_*` lemmas make
   it free. That is "Inline `ltac:` in argument position" again — but note WHY
   it is worth hunting rather than tolerating: **a `lia` certificate reifies
   the hypotheses it was handed, so the PROOF TERM carries them too.** Those
   two sentences were also the whole of that file's `Qed` cost, which fell with
   them and needed no separate work.
2. **`clear -H..` before a `lia` at a deep site — and use `match goal` to NAME
   the hypothesis, so one `Local Ltac` covers a whole family.** `destruct
   (bool_decide …); destruct (bool_decide …); lia`, closing the four arms of
   the links sweep from two equations already in hand, is expensive;
   `(clear -Hc Hold; lia)` is free. Where the wanted hypothesis is named
   differently at every site, match it by SHAPE and pass the answer as a term:

   ```coq
   Local Ltac blk_ne d3 i3 :=
     match goal with
     | H : _ <= ?b < _ |- ?b <> _ => clear - H d3 i3; lia
     end.
   Local Ltac irng :=
     match goal with
     | H : 0 <= ?z < sb_ninodes sb |- 0 <= ?z < _ =>
         exact (iblk_z_range sb z H)
     | _ => lia
     end.
   ```

   Two mechanics. **The fixed facts must be PARAMETERS of the tactic, never
   names written inside its body**: `clear`'s arguments are globalised when
   the `Ltac` is defined, so a body saying `clear - H Hibd3` fails at the
   *definition* with *"Hypothesis Hibd3 was not found in the current
   environment"* — which reads like a broken proof and is a scoping error.
   And keep a `| _ => lia` last arm: the fallback makes the rewrite a
   drop-in, so the conversion is one `sed` over the call sites (106 `Hdec`
   sites in seven files, one pass, zero fixups).
3. **Close a CONCRETE goal with `discriminate`, not `lia`.** 46 sites of
   `rewrite Hty; unfold T_DIR_z; lia` prove `1 <> 0` and still paid the
   context scan. The smallest of the three, listed because it is the cheapest
   to spot.

**Negative results from the same afternoon — do not redo them.** The suspects
that looked structural were all null: the common-ground `Section` closing
under `Set Default Proof Using "All"`, the seven per-file blocks of ~45
`Local Notation`s re-applying its seventeen context arguments, the `set … in
*` chains, and the ticket `mjoin` over `seq 0 (Z.to_nat (sb_ninodes sb))`.
`FsEffBase.v`, which carries the entire common-ground section, is trivial and
did not move.

#### `ProofFilewriteAU`: twelve one-line side conditions were the whole file

The same rule at a WHOLE-FUNCTION proof rather than a pure band, and the
worked example to copy — because the file looked innocent by every other
diagnostic.

- **`.lia.cache` hid it several-fold, which is the Diagnosis section's warning
  seen live.** Warm it reads like an ordinary file; nothing in the warm profile
  stands out and the shape is a flat RULE ONE tail. Cold, the top TWELVE
  sentences are the great majority of the file and every one of them is a
  `lia`. **If a file is reported slow and your warm reading disagrees, delete
  the cache before believing the reading.**
- **The certificates are the tell, and they are visible without any
  profiling.** This one file owned a large fraction of the whole directory's
  `.lia.cache` — because a certificate carries the hypotheses it was handed and
  `fw_loop` hands over hundreds of them (dozens arithmetic, over `Z.to_nat` /
  `bv_unsigned` / `MAXFILE * BSIZE`). After the fix its contribution is
  negligible. `ls -laS` on the per-directory cache is not a ranking tool, but a
  file that can be shown to own a large share of it is a confirmed instance of
  this section.
- **NEGATIVE RESULT — the cache's SIZE is not itself a cost, do not chase
  it.** The fixed file compiled against the full cache and against an empty one
  reads the same within load noise. micromega does not pay for entries it does
  not look up.
- **AN `ltac:(lia)` IN ARGUMENT POSITION CANNOT BE FIXED BY `clear -` — the
  goal is an evar whose instance names every variable in scope, so there is
  nothing to clear. Hoist it.** This is the "Inline `ltac:` in argument
  position" rule with its largest instance: the loop's back edge spells
  `iApply (IH … ltac:(lia) ltac:(lia) ltac:(… lia) ltac:(… lia) …)`, and that
  ONE sentence was the most expensive in the file. Four named `assert`s above
  it, passed positionally, make it free. The second and third worst
  (`fw_au_raw_fail`'s `ltac:(left; lia)`, `fw_au_raw_take`'s two) are the same
  edit.
- **One `Tactic Notation` per file makes the rest a `sed`.** The keep-lists
  differ per site, so a bare `Local Ltac` cannot carry them; `hyp_list` can,
  and this is `FastSetSolver.v`'s own `set_solver +` idiom:

  ```coq
  Tactic Notation "fwclear" hyp_list(Hs) := clear - XI Hs.
  Tactic Notation "zlia"    hyp_list(Hs) := clear - XI Hs; lia.
  ```

  **Keep the section's `CurCtx` instance (`XI`) in every list.** Half of this
  file's bounds are stated over `SpecFilewrite.FW_MAX`, which is a
  section-parameterized definition, so `clear - Hcrange` alone fails at
  *"Could not find an instance for CurCtx"* — an error that reads like a
  broken proof and is a scoping accident. Sixteen sites converted, no proof
  restructured, and the two `clear`-free repairs found on the way are the
  file's other closer bugs: a bare `discriminate` after `exfalso` (which
  walks the whole context — `discriminate Hex` instead) at two sites, and an
  `f_equal. lia.` closing `c + iz = iz + c` (`exact (Z.add_comm c iz)`).
- **What is left is honest.** A flat tail, top sentence an honest `Qed`. The
  continuation fold was NOT attempted: this file's blocks are already lemmas
  and its return closer is under the floor "THE PRIZE IS ABSOLUTE BYTES OFF Δ"
  gives.
- **The sibling has the same shape and was not touched.** `ProofFilewrite.v`
  carries five `ltac:(lia)` splices at the same four sites (its `IH` apply,
  `fw_addw_moi`, `fw_tail`'s width premise, `fw_offupd`). Nobody has measured
  it cold.

## Framing: name the context side, construct the goal side

- **Never bare `iFrame` in a large context** — it searches the whole spatial
  context for each conjunct of the goal, so cost is (context × conjuncts).
  Rebuilding a 9-conjunct resource with a bare `iFrame` did not terminate; the
  same nine by name is instant.
- **A NAMED `iFrame` still pays a GOAL-side search.** When the goal's conjuncts
  include a big payload (an escrow arm hiding a 268-element big-op), a named
  `iFrame` is minutes. **Give every multi-conjunct resource abstraction a
  CONSTRUCTOR lemma when you define it**, for the same reason it gets an
  accessor: the constructor assembles the arm structurally where the context is
  six hypotheses wide, and the caller writes one `iApply (ic_mk_parked … with
  "Hd Hn Hv Hp Hm Hg")`. Otherwise every user pays a search.
- Where no constructor exists, close a seam by naming every conjunct
  (`iSplitL "H"; [iExact "H" |]` chains), never with `iFrame`.
- **THE CHEAPEST FIX IS USUALLY TO SPLIT THE BIG CONJUNCT OFF FIRST, and it is
  a two-line edit.** A frame is priced by (names × goal conjuncts it walks), so
  it is the ONE definition-valued conjunct in the goal — the escrow arm, the
  parked bundle, the pool shape — that makes it expensive, never the six
  points-tos. Dispatch that conjunct into its own goal with `iSplitL`/`iSplitR`
  *before* framing anything, and the frame that remains is syntactic. The
  rewrite is mechanical: `iSplitL "Hl"; [iExact "Hl"|]`, then
  `iSplitR "<the rest>"` around the arm's own proof, then frame the tail.
  `IcacheEscrow.ipool_shape_to_np`, `ProofIput`'s held-arm close, `ProofIget`'s
  mid-arm re-park and `UsertrapRes.ut_res_bare_sstc` were the four worst
  instances in the tree and all four took this edit.
- **WHEN EVERY CONJUNCT IS DEFINITION-VALUED, THERE IS NO BIG ONE TO SPLIT OFF
  — build the WHOLE bundle.** The two closing-bundle lemmas
  `ProofSyscall.sysc_filestat_env` and `sysc_fclose_fs_env` assemble
  `SpecFilestat.filestat_fs_env` (13 conjuncts) and
  `SpecFileclose.fileclose_fs_env_nopid` (16), and their tails are `dev_inv`,
  `disk_geom`, an `is_lock` over `disk_res`, `bslots`, `fileclose_ic_env`,
  `fileclose_bm` — every one a definition, so every (name × conjunct) attempt
  is a conversion and no single `iSplitL` helps. Named `iFrame`s over them were
  most of that file. Replaced by the `iSplitR; [iExact "H"|]` chain in the
  goal's own conjunct order (the idiom `sysc_fs_fabric` in the same file
  already used), both statements left the profile entirely. Two tells that you
  are in this case rather than the split-one-off case above: the lemma's whole
  job is to REASSEMBLE a named bundle, and its own siblings in the file already
  spell out the chain. The same edit retired `ProofMain`'s `Hpersist` assert,
  `FsSyscalls.fs_world_all`, `ForkretParkClose.forkret_park_pkg_intro`,
  `ProofForkret`'s `first_persist_pre` premise and `Hfab` assert, and eleven
  sites in `UsertrapRes`.

  `UsertrapRes` is the one to read: no single row is enormous and no individual
  frame was expensive — it was the COUNT that made the file, and no seal fixes
  that (sealing `tf_page` locally there helped, but only partly).
  The residue's body is right-nested, so a row that is itself a bundle
  (`ut_trap_parked`'s seven) needs `iSplitR "<the tail>"; [| …]` around it
  rather than a flat chain; that is the only place the mechanical rewrite
  needs thought.

  A persistent bundle asserted with `iAssert P as "#H"` has an EMPTY spatial
  context in its goal, so every row there is `iSplitR; [iExact "H"|]`; mixed
  bundles take `iSplitL "H"; [iExact "H"|]` for the spatial rows and bare
  `iSplitR` (which sends all spatial hypotheses right) for the intuitionistic
  ones. Pure rows are `iSplitR; [iPureIntro; exact H|]`, which is also what
  retires the trailing `iFrame "%"`.
- **A rebuild is a construction, so build it — do not frame it.** Even fully
  named, `iFrame` walks the goal once per name, and the goal is the abstraction
  UNFOLDED, so its tail conjuncts are whatever the abstraction ends in. Handing
  `ut_caps` back with `iFrame "Hpi Hkd Hks Hdev Hrest Hown"` was half its
  file — its tail is `is_lock`s over `disk_res` / `kmem_res` and an
  `is_ftable`, and each match attempt against one of those is a conversion over
  a big resource. The `iSplitL "H"; [iExact "H"|]` chain over the same six
  conjuncts is a syntactic check each, and the statement leaves the profile
  entirely.
- **Extracting a persistent fact out of a bundle must not take the bundle
  APART.** `ut_res_bare_sstc` destructured `ut_caps` to read one
  `sstc_enabled` out of it and then rebuilt it conjunct-by-conjunct inside the
  residue's body. Doing the extraction in a five-line lemma over ONE hypothesis
  and handing the bundle back whole is the fix — and note the intermediate
  attempt made it WORSE, because the rebuild moved rather than disappeared.
  The tell that you are in this case: the proof reads differently from its own
  siblings, which pass `Henv` straight through.
- **A SHAPE MISMATCH turns every match attempt into a CONVERSION, and that is
  the expensive kind.** `ProcInv.tf_words` is a `big_sepL`, so its conjuncts
  carry offsets `8 * Z.of_nat i` while every consumer names them as LITERALS
  (`tf_pa tfp 40`): convertible, not syntactically equal. A bare `iFrame`
  across that pays a conversion on each of its ~36×36 attempts, which was over
  half of `ProofUservec.v` at two sites. Fix: factor the shape change into ONE
  `⊣⊢` lemma (`tf_words36`) proved by `rewrite /tf_words /= bi.sep_emp;
  reflexivity`, so the conversion happens once and both directions then frame
  syntactically. The tell in the profile is a one-token statement (`iFrame.`)
  costing tens of seconds.
- **A ONE-NAME `iFrame` IS STILL A WHOLE-GOAL WALK, so it is expensive
  wherever the goal's TAIL is, and it is the easiest hot statement in a
  profile to misread.** The 2026-09-03 profile had a cluster of them, each
  framing one small persistent row that was already the goal's FIRST
  conjunct: `BioInitAt:328` and `BioInv:1778` (`iFrame "Hllbtl"`, 4.8 s
  each), `ProofBreadParts:354` (2.6 s), `UsertrapRes`'s four
  `iFrame "Hkpt"` (1.6 s each). Read such a statement as a claim about what
  comes AFTER the conjunct being framed, never about the name. Both fixes
  apply and they are not interchangeable: where the tail's expensive
  conjunct is a big-op under a transparent name, seal it and every site in
  the tree is fixed at once (the `Hllbtl` three were one
  `Typeclasses Opaque bcache_scan2`); where it is not, the local
  `iSplitR; [iExact "Hkpt" |]` is a one-line edit and took `UsertrapRes`
  21.4 s → 14.0 s.
- **THE SAME EDIT AT A RUN OF STACK CELLS IS WORTH HALF THE FILE.**
  `UserHeap`'s four `ustack_intro_*` lemmas and `UkSh`'s twelve-cell twin
  rebuild an N-cell `ustack` from N `∃ w, uword …` hypotheses with a bare
  `iFrame` — N goal walks with a conversion per attempt. The
  `iSplitL "Hk"; [iExact "Hk" |]` chain took `UserHeap` 11.5 s → 6.6 s and
  `UkSh` 21.5 s → 18.7 s; `SpecKexecB2.kxc_slot63_split`'s two directions
  (nine `ctx_word_pointsto` cells) 10.9 s → 7.8 s. Where the two sides group
  differently — that lemma splits one cell off an eight-cell block — the
  chain needs one `iSplitR "H9"` first and `done` for the big-op's trailing
  `emp`; everything else is mechanical.
- **`iFrame "%"` IS A CONTEXT-SIDE SEARCH AND IT SHOWS UP AS A HOT
  STATEMENT.** It looks for a proof of each pure conjunct among *all* the Coq
  hypotheses in scope. `SpecFilestat:457` / `SpecFileread:721` (four pure
  rows in front of an `inode_shr_gen`) were 2.9 s each; four
  `iSplitR; [iPureIntro; exact H |]` lines took both files to under half
  their cost. Naming the pures in the destructuring pattern is the enabling
  step — a `(% & % & % & …)` pattern is what makes `iFrame "%"` look like the
  only option.
- **GIVING THE NAMES IN THE GOAL'S ORDER IS SOMETIMES WORTH A LOT AND
  SOMETIMES NOTHING — measure, do not assume.** The rule stands, but its
  size does not: reordering the fifteen `iFrame "Hcfg Hdma Hhalf …"` rebuilds
  in `VirtioProto.v` into `virtio_proto`'s own conjunct order (the list had
  the six ghost-map rows six places early) was **6.4 s of 23.6 s**, with no
  other change; the identical edit on `FirstTok.first_persist_pre` had
  already measured as noise (13.68 → 13.56). The difference is how far the
  misplaced names are from their conjuncts and how expensive the conjuncts
  they walk past are. It is a `sed`, so try it before the chain.
- **SEALING THE BIG-OP CONJUNCTS OF A THIRTY-ROW BUNDLE IS A NULL — do not
  redo it.** `virtio_proto`'s rebuild sites frame seventeen names into ~30
  conjuncts, three of which are big-ops behind transparent names
  (`WpVirtio.dma_own`, `VirtioProto.half_map`, and `dma_own_x`, whose body
  puts a `filter` in front of `dma_own`'s). `Global Typeclasses Opaque` on
  all three, with the two `Timeless` instances the seal then requires, was
  99.4 s → 99.1 s on an isolated A/B and moved no individual statement. This
  is `UsertrapRes`'s case, not `inode_blocks`': no single row is enormous,
  it is the COUNT of (name × definition-valued conjunct) attempts, and no
  seal fixes that. What is left there — the ~17 s the reorder did not get —
  needs the `iSplitL`/`iExact` chain at all fifteen sites, or a constructor
  lemma for the live body; neither has been done.
- **`proc_priv_core` IS THE WORST INSTANCE IN THE TREE, and it is reached by
  every syscall-altitude proof**: its last conjunct is `ProcInv.tf_page`, a
  **4096**-element big-op, so a bare `iFrame` rebuilding it does not
  terminate in any useful time. Do not destructure the tail at all — intro it
  as ONE hypothesis (`iIntros "(%H1 & %H2 & Hpid & Hrest)"`) and close with
  `iExact "Hrest"`, which is a syntactic check. This is the twin of
  durable-notes.md's `Set Printing Depth 40` rule: same 4096 conjuncts, one
  makes a FAILING tactic slow, this one makes a SUCCEEDING one slow, and a
  file that proves over `proc_priv` needs both guards.

## Typeclass search

### AN INSTANCE WITH A LOW PRIORITY IS AN INSTANCE THAT RUNS LAST — and if the class's OTHER instances are structural, "last" means "after the whole payload has been walked"

The regression this cost, and the one-token fix, are the reference case for
reading a profile at all.

`TsoCtx.CtxMorph R` is the transport obligation the M1/M3 context flip put on
every lock payload, and `<{ P }>` (`TsoCtx.const_pay`) is the wrapper that says
"this payload does not depend on the context". `ctx_morph_const_pay` discharges
the wrapped form in ONE step and carried priority **99**, deliberately, by
analogy with `ctx_morph_const`'s evar guard. But the class's other instances are
STRUCTURAL — `ctx_morph_exist`, `ctx_morph_sep`, `ctx_morph_if_then`,
`ctx_morph_or`, `ctx_morph_big_sepL/M` — and they carry the default priority,
which is their premise count (1, 2, ...). `const_pay` is a plain definition, so
search unfolds it and every one of them matches first: the walk peels the
payload's `∃`, its conjuncts, each guarded slot, and bottoms out on leaves that
have no instance and never will (`pstate_lock`, `hart_at_any` — the ξ-dependent
facts the class documents as deliberately uncovered). It proves nothing, and
only after backtracking over the whole space does 99 get its turn.

Changing the `| 99` to `| 0` is the entire fix, and it took the whole
`wp_acquire_sconf`/`wp_release_sconf` family — dozens of sites across the tree's
most expensive statements — down to a handful of sub-second ones.

- **THE EVAR GUARD IS NOT WHAT THE PRIORITY WAS BUYING.** `ctx_morph_const` is
  `CtxMorph (λ _, P)`, whose head unifies with a payload that is still a bare
  evar, so an eager one would silently commit `?R := λ _, ?P`; keep its 100.
  `ctx_morph_const_pay`'s head is a RIGID application of `const_pay`, which only
  a call site that WROTE `<{ … }>` can produce. Read a low priority as a claim
  about *when the head can match*, and check that claim against the actual head
  before believing the priority is load-bearing.
- **`Typeclasses Opaque` ON THE WRAPPER IS NOT THE FIX, and it is the first
  thing you will reach for.** It does kill the same search. It also seals the
  wrapper against `IntoExist`, and the payload's consumers read `R cur_ctx`
  THROUGH the wrapper — `iDestruct "HR" as (t) "H"` on a lock resource whose
  body is an `∃` is the common case. Measured: a from-scratch build fails eight
  files at *"iExistDestruct: cannot destruct"* (`ProofSysUptime`,
  `ProofAllocpid`, `ProofBpin`, `ProofBunpin`, `ProofFiledup`, `ProofFilealloc`,
  …). The general rule: **seal a definition only where nothing reads through
  it.** The big-op seals below satisfy that; a payload wrapper does not.
- **HOW IT WAS FOUND, WHICH IS THE TRANSFERABLE PART.** Two consecutive CI runs'
  profile tables, side by side. Before the flip, every one of the top thirty
  statements was an honest `Qed`. After it, **twenty of the thirty were the same
  sentence shape** — an `iApply (Acquire.wp_acquire_sconf …)` /
  `(Release.wp_release_sconf …)` — in eleven unrelated files, all within a few
  seconds of one another, with ΣCPU up sharply. That uniformity is this file's
  standing tell for ONE shared cause (see the `inode_blocks` seal below), and it
  named the cause without anyone reading a proof. The cheapest confirmation is
  the site that is the goal and nothing else: `SpecProcinit.v`'s bare `apply _.`
  discharging `CtxMorph <{ proc_lock_res … }>`.

### A HAND-ROLLED `first [apply … | apply … | …]` IS INSTANCE SEARCH, AND IT PAYS THE SAME BILL

The subsection above is about a class whose search went wrong. This one is
about the tactic that was written to *avoid* that search and reproduced it
exactly — same class, same tree, six weeks later — so read the two together,
because the tell is the same and the fix is not.

`CtxMorphTac.ctx_morph_solve` discharges a λ-payload's `CtxMorph` obligation
"by name, so nothing relies on typeclass search". As landed it was
`repeat first [ apply ctx_morph_exist | apply ctx_morph_sep | … | apply
ctx_morph_word | … | apply ctx_morph_const ]` — nine lemmas, tried in order,
at every node. **That IS instance search**, with the same three costs and none
of the tuning: one failing higher-order unification per lemma per node, no
discrimination on the goal's head, and the cheap catch-all last.

`DiskInv.v`'s four obligations were almost the whole file, and its top sentence
was the tree's most expensive non-`Qed` statement by a wide margin.
`Set Ltac Profiling` on it:

| | share |
|---|---|
| `apply ctx_morph_exist` | ~30 % |
| `ctx_morph_word` / `_word2` / `_word4` / `_string` | ~41 % |
| `apply ctx_morph_sep` | ~9 % |
| `apply ctx_morph_or` | ~9 % |
| `apply ctx_morph_big_sepL` / `_big_sepM` | ~9 % |

**Read the equal call counts.** `word`, `word2`, `word4` and `string` were all
called exactly the same number of times, which in a `first` means every one of
those visits fell through all four — the leaf lemmas had **zero successes** and
were the single largest share of the file. `ctx_word_pointsto` is not sealed
(each width is a tower over the sealed byte fact), so `apply ctx_morph_sep`,
tried earlier, matched the tower and took every `↦₈` apart byte by byte. Every
leaf visit was preceded by seven failing structural `apply`s.

**The fix is a `lazymatch` on the goal's head — one `apply` per node, no
failing unification anywhere.** The obligations become instant, the file
becomes cheap, one commit, no proof script changed:

```coq
Ltac ctx_morph_step :=
  cbv beta;
  lazymatch goal with
  | |- CtxMorph (fun _ => bi_sep _ _)    => apply ctx_morph_sep
  | |- CtxMorph (fun _ => bi_exist _)    => apply ctx_morph_exist; intros ?
  | |- CtxMorph (fun _ => big_opL _ _ _) => apply ctx_morph_big_sepL; intros ? ?
  | |- CtxMorph (fun _ => ctx_word_pointsto _ _ _ _) => apply ctx_morph_word
  …
  | |- _ => first [ apply ctx_morph_if_then | apply ctx_morph_if_else
                  | apply ctx_morph_const ]
  end.
Ltac ctx_morph_solve := try rewrite /cur_ctx; repeat ctx_morph_step.
```

Four transferable rules:

- **DISPATCH LEAVES TOO, not just composites.** The leaf lemmas were dead
  weight *because* a structural lemma matched through an unsealed tower first.
  A `first` cannot express "this node is a word cell"; a `lazymatch` can.
- **`cbv beta` PER STEP, not once at the top.** Each `apply` leaves its
  subgoals with a β-redex under the λ, and the pattern has to see through it.
- **STOPPING IS PART OF THE CONTRACT, and the `first` version broke it
  silently.** The header says the tactic stops at what it cannot decompose so
  the caller can close it with the component's own instance (`all: apply
  free_slot_res_morph`). It did not: `free_slot_res` is a transparent
  `Definition`, so `apply ctx_morph_sep` matched *through* it and re-walked a
  body a named instance already covered — three times over, which is why the
  four obligations were so unevenly priced. A head dispatch stops by
  construction.
- **DO NOT MOVE `ctx_morph_const` TO THE FRONT.** It is the obvious "cheap
  test — does the body mention ξ?" and on a *leaf* it is exactly that. On a
  whole payload body the unifier tries to eliminate ξ by delta (every cell is
  spelled `ctx_pointsto (cur_ctx ξ) …`) and does not come back.

**A HINT DATABASE IS A VALID ALTERNATIVE AND IT WAS MEASURED, NOT GUESSED.**
`Hint Extern n (CtxMorph (fun _ => bi_sep _ _)) => apply ctx_morph_sep :
ctx_morph` gives the same syntactic dispatch — an `Extern` hint's pattern IS a
filter checked before its tactic runs — and a custom db is small, so `eauto
with ctx_morph` never meets the ~55 wildcard instances in
`typeclass_instances`. Built as ten `Extern` rows plus `Hint Resolve` for the
component instances, DiskInv's four obligations close with a plain
`eauto 40 with nocore ctx_morph` and are just as fast — no
`all: apply free_slot_res_morph` tail needed, because a db is TOTAL where the
walk is partial. Two reasons main keeps the `lazymatch` for now, neither of
them performance:

- `eauto` is all-or-nothing per goal: it cannot walk as far as the structure
  goes and hand back the residual `CtxMorph (λ ξ, free_slot_res …)`, which is
  this tactic's documented contract and its only diagnostic on a class that
  DELIBERATELY leaves the ξ-dependent leaves uncovered. Registering every
  component makes it total and takes that diagnostic away.
- The walk is deterministic and linear; `eauto` backtracks and has a depth.

**And the db's real advantage, which is not speed**: the `lazymatch` is a
CLOSED table in one file, so a new payload shape or leaf family means editing
`CtxMorphTac.v` — which is why main carries an empty branch for the T-leg's
A6.125 half-cell shape. A db is open: each file registers its own rows.
**Owner's call: fix the performance now, revisit the single global table if and
when it becomes a problem.**

**And the question this leaves — why is there a tactic at all?** Because three
properties of `CtxMorph` are not tunable from the instance side. (1) Every
instance's conclusion is `CtxMorph <λ>`, and the hint net keys on the head of
the conclusion's argument, so all ~55 `CtxMorph` instances in the tree are
wildcards tried on every goal. (2) Search cannot be told to stop at a payload
component whose own instance covers it, and a descent that reaches one of the
deliberately uncovered ξ-dependent leaves (`pstate_lock`, `hart_at_any`,
`own_context`) fails and backtracks over everything it just did. (3)
`ctx_morph_const` is pinned at 100 by its evar guard, so the instance that
closes most leaves runs after ~54 failures. Making search do this job means
restating every payload as a keyed `_at` constant plus `Typeclasses Opaque` —
a ~55-instance, 20-file refactor that still cannot express (2). **Search is
already the right answer at the CALL sites**, where the payload is a named
constant with a keyed zero-premise instance. It is the INSTANCE CONSTRUCTION,
whose goal is a raw payload body, that needs a tactic.

- **A BIG-OP UNDER A TRANSPARENT NAME IS AN `iFrame` BOMB, AND SEALING IT IS A
  ONE-LINE FIX FOR EVERY CALL SITE AT ONCE.** `iFrame`'s `Frame` search unfolds
  a transparent constant to get at the `big_sepL` underneath, and then tries
  every candidate hypothesis against every element. `InodeInv.inode_blocks` is
  `[∗ list] i ∈ seq 0 MAXFILE` with `MAXFILE = 268`, and it is the last-but-two
  conjunct of `IcacheEscrow.ic_loaded` — so the bundle rebuild every fs proof
  ends with (`iSplitL "Hdlk"; [iExact "Hdlk" |]. iFrame.`) was expensive
  everywhere. **Seventeen statements in twelve files were all this one shape**;
  `Global Typeclasses Opaque inode_blocks` removed every one of them, roughly
  halved the build's wall span and critical path, and cut the effectively
  serial tail by most of its length. Diagnose it by the *uniformity*: a dozen
  sentences all within a second of each other, in unrelated files, is one
  shared conjunct, not twelve local problems.
  - **`Global`, not bare `Typeclasses Opaque` — the bare form is
    compilation-local.** `ProcDefs.v:84` and `ProcInv.v:57` seal
    `tf_words`/`tf_tail`/`tf_page` twice for exactly that reason, and their
    comment records it. The consequence nobody had drawn: **every other file
    in the tree still sees those three transparent**, and a local repeat pays
    in any file that frames past `proc_priv`.

    **THAT SEAL IS NOW `Global`, and the old advice here — a repeat line where
    the profile says so, not a global seal — was wrong on the measurement.**
    Five more files carried the same frame and never got a repeat, which is the
    uniformity tell for one shared conjunct. One `Global` line in `ProcDefs.v`
    (and `UsertrapRes`'s local repeat dropped as redundant) paid, almost all of
    it in a single file. The lesson is not "seal everything globally" — it is
    that a LOCAL seal hides the size of the prize, because the files that would
    have paid for a repeat never appear in the profile as a cluster until you
    look for one.
  - `rewrite /X` and `unfold X` are unaffected by the seal, so the sites that
    genuinely take the big-op apart keep working, and a `Timeless` instance
    proved `rewrite /X. apply _.` still goes through. Nothing in 1293 files
    broke on the `inode_blocks` seal.
- **BREADTH IS NOT THE PREDICTOR — A BIG-OP BODY IS. Measured, so do not
  re-run it.** The tempting next step after sealing a few big-ops is to seal
  the constants NAMED in the most files, whatever their body. It does not pay.
  Ranked by how many other files name them, the top unsealed iProp definitions
  are `pc_is` (483 files), `sie_cap_gpr` (418), `wp_next` (415), `instr` (332)
  — and none of them has a big-op body. Sealing `pc_is` and `sie_cap_gpr` in
  `ProofSysUnlink`, then the tree's most expensive file, measured as no gain
  and slightly negative. `wp_next` cannot be sealed at all — it is the WP
  continuation former that every proof `iIntros` THROUGH, so the seal fails at
  `iIntro: cannot turn (wp_next ...)`. The mechanism explains it: `iFrame`'s
  cost is (candidate hypotheses × ELEMENTS of the goal conjunct), so unfolding
  a non-big-op is cheap however many files do it. The same experiment on bodies
  that ARE big-ops (`bio_ctx`, `ic_sleeplocks`, `word_pointsto`) paid, while
  `disk_res` — a 47-line body with one `∃` and no big-op, named in 98 files —
  barely moved. **Filter candidates by `big_sep`/`[∗` in the body first; sort
  by breadth only within that set.**

- **AN `∃` OVER A BIG-OP ALREADY SEALS IT — do not re-run this.**
  `FdSlots.fd_frags` is a sixteen-element big-op (one `fd_st` per descriptor)
  and it rides in `UsertrapRes.ut_own` beside `proc_priv`, so it is in the
  goal of every syscall arm: exactly the profile that paid for `tf_page` and
  `inode_blocks`. `Global Typeclasses Opaque fd_frags fd_frags_any` buys
  **nothing** — every delta across five consumer files was inside the
  run-to-run spread. **The mechanism is the reason, and it generalises:** what
  these files actually hold is `fd_frags_any γ = ∃ sts, fd_frags γ sts`, and
  `iFrame` will not instantiate an existential to go looking inside it — so the
  big-op is never walked and there is nothing for a seal to prevent. Check the
  shape a consumer holds, not the shape of the definition: **if the big-op is
  under an `∃` at every use site, it is already sealed and the `Typeclasses
  Opaque` is dead weight.** `tf_page` and `inode_blocks` are bare in the goal,
  which is why they paid.

  Priced `ProcInv.proc_ofiles` (16 slots, bare inside `proc_priv`, hence in
  every syscall goal) the cheap way in the same round — a LOCAL `Typeclasses
  Opaque` in the consumer, no accessor refactor, the technique this file uses
  for `pc_is`/`sie_cap_gpr` above. Also nothing. Sixteen elements is an order
  of magnitude under the big-ops that paid, and `proc_priv`'s frame cost is
  dominated by `tf_page`, which is already sealed. **Do not pay the eight
  accessor `rewrite /proc_ofiles`es it would cost.**
- **Give every big-resource abstraction with a `Persistent`/`Timeless` instance a
  `Typeclasses Opaque` right next to it.** Otherwise each `#`-intro re-derives
  the instance by unfolding and descending into the resource: one `iIntros
  "#Hdlock"` on `is_lock … (disk_res …)` was expensive, and the one line paid
  across six other files. Diagnose by splitting the `iIntros` one name per
  sentence. Sealing the *resource* instead changes nothing — the cost is the
  persistence search, not the hypothesis. The seal costs a `rewrite /X` inside
  the projection lemmas, which is the point: nothing else can then `iDestruct`
  the abstraction apart. Measure before sealing; cost tracks the size of the
  resource, not the number of sites.
  - **AND THE MISSING SEAL SHOWS UP AS THE ENTRY `iIntros` OF EVERY PROOF THAT
    TAKES THE ROW IN — the biggest single cluster in the 2026-09-03 profile,
    and the fix is one line.** Thirty-four statements in eleven files, all of
    the shape `iIntros "Hcg Hown #Htext #Hda…"` at the top of an fs-altitude
    whole-function proof, 67 s of ΣCPU between them. That uniformity is this
    file's standing tell for ONE shared cause, and splitting `ProofIunlock`'s
    twenty-two-name intro one name per sentence named it exactly: `iIntros
    "#Hslk"` alone was 1.92 s of the 2.07 s, and `Hslk` is
    `SleepLock.is_sleeplock_genl`, which had a declared `Persistent` instance
    and no seal. Four `Global Typeclasses Opaque` lines (`is_sleeplock_genl`,
    `_gen`, `is_sleeplock`, `_tok`) took ProofIunlockput 11.8 s → 8.1 s,
    ProofSysOpenTails 28.9 s → 20.9 s, and — measured on the whole-tree
    profile — ProofCreate −20 s, ProofNamex −19 s, ProofSysOpen −16 s,
    ProofKexecB3 −12 s, none of which anyone had opened.
  - **PUT THE SEALS AT THE END OF THE DEFINING SECTION, not next to the
    definition.** A file that defines a bundle almost always also states its
    own projection lemmas (`is_sleeplock_genl_name` is `iIntros "[$ _]"`), and
    those are what a seal above them breaks — the error is *"iAndDestructChoice:
    cannot destruct"* in the file you just edited. `BioInv.v`'s `bio_ctx` seal
    already sat at the end of its section for the same reason.
  - **A CONSUMER THAT DESTRUCTURES THE SEALED NAME NEEDS ONE `rewrite /X`, and
    the build names every one.** Sealing `BioInv.bcache_scan2` (a `big_sepL`
    over the 30 buffer slots, bare in every fold's goal) cost exactly two
    repairs across the 80 references in seven files — an `iIntros` pattern in
    `bcache_scan2_floor_mono` and an `iDestruct` in `ProofBrelse` — and paid
    BioInv 21.7 s → 12.7 s, BioInitAt 12.1 s → 6.9 s, ProofBreadParts
    9.3 s → 6.8 s.
- **Prove a big `Timeless`/`Persistent` instance STRUCTURALLY, never with one
  `apply _`** — one `apply _` over an `∃/∗/∨` tower backtracks across the whole
  space, for a fact whose every leaf instance already exists. Peel one
  connective per step with `apply _` only at the leaves. A recursive helper does
  it uniformly, but **its dispatch must be SYNTACTIC**:

  ```coq
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- _ => apply _
    end.
  ```

  Second file (`BioInv`): four such instances over the buffer escrow's arms
  were most of the file — `buf_parked_timeless`'s single `apply _` alone was
  half of that — and `tl_struct` halved it. The dispatch must be SYNTACTIC: the
  `first [apply bi.exist_timeless; … | …]` spelling is a REGRESSION, an order
  of magnitude worse than even the monolithic `apply _`, because `apply`
  unifies up to delta, so it peels straight *through* a named abstraction that
  already has its own instance and then backtracks over everything underneath.
  **Descend through the connectives, never through a name.**

  **Third and fourth files, 2026-09-03, and the point is that the peel is
  worth doing on a SMALL body too.** `OffBox.off_hdr_timeless` — one
  `apply _` over `∃ v, a_foff k ↦₄ v ∗ ⌜off_wf v⌝`, three connectives — was
  **more than half the file** (3.65 s of 6.7 s), because `apply` walks
  through `↦₄`'s own instance into the byte tower and backtracks. Three
  lines of peel took the file to 3.7 s. `IcacheEscrow` still had two arms
  (`ic_hdr_bare_amb`, `ic_hdr_frz_amb`) on a bare `apply _` while the same
  file already carried `tl_struct` twice elsewhere; giving that section its
  own copy was 4.4 s, on a critical-path file. Do not read "small body" as
  "not worth peeling": the predictor is the LEAF, not the connective count.

  **And when the peel bottoms out, NAME the leaf instances rather than
  leaving `apply _` there.** `BioInv.bio_ctx_persistent`'s peel left
  `apply _` on `is_sleeplock_genl … ∗ buf_box …`, neither of which was
  sealed, and that residue was still 2.3 s;
  `[apply is_sleeplock_genl_persistent | apply buf_box_persistent]` took it
  to nothing. A named `apply` is the leaf-level twin of the syntactic
  dispatch above.
- **Pay deeply nested polymorphic structure once behind a fully typed
  wrapper.** `IcacheRef` applied `prod_local_update'` six levels down the same
  named seven-component CMRA at twelve callers; elaboration rediscovered the
  outer product at every site, and the first application alone was expensive
  each time. A helper stated over the named constructor and all seven component
  updates pays that inference once in its proof; callers then supply identity
  or component-local updates to the fixed signature. The profile now has one
  structural application instead of twelve. This is useful when the repeated
  cost is in the first polymorphic constructor application, not when the
  component updates themselves are slow.
- **Mark big concrete literals `Global Typeclasses Opaque`** (`kernel_bytes`,
  `kernel_data`, `kernel_symbols`, `mem_pointsto`) or instance search unfolds a
  23K-entry gmap every time. Use `Typeclasses Opaque`, never `Opaque` — a
  tactic may need to `unfold`, and `vm_compute`/`reflexivity` ignore the former.

## Modalities and rewriting

- **Strip only the GOAL's later with `iApply bi.later_intro`** — and this is
  worth SWEEPING, not just applying to new proofs. **THE SWEEP IS DONE: 420
  sites in 139 files**, worth a consistent fraction of a second per call site
  with no other change, and on the order of a minute and a half of tree time
  across the files it touched.

  The `iNext;` sequencing form was swept too: 24 code sites, 18 kept in 10
  files (`FsCrash`, `HartSpan`, `HartSMem` rejected it). Not separately timed —
  it is the same substitution, and 18 sites mostly in cheap files is under the
  noise floor of a shared box. **The `[iNext]` occurrences are PROSE**, the
  notes' own bracket convention for naming a tactic: all 42 are inside comments
  and none is a code site, so a `\biNext\b` sweep must blank comments first.

  **Where it is NOT replaceable, `coqc` says so**, which is what makes the sweep
  safe: ~90 files rejected it and were reverted, and they are almost all the
  engine/leaf layer (`WpSmode*`, `UserStep*`, `HartStep*`, `ParkCap`,
  `TrampStepPt`, `UptWalkPt`, `SchedCtx`, `FsCrash`, `InodeRegion`) — i.e. the
  Löb back edges, where `iNext` genuinely has to strip the hypothesis-side
  later. Reverting on failure takes ~14 build rounds because each round only
  surfaces the next dependency layer.

  Reach for `iNext` only at a genuine Löb back edge. `iNext` is `iModIntro` at
  `▷`, so it runs `MaybeIntoLaterN` over every hypothesis in both environments,
  where `bi.later_intro` touches only the goal. The tell that a file has this
  backwards is an `iNext` followed by `iAssert (▷ X)%I … { iNext. iExact "H". }`
  — that block is *repairing* a `▷` the `iNext` stripped, so both tactics are
  the expensive one and the pair does no net work.
- **A modality step at a `▷` costs the CONTEXT, so pay it in a lemma.** An
  `iMod` at a `▷` inside a whole-function proof is expensive where the
  `Timeless` search on the same bundle standalone is free. Gotcha when writing
  the lemma: **its conclusion must be a FANCY update, not `|==>`** —
  `IsExcept0 (|={E1,E2}=> P)` holds unconditionally while `is_except_0_bupd`
  needs `IsExcept0 P`, so `iMod` fails with *"cannot eliminate modality"*, which
  reads like a missing `Timeless` instance and is not. Take the mask as a
  parameter.
- **Prefer the WAND form of a big-op law to a setoid rewrite.** `rewrite
  !big_sepL_sep` is setoid rewriting over `envs_entails Δ Q`, and its cost is in
  the `Proper` proofs over the PREDICATES — so hoisting it into an empty-context
  lemma changes nothing. `iApply (big_sepL_sep_2 with …)` matches by head and
  never enters setoid rewriting. Do not sweep this — the tree's other sites are
  sub-second because their predicates are small. Check the `.v.timing` cost of a
  candidate first; the site count tells you nothing.
  - **Two sites were still on the rewrite form and BOTH were worth it**
    (`BootShared.v`'s eight-way chain is the idiom to copy, and its comment
    already cites this rule). Each zips three families into one walk:
    `FileInv.ftable_res_boot` and `ProcInv`'s ofile block — the latter small in
    itself but `ProcInv` is ON THE CRITICAL PATH, so it is chain seconds. Grep
    is `rewrite !big_sepL_sep` followed by an `iFrame`.
- **PEEL A CHAIN BY `apply`, NEVER BY `erewrite` — an equation lemma builds an
  `eq_ind_r` motive over the whole remaining term at every step.** `goodb_bind`
  is stated as `goodb D (bind m f) s = goodb D (f x) s`, so
  `repeat (erewrite goodb_bind by (vm_compute; reflexivity))` re-copies the
  entire monadic tail once per bind — and once a continuation has been
  instantiated with symbolic bitvector data the tail is large. Ltac profiling
  is what settles it: the overwhelming majority is LOCAL to the `erewrite`,
  against a few percent in the `vm_compute` side conditions and a little more
  in their `reflexivity` — i.e. the side conditions everyone suspects are not
  the cost. The intro form (`goodb_bind_i : … → goodb D (f x) s = true → goodb
  D (bind m f) s = true`, one line off the equation) has the same two side
  conditions and no motive, and the proof term becomes a chain of applications,
  which takes the `Qed` down with it. Not a sweep: the same `goodb_step` in
  `WpSconfCsr` / `WpGprCsrwC` is cheap, because nothing has put a symbolic
  value in their tails.
- **WHAT IS LEFT OF THAT PEEL IS THE `eapply` ITSELF, and five further
  interventions all measured null; do not redo them.** Ltac profiling puts the
  majority LOCAL to `eapply goodb_bind_i`, then `reflexivity`, then
  `vm_compute`. Unrolling the `repeat` shows the cost is not spread — it decays
  sharply step by step, i.e. it tracks the size of the CONTINUATION the step has
  to retype, which is exactly what a one-node-at-a-time peel cannot avoid.
  Tried and within noise: `cbv beta` before the loop; `cbv beta` after every
  step (worse); `vm_cast_no_check (eq_refl true)` for the `goodb` side
  condition; a `lazymatch` dispatch on `bind`/`bind0` instead of `first` (so no
  branch ever fails); and a `Hint Resolve` database of the per-leaf `exec_*`
  lemmas so the exec side condition is a lookup rather than a `vm_compute`.
  Getting below this needs a different formulation — a multi-bind peel lemma,
  or a `goodb` that computes without touching the data — not another tactic.
- **`Qed` re-checks and therefore DOUBLES every `vm_compute`** — the kernel
  re-runs the reflexivity check at `Qed` time, so a lemma whose tactic is heavy
  `vm_compute` costs about twice that in wall clock. Budget 2× the `-time`
  figure for any vm_compute-heavy lemma, and prefer one big boolean sweep with
  lookup spec lemmas over N per-item `vm_compute` lemmas — the sweep pays the
  2× once.
- **THE DOUBLING IS AVOIDABLE: build the cast, do not run the tactic.** The
  kernel's re-check is the reduction that has to happen; the tactic's is the
  one that does not. `vm_cast_no_check` puts the `vm_cast` straight in the
  proof term and typechecks nothing at tactic time, so the reduction is paid
  once. `ElfKernel.v` and `FsImgCheck.v` each carry it as a three-line local
  tactic replacing `vm_compute. reflexivity.`:
  ```coq
  Local Ltac vm_eq :=
    lazymatch goal with
    | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
    end.
  ```
  It roughly halves each of `FsImgCheck`, `ElfKernel` and `ElfUser`: the whole
  tactic column of those files drops to zero and only `Qed` pays.
  - **IT MUST BE THE RIGHT-HAND SIDE.** `eq_refl r` casts `r = r` to `l = r`,
    so the VM evaluates the heavy side once; the mirror spelling
    `eq_refl l` makes it evaluate that side TWICE and is **worse than the
    `vm_compute` it replaces**. The two spellings read identically; only the
    A/B tells them apart, so measure after writing one.
  - The cost is diagnostic, which is why this is for the HEAVY sentences and
    not a sweep (647 `vm_compute. reflexivity.` sites in the tree, nearly all
    sub-second): a disagreement now surfaces at `Qed` as a kernel conversion
    failure with no goal in view. Put `vm_compute. reflexivity.` back on the
    one failing lemma to see it.
- **A CONSTRUCTOR IS INJECTIVE AT VARIABLES — NEVER AT A FILE'S CONTENTS.**
  Measured on `iris/FsInitPin.v` (fs-syscall-specs lane P). The lemma wanted was

  ```coq
  file_bytes (fs_data_of fsimg_P (fs_dinode fsimg_P fsimg_sb 7)) <size>
  = ElfUser.init_elf                       (* 35,976 bytes *)
  ```

  off `FsImgCheck.fsimg_init_at`, i.e. `Some (NFile X) = Some (NFile Y)` with
  `Y` the literal. **Both obvious spellings — `injection H` and `exact H`
  through a projection `nfile_bytes` — never finished**, while every other
  sentence in the file was free. The reason is `FsImgCheck.v`'s own header
  rule one level down: conversion is free to unfold `FsTree.file_bytes`
  instead of the projection, and `file_bytes` is quadratic in the file size
  and rebuilds the block once per byte.
  The fix is to prove injectivity **at variables**, where the variable is
  rigid so the projection is the only thing conversion can unfold, and then
  close the instance by transitivity through the term both sides already
  share:
  ```coq
  Definition nfile_bytes (o : option fsnode) : list (bv 8) :=
    match o with Some (NFile b) => b | _ => [] end.
  Lemma nfile_inj (b b' : list (bv 8)) :
    Some (NFile b) = Some (NFile b') -> b = b'.
  Proof. intros H. exact (f_equal nfile_bytes H). Qed.
  (* instance: apply nfile_inj; transitivity (node_at P sb i); ... *)
  ```
  That took the file from not finishing to trivial. The same rule retired an
  `injection` on a row carrying those bytes (`Some_inj` instead). Read it as
  the converse of the `vm_eq` rule above: there the kernel SHOULD reduce and
  you make it do so once; here it should not reduce at all and you must give
  it a shape where it cannot start. And note the diagnostic trap that cost
  most of the time — **`coqc`'s output is block-buffered when redirected**,
  and `stdbuf` does not help (OCaml buffers internally), so the log's last
  line is not where the compile is. Use `script -q -e -c "coqc -time …" log`
  (a pty) or, better, bisect with `head -N file.v` probes.
- **AND MEASURE ON A QUIET VM.** Three of those five variants first read as
  clear regressions, purely because another tree was building; the same
  variants re-measured on a quiet box were within noise. `uptime` before an A/B
  is worth the second it costs — the builder is SHARED, which the isolation
  rule at the top of this file assumes away.
- **`rewrite wp_next_off` is a setoid rewrite over the whole goal — use `iApply
  wp_next_off_intro`.** Same continuation, matches only the head. A `b`-generic
  proof has no such sites at all (it threads `wp_next … b …` and discharges with
  `wp_next_chain`).
- **Do not write a trailing `[-]` in a leaf `iApply`'s spec pattern.** `with "Hcg
  Hpc Hi [-]"` and `with "Hcg Hpc Hi"` leave the same goal, but `[-]` forces an
  explicit `envs_split` of the whole spatial context at every instruction. Safe
  to omit whenever the omitted premise is the last one, which for a
  `wp_next`-continuation leaf it always is. (Mid-pattern `[-]` is a different
  shape and stays.)

## Register-file towers (`mm_rs` and friends)

A canonical register file spelled as a tower of `register_set`s — `HartMFrame`'s
`mm_rs`, 16 deep — is a **delta bomb**, and all three of the following bit
during one afternoon of writing `wp_instr`. The common cause: `register_set` is
a record update, so *any* conversion that unfolds the tower compares record
updates pairwise, and the cost is exponential in the depth.

- **Make the tower `Opaque` the moment its lookup lemmas are proved.**
  `Global Opaque mm_rs.` right after the section that establishes the nineteen
  `mm_rs_*` lookup equations. Left transparent, every `apply`/`iApply` whose
  unifier meets a concrete tower may delta-expand it: an `InstrBytes` with four
  `wp_instr` arms did not finish at all transparent, and the same arms' setup
  was instant opaque. The lookup lemmas are the only interface any consumer
  needs, so nothing is lost.

- **Never leave a goal with a tower on BOTH sides to `reflexivity`.** A
  `reg_agree_on D (mm_rs .. x ..) (mm_rs .. y ..)` goal looks like two rewrites,
  but `rewrite mm_rs_priv` fires on the FIRST occurrence only, and then `by`'s
  `reflexivity` is asked to convert `Machine` against a 16-deep tower. That
  hangs. Fixes, in preference order: (1) restate so one side is a **variable** —
  prove `<12 lookup hypotheses> -> reg_agree_on Dro rs (mm_rs ..)` once, then
  instantiate `rs` with the other tower and discharge the hypotheses
  **positionally** (`apply mm_rs_ro_agree; [apply mm_rs_priv | .. ]`); (2) failing
  that, `etransitivity; [apply L | symmetry; apply L]`, which unifies one side at
  a time and never converts. A `first [apply .. | .. ]` over 19 alternatives is
  NOT a fix — the failing branches are exactly where the unifier deltas.
  **AND FALLBACK (2) IS NOT FREE — it is the second-best answer and it reads
  as the settled one, so check for the missing `_ro_agree` twin before you
  believe a file's cost.** `WpInstrConfig.mc_ro_nPC` — `HartMFrame.mm_ro_nPC`'s
  twin at the parametric tower, and its own comment even cites `mm_ro_nPC` as
  the reason it is not a `first` — was on fallback (2): an `etransitivity`
  whose two halves are each a TWELVE-way `first [apply mc_rs_… ]`, run once
  per register, 4.0 s, most of the file. The file had `mc_rs_agree`
  (nineteen rows, `mm_Drw ∪ mm_Dro`) but no `mc_rs_ro_agree` (twelve rows,
  `mm_Dro`) — HartMFrame has both. Writing the missing twelve-row twin, a
  copy of `mm_rs_ro_agree` with `priv` parametric, and applying it
  positionally took the file 13.5 s → 9.1 s.

- **`ltac:(tac)` in argument position runs BEFORE the surrounding evars are
  solved.** `rewrite (Hag _ ltac:(set_solver))` and
  `rewrite (irrelevant_register_set _ r _ _ ltac:(vm_compute; reflexivity))`
  both hand the tactic a goal whose register is still `?r`, and `set_solver` /
  `vm_compute` on an evar does not terminate usefully. Use
  `etransitivity; [apply L; <tac> | ]` so `apply` fixes the register from the
  goal first. (Same trap as §"Inline `ltac:` in argument position", reached from
  a different direction.)

## Directed entailments, not `⊣⊢` rewrites, for frame bridges

`hreg_frame_ext`, `hreg_frame_ro_ext`, `mm_rw_split`, `mm_ro_split` are `↔`/`⊣⊢`,
so using them means `rewrite` — and **a `rewrite` inside a proofmode goal fires
on the whole `envs_entails Δ Q`, context included** (this is RULE ONE again, in
a shape that is easy to miss because the lemma looks tiny). Inside one
`wp_instr` arm, `rewrite mm_rw_split mm_rs_PC .. mm_rs_ip` — a seven-cell split
plus its seven lookup rewrites — was the whole arm; nothing else in it
registered at all.

The fix is not to tune the rewrite, it is to **not rewrite at the call site**.
Export the same steps as one-directional lemmas, proved once where the goal is
two lines long, and let callers use `iDestruct` / `iApply`:

```coq
Lemma mm_rw_ext rs rs' : reg_agree_on (mm_Drw ∪ mm_Dro) rs rs' ->
  hreg_frame rs mm_Drw -∗ hreg_frame rs' mm_Drw.
Lemma mm_rw_open <tower params> :
  hreg_frame (mm_rs ..) mm_Drw -∗ (PC ↦ᵣ pc ∗ .. ∗ mip ↦ᵣ ip).
Lemma mm_rw_close <tower params> :
  (PC ↦ᵣ pc ∗ .. ∗ mip ↦ᵣ ip) -∗ hreg_frame (mm_rs ..) mm_Drw.
```

Note `mm_rw_open`/`_close` are stated **at the tower**, so the lookup rewrites
are absorbed too and the caller neither splits nor rewrites. Rule of thumb: if a
frame lemma appears under `rewrite` anywhere downstream of the file that proves
it, that is a directed lemma waiting to be written.

The READ-ONLY twins (`mm_ro_open` in HartMFrame, `mc_ro_close` in
WpInstrConfig) were written for exactly one site that had been missed:
`WpInstrConfig.mc_ro_acc`, whose goal carries a whole `mc_rs` tower inside its
∀-closure, so its `rewrite mm_ro_split` was most of the file. **Where the goal
is small the same `rewrite` is free**, which is why the other five
`mm_rw_split`/`mm_ro_split` sites in that file and in `InstrBytes` were left
alone: read the `.v.timing` cost of a candidate site, never its shape.

## Register maps

- **`pose`, not `set`, for a whole-function proof's register chain.** The idiom
  keeps the goal one insert deep, so there is no deep term for `set`'s occurrence
  abstraction to collapse — but `set` pays a whole-goal pattern search per
  instruction, and the goal is `envs_entails Δ Q` with the entire context inside
  it. Cost scales with CONTEXT, not chain: free in a small proof, half the file
  in a big one. Keep `set` only where the abstraction is the point — a value
  that really does occur throughout the goal. Note `set (x := e)` *with
  parentheses* is vanilla Coq's `set`, not ssr's, so it does not fail when it
  finds no occurrence. A `set (X := e)` immediately followed by `change e with
  X` is the fully-redundant form — the `change` alone produces the same goal, so
  the pair is `pose` + `change`; in `ProofPipewrite` the `set`s cost an order of
  magnitude per call over the sibling's `pose`s.
  **Where the file already uses `set`, deleting the trailing `change` is the
  free half of that fix and needs no other edit**: the `change` is then a
  whole-goal conversion that folds nothing, because `set` has already folded
  every occurrence. 45 of them in `ProofForkret` were worth deleting with the
  proof script otherwise untouched. Grep is `set (X := T).` immediately followed
  by `change T with X.` with `T` equal up to whitespace.
- **`Local Strategy opaque [rget tp_pin rf_upd]` in a whole-function proof whose
  leaves state their premises over `rget`.** Every such `iApply` otherwise makes
  the unifier walk `rget → tp_pin → rf_upd` down the whole update chain, and the
  `Qed` re-walks it (ProofPipewrite: eight hot `iApply`s and the final `Qed` all
  improved sharply). The trap: any premise spelled `M !!! Regidx r` where the
  leaf's statement says `rget M r` was bridging by delta and now REGRESSES —
  restate it in the `rget` spelling via `rget_ne` (HartTp.v) before the `iApply`
  and the site goes syntactic. Audit: `-time` before and after; the regressing
  sites are the ones that got slower.
  **Sealing can regress a DIFFERENT, distant site.** `Strategy opaque` deepens
  the unifier's walk at every `rget`-typed premise in the file, and an inline
  general-purpose closer (the "Inline `ltac:`" rule below) is priced by
  exactly that depth — a `dl_need` bound three `dirlink`s deep regressed
  sharply from a `Strategy opaque` elsewhere in the same file with no textual
  connection to it. Audit `-time` across the WHOLE file after sealing, not just
  the sites the seal touches directly; fix a regressed site with the same
  inline-`ltac:` hoist as any other (`assert (H : …) by (clear -H..; lia)`),
  whose keep-list must include every hypothesis the final `lia` draws on — not
  just the ones the tactic script names textually. Grep sibling call sites for
  the same derived bound, or dump the goal and context at the failing site
  (above) if none exists.
- **`reg_lookup` (RegFile.v) by default** — one `vm_compute` over the concrete-key
  if-chain. Where the target value is SYMBOLIC, `vm_compute` would try to reduce
  it and hang; use the lemma-based `peel_reg`, which peels via `upd_eq`/`upd_ne`
  so values stay opaque. Two rules it encodes:
  - **Peel ONE layer at a time; never unfold the whole `set`-chain first.**
    Unfolding a 20–30-layer chain makes one giant term that every peel
    re-traverses — O(depth²). Must be `first [peel | unfold-var]`, NOT a
    `lazymatch` with the var branch first: the pattern `?M !!! _` also matches an
    exposed update, so `lazymatch` commits to `is_var`, fails, and silently
    stalls after one unfold.
  - **Try the HIT lemma (`upd_eq`) BEFORE the miss lemma**, and guard the
    disequality with `reg_neq` (`tryif unify a b then fail else (vm_compute;
    discriminate)`). Miss-first order attempts `upd_ne` at the terminating layer,
    whose side goal is FALSE, and `discriminate` exhaustively hunts a
    discriminating position in two equal records.
  - Auditing an existing file: a site is safe to collapse to the generic peel
    when its unfold list is EXHAUSTIVE down to the chain's genuine non-`set` base;
    it is unsafe when it deliberately stops at an interior link to hand off to a
    fact proven about that link.
- **Collapse a run of N consecutive same-register writes into ONE update with
  `upd_upd`, inline, right after the writes** — otherwise every later peel that
  crosses the block pays N layers. Keep the intermediate `set`s defined so the
  pre-existing deep peels still parse (`rewrite /Mk` on a def not in the goal is
  a harmless no-op), and you change only the block, never its readers. For a
  single-use block prefer this to a `Qed`-sealed chunk lemma; when the same body
  recurs across call sites, the sealed lemma pays instead.
- **`unfold set_reg` is a `3^N` tree bomb** — its body mentions `s` three times,
  so unfolding over an N-deep state chain writes out `3^N`, and every later
  `rewrite` copies that into an `eq_ind_r` motive. The goal after `cbn` is small,
  so nothing looks wrong and the cost lands entirely in `Qed`. **Peel with the
  projection lemmas in `RiscvLang.v`** (`rewrite ?sregs_set_reg ?mem_set_reg
  ?mdev_set_reg`), which are goal-identical drop-ins. Three shapes must keep the
  `unfold`: a whole-STATE equation (`set_reg (set_reg s r a) r b = set_reg s r b`,
  or `set_reg s r v = s`) has no projection for the rewrites to fire on and needs
  the `MState` constructor exposed for `f_equal`; and `rewrite ?<proj>_set_reg`
  immediately before a `rewrite H` whose LHS is a projection of a `set`-bound
  state breaks, because ssr's `rewrite ?L` deltas through let-bound locals while
  matching and overshoots (`cbn [mdev]` does not, and stops where the hypothesis
  wants).
- **State a whole-function WP's post in the ∀-continuation form** — never with a
  deep `let m1 := … in … let mN := … in` register-map chain in the STATEMENT.
  Every caller's `iApply` zeta-traverses the whole chain, and nested gmap inserts
  blow up quadratically. Quantify the return map abstractly (`∀ m', … gpr_file m'
  … ⌜callee_saved m0 m' ∧ <return facts>⌝ … -∗ WP`) and keep the concrete chain
  alive inside the Proof only. Callers change by one token.

## Inline `ltac:` in argument position

**Never splice a computing tactic into a term whose implicit arguments are still
evars.** The proofmode re-elaborates the spliced term without the `Qed` vm-seal,
and against unresolved width/map evars it can fail to terminate outright. Prove
it first as `assert (H : …) by (tac)` and pass `H` by name — a named hypothesis's
type is fixed, so there is no re-elaboration. This was expensive *per call site*
for the `kernel_data_string` / `kernel_data_window` byte-lookup premises, and
non-terminating for an `iApply` whose map argument is a ∀-bound `Mr` from a loop
invariant. If several such args exist, use the **unshelve hoist**: replace the
inline `ltac:`s with bare `_`, prefix `unshelve iApply`, and discharge the evar
subgoals as standalone `{ … }` goals.

**An inline `ltac:` whose tactic is a GENERAL-PURPOSE CLOSER is priced by the
DEPTH of its call site, not by its goal** — so the identical sentence
terminates in one arm of a function and does not terminate in another. Three
`lia`s in `ProofCreate.cr_mkdir_half` (the post-`dirlink` size read-back, and
two `ltac:(lia)`s in `DirLinks.dir_link_at_dirlink`'s `2 <= tot` slot) never
finished, and ate tens of gigabytes doing it, where `cr_alloc_half` runs the
same `cr_wi_size_max` chain inline and is fine; the difference is only that the
mkdir arm sits three `dirlink`s deeper, so `lia`'s atom scan meets three calls'
worth of accumulated arithmetic. Each goal was one equation away from trivial.
Hoisting them to `assert (H : …). { clear -<the one equation>. lia. }` made the
file cheaper than the baseline that did not contain the arm at all. The tell is
that the goal looks tiny; do not read a stalling `lia` as a hard arithmetic
problem, read it as a context problem, and note that `clear -H` is only
available once the goal is a NAMED assert — which is the second reason not to
splice a closer into argument position.

**AND THE GOAL CAN BE A CLOSED NUMERAL AND STILL COST SECONDS.**
`ProofSysUnlink.v:4935,6570` spliced `ltac:(lia)` for `wi16_post`'s `0 < tot`
guard — on an arm that has already `destruct (decide (tot = 16%nat)) as [-> |
_]`, so the goal is literally `0 < 16`. It was seconds each, because `lia`
reifies the context it is handed and this is the tree's largest.
`assert (Htot16 : (0 < 16)%nat) by (apply Nat.lt_0_succ).` on the line above,
passed by name, took both out of the profile. Read a slow closer as a CONTEXT
problem before you read the goal at all.

- Grep for `ltac:(intros` inside a `kernel_data_window` / `kernel_data_string`
  argument list — every hit is this bug.
- The related fix is often to state the byte premise over a SYMBOLIC index as its
  own pure lemma, which deletes a `destruct i` on the Iris goal entirely.
- **The 18k-entry `list_to_map` is NOT the cost** — the VM compiles `kernel_data`
  to bytecode once per process, so the first lookup pays and every later one is
  free. When a `vm_compute`-over-a-big-map sentence is slow, suspect the
  inline-`ltac:` position, not the map.

## Conversion and `Qed`

- **A check that grows past a few hundred MB / minutes on a small file is a
  DEGENERATE PROOF, not something to wait out** (user-wp-slot lane). The two
  culprits that session: any reduction/unification that touches the dumped
  literal `SyncInstrs.sync_bytes` (`cbn [fst]` on a goal mentioning it,
  `decide` on a symbolic image `M` — keep the literal behind opaque lemmas and
  gate `sync_layout`-first), and ssr `rewrite`/`iFrame` against the 32-insert
  `userret_gpr` chain (enumerate the 32 `mword 5` indices and peel per case; an
  insert-chain `rewrite` unifies the `Insert` instance up to delta and does not
  terminate). A THIRD DOOR into the same divergence (a lane's
  `tf_ueq_resume_gpr`): `f_equal` — it begins by trying `reflexivity` on the
  whole goal, and that conversion check delta-unfolds `userret_gpr` into the
  tower on both sides with UNEQUAL leaves and backtracks forever. Rule: never
  let `reflexivity`/`f_equal`/any unification see a goal whose two sides contain
  the tower but differ — rewrite the leaf equalities first (each pattern a
  closed `tf !!! i`), so `reflexivity` only ever runs on syntactically identical
  sides.
- **`vm_compute; reflexivity` is rechecked by the kernel's LAZY conversion at
  `Qed`** — the VM's speed does not carry over, and on model code that is a
  different order of magnitude (one such equation over the cold-boot chain ran
  the box out of memory; fifteen inside one `Qed` far worse). Close such goals
  with `vm_cast_no_check (eq_refl <rhs>)` so the kernel rechecks with the VM
  too, and compute the result ONCE into its own `Definition` plus a single
  VM-cast lemma, after which downstream facts are shallow conversions.
- **A guard fixed by `change`/a plain cast pushes a slow non-VM conversion to
  `Qed`.** Use `replace g with v by (vm_compute; reflexivity)`. For
  CSR/extension dispatch guards use `csr_dispatch_eq` (ExecCommon.v). **NEVER
  `cbv -[…]`** (negative delta) to collapse a Sail dispatch guard — it unfolds a
  definition with a huge normal form and OOMs the box.
- **Never `vm_compute` a goal containing a symbolic `mword` variable or a
  concrete built-up `mstate`** — it tries to normalize 64-bit modular arithmetic
  symbolically and does not terminate. Compute only the CLOSED offset, or prove
  the pure fact against an abstract state and `apply` it.
- **Never let an `exact`/`reflexivity` cross an update layer.** Peel every layer
  down to the map the named fact is actually about, or the kernel converts the
  whole transparent `rf_upd`/`bool_decide`/`mword_of_int` tower, and the tell is
  that the sentence right below it, four explicit layers down, is free.
- **A `reflexivity`/`exact` that folds a `gset` back into its name normalises the
  underlying `list_to_set`.** Unfold the two names first so the match is
  syntactic.
- **Sealing a definition tower halfway buys nothing — seal every layer down to
  the one that computes, or none.** `rget` → `tp_pin` → `rf_upd`: with `rf_upd`
  transparent, sealing the top two cannot change anything. Sealing all three cut
  one file and its `Qed` by more than half. **But do this per file with a
  measurement, never as a sweep** — across ten of the tree's most expensive
  proofs the same three `Strategy` lines were all inside noise, and one file
  does not even compile with them (it `unfold`s `tp_pin`). The outlier had both
  a 20+-link `pose` chain and a large Iris context; that combination is what
  makes conversion dominate. **`ProofSysUnlink` is the best-fitting candidate
  left (101 links, the tree's largest context) and it is a NULL**, compiling
  with no `rget_ne` repair needed. So the lever really is confined to
  `ProofVirtioDiskInit`'s shape; stop looking. A caution from that same A/B: the
  first pair read as a large win purely because the two arms ran at very
  different loads — the inversion this file's Diagnosis section warns about,
  seen live. Only the second pair, on a quiet box, showed the truth. The cost is
  invisible to tactic profiling — it lands in the kernel at `Qed` and inside
  `iEval`/`pm_reduce`.
- **Invert a symbolic-step executor over its ABSTRACT parameters** — never
  `cbn`/`unfold` it into a hypothesis and destruct the guards there. Each
  `destruct` of a guard buried in the reduced term reverts the hypothesis into
  the match's dependent motive, and at `Qed` the kernel must normalise the
  immediate there; an immediate carrying an `autocast` (`concat_vec`) is far
  costlier than a plain `sign_extend'`. The whole cost lands in
  `Typeops.execute`. **Not fixable by opacity** — sealing sent the file to tens
  of gigabytes at *tactic* time (the kernel never explodes from opacity; only
  the tactic engine does). The fix is one inversion lemma doing the guard case
  analysis with the displacement OPAQUE.

## Where a `Qed` actually goes

Only about a quarter of a `Qed` is typechecking (`Typeops.execute`, which is
DAG-linear and memoized). The rest is four TREE walks — `HConstr.of_constr`,
`close_proof`'s `global_vars_set`, and `sort_and_universes_of_constr` twice —
each a `Constr.fold` with no memo, i.e. linear in the number of *occurrences*.
So the lever on `Qed` is term size, and the question is never "what is the kernel
converting?" but "how big is the tree?".

Terms here are hundreds of times bigger as trees than as DAGs, and **this cannot
be fixed by sharing in the kernel — do not repeat that experiment.** A patched
Rocq with a physical-identity memo on `of_constr` and unconditional `Typeops`
memoization found almost no memo hits across three big proofs; RSS corroborates
(the tree really is materialised). The only asymptotic fix is for the proof term
to NAME the environment rather than spell it, which `pm_reduce` (a `cbv` over
the `pm_*` constants) zeta-reduces straight back open — the proofmode is
*designed* to keep the environment in normal form so `envs_lookup` computes.
That is an Iris redesign, not a tactic swap.

## Build shape

The build is **both** critical-path bound and core-saturated in the middle: the
path is a long shared prefix plus ONE whole-function proof — whichever is
slowest that day — and the wall above the path is core starvation. Reconstruct
the path from `coqdep` × per-file TIMED `real` (or from `.vo` mtimes: a file's
start ≈ mtime − its `real`), never from per-file time sums, which mislead because
big files run in parallel. `tools/proof_profile.py` does all of it in one pass
and runs in CI on every checkin.

- **THE PATH CAN REBALANCE ONTO A SECOND ROUTE, SO PRICE THE RUNNER-UP BEFORE
  YOU INVEST.** Cutting `IcacheInv -> WpSconfMem` (see `MemClaim.v`) took the
  path off the WP engine and left the tree with TWO routes within a few
  seconds of each other: engine -> `ProofCreate` -> the Link chain, and
  `TsoCtx` -> `VirtioProto` -> the fs cone.  Taking 15 s out of `VirtioProto`
  after that moved the wall by **one second**, because its route simply
  dropped below the other one.  The static model (coqdep x per-file wall,
  longest weighted path) predicts this in seconds and it agreed with the
  measurement to within 5 s on three separate cuts — run it on the runner-up
  route before spending a day on the leader.
### SPLITTING A WHOLE-FUNCTION PROOF ACROSS FILES: the recipe, and the one trap

`ProofCreate` (146 s) and `ProofSysUnlink` (139 s) were each ONE file with
one lemma per basic block, both on the critical path.  Both are now seven
files whose blocks compile in parallel — 146 → 79 s and 139 → 70 s on their
routes, and both are now OFF the path.  The recipe, in the order the checks
have to happen:

1. **Are the blocks independent?** They are if each seam is the NEXT block's
   PREMISE LIST rather than a call — that is the shape a whole-function proof
   already has, and the tell is that the capstone is a chain of `iApply`s
   with no glue.  Confirm it by listing cross-references with comments
   BLANKED: in both files nearly every apparent cross-reference was prose.
2. **Which blocks name a functor argument?** In both files no non-block
   helper named one, so the shared vocabulary is a plain functor-free file
   and each block is its own small functor over only what it names.  That is
   what makes the split cheap; a shared FUNCTOR applied per block would put
   its instances at the mercy of convertibility.
3. **Does anything shared appear in a STATEMENT?**  `ProofSysUnlink`'s blocks
   all name `Tails.…`, which would have forced a functor — but only inside
   proofs, never in a statement, so each file makes its own `Tails` and
   nothing has to match across the boundary.  Check this before writing a
   Module Type you do not need.
4. Expect ΣCPU to RISE (ProofCreate: 146 → 185 s): that is the import
   prelude paid once per new file, and it is the trade the section above
   describes.  Section-local `Notation`s do not survive `End Section`, so
   each file repeats them.

**THE TRAP, which cost three failed attempts and is invisible in the
source.**  A definition inside the section that mentions the AMBIENT `CID`
(here `wp_next (CID0 := CID)` in four parked bodies) is fine while everything
lives in one file: `CID` is the section variable and there is nothing to
resolve.  Split, and the discharged `CID` becomes an INSTANCE-IMPLICIT
argument — and every use site of those bodies sits under a
`fun CIDa : CpuId => …`, so instance search picks the **λ-bound hart**
instead of the section's.  The symptom is

```
iSpecialize: cannot instantiate (wp_next … -∗ WP Loop) with (wp_next …)
```

at a spec pattern that has not changed, which reads like an off-by-one in
the premise walk and is not one.  **It is invisible without
`Set Printing Implicit`** — the premise and the hypothesis print
identically; with implicits on, one is `@wp_next Σ GEN CID25 …` and the
other `@wp_next Σ GEN CID …`.  The fix is to say it: `cr_alloc_body
(CID := CID) …` at each body site, and the same at each cross-module
application of a block lemma (`cr_fail_mkdir_half (CID := CID)`, and the
seal's four), where the ambient `CIDX3` is likewise in scope when the
lemma's own implicit is resolved.  `ProofSysUnlink` needed none of this,
because its section `Context` binds no `CID` at all and every callee
application already writes `(CID := …)` explicitly — so **check the section
Context for an ambient hart before starting.**

- **A `Require` between two `Proof<F>.v` files is pure critical path.** A
  whole-function proof requiring a sibling whole-function proof is nearly always
  reaching for a shared *block*, not the sibling's capstone — and a shared block
  belongs in a third file both require. A Rocq functor cannot span two files, so
  whatever they share has to become its own functor, applied twice. **Do not
  expect the split to pay in ΣCPU**; it pays in the chain, and it costs an
  import prelude per new file. Judge it on the profiler's "Longest dependency
  chain" table (any `Proof*` immediately following another `Proof*`), never on
  the per-file list.
- **Do not let the build serialize along a proof's phase structure.** A function
  proved in phases turns into a strictly serial require chain. Measure the
  coupling: usually the heavy phase proofs sit ENTIRELY before the functor and
  need nothing from their predecessor but shared vocabulary, while the actual
  seam module is trivial. Hoist the vocabulary into one functor-free file
  and split each phase into heavy-part + seam. Finding the cut is mechanical:
  `.glob`'s `R` lines give every reference with its defining library; filter to
  the byte range before the functor.
- **Where ΣCPU goes tree-wide, by leading tactic:** `iApply` ~16 %, `Qed` ~15 %,
  `Require`/`From` ~17 %, `iIntros` ~8 %, `iDestruct` ~4 %. The import line is
  the one to internalise — pure module loading, a floor rather than a bug, and
  `iris.proofmode`+algebra+base_logic+program_logic is the bulk of it (`.vo`
  loading is lazy, so do not go hunting in the 22.7 MB model file).
- **Negative results — do not redo these.** `_CoqProject` order does not matter
  (three orders measured within noise; level-order visibly changed the schedule
  and make refilled the freed slots either way). Oversubscribing `-j` does not
  help (it fixes the queueing gap and costs exactly what it buys). `Proof using`
  tree-wide is a fraction of a percent of the build, and the non-minimal forms
  (`Type*`/`All`) change which section variables a lemma is generalized over,
  i.e. its ARGUMENT LIST, which breaks positional application.
  `vm_cast_no_check` in the generated decode band only MOVES cost from `Qed` to
  elaboration.
- **The generated decode band's cost is the PROOFMODE, not the `vm_compute`s** —
  the great majority is generic Iris plumbing re-paid by each of ~8,500
  `mk_rvc`/`mk_base` calls, against a small share for the side conditions
  everyone suspects first. The fix was to state the whole `instr` introduction
  as ONE lemma (`KernelText.instr_intro_rvc`/`_base`) so the proofmode work
  happens once, in those two proofs; `mk_rvc`/`mk_base` keep their signatures.
  Worth a large multiple on the band, which is what an `XV6_REV` bump re-pays.

## `Print Assumptions` is a whole-tree walk, and it is not on the build path

The assumption audit lives in **`iris/SystemAssumptions.v`**, run by `make
audit` / `make audit-only` and by CI after every build (output in the run's
step summary). It is deliberately **not** a row in `iris/_CoqProject` — the
commented-out row there is what tells `tools/proof_coverage.py --check` the
omission is on purpose. It used to be a line at the bottom of
`SystemAdequacy.v`, where it was almost the entire cost of that file — and
`SystemAdequacy.v` is the strictly serial tail of the build (`BootChain →
BootShared → SystemAdequacy`, all 1×), so it was a large fraction of a clean
build's wall clock, re-paid whenever anything in the 1000-file cone changed. CI
still pays it; a developer's `make proofs` no longer does.

**Why it costs that.** `Print Assumptions` forces the opaque body of every
constant in the transitive cone and walks it. Forcing is not a read:
`Library.access_opaque_table` re-runs, on **every** access,
`Discharge.cook_opaque_proofterm` — the section discharge, a full term rebuild,
once per enclosing `Section` that had a `Context` — and `Mod_subst.subst_mps_list`,
another full rebuild for anything reached through an applied functor. Then
`Assumptions.traverse` walks the result, running `Inductive.expand_case_specif`
at every `Case` node. Each proof term in the cone is therefore rebuilt 2–3× and
walked once. Both of this tree's universal idioms are on that path: 778 of the
1265 `iris/*.v` use `Section`, and the whole `SpecF`/`LinkF` design routes
lemmas through sealed functor applications. A controlled A/B over 400 lemmas
with byte-identical proof terms puts `Section` + `Context` packaging at roughly
2.7× plain top-level lemmas, and an applied sealed functor at roughly 1.5×.

So the command is ~linear in total proof-term bytes in the cone with a 2–3×
constant on top. It is therefore also a **proxy metric for whole-tree
proof-term size**: a jump in the audit's time is a jump in what every rule in
this file is fighting. Treat it as a tripwire.

- **Negative results — do not redo these.** It is not disk I/O: `Require
  Import SystemAdequacy` — loading the entire cone — is fast, and a *second*
  identical `Print Assumptions` in the same process costs full price again.
  Nothing is cached between calls, so **batching audits in one file does not
  amortize** — adding an `xv6_fs_adequacy_xv6Σ` audit beside the existing one
  would roughly double the bill, not ride along. Nor does auditing at lower
  altitude decompose the cost: `Print Assumptions
  BootChain.boot_hart_primary` alone is nearly the whole thing, against a
  fraction for `BootShared.boot_shared_alloc` or
  `RiscvAdequacy.riscv_power_adequacy`. `Set Printing Depth` and the printing
  of the seven-odd axioms are free.
- **`-noglob` on the audit compile is load-bearing**, not tidiness. The nightly
  dead-import sweep shortlists candidates from whatever `.glob` files it finds
  in `iris/`, and `SystemAssumptions.v`'s single `Require` is the one thing it
  must not lose; with no `.glob` the file is reported UNANALYSED and left alone.

**The cone widens faster than the tree does.** Re-measured on a tree only
slightly larger by `.vo` bytes, the audit had grown several-fold. Measured
beside it, the deepest contract audits (`Forkret.wp_forkret`,
`UserretClosedD.wp_userret_closed`) cost nearly as much as the whole system
audit, while shallower ones (`Kexec.wp_kexec_sconf`, `Fsinit.wp_fsinit_sconf`)
cost a fraction.

**So "auditing forkret takes forever" is not about forkret.** `ProofForkret`'s
own proof terms are a rounding error of its audit; the rest is the closed trap
loop it concludes in, and every contract that ends in `UserretClosedD` pays
exactly that. Cutting `ProofForkret.v`'s compile time by a third moved its
audit by nothing, with a byte-identical axiom list. Do not go looking for the
cost in the file you are auditing; audit its deepest callee first and see
whether the difference is worth anything.

**Where the time actually goes** (`perf record` over one such run, flat self
time; the tree's opam switch carries OCaml symbols, so this is readable):

| cluster | share |
|---|---|
| `Cooking.*` — the SECTION DISCHARGE (`substrec`, `share`, and the `Int.Map` memo behind it, plus the `Constr.map_with_binders` / `CArray.map` it drives) | **~40 %** |
| `Mod_subst.map_kn` + the `Names` hashing/compare it drives — the FUNCTOR substitution | ~12 % |
| `Assumptions.traverse` / `traverse_inductive` / `fold_with_full_binders` — the walk the command is nominally doing | ~8 % |
| OCaml GC (`caml_oldify_one`, `do_some_marking`) | ~4 % |

The command spends five times as long re-COOKING terms out of their sections as
it does walking them, which is the mechanism behind the section-packaging figure
above. The lever, if anyone wants it, is per-lemma `` `{!riscvGS Σ, …} ``
binders instead of `Section` + `Context` in the hot cone — `ProofForkret.v`
already writes its lemmas that way, which is part of why it contributes so
little. That is a ~778-file change, so it is a campaign, not a fix.

- **GC tuning does nothing — do not redo it.** `OCAMLRUNPARAM=s=8M,o=200`,
  `s=64M,o=400` and `s=256M,o=1000` all came back within noise of the baseline;
  the largest doubles peak RSS for nothing. Consistent with the perf profile: GC
  is a few percent of the run.

## Smaller traps

- **`lia` cannot do a nested-division chain** even mword-free and iris-free
  (`E mod 32 = 0 → E/32 mod 4 = 0 → … → E = 0` comes back "cannot find witness").
  It has no theory of iterated division; stage it with `Z_div_exact_2` +
  `Z.div_div`.
- **A `!` in `rewrite` always pays one FULL failing pass, and it is not free
  when the lemma is expensive to MATCH.** `rewrite !H` fires until failure, so
  it runs one more match attempt than the goal has occurrences — and that
  attempt is a complete setoid traversal of the goal, instance search included.
  In `ProcPtOwn.uva_dom_delete`, `rewrite elem_of_difference !elem_of_uva_dom`
  over a goal with exactly TWO `va ∈ uva_dom _` occurrences was the slowest
  sentence in a 5,000-line file by a wide margin; naming the two rewrites
  (`… elem_of_uva_dom elem_of_uva_dom`) cut it by an order of magnitude with an
  identical proof term. What makes the failing pass expensive is the LHS:
  `uva_dom` is a `list_to_set (mjoin (… <$> map_to_list _))`, so every candidate
  subterm drags the `elem_of` instance chain behind it. The rule is NOT "avoid
  `!`" — 261 files use it, nearly all harmlessly. It is that a `!` over a
  set-membership lemma with a COMPUTED carrier, in a goal big enough to
  traverse, should be spelled out at the occurrence count the goal actually has.
  (Same family as the two bullets below: what costs is the tactic that fails.)
  **`rewrite n!L` is the spelling that keeps the `!` reading without the
  failing pass** — it performs exactly `n` rewrites and never attempts an
  `n+1`th. Second instance (`FsCfgBoot.v`'s coverage-remainder `set_eq`):
  `rewrite !elem_of_difference !elem_of_union` over a goal with six differences
  and four unions, whose carriers are five *computed* sets (`log_region_set`,
  `ireg_blk_set`, `fs_live_blocks`, `fs_bitmap_spent`), paid two whole-goal
  traversals for nothing; `rewrite 6!elem_of_difference 4!elem_of_union` more
  than halved the file. Counting is mechanical: differences on both sides of the
  `↔`, unions in the set the right-hand side names. Third instance
  (`VirtioProto.vinit_dma_dom`): `rewrite !dom_union_L !range_map_dom
  ring_bytes_dom_eq` spent nearly all of its time in the one failing
  `dom_union_L` pass — deciding that `range_map (vc_used c) 4096 _` is not a `∪`
  unfolds `range_map`'s 4096-step `foldr`. `rewrite 2!dom_union_L
  2!range_map_dom …` is cheap. The carrier does not have to be a set for this to
  bite: a `gmap`-valued definition over a literal size is just as expensive to
  refute, and here the *successful* rewrites cost as much again for the same
  reason.
- **`rewrite` ABSTRACTS, `exact` only UNIFIES — and a `nat` NUMERAL makes the
  gap enormous.** `rewrite H` must locate the occurrence, abstract it and build
  a motive that conversion then carries; `exact`/`apply` of the same equation
  only unifies two terms. Where the rewritten subterm holds a `nat` numeral the
  difference explodes, because `nat` numerals are UNARY: `4096%nat` is a
  4096-constructor term, so `umem_write _ _ 4096 _` drags all 4096 through
  every conversion the motive forces. On one goal (`ProofUvmcopy.v:1695`) all
  three of `rewrite <- (umem_write_app … 4096 …)`, the same with the run length
  a VARIABLE, and `transitivity <middle>` + `apply`/`exact` close the SAME goal
  with the same proof term — and they span two orders of magnitude, with the
  literal responsible for a modest factor and the motive for the rest. The shape
  to reach for is `transitivity <the middle term>` and then `apply`/`exact` on
  each side — it names the intermediate explicitly, which reads better than a
  backwards rewrite anyway. This is the PURE-GOAL cousin of "Directed
  entailments, not `⊣⊢` rewrites" above; that section is the same trade inside a
  proofmode goal, where RULE ONE supplies the blow-up instead.
  **The cheapest instance of it is `rewrite L. reflexivity.` where `L` already
  closes the goal**: `ProofKexecPinned.v:651`'s `rewrite (fv_of_file_byte …).
  reflexivity.` builds a motive over the whole `file_byte`/`fv_of` term only to
  throw it away one line later — `exact (fv_of_file_byte …)` is the same proof
  term with no motive, and took the statement out of the profile. Grep for a
  `rewrite <lemma>.` immediately followed by `reflexivity.`
- **In a `first [ … ]` alternation, put the CHEAP-FAILING branch first.** The
  cost of a tactic that FAILS grows with the proof term, so an alternation
  leading with an expensive-to-fail branch pays that cost at every use — in one
  function it was the dominant cost, purely in the failures of the first branch,
  fixed by reordering and nothing else. `exact`/`assumption` fail cheaply on a
  type mismatch; `rewrite … in H` and `congruence` do not. Second measurement
  (`HartLift2.wp_hsil2_node`): one `all: first [RegWrite | RegRead | announce]`
  over the monad node type's constructors, where the RegWrite branch fails only
  after two `case_decide`s, two `injection`s, a `set_solver` and an `iMod` — so
  every announce-class and RegRead goal paid that whole prefix. Reordered
  announce < RegRead < RegWrite, nothing else changed, and both the site and the
  file collapsed to near nothing. Each branch still ends by closing its own
  goal, which is what makes reordering sound — `first` commits only to a branch
  that finishes.
- **A branch order is only worth changing where the branches FAIL, and a
  nineteen-wide `first [apply …]` over a family of lookup lemmas is NOT that
  case** (negative result). `HartMFrame.mm_rs_lk` / `WpInstrConfig.mc_rs_lk`
  cost several seconds at their `all:` sites, which looks exactly like the trap
  above; replacing the alternation with a `lazymatch` that dispatches on the
  register in the goal changed nothing. The towers are already `Global Opaque`,
  so the failing `apply`s are cheap and the cost is in the ~19 SUCCEEDING ones.
  Do not redo this; if these sites ever matter, the lever is the number of
  goals, not the dispatch.
- **Order `repeat (first [ … ])` loops** with cheap structural rewrites first and
  broad whole-goal normalisation LAST — the loop re-tries its first branch after
  every success.
- **Give `iFrame`'s names in the GOAL's conjunct order** — a wrong order is worse
  than none.  **And do not read the order off the frame LIST when you convert
  one to a chain: `iFrame` matches by TYPE, so a list can be in a plausible
  order and still not say which name is which row.** Converting
  `VirtioProto`'s rebuilds, `Hpos`/`Hposm` and `Hord`/`Hordm` both turned out
  to be the opposite way round from the frame lists' order, and the chain
  failed at `iExact` with the hypothesis's real type printed beside it. The
  authority is the DESTRUCTURING PATTERN consumers use on the same
  definition (`… & Hrel & Hfl & Hflr & Hpos & %Hpmh & #Hposm & …`), which is
  the definition's own order by construction — read the mapping off that.
- **`Local Strategy 1000 [pa_stk]`-style deprioritising** keeps failed
  comparisons first-order while `unfold` still works where the arithmetic is
  wanted. `Local Opaque` does not — it blocks `unfold` too.
- **CSR nested-if dispatch** (~90 clauses): use the batched peel lemmas
  (`skip_csr_false_clauses` / `drive_csr`, on `exec_if_false_g16`/`_g4`) from the
  start. Peeling one clause per `erewrite` is O(tail) retyping per clause.
- **A family of "field X is untouched" laws over one bit-level constructor should
  be N corollaries of ONE testbit reading**, not N testbit chases: the chase cost
  is per-law and superlinear in the term it walks, the reading is paid once.
- **A missing bullet at the END of a `split_and!` block is invisible to every
  obvious probe** — `Show 1.` says "No such goal", `all: match goal` prints
  nothing, `all: idtac "X"` prints once. **`Unshelve. Show Existentials.`** names
  it in one run. Reach for that whenever "incomplete proof" is reported and the
  goal list looks empty.
- **`u_pte_addr` (CommonWalk) and `pte_addr_at` (Pt4kWalk) are the same term but
  only CONVERTIBLE**, so a `rewrite` reports "no subterm matching" on a term you
  can see. Restate the fact at the `u_*` spelling in one line closed by `exact`,
  then rewrite with the restatement.
- **ssreflect `set` binds the GOAL's instance**, whose hart-indexed subterms
  carry the hart the branch just peeled — not the ambient one you typed. A later
  `rewrite` then fails with "does not match any subterm" while the printed goal
  shows the very term, character-identical. State register facts CID-generically
  up front (`assert (∀ CID', rget (CID := CID') M2 r = v)`) and rewrite with that.

## A HINT-DATABASE DISPATCH IS A DEPTH PROBLEM, NOT A BREADTH ONE

`UserTotalU`'s two dispatch tables discharge ~98 per-family `goodmb`
obligations through one tactic that ends in `eauto … with u_gm`, where
`u_gm` holds the ~80 twins of P5's catalogue plus the gpr-index side
conditions.  Breadth is cheap — a twin whose head instruction does not match
fails its `apply` immediately — but DEPTH is not: at `eauto 6` the file took
half an hour; at `eauto 3` it is trivial.  The obligation is only ever "apply
the family's twin, then its side conditions, then at most one step inside one",
so 3 is the real bound and everything above it is backtracking through side
conditions that were already going to fail.

Two companion rules from the same measurement:

* **Put the SYMBOLIC-INDEX side conditions at `Hint Extern 0`.**  A
  `Hint Extern 2 (Du_w _ = true) => vm_compute; reflexivity` is right for a
  named cell and a DISASTER at `Du_w (R_bitvector_64 (gpr_of_Z (uint i)))`,
  where `bool_decide (r ∈ u_rw_list)` is stuck on a symbolic index and
  `vm_compute` grinds.  Give the gpr shape its own cost-0 extern so the
  computing one is never reached.
* **A premise the database cannot possibly discharge is what actually
  hangs.**  Before the gate certificates existed (§11 of the user-tier
  plan), `goodmb_execute_JAL_total`'s
  `goodmb … (currentlyEnabled Ext_Zca) s ∅ = true` premise had no producer,
  and `eauto` did not fail on it — it searched for minutes. If a hint-driven
  discharge is mysteriously slow, look first for an obligation nothing in
  the database proves.
