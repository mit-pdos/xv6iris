# Proof performance & build optimization

Rules for writing proofs that compile in reasonable time, and the diagnostics
that find the cost when they do not. Apply the rules proactively; reach for the
diagnostics before believing any theory about why a file is slow.

## Diagnosis, in order

**RULE ZERO — run `coqc -time` first.** It prints a line per command as it goes,
so the last line in the log is the stalling sentence. If the slow line is a
*tactic*, no amount of proof-term work will help. Map `Chars A-B` to a line with
`head -c B <f>.v | wc -l`.

- **Isolate before measuring.** Inside a `-j32` build a file reads 3–4× its real
  cost and the per-sentence *ranking* reorders (a 5 GB-heap process pays GC on
  every allocating tactic). Judge a change by an isolated A/B, one `coqc` each,
  min of two interleaved runs — never by diffing per-file times between two
  parallel builds. Run-to-run variance on a 30 s file is ±10 s in **both**
  directions, so untouched files routinely "improve" by 10 s.
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
- **`.v.timing` roll-ups beat reading the proof.** After a build that felt slow,
  list every sentence ≥ 5 s across the tree and cross off the honest `Qed`s;
  what remains is the bug list. These sentences are exactly the ones a reader
  skips.
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
environment. Measured: 44 *trivial* `iPoseProof`s cost ~54,000 tree nodes EACH
while the DAG grew by ~50 per step. Two consequences: **`Qed` time is the size
of the context times the number of steps it survives**, and splitting a proof
into `Qed`-sealed chunks buys nothing by itself — each chunk carries its own
context.

So a whole-function proof can be the slowest file in the tree **with no hot
sentence at all** — a flat tail at 3–6× per sentence what a comparable proof
pays. That ratio *is* the diagnosis.

### Fold block continuations into named definitions

This tree hands control between basic blocks with nested `iAssert (□ wp_next …
(fun CIDs => <40–80 lines of ∀/wands>))`. Ten live at once is ~390 lines of
statement against ~40 lines of actual resources, and every step pays for all of
it. **Before hunting a hot statement, count the lines of `iAssert` statement
live at the deepest point; if they outweigh the resources, the file's cost is
its own continuations.** Folding is a drop-in — the proof script does not change
— and is worth 12–32 % on the proofs that have the shape:

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
   site, which is itself context-proportional (measured +48 % for a term only
   5 % smaller). `Typeclasses Opaque` is right for a post nobody applies inside
   the proof, wrong for a continuation applied everywhere.
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
`wp_next` wrapper either and three folded clean for −17 % (its leaves take the
zero process pointer literally, so nothing needs `?p` through the fold).

### Seal a whole-function proof's continuation

Do not spell the postcondition inline in the spec body: one `Definition` in the
spec file plus `Global Typeclasses Opaque`, with the proof unfolding it exactly
once at the return. A 20-wand continuation over three 4096-element big-ops was
**more than half** of `ProofVirtioDiskInit`. **But the seal is worth nothing if
the continuation is already a named `Definition`** — naming is the fix; the seal
is only for a spec body that spells it inline.

### Pose late, clear early

A persistent hypothesis is not free — it is re-embedded in the term of every
step that follows it. Pose an `instr` fact on the line above the `iApply` that
eats it, not in a block of 40 at the top. Write new proofs this way; retrofitting
only works on **straight-line** stretches (in a Löb/induction body a textually
single use runs every iteration, so an `iClear` after it kills the back edge, and
if the uses are spread over two arms, moving the pose into the first starves the
second).

### Hypothesis names are 10–20 % of a whole-function proof term

Iris's `ident` is a Stdlib `string` — a cons-list of `Ascii` over eight
booleans, ~10 term nodes per character — and the environment is embedded once
per step. Measured slope: **~730 nodes per character of hypothesis name**. The
only lever here is shorter names, a bad trade for readability except in the two
or three longest monoliths. **Sealing the name does not help and cannot**:
opacity is a reduction control, not a representation change, and a name behind a
constant breaks `envs_lookup`, which must COMPARE names under `pm_eval`'s
delta whitelist. What would fix it is a primitive-string `ident` upstream.

## Never let a general-purpose closer meet a large context

This is the single most productive rule in this file — instances of it have been
worth 20× on individual files.

- **`set_solver` IS FIXED — the tree overrides it, and the old prohibition no
  longer applies.** `iris/FastSetSolver.v` replaces stdpp's `set_solver` tree-wide
  (hooked in from `RiscvModelBytes.v`, a transitive dependency of 1071 of the
  1090 files; `BitmapEnc.v` and `CrashProto.v` import it directly). Read that
  file's header for the measurements. The short version:
  - stdpp's `set_solver` spends **~97 % of its time in three whole-context
    sweeps that have nothing to do with sets** — `setoid_subst`, `set_unfold`'s
    `csimpl in *`, and `naive_solver`'s `unfold … in *` / `simplify_eq/=`. The
    step that actually reasons about sets is 0.5 s of a 19.9 s call.
  - The override clears the hypotheses that cannot reach the goal (the
    connected component of the goal in the "hypothesis mentions variable"
    graph, plus every hypothesis mentioning a set operation) and then runs
    stdpp's own pipeline on what is left. Cost becomes **linear** in the
    context instead of quadratic-to-cubic: the 80-hypothesis benchmark goes
    19.9 s → 0.10 s, and 640 hypotheses still cost 0.10 s where upstream needs
    105 s at 160.
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
  - **Measured on a REAL site, not a synthetic:** `ProofSysDup.v:836`'s
    workaround (`ltac:(apply not_elem_of_empty)`, written because `set_solver`
    there cost 106 s) put back to `ltac:(set_solver)` now costs **0.73 s**
    (0.49 s filtering + 0.23 s solving) against **105.2 s** for the same
    sentence with upstream — **144×**. That one site took two further fixes,
    both worth knowing:
    - **A goal reached through `ltac:(…)` inside a term is an EVAR**, and an
      evar carries an instance listing every variable in scope. Walking into it
      made the goal "mention" the whole context, so the filter kept everything.
      `vars_of` now skips evar instances.
    - **`Std.clear` is ALL-OR-NOTHING.** One name Coq refuses — something
      outside the analysis still depends on it — fails the whole call, and then
      NOTHING is cleared and the filter silently degrades to upstream with no
      error anywhere. This is what kept that site at 105 s even once the
      analysis was running correctly (0.05 s to decide, then a 105 s solve over
      the context it had failed to clear). `clear_greedily` now bisects on
      failure and keeps the halves that go.
    - The general lesson: **a filter that fails open is invisible.** Both bugs
      presented as "the tactic is just as slow as before", never as an error.
      If the override ever looks like it is doing nothing, check that
      `set_shrink` is in scope and that it is actually clearing, before
      believing anything about the goal.
  - **A SINGLE MEMBERSHIP IN A UNION OF TWO `gset register` VARIABLES STILL
    COSTS 24 s, override or not.** `assert ((tlb : register) ∈ Drw ∪ Dro) by
    set_solver` inside a `swp` translation proof measures **24 s per call**
    (`coqc -time`) — and adding `Require Import FastSetSolver` to the file
    changes nothing, so this is not a "the override is not in scope" case.
    Two of them made `Pt2WalkPt.v` a 62 s file; `by (apply elem_of_union_l;
    exact HWtlb)` makes it 13 s. The rule the durable notes give for
    tower-carrying proofs (name the union lemma) is therefore still the rule
    whenever the sets are VARIABLES rather than literals — which is exactly
    the `Drw`/`Dro` frame idiom. `HartSKpt.swp_translate_kpt` still carries
    the `set_solver` form.
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
- **`naive_solver` on its own is still forbidden inside a whole-function
  proof** — it is the half of the old `set_solver` that the override does not
  reach when you call it directly. It ends in a search over *every* hypothesis
  in scope, and a capstone's context is ~200 register-chain facts over large
  mword terms.
- **Never `simplify_eq` inside a whole-function proof's Iris context** — like
  `congruence`, it scans every hypothesis in scope looking for equalities to
  substitute/discriminate, so cost tracks context size, not the one hypothesis
  you meant to consume. Closing `(e', b') = (Ep, uint bno) -> …` this way cost
  12–17 s **per call**, four calls in one file. Fix: `injection H as pat…`
  names exactly the hypothesis and produces one pattern per NON-trivial
  component — a component syntactically equal on both sides (`Ep = Ep`) is
  dropped automatically, so a `(Ep, b') = (Ep, uint bno)` equality takes one
  pattern (`as ->`) where a `(e', b') = (Ep, uint bno)` one — both sides
  genuinely distinct — takes two (`as -> ->`); guess wrong and the error is
  *"Unexpected introduction pattern (at most N was expected)"*, which names
  the fix. Four-call fix took one file from 95 s to 35 s.
- **Never `congruence` anywhere but LAST** in a peel's side-goal alternation
  (4–80 s per call), and never `done` / bare `cbn` / bare `reflexivity` as the
  last tactic of a step. The giveaway is that the tactic is *trivially*
  discharging a goal you can read at a glance, so nobody suspects it: `iPureIntro.
  done.` on `(0%nat = 0%nat ∧ true = true)` was 16.1 s where `exact (conj eq_refl
  eq_refl)` is free. When the same one-liner is cheap in one place and lethal in
  another, the difference is whether its subject is CONCRETE.
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

## Framing: name the context side, construct the goal side

- **Never bare `iFrame` in a large context** — it searches the whole spatial
  context for each conjunct of the goal, so cost is (context × conjuncts).
  Rebuilding a 9-conjunct resource with a bare `iFrame` did not terminate; the
  same nine by name is instant.
- **A NAMED `iFrame` still pays a GOAL-side search.** When the goal's conjuncts
  include a big payload (an escrow arm hiding a 268-element big-op), a named
  `iFrame` is 90–170 s. **Give every multi-conjunct resource abstraction a
  CONSTRUCTOR lemma when you define it**, for the same reason it gets an
  accessor: the constructor assembles the arm structurally where the context is
  six hypotheses wide, and the caller writes one `iApply (ic_mk_parked … with
  "Hd Hn Hv Hp Hm Hg")`. Otherwise every user pays a search.
- Where no constructor exists, close a seam by naming every conjunct
  (`iSplitL "H"; [iExact "H" |]` chains), never with `iFrame`.
- **A SHAPE MISMATCH turns every match attempt into a CONVERSION, and that is
  the expensive kind.** `ProcInv.tf_words` is a `big_sepL`, so its conjuncts
  carry offsets `8 * Z.of_nat i` while every consumer names them as LITERALS
  (`tf_pa tfp 40`): convertible, not syntactically equal. A bare `iFrame`
  across that pays a conversion on each of its ~36×36 attempts — **19.1 s and
  17.6 s** at the two sites in `ProofUservec.v`, over half the file. Fix:
  factor the shape change into ONE `⊣⊢` lemma (`tf_words36`) proved by
  `rewrite /tf_words /= bi.sep_emp; reflexivity`, so the conversion happens
  once (1.7 s) and both directions then frame syntactically. File went
  **66.6 s → 31.0 s** of statement time. The tell in the profile is a
  one-token statement (`iFrame.`) costing tens of seconds.
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

- **Give every big-resource abstraction with a `Persistent`/`Timeless` instance a
  `Typeclasses Opaque` right next to it.** Otherwise each `#`-intro re-derives
  the instance by unfolding and descending into the resource: one `iIntros
  "#Hdlock"` on `is_lock … (disk_res …)` was **5.1 s**, 0.14 s sealed, and the
  one line was worth 14–45 s CPU each across six other files. Diagnose by
  splitting the `iIntros` one name per sentence. Sealing the *resource* instead
  changes nothing — the cost is the persistence search, not the hypothesis. The
  seal costs a `rewrite /X` inside the projection lemmas, which is the point:
  nothing else can then `iDestruct` the abstraction apart. Measure before
  sealing; cost tracks the size of the resource, not the number of sites.
- **Prove a big `Timeless`/`Persistent` instance STRUCTURALLY, never with one
  `apply _`** — one `apply _` over an `∃/∗/∨` tower backtracks across the whole
  space (49 s for a fact whose every leaf instance already exists). Peel one
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

  The `first [apply bi.exist_timeless; … | …]` spelling is a REGRESSION (33–42 s,
  an order of magnitude worse than the monolithic `apply _`): `apply` unifies up
  to delta, so it peels straight *through* a named abstraction that already has
  its own instance and then backtracks over everything underneath.
  **Descend through the connectives, never through a name.**
- **Pay deeply nested polymorphic structure once behind a fully typed
  wrapper.** `IcacheRef` applied `prod_local_update'` six levels down the same
  named seven-component CMRA at twelve callers; elaboration rediscovered the
  outer product at every site, and the first application alone cost 4.5 s each
  time. A helper stated over the named constructor and all seven component
  updates pays that inference once in its proof; callers then supply identity
  or component-local updates to the fixed signature. The profile now has one
  4.5 s structural application instead of twelve. This is useful when the
  repeated cost is in the first polymorphic constructor application, not when
  the component updates themselves are slow.
- **Mark big concrete literals `Global Typeclasses Opaque`** (`kernel_bytes`,
  `kernel_data`, `kernel_symbols`, `mem_pointsto`) or instance search unfolds a
  23K-entry gmap, ~108 s a time. Use `Typeclasses Opaque`, never `Opaque` — a
  tactic may need to `unfold`, and `vm_compute`/`reflexivity` ignore the former.

## Modalities and rewriting

- **Strip only the GOAL's later with `iApply bi.later_intro`**; reach for `iNext`
  only at a genuine Löb back edge. `iNext` is `iModIntro` at `▷`, so it runs
  `MaybeIntoLaterN` over every hypothesis in both environments: ~1.1 s per call
  in a whole-function proof against ~0.06 s for the same effect. The tell that a
  file has this backwards is an `iNext` followed by `iAssert (▷ X)%I … { iNext.
  iExact "H". }` — that block is *repairing* a `▷` the `iNext` stripped, so both
  tactics are the expensive one and the pair does no net work.
- **A modality step at a `▷` costs the CONTEXT, so pay it in a lemma.** An
  `iMod` at a `▷` inside a whole-function proof was 34 s where the `Timeless`
  search on the same bundle standalone is 0.4 s. Gotcha when writing the lemma:
  **its conclusion must be a FANCY update, not `|==>`** — `IsExcept0 (|={E1,E2}=>
  P)` holds unconditionally while `is_except_0_bupd` needs `IsExcept0 P`, so
  `iMod` fails with *"cannot eliminate modality"*, which reads like a missing
  `Timeless` instance and is not. Take the mask as a parameter.
- **Prefer the WAND form of a big-op law to a setoid rewrite.** `rewrite
  !big_sepL_sep` is setoid rewriting over `envs_entails Δ Q`, and its cost is in
  the `Proper` proofs over the PREDICATES — so hoisting it into an empty-context
  lemma changes nothing (11.76 s vs 12.7 s). `iApply (big_sepL_sep_2 with …)`
  matches by head and never enters setoid rewriting: 1.85× on the file. Do not
  sweep this — the tree's other sites are sub-second because their predicates are
  small. Check the `.v.timing` cost of a candidate first; the site count tells
  you nothing.
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
  unifier meets a concrete tower may delta-expand it. Measured: an `InstrBytes`
  with four `wp_instr` arms did **not finish in 15 minutes** transparent, and
  the same arms' setup ran in **3 s** opaque. The lookup lemmas are the only
  interface any consumer needs, so nothing is lost.

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
a shape that is easy to miss because the lemma looks tiny). Measured inside one
`wp_instr` arm: `rewrite mm_rw_split mm_rs_PC .. mm_rs_ip` — a seven-cell split
plus its seven lookup rewrites — cost **~110 s**; nothing else in the arm cost
more than a second.

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

## Register maps

- **`pose`, not `set`, for a whole-function proof's register chain.** The idiom
  keeps the goal one insert deep, so there is no deep term for `set`'s occurrence
  abstraction to collapse — but `set` pays a whole-goal pattern search per
  instruction, and the goal is `envs_entails Δ Q` with the entire context inside
  it. Cost scales with CONTEXT, not chain: 0.1 s in a small proof, 1.7 s (158 s
  of a 305 s file) in a big one. Keep `set` only where the abstraction is the
  point — a value that really does occur throughout the goal. Note `set (x := e)`
  *with parentheses* is vanilla Coq's `set`, not ssr's, so it does not fail when
  it finds no occurrence. A `set (X := e)` immediately followed by `change e
  with X` is the fully-redundant form — the `change` alone produces the same
  goal, so the pair is `pose` + `change` (measured in ProofPipewrite: 66 such
  `set`s cost 4.4 s where the sibling's 83 `pose`s cost 0.29 s, ~20× per call).
- **`Local Strategy opaque [rget tp_pin rf_upd]` in a whole-function proof whose
  leaves state their premises over `rget`.** Every such `iApply` otherwise makes
  the unifier walk `rget → tp_pin → rf_upd` down the whole update chain, and the
  `Qed` re-walks it (ProofPipewrite: 8 hot `iApply`s ~14 s → ~1.5 s, final `Qed`
  18.9 s → 15.5 s). The trap: any premise spelled `M !!! Regidx r` where the
  leaf's statement says `rget M r` was bridging by delta and now REGRESSES —
  restate it in the `rget` spelling via `rget_ne` (HartTp.v) before the `iApply`
  and the site goes syntactic. Audit: `-time` before and after; the regressing
  sites are the ones that got slower.
  **Sealing can regress a DIFFERENT, distant site.** `Strategy opaque` deepens
  the unifier's walk at every `rget`-typed premise in the file, and an inline
  general-purpose closer (the "Inline `ltac:`" rule below) is priced by
  exactly that depth — measured, a `dl_need` bound three `dirlink`s deep
  regressed 1.36 s → 8.26 s from a `Strategy opaque` elsewhere in the same
  file with no textual connection to it. Audit `-time` across the WHOLE file
  after sealing, not just the sites the seal touches directly; fix a
  regressed site with the same inline-`ltac:` hoist as any other (`assert (H
  : …) by (clear -H..; lia)`), whose keep-list must include every hypothesis
  the final `lia` draws on — not just the ones the tactic script names
  textually. Grep sibling call sites for the same derived bound, or dump the
  goal and context at the failing site (above) if none exists.
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
    discriminating position in two equal records: ~4–8 s per call.
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
type is fixed, so there is no re-elaboration. Measured at 12–29 s *per call site*
for the `kernel_data_string` / `kernel_data_window` byte-lookup premises, and
non-terminating for an `iApply` whose map argument is a ∀-bound `Mr` from a loop
invariant. If several such args exist, use the **unshelve hoist**: replace the
inline `ltac:`s with bare `_`, prefix `unshelve iApply`, and discharge the evar
subgoals as standalone `{ … }` goals.

**An inline `ltac:` whose tactic is a GENERAL-PURPOSE CLOSER is priced by the
DEPTH of its call site, not by its goal** — so the identical sentence
terminates in one arm of a function and does not terminate in another. Three
`lia`s in `ProofCreate.cr_mkdir_half` (the post-`dirlink` size read-back, and
two `ltac:(lia)`s in `DirLinks.dir_link_at_dirlink`'s `2 <= tot` slot) ran
**>10 min at 22 GB** where `cr_alloc_half` runs the same `cr_wi_size_max` chain
inline and is fine; the difference is only that the mkdir arm sits three
`dirlink`s deeper, so `lia`'s atom scan meets three calls' worth of accumulated
arithmetic. Each goal was one equation away from trivial. Hoisting them to
`assert (H : …). { clear -<the one equation>. lia. }` took the file to **3:13 /
5.1 GB**, faster than the baseline that did not contain the arm at all. The tell
is that the goal looks tiny; do not read a stalling `lia` as a hard arithmetic
problem, read it as a context problem, and note that `clear -H` is only
available once the goal is a NAMED assert — which is the second reason not to
splice a closer into argument position.

- Grep for `ltac:(intros` inside a `kernel_data_window` / `kernel_data_string`
  argument list — every hit is this bug.
- The related fix is often to state the byte premise over a SYMBOLIC index as its
  own pure lemma, which deletes a `destruct i` on the Iris goal entirely.
- **The 18k-entry `list_to_map` is NOT the cost** — the VM compiles `kernel_data`
  to bytecode once per process, so the first lookup is ~0.15 s and every later
  one ~2 ms. When a `vm_compute`-over-a-big-map sentence is slow, suspect the
  inline-`ltac:` position, not the map.

## Conversion and `Qed`

- **`vm_compute; reflexivity` is rechecked by the kernel's LAZY conversion at
  `Qed`** — the VM's speed does not carry over, and on model code that is a
  different order of magnitude (one such equation over the cold-boot chain
  reached >3.8 GB; fifteen inside one `Qed` reached 25 GB). Close such goals with
  `vm_cast_no_check (eq_refl <rhs>)` so the kernel rechecks with the VM too, and
  compute the result ONCE into its own `Definition` plus a single VM-cast lemma,
  after which downstream facts are shallow conversions.
- **A guard fixed by `change`/a plain cast pushes a slow non-VM conversion to
  `Qed`** (minutes). Use `replace g with v by (vm_compute; reflexivity)`. For
  CSR/extension dispatch guards use `csr_dispatch_eq` (ExecCommon.v). **NEVER
  `cbv -[…]`** (negative delta) to collapse a Sail dispatch guard — it unfolds a
  definition with a huge normal form and OOMs the box (125 GB).
- **Never `vm_compute` a goal containing a symbolic `mword` variable or a
  concrete built-up `mstate`** — it tries to normalize 64-bit modular arithmetic
  symbolically and does not terminate. Compute only the CLOSED offset, or prove
  the pure fact against an abstract state and `apply` it.
- **Never let an `exact`/`reflexivity` cross an update layer.** Peel every layer
  down to the map the named fact is actually about, or the kernel converts the
  whole transparent `rf_upd`/`bool_decide`/`mword_of_int` tower — 401 s for one
  `exact`, and the tell is that the sentence right below it, four explicit layers
  down, is free.
- **A `reflexivity`/`exact` that folds a `gset` back into its name normalises the
  underlying `list_to_set`.** Unfold the two names first so the match is
  syntactic.
- **Sealing a definition tower halfway buys nothing — seal every layer down to
  the one that computes, or none.** `rget` → `tp_pin` → `rf_upd`: with `rf_upd`
  transparent, sealing the top two cannot change anything. Sealing all three took
  one file 575 s → 261 s and its `Qed` 235 s → 35 s. **But do this per file with a
  measurement, never as a sweep** — across ten of the tree's most expensive
  proofs the same three `Strategy` lines were all inside noise, and one file does
  not even compile with them (it `unfold`s `tp_pin`). The outlier had both a
  20+-link `pose` chain and a large Iris context; that combination is what makes
  conversion dominate. The cost is invisible to tactic profiling — it lands in
  the kernel at `Qed` and inside `iEval`/`pm_reduce`.
- **Invert a symbolic-step executor over its ABSTRACT parameters** — never
  `cbn`/`unfold` it into a hypothesis and destruct the guards there. Each
  `destruct` of a guard buried in the reduced term reverts the hypothesis into
  the match's dependent motive, and at `Qed` the kernel must normalise the
  immediate there; an immediate carrying an `autocast` (`concat_vec`) is ~17×
  costlier than a plain `sign_extend'`. Result: ~30 s per lemma, 100 % in
  `Typeops.execute`. **Not fixable by opacity** — sealing sent the file to 40 GB /
  16 min at *tactic* time (the kernel never explodes from opacity; only the
  tactic engine does). The fix is one inversion lemma doing the guard case
  analysis with the displacement OPAQUE: ~30 s → <1 s.

## Where a `Qed` actually goes

Only about a quarter of a `Qed` is typechecking (`Typeops.execute`, which is
DAG-linear and memoized). The rest is four TREE walks — `HConstr.of_constr`,
`close_proof`'s `global_vars_set`, and `sort_and_universes_of_constr` twice —
each a `Constr.fold` with no memo, i.e. linear in the number of *occurrences*.
So the lever on `Qed` is term size, and the question is never "what is the kernel
converting?" but "how big is the tree?".

Terms here are 200–700× bigger as trees than as DAGs, and **this cannot be fixed
by sharing in the kernel — do not repeat that experiment.** A patched Rocq with
a physical-identity memo on `of_constr` and unconditional `Typeops` memoization
found 0.5–1.6 % memo hits across three big proofs; RSS corroborates (~70 bytes
per node means the tree really is materialised). The only asymptotic fix is for
the proof term to NAME the environment rather than spell it, which `pm_reduce`
(a `cbv` over the `pm_*` constants) zeta-reduces straight back open — the
proofmode is *designed* to keep the environment in normal form so `envs_lookup`
computes. That is an Iris redesign, not a tactic swap.

## Build shape

The build is **both** critical-path bound and core-saturated in the middle: the
path is a long shared prefix plus ONE whole-function proof — whichever is
slowest that day — and the wall above the path is core starvation. Reconstruct
the path from `coqdep` × per-file TIMED `real` (or from `.vo` mtimes: a file's
start ≈ mtime − its `real`), never from per-file time sums, which mislead because
big files run in parallel. `tools/proof_profile.py` does all of it in one pass
and runs in CI on every checkin.

- **A `Require` between two `Proof<F>.v` files is pure critical path.** A
  whole-function proof requiring a sibling whole-function proof is nearly always
  reaching for a shared *block*, not the sibling's capstone — and a shared block
  belongs in a third file both require. A Rocq functor cannot span two files, so
  whatever they share has to become its own functor, applied twice. **Do not
  expect the split to pay in ΣCPU**; it pays in the chain, and it costs ~2 s of
  import prelude per new file. Judge it on the profiler's "Longest dependency
  chain" table (any `Proof*` immediately following another `Proof*`), never on
  the per-file list.
- **Do not let the build serialize along a proof's phase structure.** A function
  proved in phases turns into a strictly serial require chain. Measure the
  coupling: usually the heavy phase proofs sit ENTIRELY before the functor and
  need nothing from their predecessor but shared vocabulary, while the actual
  seam module is under a second. Hoist the vocabulary into one functor-free file
  and split each phase into heavy-part + seam. Finding the cut is mechanical:
  `.glob`'s `R` lines give every reference with its defining library; filter to
  the byte range before the functor.
- **Where ΣCPU goes tree-wide, by leading tactic:** `iApply` ~16 %, `Qed` ~15 %,
  `Require`/`From` ~17 %, `iIntros` ~8 %, `iDestruct` ~4 %. The import line is
  the one to internalise — ~1.9 s per file of pure module loading, a floor rather
  than a bug (empty file 0.36 s for Stdlib, +0.47 s stdpp, **+1.12 s for
  `iris.proofmode`+algebra+base_logic+program_logic**, +0.35 s for the whole Sail
  model — `.vo` loading is lazy, so do not go hunting in the 22.7 MB model file).
- **Negative results — do not redo these.** `_CoqProject` order does not matter
  (three orders measured within 2 %; level-order visibly changed the schedule and
  make refilled the freed slots either way). Oversubscribing `-j` does not help
  (it fixes the queueing gap and costs exactly what it buys). `Proof using`
  tree-wide is ~5 % of `Qed` = 0.75 % of the build, and the non-minimal forms
  (`Type*`/`All`) change which section variables a lemma is generalized over, i.e.
  its ARGUMENT LIST, which breaks positional application. `vm_cast_no_check` in
  the generated decode band only MOVES cost from `Qed` to elaboration.
- **The generated decode band's cost is the PROOFMODE, not the `vm_compute`s** —
  ~76 % generic Iris plumbing re-paid by each of ~8,500 `mk_rvc`/`mk_base` calls,
  against ~9 % for the side conditions everyone suspects first. The fix was to
  state the whole `instr` introduction as ONE lemma
  (`KernelText.instr_intro_rvc`/`_base`) so the proofmode work happens once, in
  those two proofs; `mk_rvc`/`mk_base` keep their signatures. 2.8× on the band,
  which is what an `XV6_REV` bump re-pays.

## Smaller traps

- **`lia` cannot do a nested-division chain** even mword-free and iris-free
  (`E mod 32 = 0 → E/32 mod 4 = 0 → … → E = 0` comes back "cannot find witness").
  It has no theory of iterated division; stage it with `Z_div_exact_2` +
  `Z.div_div`.
- **In a `first [ … ]` alternation, put the CHEAP-FAILING branch first.** The
  cost of a tactic that FAILS grows with the proof term, so an alternation
  leading with an expensive-to-fail branch pays that cost at every use — 42 s
  over one function, purely in the failures of the first branch, fixed by
  reordering and nothing else. `exact`/`assumption` fail cheaply on a type
  mismatch; `rewrite … in H` and `congruence` do not.
- **Order `repeat (first [ … ])` loops** with cheap structural rewrites first and
  broad whole-goal normalisation LAST — the loop re-tries its first branch after
  every success.
- **Give `iFrame`'s names in the GOAL's conjunct order** — a wrong order is worse
  than none (one reordering took a frame from 2.2 s to 3.8 s).
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

## A HINT-DATABASE DISPATCH IS A DEPTH PROBLEM, NOT A BREADTH ONE (measured 2026-08-18, UserTotalU)

`UserTotalU`'s two dispatch tables discharge ~98 per-family `goodmb`
obligations through one tactic that ends in `eauto … with u_gm`, where
`u_gm` holds the ~80 twins of P5's catalogue plus the gpr-index side
conditions.  Breadth is cheap — a twin whose head instruction does not match
fails its `apply` immediately — but DEPTH is not: at `eauto 6` each call
site cost **~15 s** and the file took **half an hour**; at `eauto 3` it is a
few seconds each.  The obligation is only ever "apply the family's twin,
then its side conditions, then at most one step inside one", so 3 is the
real bound and everything above it is backtracking through side conditions
that were already going to fail.

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
