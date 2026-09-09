# Proof performance & build optimization

Techniques for writing proofs that compile in reasonable time, and the
diagnostics that find the cost when they do not.

## Diagnosis

**Run `coqc -time` first.** It streams, so the last line in the log is the
stalling sentence. If the slow line is a tactic, no proof-term work will help.
Map `Chars A-B` to a line with `head -c B <f>.v | wc -l`.

- **Rank ms per sentence before opening the file.** One `awk` over the
  `.v.timing` files (sum `secs`, divide by sentence count) separates a file with
  a hot statement from one that is merely the biggest. A file at its peers' rate
  has no bug to find.
- **A/B properly or not at all**: one isolated `coqc` per arm, arms interleaved,
  min of N, `uptime` first. The box is shared and load *inverts* an A/B, not
  merely widens it. Per-file times from two different parallel builds are not a
  comparison.
- **`rm -f .lia.cache .nia.cache` before each arm.** micromega persists every
  certificate per directory; warm readings are off by a large factor, and the
  first compile after an edit re-derives what the edit moved, so an improvement
  reads as a regression on the run that introduces it.
- **`-async-proofs off`** when the question involves `Qed` — otherwise the
  kernel check runs in a worker `-time` does not count.
- **`Set Ltac Profiling`** — read the *local* (self) column. **`Set Debug
  "hconstr"`** prints each `Qed`'s tree size and DAG bindings; a high ratio means
  a small proof with an exponentially unfolded term.
- **To localise a blow-up inside one lemma**, bisect with `Axiom cheat_ : forall
  (A : Type), A.` — unlike `Admitted` this still runs `Qed`.
- **UNIFORMITY ACROSS UNRELATED FILES MEANS ONE SHARED CAUSE.** A dozen
  sentences of the same shape in unrelated files, all within a second of each
  other, is one shared conjunct or one shared instance. This is the standing tell
  and it names causes without anyone reading a proof.
- **To see what a tactic is really handed**, splice
  `match goal with |- ?G => idtac G end. repeat match goal with H : ?T |- _ =>
  idtac H ":" T; fail end.` before it; it prints on a plain `coqc` run.
- **A slow tactic looks like a hanging `Qed` and hides compile errors** — the log
  stays empty while a real error further down sits in unflushed stderr.

## RULE ONE: the cost is `|Δ|`, the Iris context

`tree ≈ 2 × (#proofmode steps) × |Δ|` — every step's term mentions the whole
context twice. So **`Qed` time is the size of the context times the number of
steps it survives**, splitting a proof into `Qed`-sealed chunks buys nothing by
itself, and a whole-function proof can be the slowest file in the tree with no
hot sentence at all.

**Find the entry worth attacking by dumping `Δ` and ranking it by printed size**:
`Unset Printing Notations. Set Printing Depth 200. Show.` mid-walk on a scratch
copy, split on the quoted names. Strip the `Esnoc` scaffolding first or the last
intuitionistic row absorbs the whole spatial prefix. The rows that LOOK big
(big-ops over the fs kit) are among the smallest.

### Fold block continuations into named definitions

Nested `iAssert (□ wp_next … (fun CIDs => <40–80 lines of ∀/wands>))` is far
more statement than resource, and every step pays for all of it. Fold the inner
body into a `Definition`; the proof script does not change.

1. **Keep it TRANSPARENT.** `Typeclasses Opaque` makes the call sites' `iApply`
   fail and forces an `iEval (rewrite /X)` each, which is a clear regression.
   Seal a post nobody applies inside the proof; never a continuation.
2. **Fold only the INNER body** — the `∀ fuel` and the `wp_next`/`□` must stay
   visible for the call sites' `iSpecialize`.
3. **For a `∀ fuel` block, parameterize by `fuel` and keep the `∀` outside**, so
   `iInduction` leaves the IH folded too.

Two limits: when `GEN`/`CID0` are lemma binders the bodies must take them
explicitly; and a continuation with no `wp_next` wrapper *in a pinned-hart
stretch* cannot be folded at all (the next leaf's implicit process pointer stops
unifying, and making `p` a parameter does not rescue it).

**A fold helps whoever SUPPLIES the closer and hurts whoever USES it**, because
every step then pays a delta-unfold of a many-argument constant. Argument count
is not the predictor; the share of Δ removed against the number of steps
carrying it is. Measure the using file. **And only fold rows that DOMINATE the
dump** — the flat tail is consumed row by row, so bundling it moves the cost
rather than removing it.

### Seal a whole-function proof's continuation

Do not spell a postcondition inline in a spec body: one `Definition` in the spec
file plus `Global Typeclasses Opaque`, unfolded once at the return. Worth nothing
if the continuation is already named — naming is the fix, the seal is only for a
body that spells it inline.

**The same applies to a PREMISE-side closer, and there it is easier to miss** —
it arrives as a hypothesis, so it never shows as a hot sentence; it just sits in
Δ. Keep that one transparent (the tail applies it).

**A closer that is a premise of a module-type contract must be defined outside
the spec file's `Section`**, with its own `` `{!riscvGS Σ, …} `` binders — inside
a `Section` fixing `CID` its rows do not take a `CID` argument yet
(*"Wrong argument name CID"*).

### Do not pose instruction facts — close them as subgoals

A leaf's `instr pc rvc ast` premise does not have to arrive as a hypothesis.
Leave it as `[]` in the spec pattern and close it from the persistent
`kernel_text`:

```coq
    iApply (wp_csdsp_s_sconf … with "Hcg Hpc [] Hr40").
    { iApply (pai_02 with "Htext"). }
```

Nothing enters Δ, and the saving is flat across the whole tail rather than in
any one sentence. `tools/instr_subgoal.py` does the edit and `--rank` predicts
the win from `min(peak live block net of iClears, poses per Qed)` — not from site
count. The limit: an `instr` used inside a Löb body is re-derived per iteration,
which is still the right trade.

### Pose late, clear early

A persistent hypothesis is re-embedded in the term of every following step. Pose
it on the line above the `iApply` that eats it. Retrofitting works only on
straight-line stretches — in a Löb body a textually single use runs every
iteration.

`iPoseProof … as "H"` files a persistent fact under `□`, so the `iApply` does
NOT consume it: a retrofit needs an explicit `iClear`, and **a pose that is never
used is invisible** (a persistent leftover does not trip the spatial-hypotheses
check at `Qed`). Grep for a pose whose name never appears again in the same
`Proof.`…`Qed.`, scoped to one proof block.

### Hypothesis names cost term size

Iris's `ident` is a `string` — ~10 term nodes per character, embedded once per
step. The only lever is shorter names, and it is a bad trade outside the longest
monoliths. Sealing cannot help: `envs_lookup` must COMPARE names under
`pm_eval`'s delta whitelist.

## Never let a general-purpose closer meet a large context

The single most productive rule here. The giveaway is always that the tactic is
trivially discharging a goal you can read at a glance.

- **`discriminate` with no argument scans every hypothesis, head-normalising
  each WITH DELTA.** So does bare `injection`, bare `congruence`, `done`, and
  every `by tac` (which ends in `done`). One `⊆` between two computed gmaps is a
  large context by itself. **Name the hypothesis**, and the bill is per branch,
  so a `destruct` over a wide inductive multiplies it. Grep `try discriminate;`
  and `discriminate.` not followed by a name. (`ltac:(vm_compute; discriminate)`
  is cheap and everywhere — there the goal really is `t1 <> t2`.)
- **Say what the goal is instead**: `exact (conj Hsl eq_refl)` for `by exists q,
  sl`; `exact (conj eq_refl eq_refl)` for `iPureIntro. done.`. `by split` is
  `split` then `done` and pays the same.
- **`naive_solver` is forbidden inside a whole-function proof.**
- **Never `simplify_eq` there either** — use `injection H as pat…`, which
  produces one pattern per NON-trivial component (guess wrong and the error names
  the fix).
- **Before believing such a sentence is intrinsically slow, `clear` the fat
  hypothesis and re-time.** One run, conclusive.
- **`upd_ne`'s side goal has exactly one answer: `CalleeSaved.reg_ne_side`.**
  Never hand-roll the alternation. Its branch order is the point, and its
  name-free branch must use `match` (not `lazymatch`) over the hypotheses.

### `lia`, and the override that handles it

`iris/FastLia.v` overrides `lia`/`nia` tree-wide from the same hook as the
`set_solver` one: before solving it clears every hypothesis `zify` could not
have read, so cost tracks the arithmetic in scope, not the context. Read that
file's header; every `set_solver` bullet below applies to it too. The rules
specific to it:

- **Never clear a hypothesis that is not a `Prop`.** Clearing one RESTRICTS the
  context of every undefined evar, silently, so a SIBLING goal stops unifying
  somewhere else entirely and the error names a broken `rewrite` rather than the
  closer. (This is what the hand-written keep-lists' `XI` was really for.)
- **Do not write new `clear -H..; lia`** — the override does it, and it reaches
  the argument-position case a hand-written `clear -` cannot.
- **A tactic filter runs on EVERY call, so nothing on its per-hypothesis or
  per-node path may be a `constr:` quotation (re-elaborated at every
  evaluation), a `constr list` scan, or a `SetShrink.vars_of`.** Gating one
  behind a `timeout` instead is refuted: it makes which arm proves a goal
  depend on machine load, and it measured slower than no override at all.
- **Derive a tactic's vocabulary from SAMPLE TERMS, never from constant names.**
  `(0 <= 0)%nat` is `Peano.le`; `Nat.le` is a different constant no goal carries,
  so a list naming it drops every nat inequality while looking right.
- **A starved `lia` does not fail fast, it can hang** — so `first [ fast | slow ]`
  is not a safety net for a filter, and a green tree is not evidence the filter
  is sound. Check it with the fallback deleted.

What the override does not fix:

1. **A side condition that is the same at every call site belongs in a lemma
   proved where the context is EMPTY** — a `lia` certificate reifies the
   hypotheses it was handed, so the PROOF TERM carries them too and the `Qed`
   cost falls with the tactic cost.
2. **Close a concrete goal with `discriminate`, not `lia`.**

### A bespoke side-condition tactic is the same bug and hides better

Read every `Ltac` a leaf's `ltac:(…)` slot invokes as a closer, and price it by
the context it runs in. A `repeat match goal … specialize` loop over the whole
context proves a one-hop equation by specializing every link in scope.

**Follow a chain from the goal, by term, not by rewriting:**

```coq
Ltac wp_next_link Hd :=
  match goal with
  | H : _ = false \/ _ = _ -> ?x = _ |- ?x = _ =>
      refine (eq_trans (H Hd) _); clear H
  end.
```

`refine (eq_trans …)` keeps the equation in the term and never touches the
context; the `rewrite` spelling of the same walk is a regression. Keep the old
loops as later branches so no call site can regress. `clear H` is what makes
`repeat` terminate against a cyclic pair.

## `set_solver`

`iris/FastSetSolver.v` overrides stdpp's tree-wide (hooked in from
`RiscvModelBytes.v`): it clears the hypotheses that cannot reach the goal, so
cost is linear in the context rather than quadratic. Read that file's header.

- **If you change the filter, re-run the check with the fallback DELETED.** With
  the fallback in place `set_solver` cannot fail, only get slow, so a green tree
  proves nothing — and a filter that fails open is invisible, presenting as "just
  as slow as before" rather than as an error.
- **The override needs `Import`, and a leaf can miss it.** `Print Ltac
  set_solver.` answering *"not a user defined tactic"* is the check.
- **A membership in a union of two `gset` VARIABLES is still expensive**, override
  or not: `by (apply elem_of_union_l; exact H)`. Grep `∈ .* ∪ .*) by set_solver`.
- **A hypothesis that is a set equation is kept by the filter by construction**
  — `clear` it once the rewrite has used it. The tell is that every atom in the
  goal is already a variable and the closer is still slow.
- **A pure union shuffle belongs in a lemma stated at VARIABLES**, where there is
  nothing to unfold and nothing to reify, plus `apply` at the site.
- Two things the override does not fix, both goal-side: `gset (mword n)` (see
  the durable notes) and `set_unfold` over a `list_to_set` of a literal-size list.
- Best of all, do not create the goal: `dom_insert_lookup_L` closes a "the slot
  was already live" identity with no set reasoning.

## Framing: name the context side, construct the goal side

- **Never bare `iFrame` in a large context** — cost is (context × conjuncts).
- **A named `iFrame` still pays a GOAL-side search.** Give every multi-conjunct
  resource abstraction a CONSTRUCTOR lemma when you define it, for the same
  reason it gets an accessor.
- **Otherwise split the ONE definition-valued conjunct off first** with
  `iSplitL`/`iSplitR`, and the frame that remains is syntactic. It is never the
  six points-tos that make a frame expensive.
- **When every conjunct is definition-valued, build the whole bundle**: an
  `iSplitR; [iExact "H"|]` chain in the goal's own conjunct order. The tell is a
  lemma whose whole job is to REASSEMBLE a named bundle. (Persistent rows are
  `iSplitR`, mixed take `iSplitL "H"`, pure rows `iSplitR; [iPureIntro; exact
  H|]` — which also retires a trailing `iFrame "%"`.)
- **A rebuild is a construction, so build it — do not frame it.** The goal is
  the abstraction UNFOLDED, so its tail conjuncts are whatever it ends in.
- **Extracting a persistent fact out of a bundle must not take the bundle
  apart** — do it in a small lemma over one hypothesis and hand the bundle back
  whole. A rebuild moves the cost rather than removing it.
- **A shape mismatch turns every match attempt into a CONVERSION.** A `big_sepL`
  carries `8 * Z.of_nat i` where consumers name literals: convertible, not
  syntactically equal, so an N×N frame pays a conversion per attempt. Factor the
  shape change into one `⊣⊢` lemma. The tell is `iFrame.` costing tens of
  seconds.
- **A one-name `iFrame` is still a whole-goal walk** — read it as a claim about
  what comes AFTER the conjunct being framed, never about the name.
- **`iFrame "%"` is a CONTEXT-side search** over every Coq hypothesis in scope.
- **Give the names in the GOAL's conjunct order** — worth a lot sometimes and
  nothing others, so it is a `sed`, try it before the chain. **Do not read the
  order off the frame LIST**: `iFrame` matches by TYPE, so the authority is the
  destructuring pattern consumers use on the same definition.
- **`proc_priv_core` is the worst instance in the tree** and every
  syscall-altitude proof reaches it: its last conjunct is a 4096-element big-op.
  Intro the tail as ONE hypothesis and close with `iExact`.

## Typeclass search and sealing

- **A low-priority instance runs LAST, and if the class's other instances are
  structural that means after the whole payload has been walked.** Read a low
  priority as a claim about *when the head can match* and check it: it is right
  for a head that unifies with a bare evar, wrong for a rigid application only a
  call site can produce.
- **`Typeclasses Opaque` on a payload wrapper is not the fix** — consumers read
  through it (`iDestruct "HR" as (t) "H"`), and the build fails at
  *"iExistDestruct: cannot destruct"*. **Seal a definition only where nothing
  reads through it.**
- **A hand-rolled `first [apply … | apply … | …]` IS instance search**, with the
  same costs and none of the tuning. Read the Ltac profile's equal call counts:
  leaf lemmas called as often as each other means every visit fell through all of
  them, because a structural lemma matched through an unsealed tower first.
  **Dispatch on the goal's head with `lazymatch`**, one `apply` per node:
  - **Dispatch leaves too**, not just composites.
  - **`cbv beta` per step** — each `apply` leaves a β-redex under the λ.
  - **A head dispatch stops by construction**, which `first` does not: `apply`
    unifies up to delta, so it matches *through* a transparent component and
    re-walks a body a named instance already covers.
  - **Do not put the "does the body mention ξ?" catch-all first** — on a whole
    payload body the unifier tries to eliminate ξ by delta and does not return.
  - A `Hint Extern` database is equally fast (an Extern's pattern is a filter
    checked before its tactic runs) and is OPEN where a `lazymatch` is a closed
    table; the reason to keep the walk is that it can stop at a component and
    hand back the residual, which `eauto` cannot.
- **A big-op under a transparent name is an `iFrame` bomb; sealing it fixes
  every call site at once.** Use `Global`, not bare `Typeclasses Opaque` — the
  bare form is compilation-local, and a local seal hides the size of the prize.
  `rewrite /X` and declared instances still work.
- **Filter seal candidates by `big_sep`/`[∗` in the body; sort by breadth only
  within that set.** Sealing the most-named definitions whatever their body
  measures null-to-negative, and `wp_next` cannot be sealed at all (every proof
  `iIntros` through it).
- **An `∃` over a big-op already seals it** — `iFrame` will not instantiate an
  existential to look inside. Check the shape a CONSUMER holds, not the shape of
  the definition.
- **Give every big-resource abstraction with a `Persistent`/`Timeless` instance a
  `Typeclasses Opaque` next to it**, or each `#`-intro re-derives the instance by
  descending into the resource. Diagnose by splitting a wide `iIntros` one name
  per sentence. **Put the seals at the END of the defining section** — a file's
  own projection lemmas are what a seal above them breaks.
- **Prove a big `Timeless`/`Persistent` instance structurally**, never with one
  `apply _`:

  ```coq
  Local Ltac tl_struct :=
    lazymatch goal with
    | |- Timeless (bi_exist _) => apply bi.exist_timeless; intro; tl_struct
    | |- Timeless (bi_sep _ _) => apply bi.sep_timeless; [tl_struct | tl_struct]
    | |- Timeless (bi_or _ _)  => apply bi.or_timeless;  [tl_struct | tl_struct]
    | |- _ => apply _
    end.
  ```

  **The dispatch must be syntactic** — the `first [...]` spelling is worse than
  the monolithic `apply _`, because `apply` peels straight through a named
  abstraction that already has its own instance. Descend through connectives,
  never through a name. Peel small bodies too: the predictor is the LEAF. And
  **name the leaf instances** where the peel bottoms out.
- **Mark big concrete literals `Global Typeclasses Opaque`** (`kernel_bytes`,
  `kernel_data`, `kernel_symbols`, `mem_pointsto`) — never plain `Opaque`, since
  a tactic may need to `unfold`.

## Modalities and rewriting

- **Strip only the GOAL's later with `iApply bi.later_intro`.** `iNext` runs
  `MaybeIntoLaterN` over both environments; reach for it only at a genuine Löb
  back edge. The tell that a file has this backwards is an `iNext` followed by an
  `iAssert (▷ X)` that repairs it.
- **A modality step at a `▷` costs the context, so pay it in a lemma** — whose
  conclusion must be a FANCY update, not `|==>`, or `iMod` fails with "cannot
  eliminate modality" (which reads like a missing `Timeless`).
- **Prefer the WAND form of a big-op law to a setoid rewrite.** `rewrite
  !big_sepL_sep` is setoid rewriting over `envs_entails`, and its cost is in the
  `Proper` proofs over the PREDICATES, so hoisting it into a lemma changes
  nothing. Not a sweep — check a candidate's `.v.timing` cost, since site count
  tells you nothing.
- **`rewrite !big_sepL_cons` is worth `iEval … in "H"` only when the target is a
  HYPOTHESIS** — `!` repeats over the whole `envs_entails`. Goal-side sites are
  neutral.
- **Peel a `set`-chain by `eq_trans`, never by `rewrite`.** A function-valued
  chain has the same head on both sides, so keyed matching delta-walks both
  towers to discover it does not match:
  ```coq
  exact (eq_trans (upd_ne nO (Regidx ra_idx) (Regidx q) _ Hra)
                  (upd_ne nN (Regidx a0_idx) (Regidx q) _ Ha)).
  ```
  The tell is a `rewrite` whose equation has `M !!! k` on both sides.
- **A list-lookup side premise belongs in a boolean, not in a `destruct i`** —
  one `vm_compute` instead of one per entry. Put the closer `Ltac` OUTSIDE the
  `Section`.
- **`rewrite n!L`, not `rewrite !L`, when the lemma is expensive to MATCH.** `!`
  always pays one full failing pass, and that pass is a complete setoid traversal
  with instance search; a set-membership or domain lemma over a COMPUTED carrier
  drags its instance chain behind every candidate subterm. Counting is mechanical
  from the goal.
- **`rewrite` ABSTRACTS, `exact` only UNIFIES — and a `nat` numeral makes the gap
  enormous** (numerals are unary, so `4096%nat` is dragged through every
  conversion the motive forces). Reach for `transitivity <the middle term>` then
  `apply`/`exact`. Cheapest instance: `rewrite L. reflexivity.` where `L` already
  closes the goal — grep for that pair.
- **Peel a monadic chain by `apply`, never by `erewrite`** — an equation lemma
  builds a motive over the whole remaining tail at every step. The intro form of
  the same lemma has the same side conditions and no motive. Not a sweep: it is
  free where nothing has put symbolic data in the tail.
- **An `iApply` of a lemma with ~20 premises is a floor, not a bug** (~99 % local
  to `iPoseProofCore`). Look elsewhere.
- **`Qed` re-checks and therefore DOUBLES every `vm_compute`.** Build the cast
  instead of running the tactic:
  ```coq
  Local Ltac vm_eq :=
    lazymatch goal with
    | |- _ = ?r => vm_cast_no_check (@eq_refl _ r)
    end.
  ```
  **It must be the RIGHT-hand side** — `eq_refl l` makes the VM evaluate the
  heavy side twice and is worse than the `vm_compute` it replaces. For heavy
  sentences only, not a sweep: a disagreement now surfaces at `Qed` with no goal
  in view. It does NOT pay inside an `ltac:` in a proofmode `iApply`, where the
  term is re-elaborated anyway.
- **Do not write a trailing `[-]` in a leaf `iApply`'s spec pattern** — it forces
  an explicit `envs_split` of the whole spatial context at every instruction.

## Register-file towers and register maps

- **`Global Opaque` the tower the moment its lookup lemmas are proved.**
  `register_set` is a record update, so any conversion that unfolds the tower
  compares record updates pairwise and the cost is exponential in depth.
- **Never leave a goal with a tower on BOTH sides to `reflexivity`.** Restate so
  one side is a VARIABLE and discharge the lookups positionally; failing that,
  `etransitivity; [apply L | symmetry; apply L]`. A wide `first [apply …]` is not
  a fix — the failing branches are exactly where the unifier deltas. And check
  for a missing read-only twin of the full-agreement lemma before believing a
  file's cost: the `etransitivity` fallback reads as the settled answer.
- **`pose`, not `set`, for a register chain.** `set` pays a whole-goal pattern
  search per instruction and the goal is `envs_entails Δ Q`, so cost scales with
  CONTEXT. Where a file already uses `set`, deleting a trailing `change T with X`
  is free (the `change` folds nothing — `set` already did).
- **`Local Strategy opaque [rget tp_pin rf_upd]`** where leaves state premises
  over `rget`. Trap: a premise spelled `M !!! Regidx r` was bridging by delta and
  now REGRESSES — restate via `rget_ne` first. **Sealing can regress a distant
  site**, because it deepens the unifier's walk at every `rget`-typed premise and
  an inline closer is priced by that depth. Audit `-time` across the whole file.
- **`reg_lookup` by default; `peel_reg` where the value is SYMBOLIC.** Peel ONE
  layer at a time (unfolding the chain first is O(depth²)), and it must be
  `first [peel | unfold-var]`, not a `lazymatch` with the var branch first. Try
  the HIT lemma before the miss lemma.
- **Collapse a run of consecutive same-register writes into ONE update with
  `upd_upd`**, right after the writes, keeping the intermediate `set`s defined so
  existing peels still parse.
- **`unfold set_reg` is a `3^N` tree bomb** — its body mentions the state three
  times. Peel with `RiscvLang.v`'s projection lemmas. Three shapes must keep the
  `unfold`: a whole-STATE equation has no projection to fire on.
- **State a whole-function WP's post in the ∀-continuation form**, never with a
  deep `let`-chain of register maps in the STATEMENT — every caller's `iApply`
  zeta-traverses it.

## Inline `ltac:` in argument position

**Never splice a computing tactic into a term whose implicit arguments are still
evars.** The proofmode re-elaborates it, and against unresolved evars it can fail
to terminate outright. Prove it as `assert (H : …) by (tac)` and pass `H`. For
several such args, use the **unshelve hoist**: bare `_`, `unshelve iApply`, and
discharge the evar subgoals as `{ … }` goals.

**A general-purpose closer spliced there is priced by the DEPTH of its call
site, not by its goal** — the identical sentence terminates in one arm and not in
another. The goal can even be a closed numeral and still cost seconds. Read a
slow closer as a CONTEXT problem before you read the goal at all.

**`clear -H` is unavailable here** — the goal in argument position is an evar
whose instance names every variable in scope, so there is nothing to keep. The
`FastLia`/`FastSetSolver` filters work anyway, because `SetShrink.vars_of` skips
an evar's instance, so COST is no longer a reason to hoist; re-elaboration
against unresolved evars still is.

## Conversion and `Qed`

**Only about a quarter of a `Qed` is typechecking.** The rest is four TREE walks
with no memo, linear in the number of *occurrences*. So the lever on `Qed` is
term size, and the question is never "what is the kernel converting?" but "how
big is the tree?". This cannot be fixed by sharing in the kernel — a patched
Rocq with a physical-identity memo found almost no hits. The only asymptotic fix
is a proof term that NAMES the environment, which `pm_reduce` zeta-reduces
straight back open. That is an Iris redesign.

Corollary: a repeated spelled-out term in hypothesis types is a real but SMALL
lever. Do not expect a spelled-out Sail term to be why a `Qed` is slow.

- **A check that grows past a few hundred MB on a small file is a DEGENERATE
  PROOF, not something to wait out.** Three doors into the same divergence: a
  reduction that touches a dumped byte literal; ssr `rewrite`/`iFrame` against a
  long insert chain (the `Insert` instance unifies up to delta); and `f_equal`,
  which tries `reflexivity` on the whole goal first. **Never let
  `reflexivity`/`f_equal`/any unification see a goal whose two sides contain a
  tower but differ** — rewrite the leaf equalities first.
- **`vm_compute; reflexivity` is rechecked by the kernel's LAZY conversion at
  `Qed`.** Close such goals with `vm_cast_no_check`, and compute a result ONCE
  into its own `Definition` plus a single VM-cast lemma.
- **A guard fixed by `change` pushes a slow non-VM conversion to `Qed`** — use
  `replace g with v by (vm_compute; reflexivity)`. **NEVER `cbv -[…]`** on a Sail
  dispatch guard.
- **Never `vm_compute` a goal containing a symbolic `mword` or a built-up
  `mstate`.** Compute only the CLOSED offset.
- **Never let an `exact`/`reflexivity` cross an update layer** — the tell is that
  the sentence right below it, four layers down, is free.
- **Seal a definition tower all the way down to the layer that computes, or not
  at all.** Do it per file with a measurement: across the tree's most expensive
  proofs the same `Strategy` lines are inside noise. The shape that pays has BOTH
  a long `pose` chain and a large Iris context.
- **Invert a symbolic-step executor over its ABSTRACT parameters** — never
  `cbn`/`unfold` it into a hypothesis and destruct the guards there, or the
  kernel must normalise a dependent motive's immediate at `Qed`. **Not fixable by
  opacity**: sealing sends the file to tens of gigabytes at *tactic* time. The fix
  is one inversion lemma with the displacement opaque.

## Build shape

The build is critical-path bound and core-saturated in the middle: the path is a
long shared prefix plus ONE whole-function proof. Reconstruct it from `coqdep` ×
per-file TIMED `real`, never from per-file time sums.
`tools/proof_profile.py` does all of it and runs in CI.

- **Price the RUNNER-UP route before you invest.** Once two routes are within a
  few seconds, taking time out of the leader moves the wall by almost nothing.
  The static model predicts this and has agreed with measurement on every cut.
- **A split returns what the path's NEXT NODE does not name, minus a per-file
  import prelude.** Find the cut by asking what the next node names, never by
  where the file's own section banners fall — a cut at a class the next node does
  name can measure negative.
- **A `Require` between two `Proof*.v` files is pure critical path.** What they
  share is a block, and a shared block belongs in a third file both require.
  Judge a split on the profiler's dependency-chain table, never on the per-file
  list, and do not expect it to pay in ΣCPU.
- **Cut a vocabulary file by DEPENDENCY CLOSURE, not by section.** Such a file
  has no slow sentence — its wall is thousands of trivial ones — so the only
  lever is which sentences the routes wait for. Two traps: a `Local Lemma`
  crossing the cut must lose its `Local`, and a file naming a moved lemma
  QUALIFIED is invisible to a `Require`-line scan.
- **A `.glob` closure does not see typeclass instances, and `Require Import` is
  not transitive.** An instance resolved by SEARCH leaves no `R` line, and a
  consumer that reached the old file through someone else's `Require Export`
  chain does not reach the new sibling. Check by grepping COMMENT-STRIPPED
  sources — and the stripper must lex Coq strings inside comments.
- **The serial tail is everything after the last `Link*`, and it pays one for
  one.** A file there must import VOCABULARY, never a proof; if its references
  into a chain file are all `def`s, move the definitions to a file with no
  `Link*` import. No whole-image `vm_compute` belongs in a tail file.
- **Where ΣCPU goes tree-wide:** `Require`/`From` ~17 %, `iApply` ~16 %, `Qed`
  ~15 %, `iIntros` ~8 %, `iDestruct` ~4 %. The import line is a floor.
- **Negative results — do not redo these.** `_CoqProject` order does not matter.
  Oversubscribing `-j` costs exactly what it buys. `Proof using` tree-wide is a
  fraction of a percent, and the non-minimal forms change a lemma's ARGUMENT
  LIST. `vm_cast_no_check` in the generated decode band only moves cost from
  `Qed` to elaboration.
- **The generated decode band's cost is the PROOFMODE, not the `vm_compute`s.**
  State the whole `instr` introduction as ONE lemma so the proofmode work happens
  once. This is what an `XV6_REV` bump re-pays.

### Splitting a whole-function proof across files

1. **Are the blocks independent?** They are if each seam is the next block's
   PREMISE LIST rather than a call. Confirm by listing cross-references with
   comments BLANKED — nearly every apparent one is prose.
2. **Does any block name a functor argument?** If not, the shared vocabulary is a
   plain functor-free file and each block is its own small functor.
3. **Does anything shared appear in a STATEMENT?** A name used only inside proofs
   lets each file make its own copy. Check before writing a Module Type.
4. Expect ΣCPU to rise, and section-local `Notation`s to be repeated per file.

**The trap, invisible in the source:** a definition mentioning the ambient `CID`
is fine in one file and becomes an INSTANCE-IMPLICIT argument once split — and
every use site sits under a `fun CIDa => …`, so search picks the λ-bound hart.
The symptom is `iSpecialize: cannot instantiate` at an unchanged spec pattern,
and **it is invisible without `Set Printing Implicit`**. Fix by writing `(CID :=
CID)` at each body site and each cross-module block application. A section whose
`Context` binds no `CID` needs none of this — check that first.

## `Print Assumptions` is a whole-tree walk

It lives in `iris/SystemAssumptions.v`, run by `make audit-only` and by CI —
deliberately not a `_CoqProject` row, and deliberately not in the serial build
tail. It forces and walks every opaque body in the cone, and forcing is not a
read: each term is re-COOKED out of its sections and re-substituted through
applied functors, 2–3× per term. Both of this tree's universal idioms (`Section`
+ `Context`, sealed functor applications) are on that path.

So it is ~linear in total proof-term bytes in the cone, which makes it a **proxy
metric for whole-tree proof-term size** — treat a jump as a tripwire.

- **Negative results:** it is not disk I/O; nothing is cached between calls, so
  a second audit doubles the bill rather than riding along; auditing at lower
  altitude does not decompose the cost, since the deepest contract carries nearly
  all of it; GC tuning does nothing.
- **The cost is the CONE, not the file you are auditing** — cutting a file's
  compile time moves its audit by nothing.
- **`-noglob` on the audit compile is load-bearing**: with no `.glob` the nightly
  dead-import sweep reports the file UNANALYSED and leaves its single `Require`
  alone.
- The lever, if anyone wants it, is per-lemma binders instead of `Section` +
  `Context` in the hot cone. That is a campaign, not a fix.

## Smaller traps

- **A `big_sepM` submap step inlined at syscall altitude does not terminate.**
  `iDestruct (big_sepM_subseteq _ _ _ Hsub with "H")` inside a U-mode entry WP
  (the goal mentions the whole program key) ran 6+ minutes at 847 MB and never
  returned; the same step as a closed lemma off the WP (`UInitKernel.
  ubyte_map_sub`) costs 8 ms. The map was a `filter` over a 1296-entry dumped
  image (`UCodeInit.init_argv_map`) -- a definition nobody computes but the
  unifier will, so it also gets `Local Opaque` beside its readers. Rule: any
  lemma about a dumped map is stated and proved closed, then applied.

- **`lia` cannot do a nested-division chain** — stage it with `Z_div_exact_2` +
  `Z.div_div`.
- **In a `first [ … ]`, put the CHEAP-FAILING branch first.** The cost of a
  tactic that fails grows with the proof term. `exact`/`assumption` fail cheaply;
  `rewrite … in H` and `congruence` do not. Reordering is sound because `first`
  commits only to a branch that finishes. (A wide `first [apply …]` over a family
  of lookup lemmas whose towers are already `Opaque` is NOT this case — its cost
  is in the succeeding applications. Do not redo that.)
- **Order `repeat (first [ … ])` loops** with cheap structural rewrites first and
  broad normalisation LAST.
- **`Local Strategy 1000 [pa_stk]`-style deprioritising** keeps failed
  comparisons first-order while `unfold` still works; `Local Opaque` blocks
  `unfold` too.
- **Use the batched CSR peel lemmas** (`skip_csr_false_clauses` / `drive_csr`)
  from the start — one clause per `erewrite` is O(tail) retyping per clause.
- **A family of "field X is untouched" laws should be N corollaries of ONE
  testbit reading**, not N testbit chases.
- **`Unshelve. Show Existentials.`** when "incomplete proof" is reported and the
  goal list looks empty — a missing bullet at the end of a `split_and!` block is
  invisible to every other probe.
