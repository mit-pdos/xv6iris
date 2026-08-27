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
- **"Isolated" MEANS CHECK `uptime` FIRST — this box is shared, and a busy one
  INVERTS an A/B, not merely widens it.** At load 13.5 the `Strategy opaque`
  arm of `ProofIput` read 118.4 s / 119.3 s against a 122.0 s baseline, i.e. a
  clean 3 % win with the per-tactic breakdown agreeing (`Qed` 23.3 → 21.1 s);
  the same interleaved A/B at load 3.4 read **+11 s and +17 s the other way**.
  The same file's baseline read 290 s and 338 s on one afternoon. Min-of-N is
  the guard that survives this, because contention only ever ADDS — a single
  reading, or two readings taken hours apart, prove nothing at all.
- **Per-file wall from two DIFFERENT parallel builds is not a comparison
  either, and it will hand you a large fake win.** `ProofIput` reads 112 s in a
  full 1327-file build and 80 s in a 396-file incremental one with nothing about
  the file changed — GC pressure tracks the width of the build, so even the
  `user` column moves. Confirm any cross-build delta with an isolated A/B
  before believing it; that one would have been reported as a 32 s improvement
  from an unrelated commit.
- **`iris/.lia.cache` MAKES A WARM MEASUREMENT LIE, BY UP TO 9×.** micromega
  persists every `lia` certificate in a per-DIRECTORY `.lia.cache` (with
  `.nia.cache` beside it), both gitignored and both excluded from the VM push,
  so they survive everything. `FsEffCreateEntry.v` measured **23 s warm and
  216 s with the cache deleted**, and the cache itself had reached 780 MB.
  Two consequences for any A/B. (1) The FIRST compile after an edit re-derives
  every certificate the edit moved, so a change that improves a file reads as
  a 3× REGRESSION on the run that introduces it — the same source measured
  17.3 s, then 43.0 s, then 15.9 s over three consecutive `coqc`s — the
  middle one being the first compile after the edit. Always take the second
  reading. (2) Compare cold against cold when the number you want is
  what CI or a fresh worktree pays: `rm -f .lia.cache` before each arm. The
  gap is not noise, it is the whole certificate search.
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

**THE SAME RULE APPLIES TO A PREMISE-SIDE CLOSER, and there it is easier to
miss** — a closer arrives as a hypothesis rather than as a goal, so it never
shows up as a hot sentence; it just sits in `Δ` making every step of the walk
dearer. `ProofForkret`'s residue closer (`∀ h pt' V', ⌜..⌝ -∗ ⌜..⌝ -∗ ⌜..⌝ -∗
ut_tfk -∗ first_done -∗ W -∗ timer_cap -∗ forkret_yield -∗ URes h pt' ksp`) was
spelled out in THREE statements — `wp_forkret_gen_body` and both of the proof's
two block lemmas — and measured **13 % of the Iris context** of every step of a
1300-step walk. One `Definition SpecForkret.forkret_closer` naming it, used in
all three, took the file **27.1 s → 20.7 s (−24 %)** with a byte-identical
assumption set. Keep it TRANSPARENT for the reason the previous subsection
gives: the tail applies it with `iDestruct ("Hyield" $! …)`.

**How to find the entry worth sealing: dump `Δ` and rank it by printed size.**
`Unset Printing Notations. Set Printing Depth 200. Show.` on a line in the
middle of the walk, on a scratch copy, prints `environments.Envs` in full;
splitting it on the quoted hypothesis names gives a size per entry. On
`ProofForkret` at the `kexec` call that was 55 entries / 15 kB, and the closer
was the biggest single row by 30 %. This beats guessing — the entries that LOOK
big (`big_opS`/`big_opL` rows over the fs kit) were 300–900 bytes each.

**A closer that is a premise of a MODULE-TYPE contract has to be defined
outside the spec file's `Section`.** The closer quantifies over the hart `h`
and applies its rows at `(CID := h)`, and inside a `Section` whose `Context`
fixes `CID` those rows do not take a `CID` argument yet — the error is
*"Wrong argument name CID"* at the first such row. Give the `Definition` its
own `` `{!riscvGS Σ, …} `{GEN : GenId} `` binders at top level, exactly as the
contract body beside it already does.

### ProofSysUnlink: the two CONTINUATIONS were 55 % of Δ (measured 2026-08-27)

`ProofSysUnlink.v` was the tree's most expensive file, and it is the worked
example for this whole section — the diagnosis, the two folds, and why it lands on the
opposite side of the ledger from `ProofIput` below.

**The profile says RULE ONE and nothing else.** Isolated `coqc -time`, 151.8 s
over 4832 sentences, no sentence above 10.9 s (a `Qed`):

| head | total | n | avg |
|---|---|---|---|
| `iApply` | 41.8 s | 402 | 104 ms |
| `Qed` | 38.9 s | 63 | 618 ms |
| `iDestruct` | 16.7 s | 215 | 77 ms |
| `iIntros` | 15.9 s | 225 | 71 ms |
| `rewrite` | 6.3 s | 330 | 19 ms |
| `set` | 5.9 s | 102 | 58 ms |
| `iEval` | 4.2 s | 329 | 13 ms |
| `iNext` | 3.5 s | 7 | **495 ms** |
| `assert` | 2.7 s | 786 | 3 ms |

82 s of proofmode steps plus 39 s of `Qed` is 80 % of the file, and both are
priced by `|Δ|`. **The 786 `assert`s, which look like the problem, are 2.7 s
total** — do not chase them.

**Δ, dumped and ranked** (`Unset Printing Notations. Set Printing Depth 250.
Show.` on a copy with the other blocks `Admitted`, then split on the quoted
names — the `Esnoc` scaffolding has to be stripped first or the last
intuitionistic row absorbs the whole spatial-env prefix and reads ~1.3 kB too
big):

| point | hyps | Δ | biggest | second |
|---|---|---|---|---|
| `su_w3` @+0x84 | 87 | 11.7 kB | `Hseamk` 5626 (**48 %**) | `Hcont` 879 (7.5 %) |
| `su_w5_dir` @+0xae | 84 | 6.5 kB | `Hcont` 879 (**13.4 %**) | `Hmetai` 429 |
| `su_w5_dir` @+0xca | 71 | 5.8 kB | `Hcont` 879 (**15.2 %**) | `Hetki` 268 |

Two entries, both continuations, both spelled inline:

- **`Hcont`, the RETURN continuation** — fifteen rows, written out TEN times
  (the contract in `SpecSysUnlink.v` and nine block-lemma statements), and a
  further copy inside each block's own seam.
- **`Hseamk`, the block's fall-through seam** — 58 / 96 / 121 source lines in
  W1 / W2 / W3, one per block, inert in Δ for the whole walk and applied twice
  at the end.

Everything else is a flat tail of ~100–150-character rows: the two 20-row
open-inode bundles, the 15-row stack frame, the ambient fs fabric. **Do not
fold those.** The walk consumes them row by row, so a bundle would have to be
taken apart at every callee call and the cost would move rather than go — see
"Extracting a persistent fact out of a bundle" below.

Both folds are DROP-IN. `Definition sys_unlink_closer` in `SpecSysUnlink.v`
(outside the `Section`, because it is a premise of the module-type contract)
and one `Definition su_wN_seam` per block beside its lemma, all TRANSPARENT.
**Not one line of proof script changed** — `iApply ("Hcont" $! …)`,
`iApply ("Hseamk" $! …)` and the `iIntros` that discharges the seam goal in
`wp_sys_unlink_sconf` all unify straight through a transparent constant.

Isolated `coqc`, arms interleaved, box at load 2–3:

| arm | wall | `.vo` | peak RSS |
|---|---|---|---|
| baseline | 153.7 s (153.7 / 154.9 / 155.3) | 8,941,931 | 3.24 GB |
| + `sys_unlink_closer` | 147.4 s | 8,513,058 (−4.8 %) | 3.07 GB |
| + the three seams | **133.1 s (−13.4 %)** (133.3 / 133.1 / 153.0) | 7,616,840 (**−14.8 %**) | 3.02 GB |

Min of three, arms interleaved. The one 153.0 s seam reading is the shared box,
not the arm: the other two agree to 0.15 % and the closer arm's own pair
(147.4 / 158.9) straddles it the same way at load 20. Contention only ADDS —
take the min, never the mean.

**`su_w3_seam` is a 58-ARGUMENT constant and it pays, where `ProofIput`'s
28-argument closer cost +13 s.** Argument count is not the predictor. What
separates them is the SHARE of Δ removed against the number of steps that
carry it: `ProofIput`'s fold took Δ 7.6 → 5.4 kB in a file whose per-step cost
was already modest, while here W3's Δ goes 11.7 → ~6 kB under a 402-`iApply`,
63-`Qed` walk. Rank Δ first; fold the row that is tens of percent of it, and
only that row. (The 6 kB is arithmetic on the printed sizes, not a second
dump — what was measured is the wall and the `.vo`.)

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
  evar and **DIVERGES**: `KexecOkQ.v` alone reached **300 GB** and had to be
  killed, against 1.57 s / 768 MB with the right list. There is no error
  message to read, and on a shared box it takes the machine with it.
  This is durable-notes.md's "NAMING AN AMBIENT CLASS FIELD OUTSIDE ITS
  CLASS'S SCOPE IS A MEMORY BOMB" (~190 GB, lane R1b) reached from a second
  direction — same root cause, a class search with an unknown `Σ` — so if
  either bites you, read both.

So derive the list, do not guess it: for each row, open the module that
defines it and copy that section's `Context`. The one that catches people is
`ProcInv` — `proc_priv` needs `` `{!riscvGS, !fileG, !xv6G, !bioslotG,
!fdslotG, !irefslotG} ``, i.e. `fileG` and `fdslotG` even though nothing in
the row's spelling mentions a file or an fd. **And cap the memory while
experimenting**: `ulimit -v 25000000` before `coqc`/`make` is ~7x the largest
legitimate file in the tree, so it never bites a real build and turns this
failure into a fast one.

**AND THE PRIZE IS PER LEMMA, NOT PER FILE — measured 2026-08-27, do not
redo it.** `ProofPrintk`'s eleven `wp_printk_arm_*` exit continuations are
character-for-character identical and 35–43 % of each statement, which reads
exactly like this section's shape. Folding all eleven measured **48.40 s →
48.44 s** (`.vo` −0.18 %) on a quiet box, two reps interleaved: nothing.
`|Δ| × steps` is per PROOF, and those eleven lemmas are 15.6 s of that file
between them — 0.3–2.7 s each, so 40 % off a 0.8 s proof's Δ is ~0.3 s and
eleven of them is noise. `su_w3` is the contrasting case: ONE lemma at 26.5 s
with a 48 % entry. **Rank candidates by the lemma's own `coqc -time` cost
times its share, never by the file's cost times the share** — the file-level
metric is what put ProofPrintk top of the list.

**Still on the table in this file, not done**: its seven `iNext`s are 3.5 s at
495 ms each, against the ~60 ms `iApply bi.later_intro` costs — which the same
file already uses at thirteen other sites. See "Modalities and rewriting".

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

**The whole tree now follows this discipline** — 226 proof files converted
2026-08-22, verified by a from-scratch rebuild (every `.vo` deleted): 1297/1297,
zero errors. Measured over the ~110 files where before/after pairs were taken:

| | range | median |
|---|---|---|
| wall | −4 % … −49 % | ≈ −18 % |
| `Qed` | −6 % … −62 % | ≈ −27 % |
| `.vo` | −24 % … **+0.2 %** | ≈ −5 % |

On the reference file (`ProofPipealloc.v`, one whole-function proof, 58 posed
facts) the proof term went 26.6 M → 8.3 M nodes (−69 %) while the shared DAG
moved only −13 % — the derivations are still there, sharing subterms, but no
longer re-embedded in every following step's environment. That is RULE ONE from
the `|Δ|` side, and it is why the saving is FLAT: no sentence gets dramatically
faster, the whole tail does.

**What predicts the size of the win** is `min(peak live block net of iClears,
poses per Qed)` — `tools/instr_subgoal.py --rank` computes it. Not the file's
site count: `ProofUartinit` (27 sites, one block) got −35 % while `ProofSysExec`
(92 sites over ~30 proofs) got −14 %, and `ProofVirtioDiskInit` (127 poses, but
posed-and-cleared one at a time) got −7.5 %. It sorts candidates; it sizes the
win only to ±10 points, and `ProofSysLink` has the tree's largest block at
−14 % because most of its time is not proofmode work at all.

Four things measurement refuted, all of which looked true after the first file:
`Qed` does NOT always improve more than wall (fails below ~20-pose blocks);
`.vo` is not a proxy and can grow; peak RSS is not a reliable benefit (−37 % to
+0.2 %); and a `Löb`/`iInduction` body is NOT a special case (in-loop and
out-of-loop discounts agree — measured −56/−45, −43/−42, −26/−30).

**Do not measure this on a loaded box.** The error is BIASED, not just noisy:
eight files measured concurrently reported seven apparent REGRESSIONS that were
all 5–20 % wins when re-measured serially. One `coqc` at a time, arms
interleaved, 2–3 reps.

**The user tier (`UProof*.v`) is out of scope and should stay that way**: its
`uinstr` is a `Prop` over a pure process image, passed positionally as a Coq
term at each leaf (1016 sites, zero `iPoseProof`), so it never enters `Δ`.

`tools/instr_subgoal.py` does the edit; see
`claude-notes/projects/instr-subgoal-sweep.md` for the recipe, the traps and
what is left.

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
its callee `fkr_tail` poses for itself). Retrofit measured on that file
(77 poses over three block lemmas): 16 dead poses dropped, 56 moved to the
sentence of their first use, 57 `iClear`s added — **28.9 s → 27.1 s**.
Grep for it with "a pose whose name never appears again in the same
`Proof.`…`Qed.`"; the name is reused across the file's lemmas, so the search
has to be scoped to one proof block or every pose looks live. **That retrofit
is superseded by the subsection above** — converting the same 61 surviving
poses to `[]` subgoals is the bigger win, and it makes the dead ones vanish by
construction; the numbers here stand only as the cost of the poses themselves.

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
    the `Drw`/`Dro` frame idiom. `HartSKpt.swp_translate_kpt` carried the
    `set_solver` form until 2026-08-20, at **24.5 s for that one `assert`** —
    the whole file was 29.6 s. Its premise `HWtlb : tlb ∈ Drw` was already in
    context, so `by (apply elem_of_union_l; exact HWtlb)` is the whole fix:
    file **29.6 s → 5.1 s**. Grep for `∈ .* ∪ .*) by set_solver` before
    believing a file is intrinsically slow.
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
  `by exists (vp_lo pr + k)%nat, sl` cost **214.9 s** to close
  `vp_pend pr !! q = Some sl ∧ vs_hd sl = vs_hd sl` — a goal whose two halves
  are a hypothesis and `eq_refl`. `coqc -profile-ltac` put 99.9 % of it in a
  SINGLE `discriminate` call, and clearing the context down to one hypothesis
  at a time named the culprit exactly: `Hrsub : ring_bytes c (vp_ring pr) ⊆
  vproto_ctl c pr`, on its own, is the whole 210 s. Nothing else in that
  17-hypothesis context cost more than 0.011 s. The mechanism is that no-arg
  `discriminate` walks the local context looking for an equation between
  distinct constructors, and to decide that it `hnf`s each hypothesis's type
  WITH delta — so a `⊆`/`##ₘ` between two *computed* gmaps (here a `write_bytes`
  fold over eight ring cells, unioned into a lease) gets unfolded, and the
  goal's own triviality never gets a chance to matter.
  - **The fix is to say what the goal is**: `exists q, sl. exact (conj Hsl
    eq_refl)` in place of `by exists q, sl` took the sentence 214.9 s → 0 s and
    the FILE **227 s → 7.9 s**. Same shape as the `iPureIntro. done.` bullet
    above, one level deeper: the giveaway is again that the goal is trivial to
    read, so nobody suspects the closer.
  - **Name the hypothesis whenever you do want `discriminate`.** The same file's
    remaining cost was a bare `discriminate` in a branch whose goal was a fat
    `⊆`: `discriminate H1`, where `H1 : None = Some _` is the equation meant all
    along, skips the walk (4.1 s → 0 s across five sites). `discriminate Hreq`
    likewise.
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

### ProofIput RESISTS ALL FOUR OF THIS FILE'S LEVERS (measured 2026-08-27)

`ProofIput.v` is 113 s in the build and 2.3x the tree's median cost per
sentence, so it reads like a textbook RULE ONE file. It is not fixable by the
rules above, and here is what was tried so nobody re-runs it:

- **Naming the closer made it SLOWER.** `ip_free_locked`'s +0x30 continuation
  was 60 rows spelled inline and measured **31.7 % of Δ** at a mid-walk dump
  (2472 B of 7.6 kB, biggest entry by 2.5x) — a bigger share than the
  `ProofForkret` case that bought −24 %. One `Definition` for it did exactly
  what it should to the context (Δ 7.6 kB → 5.4 kB, `Hcont` 31.7 % → **3.0 %**)
  and cost the file **+13 s**, confirmed on a second reading. The regression is
  +8.5 s inside `ip_free_locked` itself, spread UNIFORMLY across every tactic at
  identical call counts (`iApply` +25 %, `iMod` +24 %, `iDestruct` +20 %): the
  per-step delta-unfold of a **28-argument** constant costs more than the
  smaller Δ saves. Its CALLER improved (`wp_iput_gen` −3.0 s), which is the tell
  — a fold helps whoever SUPPLIES the closer and hurts whoever USES it.
- **Sealing that constant does not rescue it, either way.** `Typeclasses
  Opaque` and `Strategy opaque` both fail identically at
  *"iSpecialize: cannot instantiate"*, and the `iEval (rewrite /X)` repair puts
  the expansion straight back into Δ, which is the thing being removed.
- **`Strategy opaque [rget] [tp_pin] [rf_upd]` is a REGRESSION here**, +11 to
  +17 s over two interleaved pairs, even though the mechanism is real
  elsewhere (`ProofPipewrite` keeps the same three lines for −6 %).
- **Hoisting inline `ltac:` is not available**: the file's 247 splices cost
  0.18–0.27 s each (27.9 s total, max sentence 1.65 s), against the ~1.55 s per
  splice that made the same edit worth 28 s in `ProofSysUnlink`.

**AND THE FIRST THREE READINGS SAID THE OPPOSITE, because the box was loaded.**
The `Strategy` arm measured 118.4 s / 119.3 s against a 122.0 s baseline at load
13.5 — a 3 % "win" — and reversed to +11/+17 s once the same interleaved A/B ran
at load 3.4. A single reading on a shared machine is worth nothing here; take
`uptime` before believing an A/B, and interleave.

### `lia` IS A GENERAL-PURPOSE CLOSER TOO, AND 180 HYPOTHESES IS A LARGE CONTEXT

**THE EXHIBITS ARE GONE, THE LESSON IS NOT.** `iris/FsEff*.v` and
`iris/FsOp*.v` were deleted (2026-08-27) — the whole-state pure
preservation layer `design/fs-state.md` §6 superseded, with no reader
left. The measurements below stand as measurements; you just cannot
open the files to re-read them. Every rule they produced applies
unchanged to any monolithic proof with a wide context.

The whole cost of the stage-F2 effect band (`iris/FsEff*.v`: eight PURE files,
no Iris, no `set_solver`, no `vm_compute`) was one tactic. `coqc -profile-ltac`
put **86.8 % of `FsEffCreateEntry.v` in `lia`** — `xlia` 70.3 % LOCAL,
`Zify.zify` 12.5 % — across 381 calls whose goals are three atoms wide. What
they cost is their CALL SITE: a monolithic whole-transaction proof carries
~180 hypotheses, ~45 of them arithmetic, two of those mentioning `Z.div`, and
every call reifies the lot and re-eliminates the divisions. Cold, that file
was **593.9 s**; it is 65.0 s now, and the band went **946 s → 133 s**.

Three fixes, in the order they paid:

1. **A side condition that is the SAME at every call site belongs in a lemma
   proved where the context is EMPTY.** Each effect proof case-splits
   `fs_dinode` through a local `Hdec` whose premise is the inode region's
   width, `0 <= z < 16 * (sb_ninodes sb / 16 + 1)`, and all 124 sites spelled
   it `ltac:(lia)`. At the ticket sweeps that identical goal measured **19.7 s
   and 12.6 s per site**; `FsEffBase.v`'s six `iblk_*_range` / `inum_*`
   lemmas make it free. That is "Inline `ltac:` in argument position" again —
   but note WHY it is worth hunting rather than tolerating: **a `lia`
   certificate reifies the hypotheses it was handed, so the PROOF TERM
   carries them too.** Those two sentences were also the whole of that file's
   53 s of `Qed`, which fell to 5 s with them and needed no separate work.
2. **`clear -H..` before a `lia` at a deep site — and use `match goal` to NAME
   the hypothesis, so one `Local Ltac` covers a whole family.** `destruct
   (bool_decide …); destruct (bool_decide …); lia`, closing the four arms of
   the links sweep from two equations already in hand, was 4.6 s; `(clear -Hc
   Hold; lia)` is free. Where the wanted hypothesis is named differently at
   every site, match it by SHAPE and pass the answer as a term:

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
   context scan. Worth ~2 % of the band — the smallest of the three, listed
   because it is the cheapest to spot.

| file | cold before | cold after |
|---|---|---|
| `FsEffCreateEntry` | **593.9 s** | 65.0 s |
| `FsEffLinkEntry` | 275.5 s | 30.5 s |
| `FsEffUnlinkEntry` | 45.3 s | 9.3 s |
| `FsEffAllocBlock` | 23.6 s | 20.6 s |
| the other four | 7.9 s | 7.4 s |

**Negative results from the same afternoon — do not redo them.** The suspects
that looked structural were all null: the common-ground `Section` closing
under `Set Default Proof Using "All"`, the seven per-file blocks of ~45
`Local Notation`s re-applying its seventeen context arguments, the `set … in
*` chains, and the ticket `mjoin` over `seq 0 (Z.to_nat (sb_ninodes sb))`.
`FsEffBase.v`, which carries the entire common-ground section, is **3.4 s**,
and it did not move.

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
- **THE CHEAPEST FIX IS USUALLY TO SPLIT THE BIG CONJUNCT OFF FIRST, and it is
  a two-line edit.** A frame is priced by (names × goal conjuncts it walks), so
  it is the ONE definition-valued conjunct in the goal — the escrow arm, the
  parked bundle, the pool shape — that makes it expensive, never the six
  points-tos. Dispatch that conjunct into its own goal with `iSplitL`/`iSplitR`
  *before* framing anything, and the frame that remains is syntactic. Measured
  on the four worst frames in the tree (2026-08-20; isolated `coqc`, per file):
  | site | what it framed past | file before → after |
  |---|---|---|
  | `IcacheEscrow.ipool_shape_to_np` ×2 | `ipool_shape_np` (∃ over a block-map big-op) | **183.6 s → 15.7 s** |
  | `ProofIput` held-arm close | `ic_payload_np`, reached past to the mirror | 100.7 s → 82.3 s |
  | `ProofIget` mid-arm re-park (bare `iFrame`) | `ic_unloaded` | 80.1 s → 52.6 s |
  | `UsertrapRes.ut_res_bare_sstc` ×2 | the residue's whole ∃ body | 23.5 s → 14.1 s |
  The two `IcacheEscrow` sentences were 90.9 s and 83.3 s — the two most
  expensive in the tree after the assumption audit, and both on the critical
  path. The rewrite is mechanical: `iSplitL "Hl"; [iExact "Hl"|]`, then
  `iSplitR "<the rest>"` around the arm's own proof, then frame the tail.
- **WHEN EVERY CONJUNCT IS DEFINITION-VALUED, THERE IS NO BIG ONE TO SPLIT OFF
  — build the WHOLE bundle.** The two closing-bundle lemmas
  `ProofSyscall.sysc_filestat_env` and `sysc_fclose_fs_env` assemble
  `SpecFilestat.filestat_fs_env` (13 conjuncts) and
  `SpecFileclose.fileclose_fs_env_nopid` (16), and their tails are `dev_inv`,
  `disk_geom`, an `is_lock` over `disk_res`, `bslots`, `fileclose_ic_env`,
  `fileclose_bm` — every one a definition, so every (name × conjunct) attempt
  is a conversion and no single `iSplitL` helps. Named `iFrame`s over them cost
  **33.1 s and 58.4 s** — 91 s of a 123 s file, with nothing else in it above
  1.3 s. Replaced by the `iSplitR; [iExact "H"|]` chain in the goal's own
  conjunct order (the idiom `sysc_fs_fabric` in the same file already used),
  the **file went 122.7 s → 31.7 s** and both statements left the profile
  entirely. Two tells that you are in this case rather than the split-one-off
  case above: the lemma's whole job is to REASSEMBLE a named bundle, and its
  own siblings in the file already spell out the chain.
  **The three worst remaining instances were the top three statements in the
  tree**, and all three are the same edit — the bundle's conjunct order, one
  `iSplitR`/`iSplitL` per row, `iExact` at each:
  | site | the bundle | file before → after |
  |---|---|---|
  | `ProofMain` `Hpersist` assert | `FirstTok.first_boot_persist`, 16 rows (one a 50-fold `ic_sleeplocks` big-op) | **108.8 s → 32.7 s** |
  | `FsSyscalls.fs_world_all` | the 20-row unpack of `fs_world` | **30.7 s → 6.7 s** |
  | `ForkretParkClose.forkret_park_pkg_intro` | `forkret_park_pkg`, whose 7th row is the residue closer | **31.2 s → 2.6 s** |
  Three further instances, all the same edit (2026-08-21):
  | site | the bundle | before → after |
  |---|---|---|
  | `ProofForkret`'s `first_persist_pre` premise | `FirstTok.first_boot_persist`, 17 rows | statement **62.7 s → 0** |
  | `ProofForkret`'s `Hfab` assert | `SpecKexec.fs_fabric`, 16 rows | statement **61.0 s → 0** |
  | `UsertrapRes`, ELEVEN sites | the residue's ∃ body, whose last row is `ut_env` → `proc_priv` → `tf_page` | file **60.1 s → 7.1 s** |

  `UsertrapRes` is the one to read: no single row is enormous and the frames
  were only 4–6 s each — it was the COUNT that made the file, and no seal
  fixes that (sealing `tf_page` locally there was worth 8 s of the 53).
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
  `ut_caps` back with `iFrame "Hpi Hkd Hks Hdev Hrest Hown"` cost **7.5 s of a
  14.1 s file** — its tail is `is_lock`s over `disk_res` / `kmem_res` and an
  `is_ftable`, and each match attempt against one of those is a conversion over
  a big resource. The `iSplitL "H"; [iExact "H"|]` chain over the same six
  conjuncts is a syntactic check each: **file 14.1 s → 6.6 s**, and the
  statement leaves the profile entirely (nothing in the file is above 1 s).
- **Extracting a persistent fact out of a bundle must not take the bundle
  APART.** `ut_res_bare_sstc` destructured `ut_caps` to read one
  `sstc_enabled` out of it and then rebuilt it conjunct-by-conjunct inside the
  residue's body. Doing the extraction in a five-line lemma over ONE hypothesis
  and handing the bundle back whole is the fix — and note the intermediate
  attempt made it WORSE (16.9 s → 24.4 s) because the rebuild moved rather than
  disappeared. The tell that you are in this case: the proof reads differently
  from its own siblings, which pass `Henv` straight through.
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

- **A BIG-OP UNDER A TRANSPARENT NAME IS AN `iFrame` BOMB, AND SEALING IT IS A
  ONE-LINE FIX FOR EVERY CALL SITE AT ONCE** (measured 2026-08-21). `iFrame`'s
  `Frame` search unfolds a transparent constant to get at the `big_sepL`
  underneath, and then tries every candidate hypothesis against every element.
  `InodeInv.inode_blocks` is `[∗ list] i ∈ seq 0 MAXFILE` with `MAXFILE = 268`,
  and it is the last-but-two conjunct of `IcacheEscrow.ic_loaded` — so the
  bundle rebuild every fs proof ends with (`iSplitL "Hdlk"; [iExact "Hdlk" |].
  iFrame.`) paid ~50 s. **Seventeen statements between 48.9 s and 62.7 s, in
  twelve files, were all this one shape**; `Global Typeclasses Opaque
  inode_blocks` removed every one of them and the tree's serial tail with it:
  | | before | after |
  |---|---|---|
  | wall span | 891 s | 467 s |
  | critical path | 758 s | 467 s |
  | effectively serial (≤1 in flight) | 378 s | 58 s |
  | worst non-`Qed` statement | 62.7 s | 6.7 s |

  Per file (CPU): ProofNamex 277→137, ProofCreate 252→161, ProofNamexTr
  200→101, ProofSysLink 186→86, ProofSysChdir 149→59, ProofIlock 93→47,
  ProofFilestat 75→23. Diagnose it by the *uniformity*: a dozen sentences all
  within a second of each other, in unrelated files, is one shared conjunct,
  not twelve local problems.
  - **`Global`, not bare `Typeclasses Opaque` — the bare form is
    compilation-local.** `ProcDefs.v:84` and `ProcInv.v:57` seal
    `tf_words`/`tf_tail`/`tf_page` twice for exactly that reason, and their
    comment records it. The consequence nobody had drawn: **every other file
    in the tree still sees those three transparent**, and a local repeat is
    worth ~8 s in a file that frames past `proc_priv` (measured on
    `UsertrapRes`).

    **THAT SEAL IS NOW `Global` (2026-08-27), and the old advice here -- a
    repeat line where the profile says so, not a global seal -- was wrong on
    the measurement.** Five more files carried the same 1.5-2.1 s frame and
    never got a repeat, which is the uniformity tell for one shared conjunct.
    One `Global` line in `ProcDefs.v` (and `UsertrapRes`'s local repeat
    dropped as redundant) measured, isolated, min of two runs:
    | file | before | after |
    |---|---|---|
    | `ProofAllocproc` | 35.74 s | **26.77 s** |
    | `ProofSyscall` | 48.36 s | 47.17 s |
    | `UserActiveClass` | 8.92 s | 8.45 s |
    | `ProofUserinit` | 13.59 s | 13.49 s |
    | `ProofKforkB5` | 8.44 s | 8.64 s (no benefit) |
    `ProofAllocproc` is nine tenths of it, so the lesson is not "seal
    everything globally" -- it is that a LOCAL seal hides the size of the
    prize, because the files that would have paid for a repeat never appear
    in the profile as a cluster until you look for one.
  - `rewrite /X` and `unfold X` are unaffected by the seal, so the sites that
    genuinely take the big-op apart keep working, and a `Timeless` instance
    proved `rewrite /X. apply _.` still goes through. Nothing in 1293 files
    broke on the `inode_blocks` seal.
- **BREADTH IS NOT THE PREDICTOR -- A BIG-OP BODY IS.  Measured 2026-08-27, so
  do not re-run it.** The tempting next step after sealing a few big-ops is to
  seal the constants NAMED in the most files, whatever their body. It does not
  pay. Ranked by how many other files name them, the top unsealed iProp
  definitions are `pc_is` (483 files), `sie_cap_gpr` (418), `wp_next` (415),
  `instr` (332) -- and none of them has a big-op body. Sealing `pc_is` and
  `sie_cap_gpr` in `ProofSysUnlink`, then the tree's most expensive file (see
  the case study above; it is 133 s now), measured
  **150.36 s -> 151.49 s**: no gain, slightly negative. `wp_next` cannot be
  sealed at all -- it is the WP continuation former that every proof
  `iIntros` THROUGH, so the seal fails at `iIntro: cannot turn (wp_next ...)`.
  The mechanism explains it: `iFrame`'s cost is (candidate hypotheses x
  ELEMENTS of the goal conjunct), so unfolding a non-big-op is cheap however
  many files do it. Compare the same experiment on bodies that ARE big-ops:
  `bio_ctx` (92 files) bought 9.3 s in one file, `ic_sleeplocks` (NINODE) 4.7 s,
  `word_pointsto` (8 bytes) 3.8 s -- while `disk_res`, a 47-line body with one
  `∃` and no big-op in 98 files, bought 1.0 s. **Filter candidates by
  `big_sep`/`[∗` in the body first; sort by breadth only within that set.**

- **AN `∃` OVER A BIG-OP ALREADY SEALS IT — measured 2026-08-27, do not re-run.**
  `FdSlots.fd_frags` is a sixteen-element big-op (one `fd_st` per descriptor)
  and it rides in `UsertrapRes.ut_own` beside `proc_priv`, so it is in the
  goal of every syscall arm: exactly the profile that paid for `tf_page` and
  `inode_blocks`. It buys **nothing**. `Global Typeclasses Opaque fd_frags
  fd_frags_any`, measured isolated, min of two runs:
  | file | unsealed | sealed |
  |---|---|---|
  | `ProofSyscall` | 45.42 s | 45.87 s |
  | `ProofSysPipe` | 34.83 s | 35.11 s |
  | `ProofAllocproc` | 26.47 s | 26.30 s |
  | `ProofKexit` | 16.06 s | 16.12 s |
  | `ProofUserinit` | 10.81 s | 10.90 s |

  Every delta is inside the run-to-run spread (0.3–0.6 s). **The mechanism is
  the reason, and it generalises:** what these files actually hold is
  `fd_frags_any γ = ∃ sts, fd_frags γ sts`, and `iFrame` will not instantiate
  an existential to go looking inside it — so the big-op is never walked and
  there is nothing for a seal to prevent. Check the shape a consumer holds,
  not the shape of the definition: **if the big-op is under an `∃` at every
  use site, it is already sealed and the `Typeclasses Opaque` is dead
  weight.** `tf_page` and `inode_blocks` are bare in the goal, which is why
  they paid.

  Priced `ProcInv.proc_ofiles` (16 slots, bare inside `proc_priv`, hence in
  every syscall goal) the cheap way in the same round — a LOCAL `Typeclasses
  Opaque` in the consumer, no accessor refactor, the technique this file uses
  for `pc_is`/`sie_cap_gpr` above: `ProofSyscall` 45.66 s against 45.42 s
  unsealed. Also nothing. Sixteen elements is an order of magnitude under the
  big-ops that paid (4096, NINODE, 8 × 92 files), and `proc_priv`'s frame cost
  is dominated by `tf_page`, which is already sealed. **Do not pay the eight
  accessor `rewrite /proc_ofiles`es it would cost.**
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

  Second file (`BioInv`, 2026-08-20): four such instances over the buffer
  escrow's arms were 31.5 s of a 41.5 s file — `buf_parked_timeless`'s single
  `apply _` alone was 19.7 s — and the same `tl_struct` took the file to
  **20.1 s**. The dispatch must be SYNTACTIC:
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
- **PEEL A CHAIN BY `apply`, NEVER BY `erewrite` — an equation lemma builds an
  `eq_ind_r` motive over the whole remaining term at every step.** `goodb_bind`
  is stated as `goodb D (bind m f) s = goodb D (f x) s`, so
  `repeat (erewrite goodb_bind by (vm_compute; reflexivity))` re-copies the
  entire monadic tail once per bind — and once a continuation has been
  instantiated with symbolic bitvector data the tail is large. Ltac profiling
  is what settles it: **81.5 % LOCAL to the `erewrite`**, against 3 % in the
  `vm_compute` side conditions and 11 % in their `reflexivity` — i.e. the side
  conditions everyone suspects are not the cost. The intro form
  (`goodb_bind_i : … → goodb D (f x) s = true → goodb D (bind m f) s = true`,
  one line off the equation) has the same two side conditions and no motive,
  and the proof term becomes a chain of applications, which takes the `Qed`
  down with it: `WpGprCsrwA.goodb_legalize_menvcfg` **18.6 s → 6.9 s of tactic
  and 18.0 s → 9.4 s of `Qed`**, file 46.3 s → 25.9 s. Not a sweep: the same
  `goodb_step` in `WpSconfCsr` / `WpGprCsrwC` costs ~1.4 s, because nothing has
  put a symbolic value in their tails.
- **WHAT IS LEFT OF THAT PEEL IS THE `eapply` ITSELF, and five further
  interventions all measured null** (2026-08-20; do not redo them). Ltac
  profiling: **61.8 % LOCAL to `eapply goodb_bind_i`**, 30 % `reflexivity`,
  8 % `vm_compute`. Unrolling the `repeat` shows the cost is not spread — the
  five steps are 2.4 s, 2.1 s, 2.0 s, then under 0.3 s each — i.e. it tracks the
  size of the CONTINUATION the step has to retype, which is exactly what a
  one-node-at-a-time peel cannot avoid. Tried and within noise: `cbv beta`
  before the loop; `cbv beta` after every step (worse); `vm_cast_no_check
  (eq_refl true)` for the `goodb` side condition; a `lazymatch` dispatch on
  `bind`/`bind0` instead of `first` (so no branch ever fails); and a
  `Hint Resolve` database of the per-leaf `exec_*` lemmas so the exec side
  condition is a lookup rather than a `vm_compute` (6.25/6.38 s against a
  6.40/6.58 s baseline). Getting below this needs a different formulation — a
  multi-bind peel lemma, or a `goodb` that computes without touching the data —
  not another tactic.
- **`Qed` re-checks and therefore DOUBLES every `vm_compute`** — the kernel
  re-runs the reflexivity check at `Qed` time, so a lemma whose tactic is 50 s
  of `vm_compute` costs ~100 s of wall clock (measured: `FsImgCheck.fsimg_wf_ok`
  65.9 s tactic + 62.6 s `Qed`). Budget 2× the `-time` figure for any
  vm_compute-heavy lemma, and prefer one big boolean sweep with lookup spec
  lemmas over N per-item `vm_compute` lemmas — the sweep pays the 2× once.
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
  Measured, isolated `coqc`: **`FsImgCheck` 195.4 s → 99.5 s** (its
  `fsimg_wf_ok` alone was 128.5 s of that), **`ElfKernel` 54.0 s → 28.9 s**,
  **`ElfUser` 25.1 s → 14.0 s**. The whole tactic column of those files drops
  to zero and only `Qed` pays.
  - **IT MUST BE THE RIGHT-HAND SIDE.** `eq_refl r` casts `r = r` to `l = r`,
    so the VM evaluates the heavy side once; the mirror spelling
    `eq_refl l` makes it evaluate that side TWICE and is **worse than the
    `vm_compute` it replaces** — `ElfKernel` 78.3 s against a 54.0 s
    baseline. The two spellings read identically; only the A/B tells them
    apart, so measure after writing one.
  - The cost is diagnostic, which is why this is for the HEAVY sentences and
    not a sweep (647 `vm_compute. reflexivity.` sites in the tree, nearly all
    sub-second): a disagreement now surfaces at `Qed` as a kernel conversion
    failure with no goal in view. Put `vm_compute. reflexivity.` back on the
    one failing lemma to see it.
- **AND MEASURE ON A QUIET VM.** Three of those five variants first read as
  regressions of 20–30 % (25 s → 31 s on the same file), purely because another
  tree was building; the same variants re-measured at load 9 were within 2 %.
  `uptime` before an A/B is worth the second it costs — the builder is SHARED,
  which the isolation rule at the top of this file assumes away.
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

The READ-ONLY twins (`mm_ro_open` in HartMFrame, `mc_ro_close` in
WpInstrConfig) were written on 2026-08-20 for exactly one site that had been
missed: `WpInstrConfig.mc_ro_acc`, whose goal carries a whole `mc_rs` tower
inside its ∀-closure, so its `rewrite mm_ro_split` was **24.9 s** — file
38.5 s → 13.6 s once both bridges are applied instead. **Where the goal is
small the same `rewrite` is free**, which is why the other five
`mm_rw_split`/`mm_ro_split` sites in that file and in `InstrBytes` were left
alone: read the `.v.timing` cost of a candidate site, never its shape.

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
  **Where the file already uses `set`, deleting the trailing `change` is the
  free half of that fix and needs no other edit**: the `change` is then a
  whole-goal conversion that folds nothing, because `set` has already folded
  every occurrence. 45 of them in `ProofForkret` cost **1.44 s** of a 30.3 s
  file (30.3 s → 28.9 s to delete, proof script otherwise untouched). Grep is
  `set (X := T).` immediately followed by `change T with X.` with `T` equal up
  to whitespace.
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

## `Print Assumptions` is a whole-tree walk, and it is not on the build path

The assumption audit lives in **`iris/SystemAssumptions.v`**, run by `make
audit` / `make audit-only` and by CI after every build (output in the run's
step summary). It is deliberately **not** a row in `iris/_CoqProject` — the
commented-out row there is what tells `tools/proof_coverage.py --check` the
omission is on purpose. It used to be a line at the bottom of
`SystemAdequacy.v`, and that is what it cost (measured 2026-08-20, isolated
`coqc` on the GCP VM):

| | |
|---|---|
| `SystemAdequacy.v` with the statement | **98.6 s**, peak RSS 2.47 GB |
| the same file without it | **3.6 s**, peak RSS 0.85 GB |

So one sentence was 96 % of the file — and `SystemAdequacy.v` is the strictly
serial tail of the build (`BootChain → BootShared → SystemAdequacy`, all 1×),
so it was ~30 % of a clean build's wall clock, re-paid whenever anything in the
1000-file cone changed. CI still pays it; a developer's `make proofs` no
longer does.

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
lemmas through sealed functor applications. Controlled A/B, 400 lemmas with
byte-identical proof terms:

| packaging | `Print Assumptions` over all 400 |
|---|---|
| plain top-level lemmas | 0.18 s |
| inside `Section` + `Context` | **0.49 s (≈ 2.7×)** |
| inside an applied sealed functor | 0.28 s (≈ 1.5×) |

So the command is ~linear in total proof-term bytes in the cone (302 MB of
`.vo` in `iris/`) with a 2–3× constant on top. It is therefore also a **proxy
metric for whole-tree proof-term size**: a jump in the audit's time is a jump
in what every rule in this file is fighting.

- **Negative results — do not redo these.** It is not disk I/O: `Require
  Import SystemAdequacy` — loading the entire cone — is 0.76 s, and a *second*
  identical `Print Assumptions` in the same process costs full price again
  (94.5 s, then 100.6 s). Nothing is cached between calls, so **batching audits
  in one file does not amortize** — adding an `xv6_fs_adequacy_xv6Σ` audit
  beside the existing one would roughly double the bill, not ride along. Nor
  does auditing at lower altitude decompose the cost: `Print Assumptions
  BootChain.boot_hart_primary` alone is 91.4 s of the 94, against 6.5 s for
  `BootShared.boot_shared_alloc` and 2.4 s for
  `RiscvAdequacy.riscv_power_adequacy`. `Set Printing Depth` and the printing
  of the seven-odd axioms are free.
- **`-noglob` on the audit compile is load-bearing**, not tidiness. The nightly
  dead-import sweep shortlists candidates from whatever `.glob` files it finds
  in `iris/`, and `SystemAssumptions.v`'s single `Require` is the one thing it
  must not lose; with no `.glob` the file is reported UNANALYSED and left alone.

### The 95 s figure is stale: the audit is now 379 s (re-measured 2026-08-22)

Same command, same VM, `iris/` at 344 MB of `.vo` — up only 14 % from the
302 MB the 95 s was measured at, so **the cone widened, the tree did not**.
Budget the audit at ~6½ minutes and treat the number as a tripwire: it is the
proxy metric this section says it is, and it just moved 4×.

Measured beside it, on the same tree (isolated `coqc`, one `Print Assumptions`
per process):

| constant | wall | peak RSS |
|---|---|---|
| `SystemAdequacy.xv6_power_adequacy_xv6Σ` (the audit) | 379 s | 5.8 GB |
| **`Forkret.wp_forkret`** | **336 s** | 5.5 GB |
| `UserretClosedD.wp_userret_closed` | **334 s** | 5.2 GB |
| `Kexec.wp_kexec_sconf` | 149 s | 4.0 GB |
| `Fsinit.wp_fsinit_sconf` | 85 s | 2.6 GB |

**So "auditing forkret takes forever" is not about forkret.** `ProofForkret`'s
own proof terms are ~2 s of the 336; the other 334 is the closed trap loop it
concludes in, and every contract that ends in `UserretClosedD` pays exactly
that. Cutting `ProofForkret.v`'s compile time by a third (2026-08-22) moved its
audit by nothing — 336 s → 343 s, i.e. run-to-run noise, with a byte-identical
axiom list. Do not go looking for the cost in the file you are auditing;
audit its deepest callee first and see whether the difference is worth anything.

**Where the time actually goes** (`perf record` over the 336 s run, flat self
time; the tree's opam switch carries OCaml symbols, so this is readable):

| cluster | share |
|---|---|
| `Cooking.*` — the SECTION DISCHARGE (`substrec`, `share`, and the `Int.Map` memo behind it, plus the `Constr.map_with_binders` / `CArray.map` it drives) | **~40 %** |
| `Mod_subst.map_kn` + the `Names` hashing/compare it drives — the FUNCTOR substitution | ~12 % |
| `Assumptions.traverse` / `traverse_inductive` / `fold_with_full_binders` — the walk the command is nominally doing | ~8 % |
| OCaml GC (`caml_oldify_one`, `do_some_marking`) | ~4 % |

The command spends five times as long re-COOKING terms out of their sections as
it does walking them, which is the mechanism behind the 2.7× section-packaging
figure above. The lever, if anyone wants it, is per-lemma `` `{!riscvGS Σ, …} ``
binders instead of `Section` + `Context` in the hot cone — `ProofForkret.v`
already writes its lemmas that way, which is part of why it contributes so
little. That is a ~778-file change, so it is a campaign, not a fix.

- **GC tuning does nothing — do not redo it.** `OCAMLRUNPARAM=s=8M,o=200`,
  `s=64M,o=400` and `s=256M,o=1000` against a 336 s / 5.5 GB baseline came back
  350 s, 350 s and 342 s (all three run concurrently, so slightly inflated).
  `s=256M,o=1000` doubles peak RSS to 11 GB and buys ~2 %. Consistent with the
  perf profile: GC is 4 % of the run.


## Smaller traps

- **`lia` cannot do a nested-division chain** even mword-free and iris-free
  (`E mod 32 = 0 → E/32 mod 4 = 0 → … → E = 0` comes back "cannot find witness").
  It has no theory of iterated division; stage it with `Z_div_exact_2` +
  `Z.div_div`.
- **A `!` in `rewrite` always pays one FULL failing pass, and it is not free
  when the lemma is expensive to MATCH.** `rewrite !H` fires until failure, so
  it runs one more match attempt than the goal has occurrences — and that
  attempt is a complete setoid traversal of the goal, instance search included.
  Measured (`ProcPtOwn.uva_dom_delete`, 2026-08-21): `rewrite
  elem_of_difference !elem_of_uva_dom` over a goal with exactly TWO
  `va ∈ uva_dom _` occurrences cost **3.3 s in the file / 4.3 s isolated**;
  naming the two rewrites (`… elem_of_uva_dom elem_of_uva_dom`) cost **0.33 s**,
  a ~10× cut with an identical proof term, and it was the slowest sentence in a
  5 000-line file by 4×. What makes the failing pass expensive is the LHS:
  `uva_dom` is a `list_to_set (mjoin (… <$> map_to_list _))`, so every candidate
  subterm drags the `elem_of` instance chain behind it. The rule is NOT "avoid
  `!`" — 261 files use it, nearly all harmlessly. It is that a `!` over a
  set-membership lemma with a COMPUTED carrier, in a goal big enough to
  traverse, should be spelled out at the occurrence count the goal actually has.
  (Same family as the two bullets below: what costs is the tactic that fails.)
  **`rewrite n!L` is the spelling that keeps the `!` reading without the
  failing pass** — it performs exactly `n` rewrites and never attempts an
  `n+1`th. Second instance (`FsCfgBoot.v`'s coverage-remainder `set_eq`,
  2026-08-21): `rewrite !elem_of_difference !elem_of_union` over a goal with
  six differences and four unions, whose carriers are five *computed* sets
  (`log_region_set`, `ireg_blk_set`, `fs_live_blocks`, `fs_bitmap_spent`), was
  **6.1 s** — two whole-goal traversals for nothing. `rewrite
  6!elem_of_difference 4!elem_of_union` took the file **15.4 s → 6.4 s**.
  Counting is mechanical: differences on both sides of the `↔`, unions in the
  set the right-hand side names. Third instance (`VirtioProto.vinit_dma_dom`,
  2026-08-25): `rewrite !dom_union_L !range_map_dom ring_bytes_dom_eq` was
  **17.3 s**, of which **16.0 s** was the one failing `dom_union_L` pass —
  deciding that `range_map (vc_used c) 4096 _` is not a `∪` unfolds
  `range_map`'s 4096-step `foldr`. `rewrite 2!dom_union_L 2!range_map_dom …`
  is **2.1 s**. The carrier does not have to be a set for this to bite: a
  `gmap`-valued definition over a literal size is just as expensive to refute,
  and here the *successful* rewrites cost 2 s between them for the same reason.
- **`rewrite` ABSTRACTS, `exact` only UNIFIES — and a `nat` NUMERAL makes the
  gap enormous.** `rewrite H` must locate the occurrence, abstract it and build
  a motive that conversion then carries; `exact`/`apply` of the same equation
  only unifies two terms. Where the rewritten subterm holds a `nat` numeral the
  difference explodes, because `nat` numerals are UNARY: `4096%nat` is a
  4096-constructor term, so `umem_write _ _ 4096 _` drags all 4096 through
  every conversion the motive forces. Measured on one goal
  (`ProofUvmcopy.v:1695`, 2026-08-21) — all three close the SAME goal with the
  same proof term:

  | | |
  |---|---|
  | `rewrite <- (umem_write_app … 4096 …)` | 13.7 s |
  | the same, run length a VARIABLE not a literal | 5.1 s |
  | `transitivity <middle>` + `apply`/`exact` | 0.09 s |

  So ~2.7× of it is the literal and the rest is the motive; killing both is
  ~150×. The shape to reach for is `transitivity <the middle term>` and then
  `apply`/`exact` on each side — it names the intermediate explicitly, which
  reads better than a backwards rewrite anyway. This is the PURE-GOAL cousin of
  "Directed entailments, not `⊣⊢` rewrites" above; that section is the same
  trade inside a proofmode goal, where RULE ONE supplies the blow-up instead.
  **The cheapest instance of it is `rewrite L. reflexivity.` where `L` already
  closes the goal**: `ProofKexecPinned.v:651`'s `rewrite (fv_of_file_byte …).
  reflexivity.` builds a motive over the whole `file_byte`/`fv_of` term only to
  throw it away one line later — `exact (fv_of_file_byte …)` is the same proof
  term with no motive, and took the statement from **5.5 s** to nothing (file
  13.4 s → 10.0 s). Grep for a `rewrite <lemma>.` immediately followed by
  `reflexivity.`
- **In a `first [ … ]` alternation, put the CHEAP-FAILING branch first.** The
  cost of a tactic that FAILS grows with the proof term, so an alternation
  leading with an expensive-to-fail branch pays that cost at every use — 42 s
  over one function, purely in the failures of the first branch, fixed by
  reordering and nothing else. `exact`/`assumption` fail cheaply on a type
  mismatch; `rewrite … in H` and `congruence` do not. Second measurement
  (`HartLift2.wp_hsil2_node`, 2026-08-20): one `all: first [RegWrite | RegRead |
  announce]` over the monad node type's constructors, where the RegWrite branch
  fails only after two `case_decide`s, two `injection`s, a `set_solver` and an
  `iMod` — so every announce-class and RegRead goal paid that whole prefix.
  Reordered announce < RegRead < RegWrite, nothing else changed: **16.2 s →
  ~0.1 s, file 18.2 s → 2.5 s.** Each branch still ends by closing its own
  goal, which is what makes reordering sound — `first` commits only to a branch
  that finishes.
- **A branch order is only worth changing where the branches FAIL, and a
  nineteen-wide `first [apply …]` over a family of lookup lemmas is NOT that
  case** (negative result, 2026-08-20). `HartMFrame.mm_rs_lk` /
  `WpInstrConfig.mc_rs_lk` cost 5.7 s / 6.1 s at their `all:` sites, which
  looks exactly like the trap above; replacing the alternation with a
  `lazymatch` that dispatches on the register in the goal changed nothing
  (5.65 s → 5.54 s). The towers are already `Global Opaque`, so the failing
  `apply`s are cheap and the cost is in the ~19 SUCCEEDING ones. Do not redo
  this; if these sites ever matter, the lever is the number of goals, not the
  dispatch.
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
