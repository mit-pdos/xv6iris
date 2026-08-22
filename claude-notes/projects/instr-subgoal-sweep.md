# The instr-subgoal sweep

**Status (2026-08-22).** The discipline is settled and measured; `ProofPipealloc.v`
is the landed reference conversion (`baabee94`). What is left is the sweep: 214
more files still pose their instruction facts. The rule itself lives in
[`../optimization.md`](../optimization.md) under "Do not pose instruction facts
AT ALL"; this file is the RECIPE and the SCOREBOARD.

## 1. The discipline, in one line

A leaf lemma's `instr pc rvc ast` premise never arrives as a hypothesis. Leave it
as a `[]` in the specialisation pattern and close the subgoal on the spot from
the persistent `kernel_text`.

```coq
    (* before *)
    iPoseProof (pai_02 with "Htext") as "Hi02".       (* ...40 lines earlier *)
    iApply (wp_csdsp_s_sconf … with "Hcg Hpc Hi02 Hr40").

    (* after *)
    iApply (wp_csdsp_s_sconf … with "Hcg Hpc [] Hr40").
    { iApply (pai_02 with "Htext"). }
```

Why it pays: RULE ONE says `tree ≈ 2 × (#proofmode steps) × |Δ|`. A block of 60
posed facts is 60 extra entries in `Δ` re-embedded in the term of every step that
follows, and a whole-function proof has ~1700 of them. Deleting the block is a
`|Δ|` reduction, so it discounts the ENTIRE proof, flatly. Measured on
`ProofPipealloc.v`: wall −46 %, `Qed` −61 %, proof-term tree −69 %, `.vo` −18 %,
peak RSS −29 %. The table is in `optimization.md`.

## 2. The mechanical recipe

`tools/instr_subgoal.py` does the whole edit. It reads the hypothesis-name ->
lemma-name map OFF THE POSE LINES, so no per-file prefix (`pai_`, `fci_`,
`sdi_`, …) has to be guessed, and it refuses to touch a file where some
reference to a posed name is not a conforming call site. Verified to reproduce
the hand-landed `ProofPipealloc.v` conversion byte for byte.

**Step 1 — check.** `--check` changes nothing and exits 1 if the file needs hand
work:

```sh
tools/instr_subgoal.py --check iris/Proof*.v
```

```
iris/ProofBmap.v             posed  66  sites  75  CLEAN
iris/ProofIget.v             posed  58  sites  64  HAND WORK: Hi3c x1
```

`CLEAN` means every reference to a posed fact is a `with "Hcg Hpc <hyp> …")`
sentence ending on its own line. `HAND WORK` names the hypotheses used in some
other shape (a bare `iApply ("Hi3c")`, an `iSpecialize`, a use inside an
`iAssert`ed continuation, a leaf whose hypothesis order is not
`Hcg Hpc <instr> …`). Convert those sites by hand first, then re-run `--check`.

**Step 2 — convert.**

```sh
tools/instr_subgoal.py iris/ProofBmap.v
```

It deletes the pose lines (including lines carrying two or three poses), rewrites
each call site to `[]` plus a focused `{ iApply (<lemma> with "Htext"). }`, and
re-indents each brace to its `iApply`'s own indent.

**Step 3 — read the diff.** The conversion must not change the statement. Only
pose lines and specialisation patterns move; if `git diff` shows anything else,
stop.

**Step 4 — compile it, ALONE, on the VM.** Never `make` (see §3).

```sh
./gcp-rocq/run-on-gcp --sync-only
./gcp-rocq/run-on-gcp --no-sync bash -c 'cd /mnt/rocq/trees/<tree>/iris &&
  rm -f F.vo F.vok F.vos F.glob &&
  /usr/bin/time -f "WALL %e maxrss %MkB" opam exec --switch=/shared/xv6rocq -- \
  coqc -time -async-proofs off -R . xv6iris -R ../model-xv6iris Riscv \
    -R ../kernel-rocq Kernel -R ../user-rocq User -w -notation-overridden F.v \
    > /mnt/rocq/F.time.log 2> /mnt/rocq/F.wall.log; echo exit=$?;
  grep WALL /mnt/rocq/F.wall.log; grep "\[Qed" /mnt/rocq/F.time.log; ls -l F.vo'
```

Run that command ONCE BEFORE converting and once after, so the pair is
comparable; back-to-back runs on the 192-vCPU box are stable to ~1 % even under
someone else's build. Sum the sentence times with

```sh
awk '{for(i=1;i<=NF;i++) if($i=="secs") s+=$(i-1)} END{print s}' F.time.log
```

## 3. The traps

- **The `[]` subgoal usually comes first, but that is a property of the LEAF,
  not of the tactic.** Goals come out in pattern order, so a site that already
  carries an earlier `[]` with its own brace takes the new brace SECOND
  (`ProofScheduler`, three sites). Worse, a leaf carrying an unresolved PURE
  premise generates it AHEAD of the instr goal — `wp_andi_s_sconf` does, and the
  inserted brace then hits the pure goal and dies with *"iStartProof: not a BI
  assertion"* (`ProofIput`, one site). Both are one-line fixes: swap the braces.
  Always use a focused `{ … }`, never `; [ … | ]` — a site with a `[Hr40]`
  pattern later in the string produces three goals, not two.
- **`[]` splits only the SPATIAL context**, so `#Htext` — and every other
  persistent hypothesis — is still there to close the subgoal with. That is the
  whole reason this works.
- **Never run `make` for this.** Two `make`s in the same remote tree race and die
  with *"Cannot find a physical path bound to logical path"*, which reads like a
  broken switch (see `remote-build-gcp.md`), and a plain `make` on the VM can
  re-dump `kernel-rocq/`. Compile the single file with `coqc`. Several agents
  compiling DIFFERENT `Proof*.v` files concurrently in the same tree is safe —
  they are leaves, so nobody reads the `.vo` another is writing.
- **The conversion must not change the statement.** Only pose lines and
  specialisation patterns move. If the diff touches anything else, the regex
  over-matched.
- **A `Löb`/`iInduction` body is NOT a special case — measured, and the caveat
  this line used to carry was wrong.** Splitting the `-time` log by the loop
  body's byte range on three loop files: `ProofScheduler` −56 % in-loop vs −45 %
  out, `ProofIget` −43 % vs −42 %, `ProofKwait` −26 % vs −30 %. The in-loop and
  out-of-loop discounts agree everywhere, and the most loop-dominated file
  discounts MORE inside the body. Re-deriving against `kernel_text` once per
  iteration is swamped by the `|Δ|` discount. Convert loop files with the same
  expectations as loop-free ones.
- **Multi-pose lines.** Some files put two `iPoseProof`s on one line; the
  converter handles them. `--check`'s `posed a/b` prints distinct hypothesis
  NAMES over pose LINES, and the two differ whenever a file reposts a name.
- **A hypothesis name bound to two DIFFERENT lemmas is RESOLVED PER SITE, not
  refused.** Proof-local scopes legitimately rebind a name to a different
  instruction — `ProofIput` binds `Hi3a` to `ipi_38` early (an off-by-one in the
  file's own naming) and to `ipi_3a` 3000 lines later; `ProofKwait` binds `Hie0`
  to `kwi_e0` and then to `kwi_ee` in the next lemma. The first converter used a
  global last-pose-wins map and emitted a wrong-but-plausible lemma at the early
  sites, with `--check` calling both files CLEAN; it fails LOUD (`iApply: cannot
  apply (instr …)`, since a mismatched fact cannot unify with the leaf's pc), so
  nothing false can be proved that way, but it cost two agents a compile round.
  The converter now resolves each site against the **nearest preceding pose**,
  which is how the proof itself reads. Validated the only way that counts: on
  pristine `ProofKwait` it reproduces the agent's hand fix **byte for byte**, and
  on `ProofIput` it reproduces everything but the brace-order fix below. That
  unlocked `ProofSysLinkTails`, `ProofSysOpenTails`, `ProofSysUnlinkTails`,
  `ProofAcquiresleep` and `ProofSysPause`, all now CLEAN.
- **A stray reference need not be a use at all.** `ProofIget`'s lone
  non-conforming reference was the file-header COMMENT quoting a leaf
  application. Read the site before assuming it needs a proof change.

## 4. What the sweep measured

Twenty-two files converted 2026-08-22, each measured with one pristine and one
converted single-file `coqc -time -async-proofs off` run, back to back on the
VM.

| file | sites | wall | `Qed` | `.vo` |
|---|---|---|---|---|
| `ProofScheduler` | 57 | 30.1 → 15.4 s (**−49 %**) | 4.76 → 1.81 (−62 %) | −17.5 % |
| `ProofPipealloc` (reference) | 72 | 47.6 → 25.6 s (−46 %) | 7.68 → 3.02 (−61 %) | −18 % |
| `ProofIget` | 64 | 53.3 → 31.0 s (−42 %) | 9.67 → 4.54 (−53 %) | −10.9 % |
| `ProofProcinit` | 63 | 24.0 → 16.8 s (−30 %) | 3.48 → 2.05 (−41 %) | −9.4 % |
| `ProofKwait` | 99 | 32.0 → 22.8 s (−29 %) | 5.84 → 3.83 (−35 %) | −6.2 % |
| `ProofInstallTrans` | 76 | 47.6 → 35.0 s (−26 %) | 8.97 → 5.78 (−36 %) | −8.4 % |
| `ProofIlock` | 59 | 36.6 → 28.1 s (−23 %) | 6.34 → 4.31 (−32 %) | −6.5 % |
| `ProofUvmalloc` | 79 | 37.6 → 29.3 s (−22 %) | 6.44 → 4.49 (−30 %) | −6.8 % |
| `ProofSched` | 54 | 30.1 → 24.1 s (−20 %) | 3.25 → 1.81 (−45 %) | −7.5 % |
| `ProofIupdate` | 44 | 27.7 → 22.0 s (−20 %) | 5.01 → 3.80 (−24 %) | −5.4 % |
| `ProofBmap` | 75 | 42.1 → 33.9 s (−19 %) | 11.70 → 5.53 (−53 %) | −3.8 % |
| `ProofBread` | 79 | 24.5 → 19.9 s (−19 %) | 4.52 → 3.51 (−22 %) | −3.4 % |
| `ProofCopyout` | 94 | 53.6 → 43.7 s (−18 %) | 8.66 → 6.58 (−24 %) | −5.6 % |
| `ProofCopyinstr` | 90 | 37.4 → 30.6 s (−18 %) | 6.14 → 4.51 (−27 %) | −2.8 % |
| `ProofWalk` | 61 | 25.2 → 20.8 s (−18 %) | 4.91 → 3.91 (−20 %) | −0.6 % |
| `ProofEndOp` | 94 | 46.7 → 38.8 s (−17 %) | 8.86 → 6.63 (−25 %) | −3.7 % |
| `ProofCopyin` | 72 | 40.8 → 34.8 s (−15 %) | 7.17 → 5.81 (−19 %) | −1.9 % |
| `ProofIput` | 77 | 75.0 → 64.1 s (−15 %) | 16.43 → 13.33 (−19 %) | −2.7 % |
| `ProofUvmcopy` | 71 | 83.8 → 72.6 s (−13 %) | 12.56 → 10.11 (−20 %) | −9.5 % |
| `ProofVirtioDiskRwF` | 37 | 46.3 → 42.2 s (−9 %) | 5.92 → 4.90 (−17 %) | −2.9 % |

**The predictor is the LARGEST LIVE POSE BLOCK A LEAF SITS UNDER**, not the
file's site count, not its length, and not whether the leaf is in a loop. The
reference file is one whole-function proof carrying all 58 facts through all
~1700 steps, so it sits at the top; `ProofUvmcopy` has more sites (71) and a
worse result (−13 %) because its poses split 7+34+31 across three proofs;
`ProofKwait` has the most sites of all (99) and lands at −29 % because its 90
poses are nine scoped clusters of 4–24. Sort candidates by biggest block, not
by `--check`'s site count.

Secondary readings, all consistent across the twenty:

- **`Qed` always improves more than wall** (−17 % to −62 %). `Qed` walks the
  proof term and the term is what collapses; wall carries elaboration work this
  discipline does not touch. On several files the post-conversion `Qed` is a
  small minority of wall (1.8 s of 24 s on `ProofSched`), so ~20 % is near the
  ceiling for that file shape and further gains need a different lever.
- **`.vo` shrinks far less than the reference's −18 %** — typically −2 % to
  −10 %, and `ProofWalk` barely moved. The `.vo` stores the shared DAG, which
  RULE ONE predicts barely changes; the reference's −18 % is the outlier.
- **Peak RSS is NOT a reliable benefit.** −30 % on `ProofScheduler` but −5 %,
  −6 % and +0.2 % on batch 5's three. Memory on the `vm_compute`-heavy files is
  dominated by something other than `Δ`. Do not advertise it.
- The `Require` prelude is ~1.0 s in every file and unchanged, so none of the
  residual is fixed overhead.

## 5. What is left

`tools/instr_subgoal.py --check iris/Proof*.v` is the live scoreboard; run it
rather than trusting a table here. As of 2026-08-22, 22 files are converted and
~193 still pose. Three tiers:

| tier | what to do |
|---|---|
| `CLEAN` | the script converts it outright. Prefer files with one big pose block — that is where the win is (§4). |
| `HAND WORK`, a few names | look at each site: it may be a comment, a leaf with a different hypothesis order, or a pure premise ahead of the instr goal (§3). Usually minutes. |
| files whose facts are used in some OTHER shape | genuine hand work — `ProofWritei`, `ProofNamex`/`ProofNamexTr`, `ProofPipewrite`, `ProofEitherCopy`, `ProofPushOff`, `ProofReadi`, `ProofKexecC`, `ProofBalloc`, `ProofPrintk`. Convert the conforming sites, hand-convert the rest. |
| `ProofVirtioDiskInit` | 127 poses, the single biggest block left, and a special case: it already does "pose late, clear early" BY HAND — pose `Hi`, use it, `iClear "Hi"`, 127 times over. Converting it means deleting the now-dead `iClear` line with each pose. Its one genuinely stray `Hi` is a *Coq* hypothesis from `apply … as (i & Hi & ->)`, unrelated to the Iris one. Worth doing; needs an `iClear`-aware pass. |

**The next tool improvement** is teaching the converter to drop an `iClear
"<hyp>"` along with the pose it kills, which is what `ProofVirtioDiskInit` needs
and what any other by-hand "pose late, clear early" file will need.

Record each conversion's numbers in §4 as it lands.
