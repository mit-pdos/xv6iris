# The instr-subgoal sweep

**Status (2026-08-22).** The discipline is settled and measured over 63 files;
`ProofPipealloc.v` is the reference conversion (`baabee94`). What is left is
the tail: 157 files still pose their instruction facts. The rule itself lives in
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
`|Δ|` reduction, so it discounts the ENTIRE proof, flatly. Measured across 63
converted files: wall −9 % to −49 %, median ≈ −24 %, aggregate −26 % of serial
compile work; on the reference file the proof term itself went −69 % (26.6 M →
8.3 M nodes). §4 has the full dataset and the three claims it refutes.

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

63 files converted 2026-08-22, each with one pristine and one converted
single-file `coqc -time -async-proofs off` run, back to back on the VM. Every
one compiled green, and every one has the SAME NUMBER of `Qed` sentences before
and after — the cheap invariant that says no proof obligation was dropped. Run
it on every conversion:

```sh
grep -c "\[Qed" /mnt/rocq/F.before.log /mnt/rocq/F.after.log     # must be equal
```

Wall discount by file, best first: `ProofScheduler` −49 %, `ProofPipealloc`
−46 %, `ProofSysSbrk` −43 %, `ProofDirlookup` −43 %, `ProofIget` −42 %,
`ProofNamexRoot` −42 %, `ProofUartinit` −35 %, `ProofVirtioDiskRwC` −35 %,
`ProofArgfd` −34 %, `ProofWalkNoalloc` −34 %, `ProofProcPagetable` −33 %,
`ProofSysChdir` −32 %, `ProofKexecB2` −32 %, `ProofKexecB3` −31 %,
`ProofFilestat` −31 %, `ProofSysDup` −30 %, `ProofProcinit` −30 %,
`ProofKexecB` −30 %, `ProofFetchstr` −29 %, `ProofConsoleinit` −29 %,
`ProofSysRead` −29 %, `ProofMappages` −29 %, `ProofStati` −29 %,
`ProofKwait` −29 %, `ProofProcdumpParts` −28 %, `ProofSysOpen` −28 %,
`ProofSysWrite` −27 %, `ProofInstallTrans` −26 %, `ProofKforkB6` −26 %,
`ProofSysClose` −25 %, `ProofWakeupParts` −25 %, `ProofIlock` −23 %,
`ProofSysFstat` −23 %, `ProofSysMknod` −23 %, `ProofUvmalloc` −22 %,
`ProofIinit` −22 %, `ProofReparent` −22 %, `ProofInitsleeplock` −21 %,
`ProofSched` −20 %, `ProofIupdate` −20 %, `ProofIalloc` −20 %,
`ProofSysMkdir` −20 %, `ProofUvmcreate` −20 %, `ProofInitlog` −20 %,
`ProofBmap` −19 %, `ProofBread` −19 %, `ProofArgstr` −19 %,
`ProofCopyout` −18 %, `ProofCopyinstr` −18 %, `ProofWalk` −18 %,
`ProofCreate` −18 %, `ProofFetchaddr` −18 %, `ProofEndOp` −17 %,
`ProofUserinit` −17 %, `ProofFsinit` −17 %, `ProofKexecA` −16 %,
`ProofCopyin` −15 %, `ProofIput` −15 %, `ProofSysExec` −14 %,
`ProofUvmcopy` −13 %, `ProofIreclaim` −12 %, `ProofUvmunmap` −10 %,
`ProofVirtioDiskRwF` −9 %.

Median ≈ −24 %. Aggregate over the 63: **1893 s → 1400 s of serial compile
work, −26 %.**

### The predictor

**The LARGEST LIVE POSE BLOCK A LEAF SITS UNDER** — not the file's site count,
not its length, and not whether the leaf is in a loop. Every batch tested this
prospectively and it sorted the candidates correctly every time:

| | sites | largest block | wall |
|---|---|---|---|
| `ProofUartinit` | 27 | 27, one proof | −35 % |
| `ProofSysExec` | 92 | ≤19 over ~30 proofs | −14 % |
| `ProofIreclaim` | 74 | ≤21 over 9 proofs | −12 % |
| `ProofCreate` | 150 | spread over 111 lemmas | −18 % |

**But it only sorts; it does not size.** `ProofInitlog` has a 15-pose block and
hit −20 %, while `ProofUvmunmap` has 18 and hit −10 %. Expect ±10 points of
slop. Sort candidates by biggest block, then take what you get.

### Secondary readings, and what is NOT true

- **`Qed` usually improves more than wall, but this is a tendency, not a law** —
  it failed on three files. `ProofUvmcreate` (−20 % wall, −16 % `Qed`) and
  `ProofWakeupParts` (−25 %, −18 %) are small-block files, and
  `ProofWakeupParts`' first `Qed` got SLOWER outright (0.456 → 0.523 s): at
  9–17 poses the per-site re-derivation is no longer swamped by the `|Δ|`
  discount inside the term. `ProofSysOpen` rules out "small-file artifact" —
  `Qed` −26.8 % against wall −27.6 %, with `Qed` at 17.2 s of 86.5 s. The rule
  holds for blocks of roughly 20+.
- **The win is NOT mostly `Qed`.** On several files wall fell 30 %+ while `Qed`
  was already a small fraction of it (`ProofWalkNoalloc`: 2.1 s of 13.6 s after).
  Shrinking `Δ` speeds up the proofmode steps themselves, not just the kernel's
  walk of the finished term.
- **`.vo` is not a usable proxy, and can GROW.** Range across the 63 is −24 %
  (`ProofNamexRoot`) to **+0.2 %** (`ProofWalkNoalloc`, `ProofMappages`,
  `ProofStati`, `ProofArgfd`). It tracks the block predictor loosely — big-block
  files shrink most — but batch 3 saw it ANTI-correlate (`ProofProcPagetable`
  took the biggest wall and `Qed` win of its batch and the smallest `.vo` win,
  −0.2 %). Small-block files store new `iApply` subterms while their shared DAG
  barely changes, hence the sign flip.
- **Peak RSS is not a reliable benefit.** −37 % on `ProofNamexRoot`, +0.2 % on
  `ProofUvmcopy`, −0.6 % on `ProofIalloc`. Do not advertise it.
- **Dead poses exist and the converter removes them.** `ProofUvmcreate` had 23
  pose lines against 18 sites — five instruction facts posed into `Δ` and never
  used, carried through every later step for nothing. `--check` calls that CLEAN
  (no non-conforming *references*, because there are no references), so read
  `posed N/N sites M` with `M < N` as dead poses, not as missed sites.
- The `Require` prelude is ~1.0 s in every file and unchanged, so none of the
  residual is fixed overhead.

## 5. What is left

`tools/instr_subgoal.py --check iris/Proof*.v` is the live scoreboard; run it
rather than trusting a table here. As of 2026-08-22, **63 files are converted
and 157 still pose.** Three tiers:

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
