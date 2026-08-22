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

- **The `[]` subgoal comes FIRST**, before the continuation. Use a focused
  `{ … }`, NOT `; [ … | ]`: a call site that already carries a `[Hr40]` pattern
  later in the string produces three goals, not two, and the brace does not care.
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
- **A `Löb`/`iInduction` body re-derives the fact every iteration.** Still
  correct, and still expected to win (one `iApply` against a persistent
  hypothesis per iteration against a smaller `Δ` for the whole body), but it is
  the one shape where the retrofit is not free. Measure before believing.
- **Multi-pose lines.** Some files put two `iPoseProof`s on one line; the `(?:…)+`
  in the delete regex is there for exactly that. Verify with the step-3 grep.

## 4. Scoreboard

215 files pose instruction facts. Read `conf` as the number of conforming call
sites and `refs` as the total references to posed names; `conf == refs` means the
script converts the file outright.

| state | files |
|---|---|
| landed | `ProofPipealloc` (`baabee94`) |
| clean (`conf == refs`, no loop) | the bulk — `ProofCreate`, `ProofKexecB3`, `ProofEndOp`, `ProofInstallTrans`, `ProofIput`, `ProofBmap`, `ProofSysChdir`, `ProofCopyinstr`, `ProofIlock`, `ProofCopyout`, `ProofSched`, `ProofIupdate`, `ProofUvmcopy`, `ProofUvmalloc`, `ProofCopyin`, `ProofProcinit`, `ProofBread`, `ProofWalk`, `ProofVirtioDiskRwF`, … |
| clean but LOOP | `ProofNamex`, `ProofPiperead`, `ProofDirlink`, `ProofKexecC`, `ProofDirlookup`, `ProofIget`, `ProofAllocproc`, `ProofIalloc`, `ProofInitlog`, `ProofScheduler`, `ProofIreclaim`, `ProofKwait`, … |
| needs hand work (`refs > conf`) | `ProofWritei` (108/198), `ProofVirtioDiskInit` (127/255), `ProofPipewrite`, `ProofReadi`, `ProofSysPipe`, `ProofPrintk`, `ProofFileread`, `ProofEitherCopy`, … |

Regenerate the table with `tools/instr_subgoal.py --check iris/Proof*.v`.

Record each conversion here as it lands: file, `conf` sites, before/after wall,
before/after `Qed`.
