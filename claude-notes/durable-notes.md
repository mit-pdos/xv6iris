# xv6iris — durable development notes

Weakest-precondition proofs for a RISC-V (rv64) xv6 kernel, in Iris. This file
holds durable, forward-looking guidance distilled from past work — the notes
that stay relevant across tasks. See [`README.md`](README.md) for how the
`claude-notes/` directory is organized.

## Guiding principle: clean specs and good abstractions over rework

Clean, succinct specs and good general abstractions matter far more than the
effort of reaching them. It is ALWAYS worth refactoring — or rewriting outright —
to get a cleaner spec or a better abstraction. Never keep an awkward interface, a
cross-product of near-duplicate lemmas, or a leaky abstraction just because it
already compiles: **"it's already proven" is not a reason to preserve a bad
shape.** Prefer one general lemma over N special cases — abstract over the varying
axis (privilege, access type, width, A/D bits, leaf predicate, …) rather than
cloning; lift shared structure into a base; and when a spec becomes hard to state
or an abstraction starts to leak, stop and fix the shape before building further
on top of it. Spend the rework; keep the specs clean. The failure mode to avoid
is complexity accreting (hit/miss × width × compressed × fault-arm cross-products)
past the point where a clean abstraction can still be retrofitted.

## Orchestration: model roles and division of labor

This work is split between a top-level orchestration agent and the subagents it
spawns, and the split matters. The **top-level agent should run on a powerful
model (e.g. Fable)** and owns the high-level thinking: writing the specifications,
the overall design and approach, and the abstractions. It does the work the
guiding principle above is about — getting the spec and abstraction shapes right
before anything is built on them. It must **spawn subagents on Opus or Sonnet to
do the lower-level, mundane work** — the actual proofs, mechanical ports, and
similar tasks — rather than doing that itself.

When a subagent hits a problem doing its proof or other task, that is a signal
back to the orchestrator, not just a local obstacle: the **top-level agent should
help resolve it**, and where the difficulty comes from the shape of the work, it
should revise the design, architecture, abstractions, or specifications as needed
rather than pushing the subagent to force a proof through an awkward interface.
Difficulty at the proof level might indicate that the spec or abstraction needs
rework (see the guiding principle): if the difficulty points out some aspect in
which the specs or abstractions aren't quite right, the orchestrator should revise
the specifications, designs, abstractions, etc. accordingly.

## Maintaining these notes

Any project memory worth keeping goes in `claude-notes/`, committed in the repo —
not in local per-session memory files. Put it in the right file: durable rules
here; performance/build tuning in [`optimization.md`](optimization.md); subsystem
design under [`design/`](design/); an in-flight worklist or plan under
[`projects/`](projects/) (one file per project, so an agent working on one task
never has to read another task's worklist); a finished project — no remaining
work and no cleanup — moves to [`completed/`](completed/). Add a pointer line to
[`README.md`](README.md) when you create a new file. When a project is fully
done, move its file from `projects/` to `completed/` (rather than deleting it),
so its durable design notes, gotchas, and reusable recipes stay available; lift
any broadly-applicable lessons up into the design or durable notes as well.

Record only what is useful for **future** development: architecture, conventions,
gotchas, and techniques that will recur. Do NOT record narratives of refactorings
or code changes that are already finished and no longer bear on future work — once
a change has landed and its lessons are captured as a forward-looking convention,
drop the play-by-play. This applies equally to the root `README.md`: state current
behavior/config as fact, not "X used to do Y" / "Z is now fixed" narration of the
change that produced it.

## Build

- Working dir: `/shared/xv6rocq/iris`.
- Single file: `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden <file>.v`
- Full build: `make -f CoqMakefile -j16` (CoqMakefile auto-regenerates from `_CoqProject`; coqdep decides order).
- ALWAYS grep the build log for `Error` — `make …; echo $?` masks make's exit via the echo.
- **PICK `-j` BY RAM, NOT BY CORES.** A `Code*.v` worker peaks near **2 GB** and the `Code*` band runs many at once, so `-j` above `RAM_GB / 2` gets workers OOM-killed — which make reports as **`Error 137`** with no Coq error at all, on whichever targets happened to be in flight. Measured 2026-08-07 on a 15 GB / 8-core box: `-j24` killed three `Code*.v` targets; `-j6` completes, a full rebuild taking ~45 min. The `-j16`/`-j32` figures elsewhere in these notes are from a much larger machine — re-derive the bound before reusing them.
- Never `git add -A` from a parent dir (sweeps sibling untracked trees `coq-sail-stdpp*/`, `lean/`, `rocq/`, `sail-riscv/`); use `git add -A .` from `iris/`.
- Build is **both** critical-path bound and core-saturated in the middle. Measured 2026-08-03, 669 files, clean, `-j32`: **wall 479s, ΣCPU 9364s, critical path 356s, avg parallelism 19.9×.** The path is a ~86s shared prefix + a ~90s leaf-library branch + ONE ~190s whole-function proof; the ~125s of wall above the path is core starvation and is NOT recoverable by scheduling — reordering `_CoqProject` and raising `-j` were both measured and both did nothing (see `optimization.md`). Each big file pays a 12–40s `Qed` kernel-typecheck. For iterative re-checking, a `-vos`/`-vok` two-phase build drops the Qed off the critical path (no proof changes) — but interactive tactics still run, so a vos build is still >2min.
- **opam switch:** everything builds in the project-local switch `/shared/xv6rocq` (Rocq 9.0.1, coq-iris 4.4.0, coq-stdpp/-bitvector 1.12.0, coq-sail-stdpp 0.20.1). `eval $(opam env --switch=/shared/xv6rocq)` is mandatory in any raw `coqc` invocation — a fresh shell defaults to the wrong switch (→ "Cannot find SailStdpp.*"). Rocq ≥9.1 is not an option (coq-sail-stdpp 0.20.1 is capped `< 9.1~`).
- The generated Sail model (`Riscv.rv64d`, defines `try_step`) is NOT an opam package — rebuild from `/shared/xv6rocq/model-xv6iris/` in order `rv64d_types.v → riscv_extras.v → rv64d.v`.
- **Stale `.vo` trap:** compiling a new file against stale sibling `.vo` produces *impossible-looking* arity/alignment/"expected X" errors, and every address `vm_compute`s to an OLD literal after a `kernel-rocq` image regen. Whenever an argument-count or address error looks impossible, check `.v -nt .vo` and `make proofs` to resync first.
- **A `git pull` THAT TOUCHES `model-xv6iris/` MEANS `make model` FIRST, AND THE FAILURE LOOKS NOTHING LIKE A STALE MODEL.** The generated Sail model is not an opam package and nothing in `iris/`'s own makefile rebuilds it, so a pull that lands a new `rv64d.v`/`rv64d_types.v` leaves every `.vo` in the tree consistent *with each other* but stale against the new sources. Nothing breaks until make tries to rebuild the first file whose source also moved — typically `RiscvLang.v` — at which point you get a single bottom-of-the-tree error naming a model field, e.g. **`PMA_misaligned_atomicity_granule_size_exp: Not a projection`**, with the whole build behind it. That reads like a corrupt checkout or a broken proof; it is neither. The recovery is `make model` (rebuilds `rv64d_types.v -> riscv_extras.v -> rv64d.v`), then a full `iris/` rebuild — which is a near-total recompile, so budget for it. Check `ls -la model-xv6iris/*.v model-xv6iris/*.vo` after any pull: a `.v` newer than its `.vo` is the tell, and it is much cheaper to notice there than at `RiscvLang.v`.
- **NEVER RUN `make`/`coqc` FROM A SHELL WITHOUT `eval $(opam env --switch=/shared/xv6rocq)` — INCLUDING BACKGROUND ONES.** A `nohup bash -c '...'` does not inherit an interactive shell's opam env, and the resulting failure is a bogus *"Cannot find a physical path bound to logical path bitvector.definitions with prefix stdpp"* at `RiscvLang.v` that is indistinguishable at a glance from the stale-model error above. Worse, `iris/CoqMakefile` auto-regenerates from `_CoqProject`, so a make run under the wrong switch **rewrites `CoqMakefile` with the wrong Rocq version** (the file then says `generated by Rocq/Coq 9.1.1` while the switch is 9.0.1) and every later build inherits it. Recovery: delete `iris/CoqMakefile` (and `CoqMakefile.conf`) and let a correctly-switched `make` regenerate them. Chain the `eval` into the same command as the `make`; do not assume it persists.
- **AFTER A `git pull`, RUN `make xv6-rev-check` BEFORE `make proofs`.** `xv6-riscv/` is gitignored, so a pull that bumps `XV6_REV` (or that lands a re-dumped `kernel-rocq/`) leaves your local clone on the OLD revision — and `make proofs`' dump rules see a `kernel/kernel` ELF newer than the freshly-checked-out `kernel-rocq/*.v`, so they **silently re-dump from the stale ELF and clobber the tracked image**, moving every symbol address. What you then see is *not* a dump error: it is `ColdBoot.v` / `BootReset.v` failing with `Unable to unify "9223372036856090925" with "9223372036858188079"`, i.e. a bogus proof failure at the bottom of the tree. Recover with `git checkout -- kernel-rocq/`, fix the clone (`git -C xv6-riscv fetch && git -C xv6-riscv checkout --detach $XV6_REV`), rebuild the ELF, then `make dump-force` and confirm `git status kernel-rocq/` is **clean** — a byte-identical re-dump is the proof that the toolchain and the revision agree. (Related: `make proofs` does not depend on `user-rocq`, so a tree with `USpecSync.v` in `iris/_CoqProject` also needs `make user-rocq` or you get `No rule to make target '../user-rocq/SyncInstrs.vo'`.)
  - **`make dump-force` alone does NOT finish the recovery, and the symptom outlives it.** `dump-force` rewrites `kernel-rocq/*.v`; nothing there rebuilds `kernel-rocq/*.vo`, and `make -C iris -f CoqMakefile` — the command you reach for to re-check the proofs — has no rule for them either. So the proofs keep loading the CLOBBERED `KernelData.vo`/`KernelInstrs.vo` and keep failing at exactly the same line, which reads as "the restore did not take" or "this proof is genuinely broken on main". Run `make kernel-rocq` (or the top-level `make proofs`) after `dump-force`, and check `ls -l kernel-rocq/*.vo` against the `.v` mtimes before believing a failure. The 2026-08-06 instance: `ProofArgraw.v`'s `ar_tbl_bytes` failing `Unable to unify "bv_unsigned 248" with "bv_unsigned 234"` — a 14-byte relayout of argraw's `.rodata` jump table, from an ELF one xv6 revision behind.
- **AFTER ANY RE-DUMP, RUN `make check-decode`.** The dump only refreshes
  `kernel-rocq/`; the `iris/` decode layer separately states each instruction's
  encoding word and decoded immediate, and those go stale in ~145 of 188
  functions on a typical upstream bump *even where the C source did not
  change* (re-encoded call targets; linker relaxation, which can also resize a
  function). The whole layer is GENERATED from the dump —
  `iris/KernelDecode*.v` + the per-function `iris/Code<F>.v`, by
  `tools/gen_code.py` — so `make gen-code` rewrites it and the diff afterwards
  is what tells you which functions moved (`make check-decode` is that
  regeneration plus a `git diff --exit-code`, i.e. it FAILS if anything moved).
  A site where the INSTRUCTION changed rather than just its immediate shows up
  as a changed `ast`, and its proof needs a human. The addresses need no attention:
  they are symbol-relative already. Design and the measured numbers:
  [`design/code-organization.md`](design/code-organization.md).
- **Editing a file near the BOTTOM of the tree kills the single-file check loop.** Touch `RiscvFetchExec.v` / `SmodeCore.v` / `IntrDefs.v` / `WpSconfMem.v` and every downstream `coqc <one file>.v` fails with *"Compiled library X makes inconsistent assumptions over library Y"* — the siblings' `.vo`s were built against the old interface, so there is no hand-orderable sequence of single-file compiles that works. Validate such an edit with **`make -f CoqMakefile -j16 -k`** (coqdep orders it; `-k` reports every independent error in one pass) and grep the log for `Error`; reserve single-file `coqc` for leaf/proof files whose dependencies you have not touched.
- **A `nat` EQUALITY WHOSE RHS IS A LARGE LITERAL NEEDS `Z`, NOT A BIGGER STACK.** Any route to closing such a goal — `reflexivity`, `vm_compute`, even `vm_cast_no_check` — eventually makes something materialize a literal-deep unary successor chain, and that overflows a normal 8 MB stack outright (`ProofWriteiParts.v`'s old `wi_maxfile_bsize : (MAXFILE * BSIZE)%nat = 274432%nat` died this way, deterministically, in under 4 s and under 1 GB RSS — so it does NOT look like memory pressure or a `-j` artifact, it looks like a broken proof in a file you did not touch). `Z` literals are binary `Z.pos` trees (~log2 depth), so state the fact at `Z.of_nat (… )  = <literal>` instead (`rewrite Nat2Z.inj_mul` first if the LHS is a product) and close with `vm_compute; reflexivity` — the `nat`-side factors being unfolded stay small, and the literal itself is never forced into unary form. No shell tuning needed, and no `ulimit -s` bump either — `ProofWriteiParts.v` briefly grew a `nat`-typed twin of this lemma (closed by bare `reflexivity`) that reintroduced the overflow and made a raised stack look like a real prerequisite; see the next bullet for why that twin was needed and how it was fixed for good, retiring the requirement.
  - **If a CALLER genuinely needs the fact AT `nat`** (e.g. to `rewrite` a `nat` loop-invariant hypothesis), do not restate it over `nat` from scratch — that regresses straight back to the overflow, and it does not even show up as "the same bug again": `reflexivity`/`vm_compute` on the small unfolded factors (`268 * 1024`) succeed FINE in isolation (plenty of stack), so it looks safe under a standalone test, and only overflows once compiled inside the real file's Iris/stdpp-heavy import context (2026-08-07, `wi_maxfile_bsize_nat` — a second agent re-added exactly this, unaware the first agent's `Z` port existed for this reason, and it died the same way). Confirm any such standalone test against the actual file's build, not a scratch file. `lia`/`nia` cannot bridge the gap either — once a `nat` literal is past Rocq's abstraction threshold (~5000) it prints compactly but elaborates to an opaque `Nat.of_num_uint` application, and `lia` cannot relate that to a *computed* product (`(268 * 1024 <= 274432)%nat` fails with "Cannot find witness" even though both sides are closed numerals); it only works when the identical literal already appears verbatim on both sides. Instead derive the `nat` fact from the `Z` one via `Z.to_nat`, which never forces the big literal into unary form: state it as `… = Z.to_nat <literal>` and prove `rewrite <- <the Z lemma>, Nat2Z.id; reflexivity` — both rewrites are symbolic (a Z-literal pattern match and a generic `Z.to_nat (Z.of_nat n) = n` lemma), so the proof is O(1) regardless of context. `lia` resolves `Z.to_nat` of a literal symbolically at every call site downstream, so this is a transparent drop-in.
- **Fork/parallel discipline:** `make clean-proofs` nukes the shared `.vo` tree and breaks concurrent siblings — a fork must `coqc` only its OWN file, one compile at a time. Never `pkill -f coqc` (the pattern matches the killer's own shell → kills Bash, exit 144; and kills sibling compiles) — use `pkill -x coqc` or kill the `rocqworker` by PID. The same self-match trap breaks WAIT loops: `until ! pgrep -f "CoqMakefile -j16"; do …` never terminates (the waiter's own command line contains the pattern) and then makes `pgrep -f CoqMakefile` report a phantom in-progress build to everyone else. Don't poll processes at all — have the build write its own sentinel (`…; echo "EXIT=$?" >> log`) and wait on `grep EXIT` of the log.
- **Profiling:** per-file times via `make TIMED=1` (or `make proofs TIMING=1 JOBS=32` → per-sentence `*.v.timing`, parse `Chars A-B [snip] T secs`, map offset→line); per-command via `coqc -time` (a stall right after a lemma's last tactic = stuck in `Qed`). Optimize the longest Require chain, not `-j`. Delete `*.v.timing` after (don't commit). Measure any `vm_compute`/decode tactic ONE variant per `coqc` process — the 2nd variant in a process wins ~35% from bytecode-cache reuse (fabricates false savings).
  - **`tools/proof_profile.py` does all of this in one pass** and runs in CI on every checkin (`.github/workflows/ci.yml`): the iris build there is `make … --output-sync=target TIMED=1 TIMING=1` (`tee`d to a log), and the profiler consumes that log + the `*.v.timing` files + coqdep's `.CoqMakefile.d` + `.vo` mtimes to emit most-expensive statements/files, the weighted critical path (+ other deep chains), and a parallelism-over-time chart. All of it — tables + an inline Unicode block-chart of concurrent compiles — lands in the job's **step summary** and nowhere else (no artifact upload): GitHub sanitizes raw SVG/`<img>`/`data:` out of the summary, so the chart is drawn in text. The tool still writes a higher-res `parallelism.svg` + full `report-full.txt` to its `--out-dir` for local runs. Stdlib-only, `continue-on-error`, so it never fails a green build. Run it locally the same way: `python3 tools/proof_profile.py --build-log <TIMED-log> --iris-dir iris --out-dir /tmp/prof --jobs $(nproc)`.
    - **`TIMED=1` needs `--output-sync=target`, or the log is not parseable.** Every TIMED record is written by its own `command time` to the one pipe `tee` reads, and those writes are not atomic, so under `-j` two records interleave *inside* a line (`SpecConsoleintr.vo (reaSlp:e cSysPipe.vo (real: …, sys: 4.040.55,,`). Measured on a synthetic 4-target build: without `-O`, **zero** of 4 records survive intact; with it, all 4. `-O` changes nothing the profiler measures — per-file wall comes from the record, the parallelism chart from `.vo` mtimes, neither from line order. The profiler also drops (and now *counts and reports*) unparseable records rather than dying on them; the pairing matters because `continue-on-error` turns such a death into a green run carrying only a `Process completed with exit code 1` annotation, which reads exactly like a broken proof build. **When CI looks green but a run page shows that annotation, check which step it came from before assuming the proofs broke.**
- **A FAILING TACTIC IN A WHOLE-FUNCTION WP LOOKS LIKE A HANG.** Rocq prints the entire goal with the error, and a syscall-altitude goal contains `ProcInv.tf_page`'s **4096-conjunct** big-op plus every `iAssert`ed continuation; formatting that takes tens of minutes, so a one-line mistake reads as an infinite loop and every "where did it stall?" reading is wrong. Put **`Set Printing Depth 40.`** at the top of any file that proves over `proc_priv` (ProofSysPipe.v does) — it turns a 40-minute non-answer into a 30-second error message. Corollary: before hunting a "hang", check that the proof is not simply *wrong*.
- **A COMPILE THAT NEVER FINISHES IS LOCALISED BY `coqc -time`, WHICH STREAMS.** `-time` writes one line per sentence as it goes, so the LAST LINE IN THE LOG IS THE STALLING SENTENCE — run the compile redirecting to a file and `tail` it. (Map the `Chars A - B` offset to a line with `head -c B <f>.v | wc -l`.) This turned a file that had been "compiling" for 30+ minutes across three sessions into a two-minute diagnosis. **And what it found is the failure mode to suspect first: a MIS-STATED `∀`-PREMISE.** A lemma took `Hlr_ok : ∀ aq0 rl0 …, … uleaf_ok (LoadReserved (aq, rl, Data)) w0 → …` — binding `aq0 rl0` but writing the OUTER `aq rl` into the payload — so the uniformly-quantified composer could not be supplied and `iMod` span forever on the unification instead of failing. A premise that quantifies a variable it then does not use in the body is the shape to grep for; if the same names are in scope outside, Rocq's renaming (`aq0`) is the only hint in the error message, and only if you get one at all.
- **`timeout N coqc` does NOT kill the worker, and `pgrep -x coqc` does NOT find it.** `coqc` runs as `rocqworker --kind=compile`, so an exact-name wait loop returns while the compile is still going (giving truncated logs and phantom "stalls"), and `timeout`'s SIGTERM reaps only its direct child. The orphan then spins at 100% and **holds a worker slot, stalling the next build at a random point** — which is what makes the stall location look non-deterministic. Wait on `pgrep -f "rocqworker --kind=compile"`, or better, have the compile print its own sentinel (`bash -c 'coqc …; echo EXIT=$?'`) and wait for that; and `pkill -f rocqworker` before re-measuring.
- **`vm_compute; reflexivity` IS RECHECKED BY THE KERNEL'S *LAZY* CONVERSION AT `Qed` — the VM's speed does not carry over.** The tactic normalizes with the VM in a second; the proof term it leaves is a plain `eq_refl`, so `Qed` re-does the whole reduction in the kernel's lazy evaluator. On model code that is a different order of magnitude: ONE such equation over the Sail cold-boot chain measured **>3.8 GB and climbing**, and fifteen of them inside a single `Qed` reached **25 GB** before being killed, while the tactic-level `vm_compute` of the same term takes 0.75 s. `-time` shows 0 s for every sentence and the file just never finishes — the async `Qed` worker is where it went (next bullet). Two fixes, both in `iris/ColdBoot.v`: close the goal with **`vm_cast_no_check (eq_refl <rhs>)`** so the kernel rechecks with the VM too; and **compute the result ONCE into its own `Definition`** (`Definition d : T. Proof. let x := eval vm_compute in e in exact x. Defined.`) plus a single VM-cast lemma `e = d`, after which every downstream fact is a shallow conversion over `d` and costs nothing. That restructuring took the file from unbounded to **13.6 s / 0.9 GB**.
- **PROFILE WITH `-time` BEFORE THEORISING ABOUT `Qed`.** `coqc -time` prints one line per command, and if the slow line is a *tactic* then no term-size work will help. The trap this caught: **`ltac:(set_solver)` passed as a positional argument inside a whole-function proof.** `ProofSysDup` took 9 min 10 s, and `-time` put 467 s of it on three trivial side conditions (`fd0 ∉ ∅`, `fd1 ∉ {[fd0]}`) at 106/180/180 s each — `set_solver` ends in `naive_solver`, which searches *every hypothesis in scope*, and a capstone's context is ~200 register-chain facts over large mword terms. Replacing them with `apply not_elem_of_empty` / `apply not_elem_of_singleton_2` gave **9 min 10 s → 25.6 s (21x)**, after which the biggest item in the file is an ordinary 3.3 s `Qed`. The rule: discharge set/arith side conditions in a capstone with the NAMED lemma, or hoist them to a `Local Lemma` where the context is two hypotheses wide; `set_solver` is fine inside the small definitional lemmas, it is the call site that matters. See `optimization.md`.
- **A slow `Qed` is usually proof-term SIZE, not conversion — and `rocq compile -profile <f>.json` is what tells you which.** It breaks each `Qed` into `HConstr.of_constr` / `Typeops.execute` / `close_proof` / `sort_and_universes_of_constr`; measured across this tree only ~25 % is `Typeops` (real typechecking) and the rest is term-size-linear plumbing that re-walks every *occurrence* of a shared subterm. The one-command tell is **`Set Debug "hconstr".`**, which prints each `Qed`'s `tree size` and `bindings` (the DAG): a high **tree/bindings ratio** means a small proof with an exponentially unfolded term. To localise it inside a lemma, bisect with an `Axiom cheat_ : forall (A : Type), A.` stub (unlike `Admitted` this still runs `Qed`). See `optimization.md` for the whole method and for the `unfold set_reg` 3^N trap it found.
- **`coqc` offloads `Qed` kernel-checking to an async `rocqworker` subprocess, and `coqc -time` does NOT count that worker's time.** So `-time`'s per-sentence sum can be tiny (e.g. 14 s) while the real `/usr/bin/time` wall is minutes — the gap is the async `Qed`, NOT machine contention. A pathological `Qed` (e.g. a whole-function proof term over a transparent, eagerly-reducible register-map tower) hides this way. To see it: `/usr/bin/time -v coqc …` (wall + RSS), not `-time`. Also: a killed/`pkill`-ed `coqc` can leave orphan/zombie `rocqworker`s (`ps -eo pid,ppid,stat,comm | grep rocqworker`; `Z`/defunct = harmless, a live orphan holds a worker slot and can stall the next build) — reap them before re-measuring, and prefer `pkill -x rocqworker`/kill-by-PID over `pkill -f coqc`.

## Changing the kernel SOURCE: what an image shift breaks, and how to find it

Done once, 2026-08-06, for a 6-byte fix inside `writei` (`kernel-defects.md`
D1). It touched ~30 proof files and ~130 sites. Every step below was paid
for; do them in this order.

**1. GATE: prove the toolchain reproduces the image BEFORE changing anything.**
There is no record of which gcc built the tracked dumps — CI never builds the
ELF, it uses the checked-in `kernel-rocq/*.v`. So install a toolchain, build
at the **unchanged** pinned `XV6_REV`, dump to a scratch dir and diff against
the tracked files. All three must be byte-identical. (Ubuntu's
`gcc-riscv64-linux-gnu` 15.2.0 did reproduce it exactly, as of that date.)
If they differ, STOP: a rebuild would re-do register allocation and inlining
across the whole kernel and take every proof with it, and you would be
debugging that instead of your change. This is the same discipline the
README already mandates for regenerating the Sail model.

**2. Take the MINIMAL source change.** Cherry-pick the one commit onto the
pinned rev; do not move to a branch head. The `riscv` branch was 13 commits
ahead touching 8 kernel files including `trampoline.S`, `memlayout.h` and
`bio.c` — all fully-proven subsystems. Bundling them would make it
impossible to tell which change broke what.

**3. Measure the shift from the symbol tables, not by assumption.** Diff old
vs new `KernelSyms.v`. Expect ONE uniform delta over a bounded window: the
writei fix moved 46 symbols by +6 over `[0x80003752, 0x80005420)` and
**nothing above it**, because `kernelvec`'s alignment padding absorbed the 6
bytes. Data (`sb` &c.) did not move at all. A first pass that assumed
"everything above the change shifts" flagged 92 literals in 70 files; the
true set was 14. Shifting the other 78 would have broken working proofs.

**4. Regenerate, then repair, in this order:** re-dump `kernel-rocq/`; bump
`XV6_REV`; run `tools/gen_code.py` (it regenerates every Code file in
`tools/code_manifest.json` straight from the image — 117 files, and it is
what makes this tractable at all); then fix what it does NOT cover.

> **`gen_code.py --only` IS A FOOTGUN — DO NOT USE IT ALONE.** `--only`
> restricts which *Code* files are written, but `main()` ALWAYS rewrites all
> 16 `KernelDecode*.v` shards from the `decoded` dict, which under `--only`
> holds just that one function's words. Running `--only CodeReadi.v` would
> have replaced the 2306-lemma shared catalogue with 84 lemmas. To add ONE
> function: run the FULL generator into a scratch directory and copy out only
> what changed — then confirm every pre-existing Code file came back
> byte-identical, and that the shard diffs are pure additions with no removed
> lines. (Adding a function also means a `tools/code_manifest.json` entry:
> `[file, symbol, prefix, width]`, where `width` is the zero-padded hex width
> of the offset in the lemma name — `2` under 256 bytes, `3` at or above.)
>
> **A `Code<F>.v` WITH NO MANIFEST ROW IS A TIME BOMB, and its own `.vo`
> hides it.** `CodeReadi.v` sat in the tree and in `_CoqProject` with a
> `.vo`, but its 25 decode words were never in `KernelDecode*.v` — the
> ad-hoc generator run that produced it had written the shards and they were
> reverted afterwards. It surfaced only on the next full build, as
> *"Variable decname should be bound to a term but is bound to the
> identifier `kd_0ed7e663`"*, with the stale `.vo` masking it until then.
> The manifest row is what makes a Code file reproducible, so **a Code file
> the manifest does not list is the tell**; recover with the recipe above.

### The three things that bite, none of which a grep for addresses finds

- **A function that moves changes its instruction WORDS, not just its
  address.** Every PC-relative `jal`, branch, and `auipc`/`addi` pair that
  crosses the moved/unmoved boundary re-encodes: **−6 leaving** a moved
  function, **+6 entering** one; both-moved and both-unmoved are unchanged.
  That rule held for all 146 changed immediates with zero exceptions. It is
  why proofs of functions that did NOT move (`bread`, `brelse`, `binit`,
  `main`, `bmap`, `iupdate`) still break — they call into code that did.

- **NEVER compute the fix set by value arithmetic.** Three separate ways it
  is wrong, each hit for real: (a) `removed − added` set-difference silently
  drops any value that reappears as a NEW immediate elsewhere — that hid
  `ProofFilealloc` entirely; (b) immediates are written in HEX in some
  proofs and DECIMAL in others (`0x6a2` vs `1698`), so a decimal grep misses
  sites; (c) **adjacent call sites 6 bytes apart collide**, e.g. `iti_56`
  2093404→2093398 next to `iti_5c` 2093398→2093392 — a sequential value
  sweep double-shifts the first. **Build the map keyed by LEMMA NAME from
  the regenerated `Code<F>.v` diff, and apply it by LINE NUMBER.**

- **Hand-written decode files state the word AND its decoded AST, and both
  must move together.** `gen_code.py` does not cover the `Code*Aux.v` files.
  Fixing only the word in `CodeFileinitAux.v` left the lemma asserting
  `ITYPE (1468, …)` against a word that now decodes to 1462, and the file
  failed again on the next build. Diff every asserted word in such a file
  against the image rather than patching the one the error names.

### Expect cascades, and let `-k` enumerate them

Each build reveals only the next layer: a file that fails blocks its
dependants from being attempted at all, so they surface only once it is
fixed (`ProofFileinit` appeared two builds after `CodeFileinitAux`, which it
depends on). Run `make -k`, collect the whole failure set, fix it as a
batch, repeat. Do not fix-and-restart one file at a time.

Also: each immediate typically appears **twice** per call site — once as the
explicit `wp_*_s_sconf` argument and once inside a companion
`add_vec … sign_extend'` assert or `set`. Update both, or the file fails
again at the same offset.

## Write the checker for a refactor's SILENT failure mode, before the sweep

If a change has a way of going wrong that still compiles, that way WILL be
taken, and no build will tell you. A checker exists because of exactly that,
and it is cheap enough to run on every touched file:

- **`tools/lemma_diff.py [--ref REF]`** — reports top-level declarations that
  VANISHED relative to a git ref, plus `Admitted`/`admit`/`Abort` and any new
  `Axiom`/`Parameter`/`Hypothesis`. A sweep's characteristic failure is not a
  red build; it is a file that compiles because something was quietly dropped —
  a lemma deleted instead of restated, a `Module Type` that lost a `Parameter`.
  Every line it prints is a thing to justify, not necessarily a bug (a
  deliberate rename shows up as one `GONE`), which is the point.

The definitive soundness check for a whole cone is still
`Print Assumptions <the linked top-level theorem>` — it is the only one that
sees through every functor and seal. Do it once at the end of any interface
change and diff the axiom list against what the coverage report says should be
assumed; anything else is a regression.

## Two ways a build check can LIE about being green

Both cost real time in one session; check for them before believing a
"clean build".

- **`make ... | grep -E ... | head -N` truncates the check, not just the
  output.**  Once `head` has its N lines it closes the pipe, so any later
  error is never seen -- and `echo $?` after the pipeline reports the LAST
  command's status, not make's.  Capture make's own exit status
  (`make proofs > log 2>&1; echo $?`) and grep the file afterwards.

## Proof coverage report

`tools/proof_coverage.py` answers "what of the kernel is proved?" — a hierarchy
of xv6 source file → functions → status (proven / assumed / partial / none),
with the byte-weighted percentages, the file:line of each spec, and the admits
and axioms each proven function rests on. `--format text|md|html|json`.

- The kernel side comes from the **tracked** `kernel-rocq/KernelSyms.v` +
  `KernelInstrs.v` (a symbol is a function iff an instruction starts at its
  address; its size runs to the next function entry), never from a freshly
  built ELF — `xv6-riscv/` is a gitignored tree whose build routinely drifts
  from the image the proofs are about. Only source-file *attribution* uses
  `nm` on `xv6-riscv/kernel/*.o`, by name, with a `*.c`/`*.S` scan as fallback.
- The proof side is derived from the spec-module shape
  ([`design/spec-modules.md`](design/spec-modules.md)): a `_body` whose entry
  `pc_is` is `KernelSyms.<f>` at offset 0 and whose continuation `pc_is` leaves
  the function — the ra-derived return address, or (for one that never returns,
  like the boot path) a `let` bound to ANOTHER `KernelSyms` symbol — is a
  whole-function spec; it counts as proven once
  a `Link*.v` instantiates a functor sealed by its `Module Type`. **So keeping
  a new proof in that shape is what keeps it visible to the report** — no
  separate registration beyond `_CoqProject`.
- **The scan is keyed off `iris/_CoqProject`, not a `*.v` glob**, so the report
  can only ever describe files the build actually compiles: an unlisted `.v` is
  compiled by nobody, and counting a "proven" function out of one would be a
  claim no build has ever checked. Drift either way — a `.v` in the tree the
  project file omits, or an entry whose file is gone, or a duplicate entry — is
  a `--check` error that fails CI, not a silent adjustment. So **adding a file
  to `iris/` means adding it to `_CoqProject`**; without the check, forgetting
  is invisible in both directions at once (never built, still counted).
- **Spell the entry pc so the report can SEE the symbol.** The script matches
  `KernelSyms.<f>` textually, either as `pc_is (mword_of_int KernelSyms.<f>)` or
  — the form to prefer — a `let pcE : mword 64 := mword_of_int KernelSyms.<f> in`
  binding used as `pc_is pcE`. A `Notation F := KernelSyms.<f>` alias written
  into the `pc_is` hides the symbol, and the function reads as *partial* even
  though it is fully proven and linked. Keep the notation for the decode/proof
  files' addresses, but not for the spec's entry pc. Both failure modes are
  silent — a spec-shape slip shows up as a status downgrade, never as an error,
  so **check the report after adding a function** rather than assuming it
  counted.
- The whole-function proofs that predate the shape (the piecewise M-mode boot
  lemmas and the assembly: `_entry`, `start`, `timerinit`, `spin`, `swtch`,
  `kernelvec`, `userret`) name their entry pc through a local `Definition`, so
  they are listed in the script's `MANIFEST_PROVEN`. (The composed boot
  contract — `_entry` through `start` into S-mode at `main` — IS in the module
  shape: `SpecEntry.v` / `ProofEntry.v` / `LinkEntry.v`, over those lemmas.)
  Also listed are the deliberately-assumed
  contracts (`myproc`, `panic`, `kerneltrap`) in `MANIFEST_ASSUMED`. Every
  entry is verified against the tree and a stale one is reported as a manifest
  error rather than silently counted — fix those when they appear.

## Proofmode & bitvector gotchas (recur across files)

- **Some files are deliberately ssreflect-FREE, and that decides where a definition may live.** `Pt4kWalk.v` has 27 vanilla `rewrite … by …` rewrites, so it cannot `Require` anything that pulls in the iris proofmode — which `PageGeom.v` does (it needs ssreflect's `rewrite … in H |- *` for the two `uint`/`bv_unsigned` bridges it inherited from `KallocInv.v`). So a `page_base`-spelled restatement of a `Pt4kWalk` fact has to live in `PtBuild.v`, not in `Pt4kWalk.v`, even though there is no dependency CYCLE. Before planning a relocation into a low file, check whether that file uses `rewrite … by …`; the failure mode is a parse error at the first such rewrite, far from the import you added.
- In iris proofmode: `rewrite a b c` uses SPACES not commas (`rewrite H1, H2.` fails); `rewrite lem by tac` does NOT parse (ssreflect clash) — use `rewrite lem; [|tac]` / `rewrite (lem args ltac:(tac))` / `assert … by tac`. iris-FREE files can use `rewrite … by`. Rewrite a proofmode HYP with `iEval (rewrite H) in "Hpc"` — bare `rewrite H` rewrites the WHOLE `envs_entails Δ P` (hyps AND goal) and desyncs them.
- `iDestruct (lem with "…") as %pure` keeps the spatial inputs when the conclusion is pure (relied on by fetch/config lemmas) — a plain `iDestruct` of a pure-conclusion wand CONSUMES its premises. `big_sepM`/`big_sepL` byte extraction needs an EXPLICIT Φ (underscores leave TC evars unresolved).
- Value/frame binders must be `mword 64` (annotate; `add_vec` demands `mword n` and won't unify a `bv 64` binder even though `mword 64 ≡ bv 64`). Same trap for a value introduced from an EXISTENTIAL resource (`iDestruct "HR" as (t) "Hcell"` on a `∃ t : mword 32, a ↦₄ t` invariant body): `t` arrives as `bv 32`, so `sign_extend' 64 t` fails with "has type bv 32 while it is expected to have type mword ?n" — ascribe `(t : mword 32)` at every use (the ascription leaves no mark, so `change`/`set` terms still match the leaf's output). Decode-fact immediates must be the decoder's POSITIVE RESIDUE (−2016 → 2080; the signed literal fails `bv_is_wf`). Model names need `Defs.` qualification (`Defs.bind`/`Defs.read_reg`/`Defs.assert_exp'`; `rv64d_types.Read_plain`) or they resolve to raw Prompt_monad versions that won't unify with `M = Defs.monad`. A `.` immediately before `(*` parses as `.(` projection — leave a space.
- `lia` cannot evaluate `2^n`/`bv_modulus`/`bv_half_modulus` — `assert (… = <literal>) as -> by (vm_compute; reflexivity)` first. In heavy-import WP files (WpSmodeGpr+SmodeCore+program_logic) `bitvector.tactics` sets a zify hook that makes `lia` return "Cannot find witness" on trivial bounds — prefer explicit `Z.le_lt_trans`/`Z.add_le_mono_r`/`Nat2Z.is_nonneg`. The hook arrives TRANSITIVELY (dropping `bitvector.tactics` from your own imports does not help), and what trips it is a goal mentioning `bv_unsigned`: so when a proof needs real arithmetic, factor the arithmetic into a lemma over plain `Z` variables and feed it the `bv_unsigned` values (`ProofMemmove.mm_overlap_arith`), where `lia` works normally. Widths appear as `MachineWord.Z_idx n`, so `change (Z.sub 57 12) with 45` (or `change (bv_modulus 27)` won't match `bv_modulus (Z_idx 27)`) before a rewrite; conversion beats rewrite for closed masks; `and_vec` needs `unfold word_binop, with_word', with_word` before `bv_and_unsigned` matches. Use `apply f_equal` (single-arg) not `f_equal` on `add_vec` bv-address equalities (over-splits into the wf proof); same for `mword_of_int a = mword_of_int b` — `f_equal` there leaves a goal `lia` then fails on, so `assert (a = b) by lia; rewrite` it instead. Regidx disequality: `intro He; injection He as He2; vm_compute in He2; congruence`.
- **`bv_unsigned` silently elaborates at the wrong width over `Arch.pa`.** `pa_add` lands in `Arch.pa`, whose width is an unreduced `Z_idx (if xlen =? 32 then … else …)` match, so an `assert` stated as `bv_unsigned (pa_add p j) = …` gets `bv_unsigned` at THAT width and then fails to `rewrite` in a goal stated at width 64 — the two print identically, so the error reads "Found no subterm matching" on a term you can see in the goal. Ascribe: `bv_unsigned (pa_add p j : mword 64)`.
- **A stored value that itself contains an insert-lookup derails `rewrite upd_ne`/`upd_eq`.** Several leaves write a value computed from the same map (`c.addi4spn`'s `add_vec (m1 !!! Regidx csp_rs1) …`, an slli's `shift_bits_left (m2 !!! Regidx a2_idx) …`), so the NEW map contains `(<[k := v]> f) !!! j` inside itself; ssreflect then matches that occurrence instead of the peel you meant, and you get an unprovable side goal (`Regidx 2 <> Regidx 2`) or a `discriminate` failure ("No primitive equality found"). Two fixes, both worth preferring to a bare peel: pass the value to the leaf as its explicit `wval` (`wp_slli_s_sconf`/`wp_add_s_sconf` take one) so the stored term is closed, or `iEval (rewrite <the lookup fact>) in "Hcg"` BEFORE naming the map with `set`. Pinning the instance (`rewrite (upd_ne _ (Regidx k) (Regidx j))`) also works.
- **AN `is_Some` PROBE DOES NOT MEASURE A MODEL EVALUATION — FORCING A FIELD IS THE COST.** `exec <program> (MState rs0 …)` checked only for `match … with Some _ => true end` is cheap even over an open `rs0` (the architectural reset: **1.2 s / 650 MB**) because it applies no `regstate` FIELD, so every `register_set` closure stays an unforced accumulator. The instant you ask for `register_lookup r` of the result — which is what every consumer-facing fact does — the field chain is forced and it explodes: `PC`, `nextPC`, `cur_privilege`, `hart_state` and `elp` each hit a 100 s timeout at ~4 GB on that same reset. So measure the fact you actually need, never `is_Some`; and `native_compute` is not an escape (the build passes `-native-compiler no`). The escape is symbolic peeling with the tower kept FOLDED (`exec_bind0_Some` / `exec_write_reg` / `irrelevant_register_set` / `register_lookup_set`).
- **A SAIL BIT-FIELD UPDATE IS `bv_extract`/`bv_concat` UNDER A CAST, AND stdpp's TWO CONCAT LEMMAS DO NOT COVER A MIDDLE WINDOW.** `_update_X_F` is `update_subrange_vec_dec`, i.e. `MachineWord.update_slice` under Sail's `autocast`/`cast_idx`; at CONCRETE widths those wrappers are conversion, so one `change` to the bv-level term (`bv_extract i l (bv_concat n (bv_extract … w) (bv_concat … v (bv_extract 0 i w)))`) is legal and gets you into stdpp's algebra. There, `bv_extract_concat_here` (window at the bottom) and `_later` (window entirely above the split) are all that exists — a field in the MIDDLE (pmpcfg's A at 4:3 of an 8-bit entry) matches neither, `bv_simplify`/`bv_solve` answer *"Cannot find witness"*, and this stdpp has no `bitblast`. Prove the three missing pieces once — `bv_extract_concat_mid`, `bv_extract_extract_0`, `bv_extract_full` (~8 lines each: `apply bv_eq`, `bv_extract_unsigned`/`bv_concat_unsigned`/`bv_wrap_land`, then `Z.bits_inj_iff'` and the `Z.land_spec`/`Z.shiftr_spec`/`Z.ones_spec` chain, exactly as stdpp proves its own) — and compose them; `iris/BootReset.v` §3a is the worked instance (read-back of a field just written, and of a field a LATER write must not have disturbed).
- **A SAIL `vec` UPDATE IS AN stdpp LIST INSERT, AND THE OUT-OF-RANGE READ IS PART OF THE SPEC.** `vec_update_dec v i x` is `list_update (projT1 v) (length - 1 - i) x`, and `Values.list_update` IS `<[k:=x]>` (`insert_take_drop`), which is where the lookup lemmas live: `vec_access_dec (vec_update_dec v i x) i = x` and its `j ≠ i` twin are `list_lookup_insert` / `list_lookup_insert_ne` plus `nth_lookup`, over `projT2 v` for the length. Do NOT skip the out-of-range case: `access_list_inc` falls back on the `Inhabited` default below 0 and `nth` runs off the list above the end, and a predicate like `RiscvLang.pmp_all_off` quantifies over ALL of `Z`, so the fact is FALSE without it. Every index step belongs in an `mword`-free lemma over plain `Z`/`nat` — `lia` answers "Cannot find witness" with an `mword` merely in context, and a `vec (mword 8) 64` in the binder is one.
- **`destruct` CANNOT LEAVE A PREMISE AS A GOAL; A WRAPPER LEMMA + `apply` CAN.** When the term you must instantiate a lemma with comes FROM THE GOAL (a model loop body grabbed by `lazymatch … context[foreach_ZM_up' _ _ _ _ _ ?b]`), you cannot `destruct (lem b _ …)` and discharge the `_` later — it is an elaboration hole, not a goal, and `unshelve edestruct` does not help either. State a wrapper lemma whose CONCLUSION is the shape the call site wants and `apply` it: `apply` leaves every un-inferable premise as a subgoal. The alternative — transcribing the body into an `assert` — is a silent-rot machine.
- **A POWER-ON / RESET SPEC MUST NOT BE ANCHORED ON THE SIMULATOR'S OWN INITIALIZERS.** Running `sail_model_init` as part of a boot anchor narrows the modeled power-on states to exactly the simulator's boots — every register pinned to an ISA-unspecified simulator value — so real hardware powering up with garbage in a register the privileged spec does not reset falls OUTSIDE the theorem. The standing choice for this tree (decided twice) is the weaker, honest model: **garbage everywhere, plus a SHORT EXPLICIT list of board-guaranteed writes (`ArchReset.board_init`, whose comment IS the platform assumption list), plus the spec's own `reset` with its configuration validation.** A register belongs on that list only if some CONSUMED fact does not follow from the spec's reset over an open file — and the list's constants are still held to something: `ColdBoot.board_regs_after_sim` runs the simulator's init and then the board's writes on top and shows every written register reads back unchanged ("the board's values ARE the model's"). Prefer that per-register form over an equality of the two post-states: the redundant `register_set`s leave field functions that are pointwise equal but not convertible, so the state form needs funext *and* a `register_beq` reflection lemma the generated model does not provide.
- **THE ESCAPE FROM AN OPEN REGISTER FILE IS A SYMBOLIC PEEL, AND `iris/BootReset.v` IS THE WORKED KIT** (the whole boot chain — the board's writes, the config assert, the privileged spec's `reset`, the firmware step — over an arbitrary power-on `regstate`: **60 s / 0.77 GB** for the file). Four rules, each learned by paying for it:
  - **The PROGRAM is closed; only `exec`'s interpretation of it touches the state.** So the program may be reduced freely (`eval hnf`) while the state stays a FOLDED `register_set` tower. One lemma per monad constructor (`Next (RegRead …) k` / `Next (RegWrite …) k` / `Next (Message …) k` → the stepped goal, each closed by `refine … ; exact H`) makes one step = one register effect.
  - **RESOLVE EVERY READ THE INSTANT IT IS PEELED** (`register_lookup_set` / `irrelevant_register_set`, then the caller's hypotheses). This is not an optimization: an unresolved read value gets STORED into the tower, the tower then contains a copy of itself, and the term doubles at every later step. The same argument is why `reset_pmp` (whose body reads pmpcfg TWICE and writes a `vec_update_dec` built from both) must be sealed `Opaque` and handled by an induction over `foreach_ZM_up'` that keeps the vector abstract — 64 iterations of peeling it would double the term 64 times.
  - **DISPATCH ON THE PROGRAM'S HEAD CONSTRUCTOR (`lazymatch`), NEVER `first [apply …|apply …]`.** A FAILING `apply` is not free: having failed to match the constructor, unification unfolds `exec` (and a transparent goal-shape definition) and starts EVALUATING the interpreter over the tower — minutes per step, no error, and it can even SUCCEED with the state argument instantiated to a half-reduced `set_reg` tower, after which every later step is off the rails — and by the `unfold set_reg` finding in `optimization.md` such a tower is a **3^N tree** (`set_reg` mentions its state three times), which is why the damage is out of all proportion to the wrong step. Keeping every state in `MState rs m d` form, one `register_set` per step, is what makes the peel linear. Two defences, use both: syntactic dispatch, and make the goal shape an **`Inductive`** (`BootReset.pfin`) so its head can never be unfolded. (An inductive indexed by the program means the constructor's index must match, so prove each step with `refine (Pfin _ _ _ rs' _ HQ); exact H` — `exact (Pfin … H HQ)` elaborates bottom-up, fixes the index from `H`, and fails.)
  - **`hnf` IS ALL-OR-NOTHING, AND BITVECTOR EQUALITY DOES NOT REDUCE UNDER THE LAZY EVALUATOR.** `eq_vec`/`neq_vec`/`uint` on closed words block it, so `hnf` hands back the whole head untouched whenever the head's next decision is one (`currentlyEnabled`'s misa-bit test, `to_bits_checked`'s overflow check, `legalize_xenvcfg_cbie`'s guard). Fixes, in order of preference: walk the head's bind spine by LEMMA (monad associativity stated at `exec`, so no funext) until the test is at the surface and settle it with `vm_compute` on that subterm; or VM the named blocking CALL. **Do NOT VM the blocked head itself** — the `currentlyEnabled`/`hartSupports` cone behind it is a well-founded recursion whose `Acc` guard (`pos_guard_wf`'s `fun y _ => F (F wfR) y`) DOUBLES per bit, and VM-normalising one such head took the file past **7.7 GB** before it was killed. And never `cbv -[…]` (see the negative-delta OOM note).
- **NEVER EVALUATE MODEL CODE OVER AN *OPEN* REGISTER FILE.** `regstate`'s twenty fields are FUNCTIONS (`register_bitvector_64 -> mword 64`, …) and `register_set` wraps one in a fresh `fun r' => if r' =? r then v else <old field> r'`. Over a CLOSED base (`init_regstate`, a `dregs`-style literal) the VM keeps that as a closed value and a 300-write program costs well under a second; over a *variable* base the same run becomes a closure tower whose readback explodes — measured on the cold-boot chain: `vm_compute` >8 min at **4.6 GB**, `lazy` reached **19 GB**, versus 0.75 s closed. Symptom is a "hang" with RSS climbing, not an error. So state any model-evaluation lemma at a concrete register file and transport, or peel `register_set`s by hand (`irrelevant_register_set` + `register_lookup_set`) keeping the tower FOLDED — see the peel-kit bullet above for the worked version.
- **`reg_lookup` is not always the faster discharge.** It is one `vm_compute` over the whole tower, which is the right call for a deep whole-function map — but on a small tower under a full `sie_cap_gpr` context it can fail to come back at all (observed: >3 min on `m2 !!! Regidx csp_rs1 = pa_stk sp0 2`, two inserts deep, in ProofMemmove). If a `by reg_lookup` hangs, peel insert by insert instead; `coqc -time` pins it immediately (the log's last sentence is the one before the hang).
- **`set_solver` on a `gset Arch.pa` goal does not terminate.** Even `{[a]} = {[a]} ∪ ∅` ran >10 min (the address `EqDecision`/`Countable` instances are enormous). Discharge such goals algebraically — `union_empty_r_L`, `dom_union_L`, `dom_singleton_L`, a `_dom` lemma for whatever built the map — and finish with `reflexivity`/`exact`. `set_solver` on a `gset nat` is fine. Same reflex for `decide`-heavy tactics over address sets.
- **`iFrame` never discharges a RUN of separate pure conjuncts `⌜A⌝ ∗ ⌜B⌝ ∗ …`**, and the reflex `iSplitR; [iPureIntro; split_and!; assumption|]` handles only the FIRST — `split_and!` then fails with *"No matching clauses for match"* on the second, because what follows is a `∗`, not a `∧`. An invariant body that opens with N pure conjuncts (DiskInv's `disk_res` has seven) is re-closed with N lines of `iSplitR; [iPureIntro; exact H|]` followed by one `iFrame` for the spatial rest. Related: `split_and!` DOES split `a <= x < b` (it is a conjunction), so a range-discharging tactic must not run after a `split_and!` that already peeled it.
- **Reading a `ghost_map_lookup` against an auth over a UNION** (`ghost_map_auth γ 1 (m1 ∪ m2)`) is `lookup_union_Some_raw`: it yields exactly `m1 !! p = Some v ∨ (m1 !! p = None ∧ m2 !! p = Some v)`. Do not `rewrite lookup_union` and `cbn` — `union_with` leaves a two-way match to case on by hand.
- **`iFrame` does not close a goal `[∗ list] m ∈ [m1; …; mk], P m` over a LITERAL list.** It leaves goals and the closing `}` then fails far away with *"This proof is focused, but cannot be unfocused this way"*. A cons big-op IS a nest of `∗`, so a chain of `iSplitL "Hk"; [iExact "Hk"|].` ending in `done.` works and is fast.
- **`big_sepL_cons` does not elaborate when two `big_sepL`s are in scope** — its `Φ` is left as an evar and ssreflect reports "_pattern_value_ is used in conclusion". You almost never need it: `big_opL` on a cons IS a separating conjunction, so `iDestruct "H" as "[Hh Ht]"` and `iSplitL "Hh"` work directly on `[∗ list] j ∈ (x :: l), …`. Peel the list with `rewrite (seq_cons off rem)` and then destruct. When only ONE hypothesis should be unfolded, scope it: `iEval (rewrite (seq_cons 0 len)) in "Hdst"` — a bare `rewrite` hits every occurrence, including the sibling buffer that a later lemma still needs in `seq 0 len` form.
- **`iApply (big_sepS_subseteq …)` SHELVES its `Affine` side condition, and the failure has no goal attached.** Nothing errors at the `iApply`; the `Qed` reports *"Attempt to save an incomplete proof"* and `Show` says "All the remaining goals are on the shelf". Fix: `Unshelve. intros ?. apply _.` (Found selecting a covered subrange out of a whole-disk big-op in `FsBoot.v`.)
- **A bare `rewrite !big_sepS_sep` in proofmode does not come back**: it rewrites the whole `envs_entails` — hypotheses AND an existentially-quantified conclusion. Scope it (`iEval (rewrite big_sepS_sep) in "H"`, then `iDestruct "H" as "[A B]"`), one split at a time. Same family as the `iEval … in "Hdst"` note above.
- **`++` IN A LEMMA *STATEMENT* PARSES IN `string_scope`** in the usual import set (proofmode's string scope under `Local Open Scope Z_scope`): `disk_read dk o n ++ …` fails with *"has type list (bv 8) while it is expected to have type string"*. Annotate `(… ++ …)%list`. This is the statement-position twin of the recorded local-hypothesis `++` trap.
- **A DOUBLE-QUOTED PHRASE IN A HEADER COMMENT MUST NOT SPAN LINES.** The `*)` ending an intervening line lands inside the string, Coq warns *"Not interpreting `*)` as the end of current non-terminated comment"*, and swallows the rest of the file. (Live example: `FsCrash.v`'s line-260 warning.)
- **`cbn` with NO delta list next to a definition that expands into a 1024-element list is seconds per use.** `fs_blocks` unfolds into a `disk_read` of 1024 bytes and a following `injection` then walks it — measured ~7 s per `cbn` in `FsBoot.v`. Give `cbn` its delta list (`cbn [mbind option_bind]`); `coqc -time` pins it instantly.
- **A `gmap Arch.pa _` written as an explicit BINDER TYPE in a proof file is a Countable-instance trap.** `VirtioProto.v`/`DiskInv.v` (and the other `gmap Arch.pa (bv 8)` homes) deliberately do NOT `Require SailStdpp.Base`/`SailStdpp.Values` — their headers say so. A WP proof file *does* import them, and then a `Lemma` binder `(pin : gmap Arch.pa (bv 8))` elaborates against `@Countable_mword (if 64 =? 32 then 34 else 64)` instead of the instance those files used: the binder is silently a DIFFERENT type and every application fails with an unreadable "has type … while it is expected to have type …" naming two maps that print identically. Fix: write the binder as **`(pin : _)`** and let its first use (`disk_receipt γ p sl pin`) fix the type. Same for any `gmap Arch.pa _`/`gset Arch.pa` binder in an importing file. (This is the binder-position twin of the `SailStdpp.Values` instance leak noted above.)
- **At an accessor↔leaf seam, rewrite the address equation into the PURE side conditions, never into the Iris hypothesis.** An invariant accessor hands out its window at ITS address (`phys_word4 (used_elem_pa (v_cfg v) p) …`) while the memory leaf's bridge (`DiskInv.phys_to_word4`) wants the address the CODE computes. `iEval (rewrite Haddr) in "Hw4"` fails with *"The LHS of Haddr … does not match any subterm"* on a hypothesis that visibly contains it — an `Arch.pa`-vs-`mword 64` ascription mismatch under the accessor's definition defeats ssreflect's matching — while the SAME equation rewrites fine into the pure `is_aligned_paddr`/`kmap_static`/canonicality hypotheses. So: state the equation toward the accessor's form (`pa_add pu off = used_elem_pa (v_cfg v) p`), `rewrite Haddr in Halign Hstatic Hcanon`, and apply the bridge AT THE ACCESSOR'S ADDRESS; only the GOAL ever gets `rewrite Hea Haddr`.
- The Sail model (`Import Defs` / `Riscv.rv64d`) SHADOWS `filter` (a bool list filter) and `not` (bool negation): in model-importing files write `base.filter` for the stdpp map filter and `¬` (never `not`) for Logic negation, or the elaborator demands `bool`. Similarly, do NOT `Require Import SailStdpp.Values` just to name `mword` in a type annotation — it leaks typeclass instances that break unrelated Iris proofs ("Unable to find an instance"); reference it qualified (`SailStdpp.Values.mword`) instead.
- **`repeat split` CLOSES an equality goal whose sides are convertible** (`split` is `constructor 1`, and `eq`'s only constructor is `eq_refl`), so on a `sp_base`-style record of register equalities it silently discharges some conjuncts and every following bullet lands on the WRONG goal — the error surfaces far away as "`H` has type … while it is expected to have type …". It also splits nested `/\`s you meant to keep whole (a `sp_hi m M` conjunct destined for a transport lemma). Use stdpp's **`split_and!`**, which only splits conjunctions, whenever the leaves are equations. (`repeat split` is still fine for a flat conjunction you intend to prove leaf-by-leaf with matching bullets.)
- **`vm_compute; reflexivity` does NOT close `subrange_vec_dec (mword_of_int 0) 11 0 = zeros' 12`** — it fails with *"Unable to unify `0%bv` with `0%bv`"*, the two sides printing identically. `apply bv_eq; vm_compute; reflexivity` does. Same family as the width traps below: reach for `bv_eq` first on any bitvector equality that "obviously" computes.
- **Write `bv_unsigned_in_range _ x`, never `bv_unsigned_in_range 64 x`.** The explicit `64` elaborates the width as `64%N`, while everything else in the tree carries `MachineWord.Z_idx 64`. The two print IDENTICALLY, so `remember (bv_unsigned x) as v` silently fails to abstract the hypothesis, and every later `lia` then still sees a `bv_unsigned` and answers "Cannot find witness". The general escape from that hook when the goal is pure `Z` but the context is full of `bv_unsigned`s is **`clear - H1 H2; lia`**.
- **A BRANCH/JUMP LEAF'S ALIGNMENT SIDE CONDITION IS ABOUT THE *TARGET*, SO `vm_compute` ON IT DOES NOT COME BACK IN A BLOCK LEMMA.** `WpSconfCtl.wp_cj_s_sconf` asks for `eq_vec (access_vec_dec (add_vec pc (sign_extend' 64 jimm)) 0) ('b"0") = true`. In a whole-function proof the pc and the immediate are literals and the reflex `ltac:(vm_compute; reflexivity)` costs nothing; in a **block lemma parameterized by its pcs** (the "gcc emitted this block N times" recipe below) both are VARIABLES, and `vm_compute` then normalizes an open bitvector term and never returns — a file that should take seconds runs for tens of minutes with no error. The block lemma already has the target as a premise (`add_vec (mword_of_int ze) (sign_extend' 64 jimm) = mword_of_int <the label>`); discharge with **`ltac:(rewrite Hjt; vm_compute; reflexivity)`** so the term is closed before it is computed. Measured on `ProofFilecloseParts.v`: >10 min (killed) → **5.5 s** for the whole file. The same applies to `wp_jal_s_sconf`'s target condition, which is why `ProofSysPipe.sp_close2` writes `ltac:(rewrite Ht1; vm_compute; reflexivity)`.
- **A TACTIC IN AN ARGUMENT POSITION WHOSE EXPECTED TYPE IS STILL AN EVAR CAN DIVERGE, AND IT LOOKS EXACTLY LIKE A SLOW FILE.** `exact (conj (conj (Z.le_refl 1) ltac:(discriminate)) …)` — the `ltac:` hole's goal is not determined when the tactic runs (the surrounding `conj`s have not been unified with the target type yet), so `discriminate` runs on an open goal: RiscvExtras.v went from **2 s to >12 min at ~1 GB and climbing**, with no error and no hint of where. Give such a hole a real proof term (`pma_width_ok 1 eq_refl eq_refl`), or `refine`/`apply` first and discharge the goals with bullets. Corollary for the same family: `refine (f a b _ _ c); tac; [g1 | g2]` is malformed — the `;` already sent `tac` to both goals, and the bullet split then has one goal.
- **PREMISE ORDER DECIDES WHETHER AN `eq_refl` BOUND CHECK ELABORATES.** An application's arguments are elaborated left to right and its conclusion is unified with the expected type LAST, so a premise `Z.leb (n - 1) (Z.of_nat k) = true` placed BEFORE the argument that pins `n` fails with *"The term `eq_refl` has type `(?n - 1 <=? 3) = (?n - 1 <=? 3)` while it is expected to have type `(?n - 1 <=? 3) = true`"* — even though every call site passes `n` somewhere. Order a helper lemma's premises so the ones that PIN the indices (the `addr_is_ram a`/`addr_is_ram (pa_add a k)` pair, the width bound `1 <= n <= 4096`) come first and the closed `Z.leb` checks last; `RiscvExtras.pma_access_ram` says so in its comment. Equivalently, spell the indices explicitly at the call site instead of `_`.
- **`first [ unfold A | unfold B ]` UNDER AN OUTER `progress` STOPS A PEEL LOOP ONE BLOCKER EARLY, SILENTLY.** `unfold A` can SUCCEED without changing the goal (the constant occurs somewhere the printer does not show), `first` then commits to that branch, and the enclosing `progress` fails — so the loop reports "no more steps" while the real blocker (`B`) is still there, and the failure surfaces hundreds of steps later as an unrelated unification error. Put the **`progress` INSIDE each branch**: `first [ progress (unfold A) | progress (unfold B) ]`.
- **An `Ltac` body cannot reference a hypothesis by literal name.** `Ltac t := subst c; vm_compute in Hc; rewrite Hxx in H.` resolves those names at *definition* time and errors "Hypothesis c was not found". Worse, a `subst`-based variant can silently fail to peel in a large context while passing in a small standalone test, and the symptom surfaces as a confusing `apply` unification error one line later. Write the tactic name-free (`first [ … ; assumption | congruence ]`, `lazymatch goal with H : … |- _ => … end`); `congruence` sees through `Regidx`'s injectivity, so no `injection`/`subst` is needed for a register disequality. But see optimization.md before putting `congruence` in a peel loop.
- **An argument to a LOCAL hypothesis parses with no scope information.** For a global constant, `f (l ++ bs)` picks list_scope from the argument's type; for a hypothesis (e.g. an induction hypothesis `IH`) there is no `Arguments` scope binding, the innermost OPEN scope wins, and with string_scope open `++` elaborates as String.append — a baffling "has type list … expected string" error at the call. Annotate the argument (`((l ++ bs)%list)`). Related list-append recipe: to feed a continuation expecting `P (l ++ [])` (or a reassociated `l ++ bs ++ bs'`) from a hypothesis about `l`, do NOT `rewrite -(app_nil_r l)` in your own hypothesis — the replacement contains the pattern and the rewrite dies on an evar-scope error. `iSpecialize` the continuation at the concrete lists FIRST, then rewrite the SHRINKING direction in it: `iEval (rewrite (app_nil_r l)) in "Hcont"` (or `(app_assoc l bs bs')`).
- **`tramp_vpn` lives in `KptExecMap.v` and `tf_vpn` in `TrampPt.v`**, not in `UptTree.v` where `tramp_vpn_unsigned` / `tf_vpn_unsigned` are stated. A `proc_pt`-altitude proof that NAMES either constant must `Require Import` those two files directly — `Import` is not transitive. Likewise `KALLOC` / `KFREE` take `γl : gname` AND `γk : gname * gname`; passing only `γk` gives "has type (gname * gname)%type while it is expected to have type gname".
- **AN IMPLICIT BINDER INSIDE A `Definition`'s BODY IS SILENTLY IGNORED, AND A LOCAL HYPOTHESIS OF A Pi TYPE HAS NO IMPLICIT ARGUMENTS AT ALL.** Writing `Definition c : Prop := forall `{GEN : GenId} `{CID : CpuId} …, wp_<f>_body …` — the natural way to name a callee's contract so it can be passed as a HYPOTHESIS rather than a functor argument (ProofBmap.v's `balloc_contract`, which is what keeps the no-alloc instance free of balloc's Axiom) — gets you *"Warning: Ignoring implicit binder declaration in unexpected position"* and two EXPLICIT binders; implicit binders are only honoured in the ascribed TYPE of a `Definition`/`Parameter`/`Lemma`, never in a term-position `forall`. And even where the type does carry them, a hypothesis (`H : c`) is not a global reference, so no implicit-argument metadata attaches to it. Write the binders explicit, spell the body `wp_<f>_body (GEN := GENa) (CID := CIDa) …`, and pass `_ _` at the call site: **nothing is lost, because an evar whose type is a CLASS is still filled by typeclass resolution** — with the most recently introduced `CpuId`, which is exactly what an implicit-instance argument would have picked (and is why every such call site transports `cpu_own` to the current hart first). Related, same family: **`bi.emp_intro` does not exist in this iris** — an `⊢ emp` goal is closed by plain `done`.
- **`pc_is` is not in scope transitively.** It is defined in a Section of `InstrBytes.v` and nothing in a typical ProofSched-derived import list re-exports it, so a proof file that only ever FED leaves compiles fine, while one that STATES a loop invariant (`iAssert (∀ m, … pc_is …)`) fails with *"The variable pc_is was not found in the current environment"* — reported at the line inside the iAssert, and possibly after `-time` already printed a success line for that sentence. Fix: `Require Import InstrBytes.`
- **Replacing a `destruct H as [A|B]` with a `destruct <bool>` does NOT keep the two bullets' order stable, and `cycle 1` cannot be trusted to fix it.** Observed in ProofBread: after the swap the first bullet still received the `true` case, `cycle 1` did not reorder, and the failure surfaced as an `iExact` mismatch printing the OTHER branch's payload (which is what identifies this). Swap the two arm BODIES textually instead of relying on goal reordering.
- **A scripted binder-drop must keep the line's terminator.** Deleting a spec binder line that carried the closing `:` (`(bs_disk : list (bv 8)) :`) produces `Syntax error: ':=' or ':' expected` reported ~40 lines later at the NEXT lemma, with nothing wrong there.
- **`destruct <term> eqn:H` substitutes the scrutinee into pure HYPOTHESES too, not just the goal.** A tie hypothesis shaped `cond = false -> P` becomes `false = false -> P` after `destruct cond eqn:Hc`, and `apply Htie; exact Hc` then fails ("has type … while it is expected to have type false = false"). Same family as the `Nat.eqb_spec` warning in kernel-proofs.md. Escape: `first [exact Hc | reflexivity]`, or restate the tie before destructing.
- **`Qp_scope` has no `<=` notation — only `≤`.** `((1/2) <= 1)%Qp` silently
  parses the `<=` in nat_scope (the `%Qp` only reaches the operands), so the
  "fraction bound" you proved is `0 ≤ 1`. Write `≤` in every Qp side
  condition. (Found writing bio's fraction ties.)
- **`iSpecialize`/`$!` cannot instantiate a `∀ h : CPU` whose BODY IS A BARE CID-INDEXED ATOM.** `Definition D := (□ ∀ h : CPU, panic_wp (CID := h))%I` — then `iIntros "#H"; iApply ("H" $! h)` fails with *"iSpecialize: cannot instantiate (∀ h : CPU, panic_wp)%I with h"*, on a hypothesis the proofmode prints as an ordinary `∀`. It works fine when the quantified body is a wand chain (`∀ h g, trap_csrs (CID := h) -∗ …` specializes normally), which is why every parking contract's `∀ h g mf` continuation is unaffected. Escape: `iPoseProof (bi.forall_elim h with "H") as "H2"`.
- **A whole-function proof's post-resume half must be its OWN lemma with `CID` as a BINDER.** Everything after a `swtch`/park runs at a hart the continuation quantifies over, and a `Context {CID : CpuId}` section variable cannot be instantiated from inside its own section — so the half goes in a separate `Section` BEFORE the main one (same `Module`), with `CID` bound by the lemma, and is applied once as `iApply (f_post (CID := h) g … with "…")`. Its premises are the pre-half register tower's facts restated at the returned file. Worked examples and the full recipe: `claude-notes/completed/sched-hart-generic.md`. Corollary: any `Local Ltac` the half uses must be defined above it, and after `subst eb` every remaining textual `eb` in a tactic argument has to be spelled `true` (a `subst` erases the name; the failure reads *"variable eb was not found"* hundreds of lines away).
- **`csp_rs1` is NOT `mword_of_int 2`** — it is `zero_extend' 5 ('b"10")` (WpMmodeLeafBase.v). The two are convertible, so a statement using either compiles, but `congruence` cannot bridge them: a mid-function register-preservation predicate (`∀ r, is_cs_idx r = true → r ≠ … → M !!! Regidx r = m !!! Regidx r`) stated with `r <> mword_of_int 2` makes every `rewrite /Mk upd_ne; [| congruence]` over an sp-writing layer fail with *"congruence failed"*, one line at a time. **State such predicates with `r <> csp_rs1`** (`s0_idx`/`s1_idx` are plain `mword_of_int` and need no care); the concrete-`r` discharges stay `vm_compute; discriminate` either way.
- **`set (x := e)` does not make `rewrite H` work when `H`'s LHS is `e`.** The abstraction is syntactic and a hypothesis whose LHS elaborated slightly differently (a notation, an ascription) keeps the unfolded term, so `rewrite H` reports *"The LHS of H … does not match any subterm of the goal"* on a goal that visibly mentions `x`. `exact H` still works (conversion sees through the let), and the general escape for a goal `x = v` is **`etransitivity; [exact H | <close the residue>]`**.
- **`cbn match` REDUCES `execR (returnR …)` / `exec (returnM …)` OUTRIGHT, so a following `rewrite execR_returnR_fwd` fails** with *"Found no subterm matching"* on a goal that visibly is a `returnR`. `execR` is a fixpoint matching on the monad term, and `returnR` is a constructor application, so `cbn match` finishes the job itself. This bites when one `destruct b; cbn match` leaves one branch already at `Some (inr v, s)` and the other still a bind: close both with **`apply execR_returnR_fwd`** (unification, not rewriting) or `first [ apply execR_returnR_fwd | reflexivity ]`.
- **Do NOT restate a giant model subterm just to name it in an `assert`.** `match goal with |- context[and_boolM ?A ?B] => assert (Hab : execR (and_boolM A B) s = Some (inr <the value>, s)) end` gets the term from the goal, so nothing has to be transcribed and nothing has to be kept in step with the model when it is regenerated. (Used for `execute_AMO`'s CAS guard, whose second argument is an `if width <=? xlen_bytes` branch already reduced by an earlier rewrite; also the pre-existing idiom for `foreach_ZM_up` in the pmpCheck lemmas.)
- **TWO IRIS ARMS THAT END IDENTICALLY CONVERGE THROUGH AN `iAssert` OVER THE POST STATE.** When a case split's branches differ only in whether memory moved and then run the same long bookkeeping tail, do not duplicate the tail and do not extract an Iris lemma: split inside `iAssert (|==> ∃ sx : mstate, ⌜<the exec fact at sx>⌝ ∗ ⌜sx.(sregs) = …⌝ ∗ ⌜sx.(mdev) = …⌝ ∗ gen_heap_interp sx.(mem) ∗ <the ghost resources>)%I with "[…]" as ">H"`, give ~10 lines per arm, and run the tail once over the abstract `sx`. Worked example: `UserMemClassify.mem_exec_amo_16`'s store vs. CAS-mismatch arms over a 55-line register-PAIR write. (Remember the pure-conjunct rule below: close the `⌜⌝`s with a run of `iSplitR; [iPureIntro; …|]`, not `iFrame`.)
- Section gotchas: a lemma using NO section vars is not generalized over them; `intros ->` on a section-variable equation BREAKS references to sibling section lemmas (state such wrappers outside the section); `Proof using All` generalizes over ALL context vars (callers must then pass them). A section `Variable` (e.g. `root_ppn`) auto-threads intra-file but external callers pass it as the LEADING argument.

## Proof-check speed: what actually costs time in these files

Measured on ProofPrintk.v.  **The "~65 s" figure below is for the 4800-line
version of that file and is now badly stale** -- it grew to 7903 lines long
before the explicit-cpuid branch, and a pre-refactor compile measures **93 s**
(105 s on that branch).  A stale baseline here cost real time: it produced a
"+56% regression" that did not exist, and the arithmetic looked convincing.
Re-measure the baseline before believing any regression claim about this file.  `coqc -time` plus a
per-lemma roll-up is the tool; two findings generalise:

- **`vm_compute` in the leaf side conditions is FREE** -- the ubiquitous
  `ltac:(vm_compute; discriminate)` on `uint (mword_of_int 15 : mword 5) <> 0`
  measures at well under a millisecond.  Do not go hunting there.
- **The cost is Iris unification against `mword`/`bv` terms.**  A bare
  `iFrame.` over a separating conjunction of a dozen `pa_stk sp0 j` cells
  costs ~1 s, because every FAILED match unfolds `pa_stk` through
  `add_vec_int` down to the bitvector records.  Two fixes, both cheap:
  - `Local Strategy 1000 [pa_stk].` -- keeps failed comparisons first-order
    (the slot indices are literals) while `unfold pa_stk` still works where
    the arithmetic is wanted.  `Local Opaque` does NOT work: it blocks
    `unfold` too.  Worth ~8% of the file.
  - name the hypotheses (`iFrame "S9 S19 ..."`) instead of a bare `iFrame.`
    -- 6.5 s to 0.5 s on one seven-way frame.  Give them in the GOAL's
    conjunct order; a wrong order is worse than none (one reordering
    experiment took a frame from 2.2 s to 3.8 s).

- **In a `first [...]` alternation, put the CHEAP-FAILING branch first.**
  The cost of a tactic that FAILS grows with the proof term, so an
  alternation that leads with an expensive-to-fail branch pays that cost at
  every use.  Measured on `ProofProcPagetable.v`'s callee-saved transport:
  `first [ rewrite Hx2 in Hc; vm_compute in Hc; discriminate | exact (H2
  Hx2) | ... ]` cost ~1.3 s per use in the prologue and ~10 s per use in the
  epilogue -- 42 s over the function -- purely in the failures of the first
  branch.  Swapping the four `exact`s (which fail instantly on a type
  mismatch) to the front took every use to milliseconds.  Same total work,
  same proof, one reordering.  The rule of thumb: `exact`/`assumption` fail
  cheaply, `rewrite ... in H` and `congruence` do not.
- **A proof obligation that cannot be discharged may be telling you the CODE
  is wrong.**  freeproc's `p->parent = 0` could not be proved because the
  cell is owned by nothing -- and the reason it is owned by nothing is that
  xv6 writes it there without `wait_lock`, which its own proc.h says is
  required.  The fix was upstream, not a new ownership story.  Ask "is this
  a bug?" BEFORE designing a bundle to hold the resource; modelling a bug
  makes it permanent in the spec.
- **`congruence` is not free in a whole-function context.**  Seconds per
  call once the context is a hundred hypotheses deep.  Where the
  contradiction is known, pass the hypothesis in by name and `exact` it.

Beware when measuring: this is a shared machine.  Wall AND user time swing
30%+ with someone else's load, so A/B by re-running interleaved and taking
the minimum, or align the two `-time` logs sentence-by-sentence and calibrate
on the median ratio of the sentences you did not touch.

Splitting a file to shrink the edit-check loop was tried and REVERTED: three
files cost the same as one for a clean build (the per-file import overhead is
only ~1.8 s), and at a minute per check the single file is not worth the
extra structure.

## Reusable recipes (validated; reuse verbatim)

- **WHEN A MODEL FACT AND A TREE CONSTANT DISAGREE, ASK WHICH ONE DESCRIBES THE MACHINE YOU MEAN TO VERIFY.** `RiscvFetchExec.MISA_C` and the model's `reset_misa` disagreed on misa; correcting the CONSTANT compiles the whole kernel side green and quietly falsifies `DecodeSetU.decode_total_u_set` (extra extensions reach decoder leaves, so the "complete decode image" no longer is), while correcting the model's CONFIG — B and V off, since xv6 is rv64gc and contains neither — makes the constant a derived fact. The cheap edit was the wrong one. Related: **a model regen must be done ONCE with the config unchanged first**, checking `git diff model-xv6iris/` is empty, or upstream drift in the `sail-riscv` checkout masquerades as config fallout. And **flipping one extension can invalidate the config**: the model's own `config_is_valid` rejected V-off until the fourteen V-dependent extensions were disabled too, which surfaces only as `ColdBoot`'s cold-boot evaluation failing at `init_model`'s assert — evaluate `config_is_valid` after any flip.
- **A HAND COPY OF MODEL CODE CAN BE KERNEL-CHECKED: lift the awkward part to a PARAMETER and close the equation by `reflexivity`.** Several generated model functions call a *platform hook* that rv64d declares as an `Axiom` (`cancel_reservation`, `plat_term_write`, the reservation trio). An opaque element of the monad is not a constructor application, so `run`/`exec` — structural fixpoints on the program — are **stuck** on it: there is no interpretation of the enclosing function, and destructing the axiom loses every value. Do NOT re-transcribe the function as a predicate (that is a silent-rot machine). Copy the model's definition verbatim with the hook replaced by a parameter (`ColdBoot.reset_sys_at (hook : M unit)`), prove `<model fn> args = <copy> (<the hook>)` by **`reflexivity`** — the kernel then checks the copy's fidelity, and the elision is provably the only difference — and instantiate the parameter with whatever the hook's documented meaning is (usually `returnm tt`). Works through `>>`/`>>=` at any nesting depth because it is one `Definition`, not a re-association. Worked example: `iris/ColdBoot.v` runs the model's whole cold boot this way and proves `RiscvLang.reset_regs` of the result.
- **WRAPPER RECIPE — generalizing a lemma without churning call sites.** The generic lemma gets the NEW name; the old name becomes a RESTATEMENT `Lemma` with the verbatim original statement, closed by `exact (<generic> <instance> <explicit binders>)`. NEVER make the old name a `Definition`/notation alias — an implicit argument (`dq`, a section variable) becomes positional and every call site churns. This is how the whole S-mode leaf layer went regime-generic (`R : s_regime`) with zero consumer edits.
- **A SPEC BODY'S `let`-BOUND VARIABLES CANNOT BE `rewrite`-UNFOLDED, BUT `exact` SEES THROUGH THEM.** After `cbv beta delta [wp_<f>_sconf_body]; intros pcE sz vpn0 n …`, `n` is a local *definition*: `rewrite /n` does nothing. State every fact about it AT `n` and close it with `exact (<lemma> args)` — conversion does the delta. This is also what makes a callee's post land syntactically right: state the fact at the form the zeta-expanded callee statement shows, prove it with the `let` name.
- **AN EDIT TO A CENTRAL FILE OBSOLETES EVERY `Spec*.v` OVER IT, AND NOTHING REBUILDS THEM.** A downstream agent/session then hits *"Compiled library xv6iris.Spec<X> makes inconsistent assumptions over library xv6iris.<Central>"* with no build running to fix it. The spec files are cheap (~2 s each); `coqc` the ones in the cone by hand after touching `ProcPtOwn.v` / `PtTree.v` / similar, or run the full build before handing work downstream.
- **SEALING ONE PROOF AGAINST SEVERAL MODULE TYPES: the `*Core` functor.** When one function's proof has to be handed out at more than one altitude (uvmunmap is proved once over `BarePt.uptg` and sealed as both `UVMUNMAP` and `UVMUNMAP_BARE`), write an **unsealed** `Module <F>Core (callees…)` holding the whole proof, and then N sealed functors, each `Module Core := <F>Core Args.` plus a short wrapper. The generic lemma elaborates ONCE; the functor application at each Link site is pure substitution and costs nothing (measured: no change to `LinkUvmunmap.v`'s 1.0 s, and the whole generalization came in at +1.3 % of the proof file's 25 s). `Local Lemma`s inside the core functor stay invisible to consumers. This is strictly better than duplicating the proof or parameterizing the *spec* — every existing caller keeps its statement verbatim.
- **DESTRUCT A CALLEE'S DISJUNCTIVE POST AS LATE AS THE CODE DOES, NOT WHERE IT ARRIVES.** When a callee returns `success ∨ failure` and the caller runs a few instructions before branching on the result, those instructions are usually value-INDEPENDENT (`c.mv` into a callee-saved reg, `c.sd` of the returned word into a struct field). Carry the post whole past them and `iDestruct` it at the `c.beqz`. Splitting at the call site instead duplicates every intervening instruction into the failure tail for nothing — allocproc's two tails would each have grown `+0x46`/`+0x48` and `+0x52`/`+0x54`. The cost is that the register fact has to be stated at the uninspected value (`HF7a0 : F7 !!! a0 = mpt !!! a0`) and each arm rewrites it afterwards; that is two lines, versus ~40 duplicated.
- **THE MACHINE'S ZERO HAS SEVERAL SPELLINGS AND THEY ARE NOT ALL CONVERTIBLE.** `zero_reg`, `nullp` and `mword_of_int 0` all denote the 64-bit zero, but only some pairs are convertible: a callee reporting failure as `nullp` (kalloc) or as `mword_of_int 0` (proc_pagetable) will NOT close a `c.beqz` obligation stated at `zero_reg` by `exact`. Keep one tiny bridging lemma per pair (`ap_null_eqz`, `ap_zero_eqz`, `ap_zero_of_int`) rather than debugging it at each use — the failure message points at `regval_into_reg`/`upd_eq` and reads like a coercion problem when the mismatch is entirely in the zero.
- **A `Local Lemma` at a file's TOP LEVEL is reachable by qualified name from another file.** `Local` only suppresses the unqualified `Import` path, so `PtTree.pte_s0` / `PtTree.pte_z_hi_zero` can be used downstream without un-`Local`ing anything. Never re-prove a helper just because it is `Local`.
- **A C LOCAL TAKEN BY ADDRESS.** A 4-byte local can sit in either half of an
  8-byte frame slot (sys_close's `int fd` is at `s0-20`, the UPPER word of
  slot 3), so the stack hands out `↦₈` and the callee's contract wants `↦₄`.
  `InstrBytes.word_pointsto_split4` / `word_pointsto_join4` are that split and
  its inverse, at any dfrac, with `word_lo`/`word_hi`/`word_of_words` spelled
  through `RiscvModelBytes.assemble_bytes` (so every byte obligation is one
  `nth_byte_assemble_len` and no bit-shifting). Take the 8-alignment fact out
  with `word_pointsto_aligned_p` BEFORE splitting — the join needs it and the
  two halves no longer carry it. `StackOwn.stack_own_{4_elim,4_intro}` peel and
  rebundle a 32-byte frame the way `_2_elim`/`_2_intro` do a 16-byte one.
- **"THE POINTER I PASSED IS NOT NULL" IS PROVABLE, NOT AN ASSUMPTION.** A
  callee that null-checks an out-parameter (argfd's `if (pfd)`) has to be given
  the disequality, and by the caller-obligation rule above the caller must be
  able to discharge it. It can, with no assumption about where the kernel
  stack lives: every owned address is canonical (`< 2^38`,
  `RiscvPtsto.mem_canonical`), so an `sp` below 8 would put the next frame slot
  at ~2^64. `StackOwn.stack_own_sp_bounds` reads `8 ≤ uint sp < 2^38 + 8` out of
  one owned slot; `stack_off_nonzero` lifts it to any non-negative offset from
  sp. Both are stated at `mword 64`, not `Arch.pa`, so the rewrites see the
  reduced width.
- **A CODE BLOCK gcc EMITTED TWICE IS ONE LEMMA, PARAMETERIZED BY ITS PCs AS LITERALS.** sys_pipe has two copies of "close both files, return −1" and three of "p->ofile[fd] = 0"; each is one section lemma taking the block's `instr` facts and pc-successor equations as premises. Parameterize by the **pcs themselves** (`za zb zc … : Z`, instantiated `(SP + 0xc4) (SP + 0xc8) …`), never by an entry offset `a` with `a + k` arithmetic: an `instr` fact whose address must be *converted* to match (`0xb8 + 2` against `0xba`) makes every `iApply` reduce a `Z_to_bv` over a kernel address. Discharge the pc equations as named `assert`s once, outside the WP goal, and pass the names. Worked example: `ProofSysPipe.sp_close2` / `sp_ofile_null` (`claude-notes/completed/sys-pipe.md`).
- **DECODE-WORD DEDUP SWEEP — two rules, both validated three times** (the copy-inout sweep, `completed/copy-inout.md`; the either_copy sweep, `completed/either-copy.md`; the bio sweep, `projects/bio.md` — where FIVE of seventeen words had only offset- or mnemonic-named homes, so a word-keyed grep would have found none of them). A word proved privately in two or more `Wp*Decode.v` files belongs in `KernelRvcDecode.v`, and so does the load/store SHAPE lemma that converts its cregidx AST to the literal-displacement form a WP leaf takes (`cshape_653c` / `cshape_68a8` / `cshape_6928` are the pattern). (i) **Grep the STATEMENT, not the word.** Some homes are offset-named (`wdec_1c`, `pmsdec_48`) and shape lemmas are named per-FUNCTION (`fa_ld80` / `fs_ld80` / `vf_ld80` / `ec_ld80` were four copies of two lemmas), so a word-keyed grep finds none of them. (ii) **Diff every `*_<off>` instruction fact against HEAD when you are done** — extract the statements from `git show HEAD:<file>` and from the working tree and compare; only the decode lemma each is proved FROM may change. Both sweeps came out at 0 mismatches, and a slip there is silent: it changes what the proof is about without failing.
- **`iFrame` on a goal that mentions `proc_priv` does not come back.** Framing an `fd_slot` into `(A ∨ B) ∗ fd_slot ∗ fd_slot` sends iFrame searching inside `proc_priv` — sixteen `ofile_slot`s and a 4096-byte trapframe page deep. Split the conjunction FIRST (`iSplitR "Hua Hub"; [| iSplitL "Hua"; …]`) and use `iExact` on the leaves. Same rule for `iDestruct … as (γ) "#(…)"` on a bundle like `KvmSpec.kalloc_env`: `rewrite /kalloc_env` first so the `IntoExist` search never enters the lock invariant.
- **Large pure-map / big-literal work** (e.g. a page-table map built by `pt_insert_run` over 16384- and 31977-page regions — KvmMap.v is the worked example). These are not micro-optimizations; each mistake is a 200 s+ compile or an OOM:
  - **Peel ONE run at a time with the accumulator kept FOLDED.** Never unfold a chain of run-inserts into a single term before rewriting — every subsequent rewrite then traverses the giant term and the cost compounds to a timeout. Write per-step peel helpers (`kvm_m*_peel`).
  - `Typeclasses Opaque`/`Opaque` do NOT stop kernel/`rewrite` conversion. The folding discipline above is the only real fix.
  - `cbn` unfolds `pte_set_ad` and `bv_unsigned`-of-literal; use `cbn [fst snd]`.
  - **Never `simpl`/`/=` to reduce a RECORD PROJECTION whose record holds a derived set or a bitvector address** — name the fields: `cbn [ud_root ud_tfp ud_um]`. A `rewrite /a /b /=` on `proc_pt (upt_desc root tfp)` (ProcPtOwn.v) went from 11 s to >16 min *without returning*: `/=` walked into `um_pas ∅` (a `⋃`-of-`list_to_set` footprint), `page_base` (a `zero_extend'`/`concat_vec`), and the 4096-conjunct big-op bodies. `coqc -time` pins this instantly — the log's last sentence is the one *before* the offending tactic, so the hang is always in the next one.
  - Folding one call's post into the next accumulator with `change`/`reflexivity` makes the KERNEL normalize the fixpoint over the page count (220 s+, >2 GB RSS). Discharge such a `⌜pt_rep0 t' m_k⌝` obligation with `unfold m_k; exact Hrep'` — one delta step plus a syntactic `exact`, no normalization.
  - `lia` fails on large-literal and evar goals under the `bitvector.tactics` zify hook (see the gotchas above), and ALSO fails when ANY `mword` is merely in CONTEXT. Package the arithmetic into `mword`-free top-level helper lemmas and apply them as closed facts; project booleans explicitly (`Z.leb_gt`/`Z.ltb_ge`).

## Spec-design preferences (durable)

- **Cleaner specs and abstractions beat avoiding rework** (see the guiding principle at the top of this file). Refactor or rewrite freely to reach a better shape; do NOT keep near-duplicate lemma families, awkward interfaces, or leaky abstractions merely because they already compile. Prefer one parametric lemma over a cross-product of special cases.
- **STATE A HARDWARE-ATTRIBUTE OBLIGATION AS WHAT THE CONSUMER CONSUMES — AND *MEASURE* WHAT THAT IS BEFORE WEAKENING IT.** Two instances, and they came out opposite ways. `RiscvLang.reset_regs`' PMP clause used to pin a 64-entry `pmpcfg_boot`; every consumer (`SpecEntry.wp_entry_boot`, `BootBridge.boot_bridge`) already quantified over the value and took only `pmp_all_off` of it, so the clause became `pmp_all_off (register_lookup pmpcfg_n rs)` and the ripple was three lines. The sibling `mseccfg = 0` pin looks identical — architecturally only PMM and MLPE matter — but the grep says the WHOLE 64-bit value is consumed, by a *proof-engineering* artifact: the fast concrete-state decode bridge's read-frame congruence (`WpDecodeBridge.exec_goodb_congr`) transports a decode from a reference state on the condition that the two states AGREE on every register the program reads, and `goodb` cannot express "reads it but the value cannot matter" — so 1220 per-word decode lemmas rest on the pin. **A read-frame/agreement bridge is whole-value by construction; a field-wise obligation above one is unprovable until the bridge itself changes.** So before restating an over-claiming conjunct field-wise, follow the pin to its LEAF consumers (`grep` the premise, not the register), and if a congruence bridge is one of them, price that out first (measured: running the bridge at a symbolic reference value costs 15× on the `goodb` obligation and does not return at all on the concrete-decode one — a single symbolic leaf inside a `regstate` field function is enough, the open-register-file rule above in miniature). Full account: `claude-notes/projects/crash.md`, "MSECCFG / MENVCFG PATCH SHARPENING".
- **STATE A HARDWARE-ATTRIBUTE OBLIGATION AS WHAT THE CONSUMER CONSUMES, NEVER AS A PINNED ENUM LEVEL.** `RiscvFetchExec.pma_allows_ram` used to pin `PMA_atomic_support = AMOSwap`; the U-mode AMO classifier then *concluded a fault* for a user-mode `amoadd`, i.e. the pinned level leaked into a theorem about the machine and made it FALSE (the real DRAM is AMOCASQ). The conjunct is now `∀ op n, Z.leb n 16 = true → pma_allows_atomic_op … op n = true` — "every AMO the decoder can produce is permitted" — which every consumer instantiates and no consumer can over-read. Two shape rules that came with it: make such a conjunct a `∀` rather than a conjunction (a `∀` survives the `repeat split; assumption` that config-bundle preservation proofs end with), and state the side condition as a **`Z.leb … = true`** so a literal call site discharges it with `eq_refl` (`Hatomic AMOSWAP 4 eq_refl`).
- A `stack_own` (or any) resource bound must be the function's own max depth as a CONSTANT, stated `∀ n, (K ≤ n) → … stack_own sp n` — never a value coupled to the function's arguments.
- **A spec whose function ACQUIRES a lock and then calls a callee that itself acquires must state `Z.of_nat n + 2 < 2^31`, not `+ 1`.** The callee runs at level `S n`, its own premise becomes `n + 2`, and the `+1` form is unobtainable at the call site — `cpu_cells`' own `⌜n < 2^31⌝` at level `S n` gives back only `+1`, and nothing else carries a nesting bound. The gap compiles and surfaces only at the callee application, far from the spec. Precedents: SpecPipeclose, SpecConsoleintr, SpecDevintr, SpecUartintr, SpecVirtioDiskIntr, SpecLogWrite.
- **Model undefined behaviour as "anything", never as "nothing".** A transition
  that is merely ABSENT from a model silently excuses the software that caused
  it: a WP over that model is then provable for code that in reality corrupts
  memory. So when the software does something the hardware calls illegal, either
  model what the hardware really does, or give the model a transition that may
  do ANYTHING — and let the proof obligation of ruling that out fall on the
  software. This bites hardest for a device the software configures: a
  misconfigured device that quietly does nothing lets a conditional obligation
  ("if the device acts, its writes are bounded") be satisfied vacuously. State
  such obligations POSITIVELY instead. Config-time misuse is the one case that
  belongs elsewhere: refuse the offending MMIO write, so a stuck CPU store makes
  it the driver's obligation. Worked example: `claude-notes/completed/virtio-disk.md`.
- **A caller obligation that the caller cannot actually discharge is a design smell — absorb the arm with the contract of the code that handles it.** xv6's `acquire` re-checks `holding(lk)` and panics; a non-holder provably knows nothing about `lk->cpu`, so proving that arm dead would need callers to thread a per-(lock,hart) "I don't hold it" ticket. The right shape is the `panic_wp` convention (SpecPanic.v): `panic` never returns, so a `□`-persistent safety WP for it closes the arm at zero cost to callers, and the spec honestly reads "acquires, or panics".
- **An invariant that takes an EXCLUSIVE ghost fragment across a sleep must
  RECORD the fragment's value.** If the invariant stores it under an
  existential (`∃ bs, … disk_bytes γ off bs`), the process that handed the
  fragment in and then slept gets back a resource about an OPAQUE value and can
  never identify it with what its own caller gave it — its postcondition
  becomes unprovable, and the hole only surfaces at the very end of the proof.
  Put the value in whatever per-position record the invariant already keys on
  (worked example: `VirtioQueue.vslot.vs_data` was extended to record a READ
  request's block content, which is what makes `virtio_disk_rw`'s read
  postcondition provable — claude-notes/completed/virtio-disk-rw.md).
- Avoid ad-hoc argument couplings in preconditions (e.g. a precondition like `eq_vec (m0!!!a2) zero_reg = Nat.eqb N 0` that ties an argument to a branch condition). Prefer deriving branch conditions internally / a natural contract; if a coupling is genuinely unavoidable, flag it and confirm the form before building it out.
