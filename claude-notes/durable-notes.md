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

**A HOIST PROPOSED BECAUSE TWO NEAR-DUPLICATES CANNOT SEE EACH OTHER IS
USUALLY A GENERALIZATION IN DISGUISE.** When the reason given for moving a
lemma is "its twin lives in a sibling file and neither may import the other's",
check first whether making them HYPOTHESIS-FREE makes them the same lemma. The
worked instance: kerneltrap's `if ((sstatus & SPP) == 0) panic` and usertrap's
`if ((sstatus & SPP) != 0) panic` each carried a two-lemma pair in their own
parts file, and both pairs are readings of ONE equation —
`WpGprCsrwC.sstatus_spp_mask`, whose statement takes no hypothesis at all
(`… = negb (Z.testbit (bv_unsigned (_get_Mstatus_SPP ms)) 0)`), leaving each
handler one `rewrite`. Four lemmas became one plus two corollaries. The import
problem was the symptom; the special-casing was the cause.

## Orchestration: model roles and division of labor

The **top-level agent runs on a powerful model and owns the high-level thinking**
— the specifications, the overall design, the abstractions — i.e. the work the
guiding principle above is about: getting the shapes right before anything is
built on them. It **spawns subagents on smaller models for the lower-level,
mundane work**: the actual proofs, mechanical ports, and similar.

A subagent hitting a problem is a signal back to the orchestrator, not just a
local obstacle. **Difficulty at the proof level often means the spec or
abstraction is wrong**; the orchestrator should revise the design rather than
push the subagent to force a proof through an awkward interface.

## Maintaining these notes

Any project memory worth keeping goes in `claude-notes/`, committed in the repo —
not in local per-session memory files. Record only what is useful for **future** development: architecture, conventions,
gotchas, and techniques that will recur. **Everything else is deleted, not
archived in place.** In particular:

- **No play-by-play.** Once a change has landed and its lesson is captured as a
  forward-looking rule, the narrative of how it went goes away. State current
  behavior as fact — never "X used to do Y", "Z is now fixed", "the sweep was
  run and six files landed".
- **No status commentary, no dates, no stage journals** in a durable file. A
  design note says what the design IS. A project worklist says what is LEFT.
- **A fact about something that no longer exists is deleted.** A deleted
  apparatus, a fixed upstream bug, a superseded design — these leave a rule
  behind, if anything, and nothing else.
- **A measurement is durable only when it sets the SCALE of a rule** ("~5 s per
  call", "20×"). A measurement that only records what one run of one sweep did
  is not.
- **Trim on the way past.** If you read a file to do your task and it has grown
  gunk, cut it then — do not add a section about how you found it.

Put it in the right file: durable rules here; performance/build tuning in
[`optimization.md`](optimization.md); subsystem design under [`design/`](design/);
an in-flight worklist under [`projects/`](projects/), one per effort. A finished
project — no remaining work, no cleanup — moves to [`completed/`](completed/),
which nobody reads for guidance and which is therefore the one place a narrative
may survive; lift any broadly-applicable lesson up into the design or durable
notes before it goes. Add a pointer line to [`README.md`](README.md) for any new
file, and delete the line when the file goes.

## Build

- Working dir: `/shared/xv6rocq/iris`.
- Single file: `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden <file>.v`
- Full build: `make -f CoqMakefile -j16` (CoqMakefile auto-regenerates from `_CoqProject`; coqdep decides order).
- ALWAYS grep the build log for `Error` — `make …; echo $?` masks make's exit via the echo.
- **PICK `-j` BY RAM, NOT BY CORES.** A `Code*.v` worker peaks near **2 GB** and the `Code*` band runs many at once, so `-j` above `RAM_GB / 2` gets workers OOM-killed — which make reports as **`Error 137`** with no Coq error at all, on whichever targets happened to be in flight. Re-derive the bound on the machine you are on; the `-j16`/`-j32` figures elsewhere in these notes are from a large one.
- Never `git add -A` from a parent dir (sweeps sibling untracked trees `coq-sail-stdpp*/`, `lean/`, `rocq/`, `sail-riscv/`); use `git add -A .` from `iris/`.
- The build's shape (critical-path bound, where the CPU goes, what does and does not move it) is in [`optimization.md`](optimization.md) §"Build shape".
- **opam switch:** everything builds in the project-local switch `/shared/xv6rocq` (Rocq 9.0.1, coq-iris 4.4.0, coq-stdpp/-bitvector 1.12.0, coq-sail-stdpp 0.20.1). `eval $(opam env --switch=/shared/xv6rocq)` is mandatory in any raw `coqc` invocation — a fresh shell defaults to the wrong switch (→ "Cannot find SailStdpp.*"). Rocq ≥9.1 is not an option (coq-sail-stdpp 0.20.1 is capped `< 9.1~`).
- The generated Sail model (`Riscv.rv64d`, defines `try_step`) is NOT an opam package — rebuild from `/shared/xv6rocq/model-xv6iris/` in order `rv64d_types.v → riscv_extras.v → rv64d.v`.
- **Stale `.vo` trap:** compiling a new file against stale sibling `.vo` produces *impossible-looking* arity/alignment/"expected X" errors, and every address `vm_compute`s to an OLD literal after a `kernel-rocq` image regen. Whenever an argument-count or address error looks impossible, check `.v -nt .vo` and `make proofs` to resync first.
- **A `git pull` THAT TOUCHES `model-xv6iris/` MEANS `make model` FIRST, AND THE FAILURE LOOKS NOTHING LIKE A STALE MODEL.** The generated Sail model is not an opam package and nothing in `iris/`'s own makefile rebuilds it, so a pull that lands a new `rv64d.v`/`rv64d_types.v` leaves every `.vo` in the tree consistent *with each other* but stale against the new sources. Nothing breaks until make tries to rebuild the first file whose source also moved — typically `RiscvLang.v` — at which point you get a single bottom-of-the-tree error naming a model field, e.g. **`PMA_misaligned_atomicity_granule_size_exp: Not a projection`**, with the whole build behind it. That reads like a corrupt checkout or a broken proof; it is neither. The recovery is `make model` (rebuilds `rv64d_types.v -> riscv_extras.v -> rv64d.v`), then a full `iris/` rebuild — which is a near-total recompile, so budget for it. Check `ls -la model-xv6iris/*.v model-xv6iris/*.vo` after any pull: a `.v` newer than its `.vo` is the tell, and it is much cheaper to notice there than at `RiscvLang.v`.
- **NEVER RUN `make`/`coqc` FROM A SHELL WITHOUT `eval $(opam env --switch=/shared/xv6rocq)` — INCLUDING BACKGROUND ONES.** A `nohup bash -c '...'` does not inherit an interactive shell's opam env, and the resulting failure is a bogus *"Cannot find a physical path bound to logical path bitvector.definitions with prefix stdpp"* at `RiscvLang.v` that is indistinguishable at a glance from the stale-model error above. Worse, `iris/CoqMakefile` auto-regenerates from `_CoqProject`, so a make run under the wrong switch **rewrites `CoqMakefile` with the wrong Rocq version** (the file then says `generated by Rocq/Coq 9.1.1` while the switch is 9.0.1) and every later build inherits it. Recovery: delete `iris/CoqMakefile` (and `CoqMakefile.conf`) and let a correctly-switched `make` regenerate them. Chain the `eval` into the same command as the `make`; do not assume it persists.
- **AFTER ANY `git pull`, THE IMAGE IS THE FIRST SUSPECT — and every way it goes wrong surfaces as the SAME bogus address failure** at the bottom of the tree (`Unable to unify "2147558264" with "2147558418"` in `ProcGeom.v` / `ColdBoot.v` / `BootReset.v`, taking all 145 `Code*.v` with it). It reads like a broken proof or a corrupt checkout and is neither. **Sequence after any pull that touches `kernel-rocq/`: `make xv6-rev-check` → `make kernel-rocq` → the `iris/` build.** Three independent causes, all with that one symptom:
  - `xv6-riscv/` is gitignored, so a pull that bumps `XV6_REV` leaves your clone on the OLD revision — and `make proofs`' dump rules then see an ELF newer than the freshly-checked-out `kernel-rocq/*.v` and **silently re-dump from the stale ELF, clobbering the tracked image**. Recover: `git checkout -- kernel-rocq/`, fix the clone (`git -C xv6-riscv fetch && git -C xv6-riscv checkout --detach $XV6_REV`), rebuild the ELF, `make dump-force`, and confirm `git status kernel-rocq/` is **clean** — a byte-identical re-dump is the proof that the toolchain and the revision agree.
  - **`kernel-rocq/*.vo` is rebuilt by nothing in `iris/`**, and neither `dump-force` nor `make -C iris -f CoqMakefile` has a rule for it — so new tracked sources sit beside whatever `.vo` you last built and every proof loads the OLD image. `make xv6-rev-check` and `make check-decode` both PASS (they read the `.v`), which is the tell. Compare `ls -la kernel-rocq/*.v kernel-rocq/*.vo` mtimes; it is a two-second check and it is the first thing to do.
  - `make proofs` does not depend on `user-rocq`, so a tree with `USpecSync.v` in `iris/_CoqProject` also needs `make user-rocq` (else `No rule to make target '../user-rocq/SyncInstrs.vo'`).
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
- **A `nat` EQUALITY WHOSE RHS IS A LARGE LITERAL NEEDS `Z`, NOT A BIGGER STACK.** Any route to closing such a goal — `reflexivity`, `vm_compute`, even `vm_cast_no_check` — eventually materializes a literal-deep unary successor chain and overflows a normal 8 MB stack outright, deterministically, in under 4 s and under 1 GB RSS. So it does NOT look like memory pressure or a `-j` artifact; it looks like a broken proof in a file you did not touch. `Z` literals are binary `Z.pos` trees (~log2 depth), so state the fact at `Z.of_nat (…) = <literal>` (`rewrite Nat2Z.inj_mul` first if the LHS is a product) and close with `vm_compute; reflexivity`.
  - **If a CALLER genuinely needs the fact AT `nat`**, do not restate it over `nat` — that regresses straight back to the overflow, and it hides: `reflexivity`/`vm_compute` on the small unfolded factors (`268 * 1024`) succeed FINE in isolation and only overflow inside the real file's Iris/stdpp-heavy import context, so a standalone test says it is safe. `lia`/`nia` cannot bridge it either — past Rocq's abstraction threshold (~5000) a `nat` literal elaborates to an opaque `Nat.of_num_uint`, which `lia` cannot relate to a *computed* product (`(268 * 1024 <= 274432)%nat` fails with "Cannot find witness" though both sides are closed numerals). **Derive the `nat` fact from the `Z` one via `Z.to_nat`**: state `… = Z.to_nat <literal>`, prove `rewrite <- <the Z lemma>, Nat2Z.id; reflexivity`. Both rewrites are symbolic, so it is O(1) regardless of context, and `lia` resolves `Z.to_nat` of a literal symbolically downstream — a transparent drop-in.
- **Compile-time budget: a single file taking over ~5 minutes is a RED FLAG, not a cost to absorb** — something in a proof is degenerate (a `rewrite ?lemma_a ?lemma_b …` chain over an opaque tower, an unbounded `repeat rewrite` peeling into `s_rs`/`mm_rs`, `set_solver` over `gset (mword n)`, `cbn`/`vm_compute` on data-bearing terms, `iFrame` over a huge context). Bisect with `Time` per lemma and fix the offender; do not ship the slow proof and do not raise timeouts around it.
- **Fork/parallel discipline:** `make clean-proofs` nukes the shared `.vo` tree and breaks concurrent siblings — a fork must `coqc` only its OWN file, one compile at a time. NEVER `pkill` coqc/rocqworker AT ALL in a shared checkout — not `-f`, not `-x`: `pkill -x coqc`/`pkill -x rocqworker` kills every SIBLING agent's compile too (one agent doing this at the start of each iteration killed ~15 of another's builds and cost a session). Kill only your OWN compile, by the PID you started (`$!` of your background command, or the PID from `run_in_background`). The same self-match trap breaks WAIT loops: `until ! pgrep -f "CoqMakefile -j16"; do …` never terminates (the waiter's own command line contains the pattern) and then makes `pgrep -f CoqMakefile` report a phantom in-progress build to everyone else. Don't poll processes at all — have the build write its own sentinel (`…; echo "EXIT=$?" >> log`) and wait on `grep EXIT` of the log. **And never `git stash` in a shared working tree** — the stash captures every concurrent agent's uncommitted edits along with yours, and the pop conflicts with (or silently wipes) work you never saw. For an "untouched baseline" compile, `git show HEAD:iris/<f>.v > /tmp/copy.v` and compile the copy; leave the live tree alone. **The same rule kills `git commit -a` and `git add -A`**: a sweep-everything commit lands every OTHER agent's in-flight files under YOUR message, and the loser finds their increment already committed, unattributed, with its own record gone missing — one increment's five files were absorbed into a sibling's commit exactly that way. Commit by explicit path (`git commit <paths> -m …`), and before you do, `git status --porcelain` and account for every line that is not yours. **`git commit --amend` and any `git reset` (even `--mixed`/`--soft`) are in the same family**: an amend folds YOUR delta into a SIBLING's last commit (their message, your file), and a `reset` to an older commit drops the siblings' commits off the branch (one lane's commit was wiped that way; the file survived only because it was still on disk). Never amend or reset in a shared tree; if you committed the wrong paths, add a NEW commit that fixes it. Likewise NEVER leave anything staged in the index (`git rm --cached`, `git add` without an immediate commit): a sibling's `git commit <its paths>` will absorb your staged entry into ITS commit. Delete with plain `rm` and let `git commit <path>` record it. Corollary for the reader of a shared tree: `git status` is not a private view, so a file you did not touch appearing modified means a sibling is live — re-check the MIRROR's md5s before trusting any build you started.
- **A SINGLE-FILE `coqc` LOOP SILENTLY ACCEPTS A STALE BASE, AND IN A TREE THAT BUILDS ON THE VM THE LOCAL BASE IS ROUTINELY A WHOLE COMMIT BEHIND.** `coqc <one file>.v` loads sibling `.vo` without ever comparing them to their `.v`, so a checkout whose `.vo` were pulled back (or last built) before a mid-tree commit compiles new work happily against the OLD interfaces — for hours, with `git status` clean and every proof green. The tell is one `ls`: `ls -la iris/*.v iris/*.vo` and look for a `.v` NEWER than its own `.vo` (here `UserExec.v` was, by a commit that changed `user_cfg`'s conjuncts and two step engines' invariant masks). The damage is a file written to the old interface that no local check can fail. **Before starting a session of single-file work, run one `make -f CoqMakefile -j<N> -k` (or the VM equivalent) to establish that the base is current**, and validate anything that reaches into an engine's internals — a new leaf file, anything mirroring `WpUmodeStore.v` — with a real build, not a `coqc`. The GCP tree keeps its own `.vo` and rebuilds from synced sources, so `run-on-gcp make` is the cheap authoritative answer.
- **`make` SAYING "Nothing to be done" WITH ZERO COMPILE LINES IS NOT A GREEN CONE — ON A SHARED BUILD BOX IT IS USUALLY A MTIME ARTEFACT.** A whole-tree sync (`rsync -a`, a `tar` restore, a bulk `touch` of `*.vo` to force "staleness 0") leaves every `.vo` newer than every `.v` — check with `ls --time-style=full-iso`: **identical timestamps to the NANOSECOND across unrelated files is the tell**, and no compile ever produces that. `make` then skips the cone you meant to validate and reports success, which is indistinguishable at a glance from a real green. Force the cone instead of trusting it: take the reverse transitive closure of the file you edited out of `iris/.CoqMakefile.d` (the `X.vo: … Y.vo …` lines are already the dependency graph), `rm` those `.vo/.vos/.vok/.glob`, then `make -f CoqMakefile -jN -k`. The closure is small for a leaf-ish file (`DirLinks.v` → 142) and it is the only way to know the consumers actually recompiled. Do NOT reach for `-B`: that rebuilds the whole tree.
- **A PARTIALLY-BUILT LANE HOLDS TWO GENERATIONS OF `.vo`, AND "STALENESS 0" FOR ONE TARGET PROVES NOTHING ABOUT A NEW ONE.** A lane built by `make <one>.vo` is green and `make -n` emits 0 compile lines — for that chain. The first file you add that Requires something OUTSIDE it dies with **"Compiled library X makes inconsistent assumptions over library Y"**, which reads like a corrupt checkout and is not one: X was compiled against an older Y, and `make` will never notice because every stale `.vo` is still newer than its own `.v`. **The mtime test that finds them is not "older than the file that was rebuilt"** — that flags every base file the rebuilt one sits on top of (27 false positives out of a 208-file chain) — **it is "older than a `.vo` it DEPENDS on", iterated to a fixpoint** over `iris/.CoqMakefile.d`. `rm` the few that names and re-make. And after adding a `_CoqProject` row, regenerate with `coq_makefile -f _CoqProject -o CoqMakefile` **chained into the same command as the `eval $(opam env …)`** — a regeneration under the wrong switch stamps the wrong Rocq version into `CoqMakefile` and every later build inherits it.
- **DO NOT `set (pj := proc_addr j)` IN A BLOCK LEMMA.** A callee's contract carries its own `let pj := proc_addr j`, so its postcondition hands resources back spelled `proc_addr j`; a walk that folded its goal with `set` then meets them unfolded, and the hart-mismatch error it is really looking at (`iSpecialize: cannot instantiate (cpu_own 0 eb … -∗ …)`) loses its usual tell — the two propositions printing IDENTICALLY — and looks like a `pj`-vs-`proc_addr j` problem instead. Spell the address out and read the error as what it is: a missing `cpu_own_transport`. Plain instructions between a callee's return and a block's seam move the hart just as a call does, and a seam stated over a `∀`-bound `CpuId` demands the transport that the seam's own binder makes invisible. (`ProofSysUnlink.su_w1`'s seam at +0x30, two instructions past nameiparent.)
- **THE REBUILD CONE IS THE DEV-LOOP COST — know it before you edit, and route around it.** Touching `ProcInv` rebuilds 316 dependents ≈ 4–5 min wall at `-j28`; `BioInv`/`InodeInv`/`LogInv`/`FileInvDefs` ≈ 350 files; `WpLock` 548; `IntrDefs`/`SmodeCore` 600–700. `Spec*` files are cheap (3–29 dependents) — the spec-module architecture works. Three consequences:
  - **While iterating, build the CHAIN, not the cone:** `make -f CoqMakefile Proof<X>.vo` compiles only the prerequisites of the one file you care about (seconds after a mid-tree edit), and a single-file `coqc` checks the file you edited. Pay the full cone ONCE, in the validating `make -j` before landing — never per iteration.
  - **An ADDITIVE change to a shared invariant file belongs in a NEW leaf file** (`ProcInvExtra.v`-style, folded back at a milestone): a new file Requiring `ProcInv` costs only itself; a new lemma INSIDE `ProcInv.v` costs the 316-file cone on every iteration that recompiles it.
  - **`-vos` is NOT a fast cone check in this tree and do not reach for it:** everything lives inside `Section`s, so vos still runs all the tactics and skips only the kernel check — ~40 % per file, and a whole cone at `-j16` is no better than the real vo cone at full `-j`.
- **Profiling:** per-file times via `make TIMED=1` (or `make proofs TIMING=1 JOBS=32` → per-sentence `*.v.timing`, parse `Chars A-B [snip] T secs`, map offset→line); per-command via `coqc -time`. Delete `*.v.timing` after (don't commit). Measure any `vm_compute`/decode tactic ONE variant per `coqc` process — the 2nd variant in a process wins ~35 % from bytecode-cache reuse (fabricates false savings). **`tools/proof_profile.py` does all of it in one pass** (most-expensive statements/files, the weighted critical path, a parallelism chart) and runs in CI on every checkin, emitting to the job's step summary. Locally: `python3 tools/proof_profile.py --build-log <TIMED-log> --iris-dir iris --out-dir /tmp/prof --jobs $(nproc)`. Two traps:
  - **`TIMED=1` needs `--output-sync=target`** or the log is not parseable: each record is written by its own `command time` to the one pipe `tee` reads, non-atomically, so under `-j` two records interleave *inside* a line and none survives. `-O` changes nothing the profiler measures.
  - The CI step is `continue-on-error`, so a profiler crash shows as a green run carrying only a `Process completed with exit code 1` annotation — which reads exactly like a broken proof build. **When CI looks green but a run page shows that annotation, check which step it came from before assuming the proofs broke.**
- **A FAILING TACTIC IN A WHOLE-FUNCTION WP LOOKS LIKE A HANG.** Rocq prints the entire goal with the error, and a syscall-altitude goal contains `ProcInv.tf_page`'s **4096-conjunct** big-op plus every `iAssert`ed continuation; formatting that takes tens of minutes, so a one-line mistake reads as an infinite loop and every "where did it stall?" reading is wrong. Put **`Set Printing Depth 40.`** at the top of any file that proves over `proc_priv` — it turns a 40-minute non-answer into a 30-second error message. **Before hunting a "hang", check that the proof is not simply *wrong*.**
- **A COMPILE THAT NEVER FINISHES IS LOCALISED BY `coqc -time`, WHICH STREAMS** — the LAST LINE IN THE LOG IS THE STALLING SENTENCE, so redirect to a file and `tail` it. (Map `Chars A - B` to a line with `head -c B <f>.v | wc -l`.) **The failure mode to suspect first is a MIS-STATED `∀`-PREMISE**: a premise that binds variables it then does not use in its body (`∀ aq0 rl0, … <the OUTER aq rl> …`) can never be supplied, so `iMod` spins forever on the unification instead of failing. Grep for that shape; if the same names are in scope outside, Rocq's renaming (`aq0`) is the only hint in the error message, and only if you get one at all.
- **`timeout N coqc` does NOT kill the worker, and `pgrep -x coqc` does NOT find it.** `coqc` runs as `rocqworker --kind=compile`, so an exact-name wait loop returns while the compile is still going (giving truncated logs and phantom "stalls"), and `timeout`'s SIGTERM reaps only its direct child. The orphan then spins at 100 % and **holds a worker slot, stalling the next build at a random point** — which is what makes the stall location look non-deterministic. Wait on `pgrep -f "rocqworker --kind=compile"`, or better, have the compile print its own sentinel (`bash -c 'coqc …; echo EXIT=$?'`); `pkill -f rocqworker` before re-measuring, and reap orphans (`ps -eo pid,ppid,stat,comm | grep rocqworker`; `Z`/defunct is harmless, a live orphan is not).
  Counting variant of the same trap: **`pgrep -c` prints `0` AND exits 1 on no match**, so `$(pgrep -c rocqworker || echo 0)` yields TWO lines (`0\n0`), and under `set -e` the bare `W=$(pgrep -c …)` form aborts the whole script silently. Correct form: `W=$(pgrep -c rocqworker 2>/dev/null || true)` then `head -1` (GR-21's is-a-lane-compiling guard failed twice this way, both times with no output at all).
- **`git reset --hard` in a shared tree is `git stash`'s destructive twin, with a TOCTOU window.** A stamp/sync script that inventories dirty files, backs them up, then resets in a later step will silently destroy any file that turned dirty BETWEEN the inventory and the reset — a live lane needs only seconds to dirty a tracked file (GR-24 lost a lane's in-flight `DirLinks.v` exactly this way; recovered only because the post-stamp verification re-diffed). Rule: re-run `git status --porcelain` IMMEDIATELY before the reset and abort if any tracked file appears that was not in the backup inventory; prefer `git checkout <commit> -- <paths>` over whole-tree `reset --hard` when live lanes share the tree.
- Everything about what makes a file slow and how to measure it is in [`optimization.md`](optimization.md).

## `set_solver` DOES NOT WORK OVER `gset (mword n)`

This one is NOT fixed by `iris/FastSetSolver.v`'s override (which cures the
*context*-size blow-up); it is a goal-side instance problem and the workarounds
below still stand.

It fails with **"No matching clauses for match"**. **That message is not
diagnostic** — it is stdpp's generic noise for *any* goal `set_solver` cannot
close, and the identical message comes back from an ordinary unprovable
`gset Z` goal (`ProofIput.ip_pool_set` is one). So do not read it as evidence
of an instance problem; read it as "set_solver failed". The actual tells are
the ones that discriminate: **`set_unfold` alone is fine** (on `a ∈ {[a]}` it
leaves exactly `a = a`, which `exact eq_refl` then closes), and the identical
goal over `gset (bv n)` is fine. The cause is the instance divergence
`RiscvPtsto.riscvF_kmapGS` pins against: a set over `mword` elaborates with
SAIL's `Decidable_eq_mword`, and `set_solver`'s closing step wants stdpp's
`bv_eq_dec`. Measured: with a `gset (mword 64)` anywhere in the section
context, every shape fails — singleton membership, `S ⊆ S ∪ T`, disjointness,
`{[a]} = {[a]} ∪ ∅` — and clearing the context does not help, which is what
separates this from the context-size trap.

Discharge the side conditions by named lemma instead — `disjoint_singleton_l`,
`singleton_subseteq_l`, `elem_of_singleton`, `big_sepS_delete` — or drop to
`intros x Hx …` and finish by hand. `LockSet.v` is written this way
throughout and its `cpu_locks_insert` carries the note at the point of use.

The same pinning rule applies when a set over machine words reaches a CAMERA:
state it as `gset_disjUR (mword 64) (EqDecision0 := @…Decidable_eq_mword 64)
(H := @…Countable_mword 64)`, exactly as `RiscvPtsto.lockSetR` does — an
unpinned functor field takes stdpp's instances and then fails to unify at
every use site, with an error naming neither.

### AND `FastSetSolver` DOES NOT CURE THE CONTEXT BLOW-UP EITHER — measured

`iris/FastSetSolver.v` is `Require Export`ed from `RiscvLang.v`, so it is in
scope everywhere, and the note above says it cures the context-size blow-up.
It does not cure it in a proof carrying the S-mode towers.

Measured 2026-08-19. One `set_solver`, proving `r ∈ SD ∪ s_Dro -> r ∈ s_Drw ∪
s_Dro` from `SD ⊆ s_Drw` inside `SmodeCorePt.spt_tr_obl_of_regime_D`, cost
**417 of that file's 438 seconds**; every other command in the file was under
0.7 s. The context at that point holds the 25-cell towers and a
tower-to-tower `reg_agree_on`, and `set_unfold` goes through all of it.
Written by name instead —

```coq
apply elem_of_union in Hr as [Hr | Hr].
- apply elem_of_union_l. exact (proj1 (elem_of_subseteq A B) Hsub r Hr).
- apply elem_of_union_r. exact Hr.
```

— the file builds in **20.3 s**. So: inside any proof that holds a tower,
discharge set side conditions by named lemma, exactly as the `gset (mword n)`
rule above already requires for a different reason. `HartSFrame.v`'s
precomputed `s_w_*` / `s_in_*` family exists for this, and its header says so;
`ltac:(set_solver)` written inside a TERM is the same trap and is easy to miss.

TO PROFILE (the rule is that a per-file build over five minutes is a bug):

```
./gcp-rocq/run-on-gcp opam exec --switch=/shared/xv6rocq -- \
  make -C iris -f CoqMakefile TIMING=1 X.vo
./gcp-rocq/run-on-gcp --no-sync sh -c \
  "sed 's/.*\] \([0-9.]*\) secs.*/\1 &/' iris/X.v.timing | sort -rn | head"
```

Artifacts are not synced back from the VM, so read `X.v.timing` there with
`--no-sync`.

## `vm_compute` ON A GOAL CONTAINING A SECTION VARIABLE DOES NOT FAIL — IT HANGS

`apply bv_eq; vm_compute; reflexivity` is the tier's idiom for a CLOSED
bitvector identity. Point it at a goal mentioning a section variable
(`moi hbase = add_vec (moi hbase) (sign_extend' …)`) and it does not report
anything: it runs for 12+ minutes with no output, and `coqc -time`'s last
streamed line is the sentence BEFORE it, so the log blames the wrong
sentence. **Rule: `vm_compute` only closed immediates.** Pull the immediate
out as its own `Hc : sign_extend' 64 … = mword_of_int k` (closed, so
`vm_compute` is instant), then `rewrite Hc moi_add; f_equal; lia`.

**AND THE SAME TRAP AT AN OPAQUE INSTANCE, which is the shape that bites at
the top of the tree (2026-08-19).** `vm_compute` ignores `Qed`-opacity: point
it at a goal whose head sits behind an opaque instance and it will unfold
that instance's proof term. `FileInv.subG_fileΣ` is `solve_inG. Qed.`, so at
`xv6Σ` the ambient `IcacheRef.icfg` — a superclass FIELD of `fileG` — is
behind it, and a goal as small as `icfg_dev = ROOTDEV` behaves like this:

- `reflexivity` FAILS, with *"Unable to unify `ROOTDEV` with `icfg_dev`"*,
  even though the instance visibly says `mword_of_int 1`;
- `apply bv_eq; vm_compute; reflexivity` does NOT fail — it grinds through
  the `solve_inG` term for **fifteen minutes** and reports nothing, and
  `make` looks stalled rather than wrong.

**The rule: a fact about the ambient `icfg` is not provable by conversion
anywhere below the boot fupd, and reaching for `vm_compute` to force it is
the failure above.** It is `fs-icache.md` C7 (c)'s ambient-`icfg` tie seen
from below — only `IcacheRef.icfg_alloc` can establish anything about the
cache's configuration. Where the configuration matters (it does: at
`icfg_nib = 0` an `IcacheRef.inode_held` cannot exist), make it a property
of the concrete INSTANCE and say so at its definition, as
`SystemAdequacy.adequacy_icfg` now does — do not make it a premise and
thread it, because nothing at the far end can discharge it.

Three smaller ones from the same effort:

- **`exact (f … _ _ H ltac:(lia) …)` fails with "Cannot find witness"** — the
  inline `ltac:` is elaborated BEFORE the conclusion is unified with the
  goal, so `lia` sees a goal full of evars. Use
  `refine (f … _ _ H _ _ _); lia`. (Same family as the other inline-`ltac:`
  traps above; this is the one that bites in `exact`.)
- **`change C with <lit> in *` does not reach hypotheses a callee's contract
  delivers LATER**, and the failure surfaces as a `lia` "Cannot find witness"
  comparing `C` to the literal. Re-`change` on each hypothesis as it arrives.
- **A Coq comment containing `(void *)` closes early**: `(* … free((void
  *)(hp+1)) … *)` ends at the `*)` inside the cast, and the syntax error is
  reported ~60 characters later with an unrelated `[ltac_use_default]`
  message. Quoting C in a comment needs the `*` broken up.

## `rewrite` CAN FAIL ON A SUBTERM THAT PRINTS CHARACTER-FOR-CHARACTER

**"Found no subterm matching `X`" where `X` visibly IS a subterm of the goal
is not a printing illusion and not a scope problem** — it is ssreflect's
keyed matching declining a term that is only CONVERTIBLE, not syntactically
equal, to the pattern. Printing both with `idtac` confirms they are
identical and gets you no further. (Seen rewriting `m !!! Regidx ra_idx`
inside `uM_bytes … 8 (m !!! Regidx ra_idx)` against a hypothesis
`mA !!! Regidx ra_idx = m !!! Regidx ra_idx`.)

The fix is not to rewrite at all: state a one-line CONGRUENCE lemma for the
predicate (`uM_bytes_val : w1 = w2 -> uM_bytes M a 8 w1 -> uM_bytes M a 8 w2`)
and `apply` it, so the equation is discharged by unification and conversion
instead of by syntactic matching. Same family as the `regval_into_reg`
`f_equal` paper cut above.

Two smaller ones from the same proof:

- **`unfold c in H1, H2` unfolds only in `H1`.** The failure surfaces as a
  `lia` two lines later that has every fact it needs — except that the second
  hypothesis was never unfolded. Write two `unfold`s.
- **An inline `ltac:(lia)` inside `rewrite (lem _ _ _ ltac:(lia))` fails when
  an earlier `_` is still an evar at splice time.** Spell out the argument the
  side condition mentions. (Same root cause as the `Qp.div_2` and
  `co_license` traps: a hole whose expected type is still an evar.)

## INCONSISTENT PREMISES ARE THE WORST DEFECT, AND NOTHING IN THE BUILD SEES THEM

A hedged conjunct makes a postcondition say nothing. **Contradictory
PREMISES make the whole contract say nothing** — it is vacuously true, its
proof goes through, its callers apply it, and every check in this tree stays
green. `Print Assumptions` does not see it. There is no compile error to
find.

The instance: adding `Hbss : sh_zeroed M (SH_DATA_PG + 0x10) 0 0x88` to
`wp_sh_free_first_body`, which already carried
`Hfreep : uM_bytes M SH_FREEP 8 (mword_of_int SH_BASE)`. `SH_DATA_PG + 0x10`
IS `SH_FREEP`, so one premise says that byte is 0 and the other says it is
0x88. It was caught only because a proof agent noticed the two addresses
coincide and wrote the four-line refutation.

Two rules follow:

- **Adding a premise to a contract is not a safe operation.** When a premise
  is added because some OTHER function needed it, check it against every
  premise already there — especially any that names an address, since a
  contract's addresses are usually literals that no type discipline relates.
  Here the premise belonged to `malloc`'s contract (where `freep` really is
  0, before `malloc` writes it) and was over-applied to `free`'s (where
  `malloc` has already set `freep = &base`, which is the entire point of the
  scan).
- **When two premises mention overlapping ADDRESS RANGES, prove they are
  jointly satisfiable, or delete one.** A four-line `Lemma … -> … -> False`
  attempt is cheap and is the only thing that finds this.

### The commoner variant: SATISFIABLE IN ISOLATION, REFUTABLE AT THE CALL SITE

Contradictory premises are the extreme case and the rare one. The variant
that keeps recurring is milder and just as invisible: a premise that is
perfectly satisfiable on its own, so the callee's proof compiles and
`Print Assumptions` is clean, but that is **false in the state the only
caller is actually in**. The lemma is correct and unusable, and nothing
discovers it until someone writes the caller.

Three instances in `sh` alone, all the same shape — a premise about the
program's `.bss` stated over too WIDE an address range:

| where | the range | why it is false there |
|---|---|---|
| `wp_sh_free_first_body` | `sh_zeroed M (SH_DATA_PG+0x10) 0 0x88` | `free` runs from `morecore`, i.e. after `malloc`'s head has already written `freep` and `base.s.ptr` |
| `wp_sh_malloc_first_body` | same | the range covers `buf.0` at 0x2020, so it says the command buffer is all zeros — but `parseexec` reaches `malloc` after `gets` filled it |
| `wp_sh_execcmd_body` | same | ditto, one frame up |

The fix each time was the same: **state the windows the proof actually
reads, and nothing between them.** `malloc` consumes exactly offsets
`[0,8)` (`freep == 0`) and `[128,136)` (`base.s.size`, plus the four bytes
of union padding above it that no instruction writes and that only the
zeroing establishes). So the premises became

    (Hfreep0  : sh_zeroed M SH_FREEP 0 8)
    (Hbasesz0 : sh_zeroed M (SH_BASE + 8) 0 8)

and the whole-`.bss` claim survives only in `main`/`start`, which is where
it is true.

The habit that catches it: when a premise covers a RANGE, list what else
lives in that range and ask whether the caller has written any of it yet.
A range premise is a claim about every byte in it, including the ones you
were not thinking about. Grepping the layout constants for addresses inside
the range takes a minute and is the whole check.

### FIXING A DEFINITION CAN TURN A DOWNSTREAM LEMMA VACUOUS INSTEAD OF BREAKING IT

The reassuring assumption about a definition change is that everything
depending on it either still compiles or fails loudly. That is true when
the definition appears in a lemma's CONCLUSION. When it appears in a
PREMISE, the third outcome is available and it is silent: the lemma still
compiles, and is now unusable.

`UmodeIo.xv6_io_sem SYS_wait` was `IoPureRet`, which was wrong — `wait(p)`
for `p ≠ 0` writes through `p`, so the arm cannot claim the image is
untouched. It was corrected to `IoWaitNull`. But `UProofShLib.wp_sh_wait`
proves `wp_sh_pureret_body ShSyms.wait SYS_wait`, whose premise list
contains

    Hsem : xv6_io_sem SYS_wait = IoPureRet

and that equation is now FALSE. Nothing broke. The lemma is still there,
still proved, still axiom-clean — and no caller can ever supply `Hsem`, so
`main`, its only caller, had no usable `wait` contract at all. The gap was
found months of proof-work later, by the first person to actually call it.

**After changing a definition, grep for it in PREMISE position, not just
for compile failures.** A premise mentioning a changed definition is a
place where the build's silence means nothing. The `_body`-with-`Hsem`
idiom is especially exposed — parameterising a contract by a semantic
equation makes every instantiation a claim that can quietly go false — so
prefer a contract that COMPUTES the arm to one that takes the arm's
identity as a hypothesis.

## A PERSISTENT POINTS-TO AT A **WRITABLE** IMAGE BYTE IS AN INCONSISTENT PREMISE

The loaded image is not two ranges but THREE, and the middle one is invisible
in the program headers. xv6 links a SINGLE RWX `PT_LOAD`, so
`KernelData.kernel_segments` — and `RiscvLang.img_end`, derived from it — can
only say where the file image ends. The read-only/writable split lives in the
ELF's SECTION table:

| | |
|---|---|
| `[ram_lo, rodata_end)` | `.text` / `.rodata` / `.eh_frame` — read-only forever |
| `[rodata_end, img_end)` | `.data` / `.got` / `.got.plt` — initialized and WRITABLE |
| `[img_end, kernelMemEnd)` | `.bss` — zero-filled and writable |

`RiscvLang.rodata_end` is that boundary. It is GENERATED, like every other
image constant: `tools/dump_elf.py` parses the section headers and emits
`KernelData.kernelRodataEnd` (the lowest writable *allocated* section's
address) with the whole allocated-section table beside it as a comment, so the
reading is auditable in the file rather than in a tool.

**Anything that resides image bytes at `DfracDiscarded` must stop at
`rodata_end`, not at `img_end`.** `KernelDataInv.kernel_data` used to stop at
`img_end`, so it claimed permanent read-only status for `first` and `nextpid`
— two `.data` globals xv6 *stores* to (`first = 0` in forkret,
`nextpid = nextpid + 1` in allocpid). Nothing failed to compile, and the
consequence is the section above's, exactly: any contract holding
`kernel_data` *and* ownership of one of those cells is VACUOUS, so
`SpecForkret.wp_forkret_body`'s proven contract said nothing to a caller that
also held `kernel_data`.

**The tier index does not save you.** `mem_pointsto` bottoms out in a
`pointsto` keyed on the PHYSICAL address, with `ktier_pin` only a pure side
condition, and a kernel global is identity-mapped — so `↦ₘ□` and `↦₄` at the
same `.data` address really do collide, at every tier.

**State the tripwire POSITIVELY.** `kernel_data ∗ first ↦₄{dq} w ⊢ False` is
the wrong shape: after the fix that conjunction is precisely what must be
SATISFIABLE. `KernelDataInv`'s §T instead pins the DOMAIN — `kdata_ro_bounds`
(everything resident is in `[text_end, rodata_end)`) plus `kdata_ro_first` /
`kdata_ro_nextpid`, two `vm_compute`d instances saying the globals xv6 writes
are not in it. Re-widen the filter, or move the image so a written global
falls below the boundary, and those two fail.

**Writable-by-flags is not the same as written.** `.got`/`.got.plt` are
writable sections xv6 never writes (statically linked, non-PIE), and `_entry`'s
GOT slot must persist so all eight harts share the `&stack0` word. That ONE
word is persisted by name out of the boot carve
(`BootCarve.boot_ran_phys_word`, off the owned range) rather than by widening
`kernel_data` back over a whole writable section — a claim about one cell,
which is checkable, in place of a claim about a section, which is not.

### The tactic trap this dragged in: `by apply map_lookup_filter_Some_2`

Adding the second bound turns the filter's side condition into a two-conjunct
BETA-REDEX, `(fun p => text_end <= p.1 < rodata_end) (a, b)`, and stdpp's
`done` on that over `KernelData.kernel_data`'s 17932 entries takes **minutes**
— 1.3 s with an explicit proof, over 14 minutes with `by`, with no error and
no output, so it reads as a hung build rather than a slow tactic. The
one-condition form is fine, which is why the regression arrives exactly when
you tighten the filter. **Reduce the side condition before closing it**
(`apply map_lookup_filter_Some_2; [exact Hlk | cbn; split; assumption]`), and
treat any `by`/`done` over a `map_lookup_filter_Some*` goal on an image map as
a bug.

## A HEDGED CONJUNCT IS A FALSE STATEMENT THAT COMPILES

**Never write `⌜P \/ True⌝` (or `(H : True)`) into a contract as a
placeholder for a fact you have not pinned down yet.** `right; exact I`
discharges it, so the postcondition says NOTHING where it appears, and it
reads at a glance exactly like a postcondition that says something. Three
of `USpecSh.v`'s image postconditions shipped that way and were caught only
because a proof agent was asked to report contract drift rather than work
around it. If the fact is not yet known, leave the conjunct OUT — a missing
conjunct fails loudly at the first call site that needs it; a vacuous one
never fails at all.

The same rule covers the mirror case: **a textual reorder of a contract can
silently EAT a conjunct.** Reordering `wp_sh_sbrk_body`'s two image effects
by `str.replace` dropped its return-value conjunct, so the contract stopped
saying what `sbrk` returns — which is the one thing its only caller needs.
After any edit to a `_body` definition, diff the conjunct COUNT, not just
the compile result.

## A STACK-BUDGET PREMISE IS ARITHMETIC — SPELL IT AS THE SUM, NOT A ROUND NUMBER

`uv_stack pt M sp0 n` looks like a formality and is not: `n` is a claim
about the deepest call chain below this function, and if it is too small
the contract is simply **unprovable**, which is a defect that surfaces only
when someone sits down to prove the body — potentially thousands of lines
of work later.

`wp_sh_main_body` asked for 512. `main`'s own frame is 64 (`addi sp,sp,-64`
@0x8e2) and the deepest chain below it is `parsecmd`'s 480, so the honest
number is 544. It was short by 32, and nothing could have revealed that
except attempting the proof: the premise is *weaker* than needed, so no
caller complains either — `wp_sh_start_body` happily supplies 576.

**Write the budget as the sum of its parts**, exactly as the contract below
it spells its own:

    (Hst : uv_stack pt M sp0 (64 + (64 + 48 + 48 + 128 + 112 + 64 + 16)))

not `544`, and certainly not a number rounded up "for safety". A rounded
constant loses the correspondence with the chain, so the next person to add
a frame cannot tell whether it still fits, and the two numbers drift apart
with nothing to notice. If a comment records the arithmetic (as
`wp_sh_start_body`'s does), the sum in the premise and the sum in the
comment must be the same expression — otherwise the comment is the thing
that gets updated and the premise is the thing that is wrong.

## A FUNCTION THAT WRITES A CALLER'S BUFFER DISTURBS *TWO* WINDOWS

`uM_only M M' a n` says "only `[a, a+n)` moved", which is right for a
function whose only writes are its own frames. It is WRONG — not weak — for
one that also writes a caller-supplied buffer: the gcc prologue spills `ra`
and `s0` into the frame and the epilogue only RELOADS them, so those bytes
differ in `M'` and any "only the buffer moved" claim is false. `memset`'s
first contract asserted exactly that and was unprovable.

The fix is `UmodeAbi.uM_only_in M M' ws` over a LIST of windows, with
`uM_only` recovered as the one-window case (`uM_only_in_one`) and the usual
`_trans` / `_weaken` / transports. State a callee's image effect as its own
frame window PLUS whatever it was asked to write.

## THREE `f_equal`/`rewrite` PAPER CUTS THAT REPORT SOMETHING ELSE

All three cost real time in the verified-user proofs and none of the messages
names the cause.

- **`f_equal` cannot see through a leaf's `regval_into_reg` wrapper.** A leaf
  stores `regval_into_reg wval`, so a goal reached by `upd_eq` is
  `regval_into_reg (mword_of_int z) = mword_of_int z'`; `f_equal` there fails,
  and the failure surfaces from the following `lia` as **"Cannot find
  witness"**, which reads like an arithmetic gap and is not one. Fix the `Z`
  argument first (`replace z with z'`), then `exact (upd_eq …)`.
- **`f_equal. lia.` as two sentences dies with "No such goal"** whenever the
  two arguments turn out convertible (`x - 16` vs `x + -16`) and `f_equal`
  closes the goal outright. Write `f_equal; lia`.
- **An equation over a whole `if b then … else …` rewrites only on the
  arm where `b` is still symbolic.** A branch leaf hands its continuation
  `pc_is (if taken then tgt else pc+k)`; with `taken := false` the `if` is
  still a redex when it reaches the context and an `iEval (rewrite E)` stating
  the whole term's value applies, but with `taken := true` it has already
  iota-reduced and the same rewrite fails with **"all matches … are equal to
  the RHS"**. Rewrite on the fall-through arms only.

## A `[-]` SPEC PATTERN EATS THE HYPOTHESES NAMED *AFTER* IT

`with "… [-] Hcont"` is self-defeating, and the error blames the wrong thing:
it fails with **`iSpecialize: "Hcont" not found`** even though `Hcont` was
introduced at the top of the proof and nothing since touched it. `[-]` is
`envs_split` with the complement flag and an EMPTY exception list, so it
moves *every* remaining spatial hypothesis into that premise's goal — the
continuing context is empty by the time the parser reaches `Hcont`. The fix
is one character class: **`[-Hcont] Hcont`** ("all remaining EXCEPT Hcont").
Spaces are irrelevant (`-` is its own token), so `[- Hcont]` is the same.

This is worth knowing because the natural diagnosis — "an earlier `[-]` in
the straight-line run swallowed it" — is wrong and expensive: the `[-]`
goals in a whole-function run each carry the WHOLE context forward, so a
hypothesis crosses any number of them intact. Look at the failing `iApply`
itself first. (Found in `ProofKexecA.kxc_a2`, at both `kxc_bad64` sites.)

**Its sibling `[]` produces the SAME ERROR MESSAGE for the opposite reason,
and the reason is not a bug at all.** `[]` proves that premise with an EMPTY
spatial context, so anything you still need INSIDE the sub-goal — typically a
caller's exit continuation that the *next* block will consume — is simply not
there, and the failure surfaces as `iSpecialize: "Hcont" not found` several
lines into the sub-proof. Whenever a bracketed premise is where the rest of
the function is proved, list what it needs: `[Hcont]`, not `[]`.
(`ProofKexec.v`'s phase-B `phnum = 0` arm.)

Directly behind it sits the hart trap, because the next error looks like a
non-error: **`iSpecialize: cannot instantiate (X -∗ …) with (X)` where both
`X`s print identically** means the implicit `CID0` differs. A lemma whose
FIRST premise is hart-indexed (`sie_cap_gpr …`) pins its own `CID0` from the
hypothesis you hand it — i.e. to the CURRENT hart, `CID15` — while the
caller's exit continuation is still anchored at the section's `CID0`.
Re-anchor it with `WpNext.wp_next_retarget`, and get the crossing fact by
NAME (`assert (Hcr : true = false \/ p = zero_reg -> (CID15 : CPU) = (CID0 :
CPU)) by wp_next_chain.`) rather than as an inline `ltac:` in argument
position, where `K` is still an evar.

## CHAINING TWO HALVES OF A FUNCTION: THE EXIT MUST BE HANDED BACK

**A SEAM MUST EXPORT EVERY *CALLER-SAVED* REGISTER THE NEXT BLOCK READS.**
A whole-function walk split into blocks threads a register BUNDLE across
each seam (`su_regs`, `cr_regs3`, `sl_regs`), and those bundles pin the
CALLEE-SAVED registers — by construction they say nothing about `a0`–`a7`.
So a seam placed one or two instructions after a call, where the callee's
return value is still live in `a0` and the next block's first act reads it,
is silently short one fact: the block's premise `⌜M !!! Ra0 = dpv⌝` cannot
be produced from the bundle, from the seam's pure list, or from anything
downstream. It is invisible until the SEAL composes the two blocks, which
is typically the last thing written. When you cut a seam, list what the
next block reads out of the register file and check each name against the
bundle. (`ProofSysUnlink.su_w1`'s +0x30 seam, found by the seal; the fix
is one conjunct and one `eq_trans` at the site.)


A single `wp_next` exit continuation is LINEAR, so if both halves of a split
function own a failure tail, the second half's premise list cannot be
satisfied by the caller's one copy — the two continuation premises of the
first half are `∗`-separated and nothing duplicates a `wp_next`. The shape
that works is `ProofKforkMain`'s: the first half's FALL-THROUGH continuation
hands the exit BACK, so the exit is supplied once and whichever continuation
runs receives it —

```coq
    wp_next b p (fun (CID : CpuId) =>
      ∀ …, <the seam> -∗
        wp_next (CID0 := CID) b p (fun CIDx => <the exit>) -∗
        WP Loop) -∗
```

`(CID0 := CID)` is mandatory: written bare inside the binder, instance
resolution anchors it at the innermost `CpuId` and the guard degrades to a
tautology (WpNext.v's note on `wp_next_at`). And the chaining lemma itself
needs its OWN section: applying the second half at the seam's hart requires
`(CID0 := CIDs)`, which a still-open section rejects ("Wrong argument name
CID0") because `Context CID0` is one shared variable, not a per-use argument.
`ProofKexecA.kxc_phaseA` is the worked instance.

## `rewrite -(Qp.div_2 q)` INSIDE THE PROOFMODE PUTS THE SPLIT'S EVAR OUT OF SCOPE

The idiom for "split a fractional resource in half" is to rewrite `q` into
`q/2 + q/2` and then apply the split equivalence. Written at a CALL SITE
inside an Iris proof — `iEval (rewrite -(Qp.div_2 q) foo_split) in "H"`, or
`rewrite foo_split` on the goal — it fails with

    Unable to unify "?b@{q:=(q / 2 + q / 2)%Qp}" with "<the split's RHS>"
    (cannot instantiate "?b" because "q" is not in its scope)

because the rewrite abstracts over `q` before the split's own evar is
solved. Bit twice in one session (`ProofKexit`, `ProofKforkB4`). The fix is
never to write it inline: state the halving as its OWN lemma, where the goal
is closed and the rewrite is the last step —

```coq
Lemma foo_shed x q : foo x q -∗ foo x (q/2) ∗ bar x (q/2).
Proof.
  iIntros "H".
  iDestruct (bi.equiv_entails_1_1 _ _ (foo_split x (q/2) (q/2)) with "[H]")
    as "[$ $]".
  { rewrite Qp.div_2. iExact "H". }
Qed.
```

— and call THAT. `InodeRef.iref_at_shr` and `IcacheInv.inode_ref_shed` are
the two instances. Same family as the inline-`ltac:` trap: a hole whose
expected type is still an evar at splice time.

## TWO TRAPS AT THE *SHAPE* OF A HYPOTHESIS, both of which report the wrong thing

- **A MOVER WHOSE CONCLUSION DROPS ONE OF ITS ARGUMENTS CANNOT INFER IT,
  AND THE ERROR NAMES AN UNRELATED GOAL.** A register-bundle mover
  (`su_regs_wr_s2 m sp0 dpv ipv ipv' s3v Mx v` — "s2 was `ipv`, is now
  `ipv'`") mentions the OLD value only in its hypothesis, so writing it
  with `_` there fails with *"Cannot infer this placeholder of type
  `mword 64`"* — reported at a `pcw`-closed `assert` from further down the
  proof, because that is where the elaborator finally gave up. Spell out
  every argument the conclusion does not mention. Same family as
  `co_license`'s dropped arguments (see the `Qed`-time symptom above), one
  tier up and with a different message.
- **NEVER RE-ASSEMBLE A RECORD-SHAPED `Prop` CONJUNCT BY CONJUNCT.** A
  bundle like `InodeLock.inode_ok` is a right-nested seven-way `/\`;
  destructuring it to feed a callee's three numeric premises and then
  rebuilding it with `split_and!` fails with *"The term `Hrest` has type
  `A /\ B` while it is expected to have type `A`"*, which reads like a
  wrong conjunct ORDER and is not — it is an off-by-one in how many
  conjuncts the pattern named. Keep the whole fact (`pose proof Hiok as
  Hiok0`) and rebuild with `exact Hiok0`. The rule generalizes: a `Prop`
  you only ever pass along should be destructured for READING and
  reconstructed from the SAVED original, never from its pieces.

## A PREDICATE'S DEPENDENCY CONE IS EVIDENCE; ITS PROSE IS NOT

If some predicate's cone contains a layer it has no business containing,
the conclusion is almost never "these layers are entangled" — it is that
ONE definition is in the wrong file, and the cone is how you find it.

Worked example (`design/fs-ghost-state.md` §7e): `FsReady.fs_ready`'s cone
contained `ProcInv`, i.e. the whole process layer, which reads as "the file
system depends on process abstractions".  It does not.  Two edges, one
real: a vestigial `Require Import ProcInv` (checked: zero of the 132 names
`ProcInv`/`ProcDefs` define were used), and `FsReady` → `SpecDirlink` →
`SpecWritei` → `ProcInv`, where only the last hop is legitimate (writei
takes the process block to copy user memory).  `SpecDirlink` was in the
chain solely because it owned `ic_sleeplocks`, five lines of pure icache
invariant, in a *function spec*.  Moving it beside `ic_tok` in
`IcacheEscrow.v` took the process layer out of the file system's cone.

Three practical points:

- **Compute the cone; do not read imports.**  `iris/.CoqMakefile.d` already
  IS the graph (`X.vo: … Y.vo …`).  A dozen lines of Python over it answers
  "why does A depend on B" and "what breaks if I move this" exactly, and
  the shortest path it prints is usually the whole diagnosis.
- **The rule this sharpens** is the one `SpecFsinit.v` and `SpecDirlink.v`
  already state — *a Spec file must not require another function's Spec*.
  The sharper form: **a spec file must not OWN a definition the invariant
  layer needs.**  A spec is allowed to depend downward; a definition it
  owns forces everything that wants it to depend UPWARD, through the whole
  function-spec cone, and nothing in the build reports that as wrong.
- **"Leave the old name as an alias" is not always available.**  It works
  for a `Prop` (`SpecDirlink.ireg_blocks_ok` is the tree's precedent) and
  fails for anything a caller unfolds: five sites did
  `rewrite /SpecDirlink.ic_sleeplocks` followed by `big_sepL_lookup`, which
  needs the BODY one unfold away, and a transparent alias leaves them one
  unfold short.  Check for `rewrite /<name>` at the call sites before
  promising a zero-churn move.

## ONE BUNDLE PER GHOST CLASS, OR THE SAME `inG` GETS TWO INSTANCE PATHS

`Xv6G.xv6G` bundles the thirteen ghost classes that are PURE CAPACITY -- only
`inG`/`ghost_varG`/`ghost_mapG` fields, no `gname`.  That is the membership
test, and it is also why adequacy can hand the whole thing out before a single
instruction runs: there is nothing in it to allocate (`xv6GΣ` +
`subG_xv6GΣ`).  The rule that comes with it: **a file at or above `Xv6G.v`
binds `xv6G` and does NOT bind any member.**  Binding both compiles.

**Why it matters.** Two instances of one `inG` are not equal, so resources
built at each are different propositions THAT PRINT IDENTICALLY.  The failures
read `iFrame: cannot frame`, `iSpecialize: cannot instantiate`, or eleven
UNDEFINED EVARS naming classes that are not the culprit.

**What was found doing it, and the general shape.** Three ad-hoc bundles each
carried capacity belonging to the one bundle:

- `FileInvDefs.fileG` carried `pipeG`/`icacheG`/`cinvG`.  Its own comment
  stated the right motive and the wrong remedy, with an unenforceable rule
  ("a file that needs both takes `fileG` alone") -- **twenty-seven files bound
  `fileG` and `!icacheG` side by side**, and `FsReady.v` deliberately declared
  `icacheG`/`icfg` LAST so resolution would prefer them.  `fileG` now keeps
  only its own camera and `icfg`.
- `RiscvAdequacy.riscvGpreS` carried `uartGhostG`/`diskGhostG`.  Removed;
  `riscvΣ` still supplies the functors, so `subG_riscvGpreS` is unchanged in
  strength -- only who NAMES them moved.
- **`mono_natG` has FIVE owners** (`DiskPtsto.disk_nc_inG`, `CrashProto`'s
  two, `riscv_pre_genGS`, `riscvF_genGS`) and is NOT fixed.  It forced the
  tree's one carve-out: `RiscvAdequacy`'s `Section power` deliberately binds
  `!sieG Σ` rather than `xv6G`, because `xv6G` drags in `diskGhostG`'s
  `mono_natG` and shadows the generation counter.  **Reordering the binders
  does not help** -- the allocation lemma fixes the instance at ITS
  statement, not at the consuming section.  Giving `mono_natG` one owner is
  the next increment.

**Four ways a binder sweep breaks that the build reports as something else:**

- **Duplicate insertion.**  The unit is not the binder GROUP: adjacent groups
  (`` `{…} `{…} ``) are one construct, and consecutive `Context` COMMANDS
  share a section.  Insert once per construct and once per lexical scope
  (a `Section`/`End` stack), or you manufacture the very double path you are
  removing.  Symptom: `Signature components ... do not match` with the class
  appearing twice in the expected type.
- **Import placed after first use.**  A file with a SECOND `Require` block
  below its sections gets the import too late, and backtick generalization
  then invents a fresh `xv6G : gFunctors → Type` VARIABLE, silently.  Insert
  after the FIRST `Require` block.
- **Module-qualified binders.**  `!WpLock.lockG Σ`, `!LogInv.logG Σ` -- some
  written deliberately, with a comment, to dodge an import.  A pattern
  matching only unqualified names leaves them, and they are then a second
  path beside the bundle.
- **Positional `@` applications.**  Changing a section's binder count
  silently mis-aligns `@f Σ inst _ _ _ …`.  Symptom: `Illegal application
  (Non-functional construction)`, naming nothing relevant.

Selecting files by NAME (`Spec*`/`Proof*`/`Link*`) is also wrong: select by
dependency position (not in the bundle's own cone), or the `Wp*`/`User*`
files above the boundary keep their own binders and fail.

## A CLASS USED AS AN INDEX NEEDS ITS INSTANCES DECLARED TWICE

When a class is a *definitional* one used as an INDEX rather than as a
capability — `Class CurKtier := cur_ktier : ktier`, whose inhabitants are
just values — a term of that index type reaches a goal by one of two
routes, and `simple apply` (hence `typeclasses eauto`) will NOT unfold the
class to reconcile them:

- through the AMBIENT INSTANCE, so the argument has the CLASS type
  (`curktier_default : CurKtier`);
- written out at a LITERAL, so it has the UNDERLYING type (`KT1 : ktier`).

An instance whose index binder is the backtick class form
(`` `{KTR : !CurKtier} ``, which is what a section `Context` gives you)
is worse than either: the binder becomes an instance-SEARCH argument, so
the only index it can ever produce is the default — it silently refuses
every goal at a literal, reported as **`no match for (Persistent …), N
possibilities`**, naming nothing about the index. A plain
`(k : TheClass)` binder covers the ambient route and reports **"Unable to
unify ktier with CurKtier"** on the literals; a plain `(k : Underlying)`
binder covers the literals and reports the mirror image.

**So declare each such instance TWICE** — once at the class type, once at
the underlying type, the second `exact`ing the first — and do the same for
any auxiliary class indexed by it (an order class `KtierLe` needs `_c`
twins for exactly the same reason: a goal `KtierLe KTR KTR` over a section
variable matches none of the underlying-typed instances). The symptom that
identifies the trap: a `Persistent` / `Timeless` / order goal that fails
ONLY in the files that name a literal, or ONLY in the ones that do not.

Two neighbours of the same shape:

- **A SECTION VARIABLE CANNOT BE INSTANTIATED FROM INSIDE ITS OWN
  SECTION.** `Context `{KTR : !CurKtier}` makes the section's lemmas
  index-generic *for callers*; inside the section the index is fixed, so a
  lemma that must be at one index cannot sit beside one that must be
  generic. Split the section. The tell is **`Wrong argument name KTR`** at
  a `(KTR := …)` written in the defining file.
- **A CLASS HYPOTHESIS IN A SECTION BEATS A GLOBAL INSTANCE.** Adding
  `Context `{!KtierLe ktb kt}` for one two-index callee makes every OTHER
  application in the file resolve its index to `ktb` instead of the
  default the global `refl` instance would have given — so a whole file's
  worth of unrelated goals break at once, and each has to name its index
  out loud. Put the note at the `Context`, not at the failures.

## Typeclass sweeps: the three traps that do not look like typeclass problems

Adding a class constraint to a bottom-of-the-tree predicate (e.g. giving
`ProcInv.proc_priv` an `!irefNameG Σ`) is a mechanical sweep with three
failure modes that produce errors naming something else entirely.

- **A class that is not IMPORTED becomes a fresh VARIABLE, silently.** Rocq's
  backtick binders do implicit generalization, so `` Context `{!irefNameG Σ} ``
  in a file where `irefNameG` is not in scope does not fail — it *invents* a
  section variable `irefNameG : gFunctors → Type`. Everything then elaborates
  against a bogus binder and the error surfaces far away as
  **`UNDEFINED EVARS` with `?Σ` unresolved on unrelated constants**
  (`riscvGS0 of word_pointsto`, `riscvGS0 of pc_is`). The tell is the printed
  local context containing both `irefNameG` and `irefNameG0`. Fix: `Require
  Export` the class from the file that puts it in the predicate's type
  (`ProcInv.v` exports `InodeRef.v` for exactly this), or `Require Import` it
  at each site. Verify with
  `grep -L 'Require .*\(ProcInv\|InodeRef\)' $(grep -l irefNameG *.v)`.
  A second symptom of the SAME trap, easy to misdiagnose as a genuinely
  hard unification failure: a Module Type `Parameter` that both re-states
  a callee's full `` `{!ClassG Σ, ...}`` list (e.g. mirroring
  `usertrap_res`'s 14-class signature to call it from a sibling spec, as
  `SpecUservec.v`'s `USERVEC` does over `SpecUsertrap.USERTRAP_RES`) AND
  is missing the direct `Require Import` for some of those classes'
  home files — even though the file compiles clean on its own — reports
  **`Could not find an instance for the following existential variables:
  ?fooG0 : Real.fooG Σ`** for exactly the classes whose homes weren't
  imported, while classes the file ALREADY needed for other reasons (here
  `riscvGS`/`sieG`, pulled in via `RiscvPtsto`) resolve fine. This looks
  like it must be about HOW the callee identifier is applied (bare vs.
  `(ClassArg := ...)`-named vs. positional `@`) and burns real time chasing
  that — it never is; reducing/renaming the call site changes nothing.
  Check imports FIRST whenever the unresolved list is a strict subset of a
  callee's own class list and lines up with classes this file has no other
  reason to mention.
- **A class that carries another class as a FIELD instance must not be
  bound alongside it.** `Class irefNameG Σ := { irefname_icacheG :: icacheG Σ;
  iref_name : gname }` means a context with BOTH `!icacheG Σ` and
  `!irefNameG Σ` has two `icacheG` instances, and predicates that take
  `{!icacheG Σ}` get different ones in different places. The propositions
  then print IDENTICALLY and fail to unify — the symptom is
  **`iSpecialize: cannot instantiate (P -∗ Q) with P`** where the two `P`s
  are character-for-character the same. Fix: drop the standalone `!icacheG Σ`
  and let the bundling class supply it. (Six files needed this: the kfork
  chain and fileread.)
- **MOVING a class's `Class` declaration to a lower file breaks every
  `Require Export` chain built on the OLD location, silently.** When
  `irefNameG` moved from `InodeRef.v` into `IcacheInv.v` (so `itable_inv`/
  `itable_half`/`iref_tok` could be stated over it directly, retiring their
  explicit `γ` parameter), `InodeRef.v` still only `Require Import
  IcacheInv`d it — so a file like `ProcInv.v` that does `Require Export
  InodeRef` no longer re-exports `irefNameG` at all, and every one of ITS
  `Require Export ProcInv` downstream files hits trap one (`irefNameG` /
  `irefNameG0` both in context) despite `ProcInv.v` itself compiling fine in
  isolation. **The fix is always to promote the broken link's `Require
  Import` to `Require Export`**, not to patch every downstream site — the
  chain is supposed to carry the class, and the mid-chain file is where it
  broke. Check every `Require Import <file-you-moved-the-class-out-of>` in
  files the class's own definitions/notations appear in.

A further shape shows up once the class reaches BOOT: **a class that carries
a ghost NAME cannot be a functor constraint the adequacy theorem assumes.**
`irefNameG` holds `iref_name : gname`, so `xv6Σ` cannot supply it and the
top-level corollary has nothing to instantiate it with. It has to be minted
inside the boot fupd and handed out EXISTENTIALLY, exactly as
`FdSlots.fd_slots_alloc` does for `fdslotG` — see `InodeRef.iref_name_alloc`
and `BootShared.boot_shared_alloc`'s `∃ (_ : irefNameG Σ)`. What the
adequacy theorem may assume is the FUNCTOR half (`icacheG`, an `inG`).
Corollary: do not bundle an allocated-at-boot class (`irefslotG`) into a
name-carrying one — the boot lemma then cannot build it piecemeal. That was
tried and reverted here.

Two smaller traps in the same area: a lemma whose statement pins its PROP
only through the body (`⊢ |==> ∃ _ : C Σ, True`) leaves `BUpd ?PROP`
unresolved — annotate (`(True : iProp Σ)`). And a section variable that a
`Lemma`'s *statement* does not mention but its proof needs is fine for an
ordinary hypothesis, yet an unresolved *instance* evar for it surfaces only
as **"Attempt to save an incomplete proof"** at `Qed`; `Show Existentials.`
before the `Qed` names it in one line.

The same `Qed`-time symptom has a second, non-typeclass cause worth knowing,
because the fix is different: **a definition that is an `if` (or a `match`) on
a ghost index DROPS the arguments the taken branch does not mention**, so at a
literal index those arguments are phantom, and any crossing that leaves them
to unification *shelves* them. `SpecCopyout.co_license arm …` drops `dstva`
and `len` at `arm := true` and the two cell arguments at `false`; the result
was six shelved goals (`mword 64` ×3, `dfrac` ×2, `nat`) reported as
"Attempt to save an incomplete proof" **~350 lines past the cause**, again
localised in one step by `Show Existentials.`. The fix is not an instance
annotation but **applying the mover with every argument explicit**
(`co_lic_unpack (GEN:=GEN) (CID:=CID) P p szv dstva0 len dqs dqp`). Worth
weighing when you choose an index over a disjunction (see the spec-design
preferences): the interface is better, and this is what it costs.

All of the first three are invisible to a per-file `coqc` of the file you
edited; they appear only where the predicate is USED, and can appear only
once every `.vo` in the tree is actually fresh (a stale sibling `.vo` — see
the "Stale `.vo` trap" bullet above — reproduces trap one's exact symptom
and wastes time chasing a phantom fix). Do the sweep by fixing exactly the
files the build names, in both the `_body` Definition and the `Module Type`
Parameter — a `Parameter` binder list that disagrees with the `Definition` it
seals fails at `Module` instantiation with *"Signature components for field
… do not match"*, which reads as a spec/proof mismatch and is not one. Once
every file compiles standalone, validate with a full `make proofs` (or
`make -f CoqMakefile -j16 -k` from `iris/`) rather than trusting a chain of
individual `coqc` runs — those load whatever `.vo` already sits on disk for
every dependency, so two files edited in the same sweep but checked out of
dependency order can each "pass" against a stale sibling and still fail
together under `make`.

## A HART-INDEXED TERM WRITTEN FRESH IN A PROOF MEANS THE *SECTION* HART

Almost everything in the S-mode tier is per-hart, including things that do not
look it. `Print`ing their `Arguments` is the only reliable check, and the list
is long: `reg_pointsto` (i.e. **every `r ↦ᵣ v`** — `reg_name` is the ghost name
of `cpu_id`), `reg_interp`, `mstate_interp`, `gpr_file`, `gpr_pt_value`,
`tp_pin`, `rget`, `sconf`, `sie_cap`, `sie_arm`, `sie_gname`, `intr_count`,
`intr_inv`, `intr_handler_spec`, `sr_transform`, `sr_absorb`, `sr_tmode`,
`trap_csrs`, and `intr_frame` (it holds `menvcfg ↦ᵣ`, so "it is only a stack
carve and a TLB arm" is wrong).
**`WpNext.wp_next` IS HART-INDEXED TOO, and a `∀`-fuel LOOP must RETARGET
it on the back edge.** `cpu_own_transport`'s twin, and the first tree
instance is `ProofFilewrite.fw_loop` (fs-sysfile S3t). A loop lemma holds
its caller's crossing at the hart the iteration STARTED on and its own `IH`
demands it at the hart the iteration is RE-ENTERED on; those are different
propositions because `wp_next`'s guard names the anchor. One line fixes it:
`iDestruct (wp_next_retarget CID0 CIDnew true pj _ ltac:(wp_next_chain)
with "Hcont") as "Hcont"`. **The failure is `iSpecialize: cannot instantiate
(wp_next … (λ CID, …))` with a term whose printed type is IDENTICAL** — same
tell as the `cpu_own` one, and the only visible difference is an extra pair
of parentheses the pretty-printer adds around the `∀`.

**`KvmSpec.kalloc_env γ None` IS PERSISTENT (`KvmSpec.v`:141) and a loop
must intro it with `#`.** writei/readi/copyin CONSUME it and do not return
it, so a loop body that intros it exclusively cannot instantiate its own
`IH`; the error is `iSpecialize: "Hkenv" not found`, which names the
hypothesis and not the reason.

### THE SAME MISMATCH IN A `set`/`change` IS SILENT, AND IT SURFACES AS A HANG

The trap above is about two terms that fail to UNIFY. The register-map
abbreviation every straight-line walk builds hits the same `rget`-vs-`!!!`
distinction one level down, where nothing fails at all:

```coq
(* WRONG: the leaf hands the map back at [rget], not [!!!] *)
set (C3 := <[Regidx Ra5 := regval_into_reg (add_vec (C2 !!! Regidx Ra5) (C2 !!! Regidx Ra4))]> C2).
change (… same …) with C3.
```

`wp_cadd_s_sconf`, `wp_addi4_s_sconf` and their siblings spell the written
value at the HART-INDEXED read (`rget m r`), so a `set` written with `!!!`
finds **no occurrence to fold**, and `change A with B` **succeeds vacuously**
when `A` does not occur. The proofmode hypothesis therefore keeps the
unfolded, `rget`-spelled map while every later step passes the abbreviation.
Nothing reports it — and the `assert`s about the new name still prove fine,
because they never touch the hypothesis.

**The two forms are CONVERTIBLE, so this degrades instead of failing, and the
degradation is superlinear.** `regfile` is a function and `rget` only reroutes
`tp`, so conversion succeeds — but it must normalise the whole insert chain
down to the symbolic entry map at every nested read. One nesting level costs
~0.1 s; two never return. **So the previous instruction compiling fine is not
evidence the spelling is right** — it is the same bug one level cheaper. The
symptom is an `iApply` that reads as an infinite loop with no error message,
several instructions AFTER the mis-spelled `set`.

The one-line localiser, which separates "the term I wrote does not match the
hypothesis" from everything else and costs milliseconds:

```coq
iAssert (<the premise, spelled out>) with "[Hcg]" as "Hcg". { iExact "Hcg". }
```

A fast `iAssert` and a hanging `iExact` is the mismatch, positively
identified. Fix by spelling the `set`/`change` in `rget` form and adding the
`rgne` normalisations the surrounding `assert`s then need;
`ProofUvmunmap.v:600` / `ProofUvmdealloc.v:722` instead follow every such leaf
with `iEval (rgne) in "Hcg"`, which is the same fix taken at the hypothesis.

**A section-level lemma whose conclusion is `WP Loop` cannot be applied after
a hart crossing.** `Loop` names `cpu_id`, so the statement is rigid at the
section hart while the goal moved with the walk's `wp_next`s. Give such a
lemma its own `` `{CIDh : CpuId} `` binder shadowing the section's
(`ProofArgraw.ar_join` is the shape); the error is `iApply: cannot apply
(WP Loop)`, which names neither hart.

Hart-FREE, despite appearances: `stack_own` (physical stack memory),
`mem_pointsto` and the whole `word_pointsto` family (memory is shared),
`ghost_var_agree` and the other generic Iris lemmas, and every
`exec_execute_*` (they are pure facts about `mstate`).
Annotating a hart-free term fails loudly — *"Wrong argument name CID (possible
names: Σ riscvGS0)"* — so read the names before you annotate.

**THE SAME ERROR ALSO MEANS "you are inside the section that fixes it".** A
`Definition foo := M.foo.` written inside a `Section` with
`Context `{CID : CpuId}` has *no* `CID` implicit yet — section variables are
discharged only at `End`, so within the section `foo` simply mentions the
section's hart. A statement in that section that needs the FAMILY
(`fun h : CpuId => foo (CID := h)`, the shape `wp_usertrap_body`'s `R` and
`wp_uservec_pt_body`'s `URes` take) must name the ORIGINAL — `M.foo (CID := h)`
— whose module-type binder is still there. The two are convertible, so a
`<: MODULE_TYPE` check phrased on the alias still accepts the qualified form.

**`WP e` IS HART-FREE BUT `WP Loop` IS NOT.** `riscv_irisGS` takes no `CpuId`,
so the WP FORMER is hart-free — but the EXPRESSION names the hart
(`Notation Loop := (LoopE gen_id cpu_id)`, RiscvLang.v). So a statement that
quantifies a hart over a `WP Loop` goal must bind it as `(h : CpuId)`, not as
`(h : CPU)`: with a bare `CPU` nothing puts an instance in scope and the body
does not elaborate, with the error *"Could not find an instance for `CpuId`"*
reported at `Loop` itself rather than at the binder. (`ProofPanic.pn_spin` is
the worked instance; `panic_wp_any`'s `∀ h : CPU` gets away with `CPU` only
because its body is a DEFINITION applied at `(CID := h)`, never an inline
`WP`.)

**Why the per-hart/shared split is the shape and not an accident:**
`gregs_interp` holds EVERY hart's register map; `mstate_interp σ` at `CID` is the focused view of the one that is running
(`gregs_interp_acc` does the focusing). So "the machine" is shared and "the
registers I can step" are per-hart — which is exactly why a funnel whose engine
can migrate the thread must hand its σ-callback the interp at an ARBITRARY hart,
and why the leaves under it have to be hart-generic rather than the funnel
absorbing the difference.

Inside a proof that introduces a SECOND hart (the funnel's rebound `CID`), a
hart-indexed term **written fresh** — in an `iAssert`, a pure `assert`, or as a
lemma application — resolves its `CpuId` from the *section* slot, i.e. it means
the ENTRY hart, no matter what the surrounding hypotheses are at. Two
consequences:

- The error prints the SAME TERM TWICE: *`iSpecialize: cannot instantiate (P -∗
  Q) with P`* where both `P`s are character-for-character equal. (Same symptom
  as the duplicate-class-instance trap above, different cause.)
- Unification can still save you: a hart-indexed term appearing as an EXPLICIT
  argument that is matched against an Iris hypothesis gets its hart from the
  hypothesis (`gpr_file_lookup_acc (tp_pin m) …` is fine), while the same
  `tp_pin m` in a PURE `assert` about the map is not. So a proof can be half
  right and fail 100 lines later.

The recipe for making a leaf's σ-callback hart-generic, validated across
`WpSconfCsr`/`Mem`/`Alu`/`Btype`/`Lock`/`Ctl` and `ProofUart`:

```coq
rename CID into CID0.          (* AFTER any same-open-section lemma application *)
iIntros (CID Hs σ Hpceq) "…".
assert (Lpin_rs1 : tp_pin (CID := CID) m (Regidx rs1) = rget m rs1)
  by exact (src_ok_rget_indep m rs1 CID CID0).   (* one per SOURCE register *)
…                              (* (CID := CID) on every hart-indexed term below *)
rewrite Lva ?Lpin_rs1 …        (* wherever a read reaches a statement-level fact *)
iApply ("Hcont" $! CID with …). iPureIntro. exact Hs.
```

with `destruct (rget_next_ops_indep (CID := CID0) b p CID m rd rsa rsb Hs Hops)`
(or two `rget_next_indep`s off `ops_ok_sp_s1`/`_s2`, which is what the cap
engine needs — it carries `ops_ok_sp`, not `ops_ok`) where a step engine's
`Hbexec` wants the entry hart's operand words. Mechanically, `(CID := CID)` on
every hart-indexed head in the converted range is right and cheap to script —
104 annotations in `WpSconfMem`, 210 in `WpSconfBtype` — but **exclude
`rewrite /name`**: the script that adds them will happily produce `rewrite
/sie_cap (CID := CID)`, which is a syntax error, not a type error.

### Three shapes no annotation can fix

- **A CROSS-HART REFUTATION IS NOT A REFUTATION.** `wp_csrsi_sstatus_x0`'s
  already-enabled arm derives `False` from the payload's `sepc` cell and the
  arm's; `wp_csrci_sstatus_x0`'s from two SIE eighths. Held inside the
  callback, one is the rebound hart's and the other the entry hart's — and two
  harts each owning their own `sepc` is perfectly consistent. **Hoist the
  `destruct b` ABOVE the funnel**, where the caller still holds both at one
  hart. That pays twice: the surviving arm is often `b = false`, where
  `wp_next_off_intro` retires the hart question outright and the body needs no
  annotations at all.
- **A `b = false` ARM THAT THREADS A PER-HART RESOURCE NEEDS THE GUARD.** If
  the statement hands in, say, `intr_count_pre b k eb` and the post owes
  `intr_count (S k) eb`, the `b = false` arm is crossing harts with something
  nothing transports. Collapse them:
  `assert (Hcc : CID = CID0) by exact (Hs (or_introl eq_refl)). subst CID.`
  (`CpuId` is a definitional class, so the guard's `(CID : CPU) = (CID0 : CPU)`
  IS that equation up to conversion — `exact` crosses it, while `subst` on the
  un-`assert`ed form fails with *"Cannot find any non-recursive equality"*.)
  After the `subst`, any `(CID := CID)` already written in that arm must become
  `(CID := CID0)`. The `b = true` arm usually needs no collapse: there the
  count premise is a pure fact and everything in the post comes out of the arm,
  which the callback already delivers at the rebound hart.
- **A CALLER-SUPPLIED TRANSFORMER MUST BE HART-GENERIC.** A leaf that takes
  `sie_cap m n b p -∗ sie_cap m' n' b p ∗ P` from its caller and applies it to
  the capability the callback delivers cannot: `sie_cap` is per-hart. Quantify
  the premise `∀ CIDx : CpuId`. Every proof of such a transformer is uniform in
  the hart, so the cost is one `iIntros (CIDx)` per builder — and if the
  builders all live in the same file as the leaf (as `WpSconfAlu`'s
  push/pop/16sp wrappers do), no call site outside it changes.

### A BUNDLE FRAMED ACROSS AN INTERRUPTS-ENABLED STEP MUST BE HART-FREE

At `b = true` every step's `wp_next` may resume on a different hart, and the
only things that cross are what a leaf RE-DELIVERS (`sie_cap_gpr`) and what
TRANSPORTS — `cpu_own`, `trap_csrs_ext`, `cpu_claim_ext`, and each of those
only because its proposition is `emp` or a pure fact at `true`. Everything
else a function holds there is FRAMED, and framing a hart-indexed proposition
across a possible migration is unsound. So **the environment bundle of any
function that runs at `b = true` has to be hart-free**, and that is a
constraint on the INTERFACES it takes, not something the proof can arrange.

Two shapes discharge it, and usertrap needed one of each:

- the resource genuinely is per-hart → carry the `□ ∀ h` form, as
  `SpecPanic.panic_wp_any` does for panic's contract and
  `UsertrapRes.devintr_caps_any` does for `SpecDevintr.devintr_caps`
  (`TimerCap.timer_cap` holds this hart's mcounteren/stimecmp;
  `SpecClockintr.tick_keeper`'s left disjunct is about this hart). Check
  satisfiability at the boot end before adopting it — the `∀ h` form can be
  strictly stronger, and here it is: it rules out satisfying the tick keeper
  with `tick_hart = false`, which is right, because a process can migrate onto
  hart 0.
- the resource is an ABSTRACT family, so nothing can transport it → drop
  `{CID : CpuId}` from its declaration. `SpecSyscall.syscall_env` did. That is
  not a hack: the union it stands for is locks, invariants, ghost fragments and
  memory points-to, and its own eventual proof would hit the same wall (a
  parking table entry returns at `true` and syscall's tail runs on from there).

The one-command check is `About <bundle>`: its argument list must not contain
`CID`.

### `CpuId` IS A CLASS, SO A CROSSING NEEDS A NEW SECTION — `rename` DOES NOT WORK

A leaf applied after a crossing resolves its hart by INSTANCE RESOLUTION, not
by unifying against the hypothesis handed to it, so it picks the SECTION
variable and fails with the *"iSpecialize: cannot instantiate (X -∗ …) with
(X)"* both-print-identically error above. The leaves' own recipe —
`rename CID into CID0` so the rebound hart can be called `CID` — **does not
transfer to a caller**: what it moves is a name, what picks the hart is
resolution, and the first leaf after the crossing still resolves at the entry
hart (measured, in usertrap's tail). Two routes:

- annotate `(CID := CIDx)` on every leaf, `(CID0 := CIDx)` on every
  `wp_next_off_intro`, and `(CID := CIDx)` on every hart-indexed term written
  fresh (`rget`, `tp_pin`, `cid_word`, `cpu_claim`, `sie_cap_gpr`, …);
- or put the post-crossing stretch in a SECTION OF ITS OWN, where the ambient
  `CID` *is* the post-crossing hart and not one annotation is needed. This is
  the "CHAINING TWO HALVES OF A FUNCTION" recipe above, applied for a reason
  other than the linear exit: **one section per hart EPOCH.**

Annotate for one or two steps; split for anything longer.
`ProofUsertrapTail`'s `ut_ret` (the `jal`, then prepare_return) / `ut_ret2`
(+0xb2 to the exit, applied at `(CID := CIDp)`) is the worked instance, and
splitting is what made a fifteen-instruction stretch annotation-free.

**A FUNCTION BUILT OUT OF SHARED TAILS NEEDS *N* SECTIONS, ORDERED BY WHO
APPLIES WHOM ACROSS A CROSSING — and the stack is easy to under-count.** A
dispatcher factors naturally into layers that each end in the next one
(`ProofSyscall.v`: epilogue ← return tail ← per-syscall arm ← capstone), and
every layer applies the one below it *after* its own `wp_next` — the store's
crossing, the callee's crossing, the `c.jalr`'s. A sibling in the SAME
section is rigid at that section's hart, so each layer has to sit in its own
section, in that order; `End` is what turns the hart into an ordinary
`(CID := …)` argument. Two corollaries: **hoist the `Notation`s and `Ltac`s
above all the sections** (an in-section abbreviation does not survive `End`),
and note that a **`Definition` with its own `` `{CIDh : CpuId} `` binder is
already hart-generic** — the binder wins over the ambient section variable —
so the shared *vocabulary* (`_pre`/`_hcont_ty`/`_goal` predicates) stays in
one place while only the *lemmas* stratify. Getting the count wrong shows up
as `iApply: cannot apply (WP Loop)`, which names neither hart.

## Changing the kernel SOURCE

Editing `xv6-riscv/` moves symbol addresses and takes every proof that names one
with it. The breakage itself — relayout, immediates, `.rodata` addresses, data
symbols, stack-budget cascades, register reallocation, Link functor arity, and
the two tools that do the mechanical 90 % — is the same as an upstream bump and
is documented once, in [`xv6-bump-playbook.md`](xv6-bump-playbook.md). Three
things are specific to changing the source yourself, and they come first:

**1. GATE: prove the toolchain reproduces the image BEFORE changing anything.**
There is no record of which gcc built the tracked dumps — CI never builds the
ELF, it uses the checked-in `kernel-rocq/*.v`. Install a toolchain, build at the
**unchanged** pinned `XV6_REV`, dump to a scratch dir, and diff against the
tracked files: all three must be byte-identical. If they differ, STOP — a
rebuild would re-do register allocation and inlining across the whole kernel and
take every proof with it, and you would be debugging that instead of your change.

**2. Take the MINIMAL source change.** Cherry-pick the one commit onto the pinned
rev; do not move to a branch head. Bundling unrelated commits makes it impossible
to tell which change broke what.

**3. Measure the shift from the SYMBOL TABLES, not by assumption.** Diff old vs
new `KernelSyms.v`. Expect one uniform delta over a BOUNDED window — a 6-byte
fix inside `writei` moved 46 symbols by +6 and **nothing above it**, because
`kernelvec`'s alignment padding absorbed the 6 bytes, and the data symbols did
not move at all. Assuming "everything above the change shifts" flagged 92
literals in 70 files where the true set was 14; shifting the other 78 would have
broken working proofs.

## A PREMISE SET CAN BE UNSATISFIABLE AND STILL COMPILE — state register agreement POSITIVELY

A block lemma in the middle of a function has to say which registers still
hold their entry values, and the tempting way to say it is by EXCEPTION:

```coq
    forall r, is_cs_idx r = true -> r <> Rs1 -> r <> Rs2 -> r <> Rs3 ->
      M !!! Regidx r = m0 !!! Regidx r          (* WRONG *)
```

`CalleeSaved.is_cs_idx` contains **sp (x2) and s0 (x8)**, and a prologue
moves both — sp to `pa_stk sp0 k`, s0 to the frame pointer.  So the premise
also demands `M !!! sp = m0 !!! sp`, which is false the moment the frame is
pushed.  The lemma is then *easier* to prove (it has a contradictory
hypothesis) and **no caller can ever apply it**; `coqc` is green and the
block is dead.  It surfaced in `ProofConsoleintr`'s kill-line loop and its
restore stub, both of which had compiled for a whole commit.

State the claim POSITIVELY instead — the explicit list of the registers that
really are untouched (`ct_cs_top` = s4..s11) — and account for sp and s0
separately, sp by the explicit `pa_stk` equation the block already carries
and s0 by the epilogue's reload.  Transport lemmas
(`ct_cs_hi_thr`-style: "a run that writes no callee-saved register carries
the claim") make the positive form as cheap at the call sites as the
quantified one looked, and they replace the ten-way `split_and!` each site
would otherwise repeat.

**The general rule: a hypothesis of the form "everything in <set> except
<list>" is a claim about a set you have to go and read.**  Two cheap
defences — write a one-line `Lemma foo_refl : P m m` and check it still
applies where you expect, and grep for a caller that can supply the premise
BEFORE building on top of it.

### The RESOURCE form of the same trap: two owners of one address space

The register version above is about a pure premise.  The resource version is
worse, because the two claims are spelled in different vocabularies and look
unrelated on the page.  It cost a session at the uservec boundary
(`claude-notes/projects/uservec.md`): `wp_uservec_pt` took the kernel-side
residue `usertrap_res pt vksp` BESIDE the user-mode frame
`user_trap_frame C pt Rut`, and those two share **the entire user address
space** — four separate overlaps, none of them syntactically visible:

| resource | kernel-side spelling | user-side spelling |
|---|---|---|
| satp / tlb | `sie_cap` → `strans_inv` → KPT arm → `KptShare.tlb_res_pt` | `UptTree.utlb_inv_pt` |
| page-table tree | `proc_priv` → `proc_pt_at` → `proc_pt` → `pt_frame` → `ptree_own 2 (DfracOwn 1)` | `utlb_inv_pt` → `ptree_own 2 (DfracOwn 1)` |
| data pages | `proc_pt` → `proc_pt_own` = `upt_pages_own` | `user_pt_inv` → `udata_own` |

The 44-instruction walk went through, the hart crossing went through, and the
whole thing looked three plumbing bugs from done.  It was vacuous.

**The diagnostic is one scratch lemma, and it takes minutes.** Pick the
resource you suspect and try to prove `False` from the two premises:

```coq
Lemma satp_double_owned (uroot tfp : mword 44) (um : gmap (mword 27) (mword 64)) :
  strans_inv -∗ strans_bit strans_bit_kpt -∗ utlb_inv_pt uroot tfp um -∗ False.
```

If it compiles, the spec above it is dead.  **Do this whenever a new spec
takes two bundles that were written by different tiers** — especially when one
of them is a `_res`/`_inv` whose internals you have not read.  A bundle is a
claim about a set you have to go and read, exactly like the register case.

**And the fix is never per-resource accessors.**  Adding `_tf_open`, then
`_tlb_open`/`_tlb_close`, then one for the tree, then one for the pages, is
rediscovering the table one `False` at a time.  The fix is ONE split, at the
boundary between what the two tiers genuinely own: name the reduced residue
(`ut_res_bare` = everything the kernel still owns while user code runs) and
prove `bare ∗ <address space> ⊣⊢ full` as an exact open/close pair.  Then the
view conversion is a separate, already-existing lemma
(`ProcPtOwn.proc_pt_own_udata`, the pt2 switch window) applied once.

**IT RECURS AT EVERY *ENTRY* TO A LOOP WHOSE ROUNDS ARE ALREADY RIGHT, and
that is the case that survives longest.**  `SpecUserretClosed`'s theorem took
the residue `usertrap_res_bare pt ksp` AND the trapframe's 31 save slots
(`tf_pa (ud_tfp pt) off ↦ₚ₈{dqm}`) as sibling premises -- and the residue owns
that page in full, through `proc_priv_nopt` → `ProcInv.tf_page`.  Every LOOP
round was fine (`wp_uservec_pt` opens the page out of the residue, hands
userret the slots, takes them back, closes), so nothing downstream was wrong;
only the ENTRY was, and it stayed wrong until a caller (forkret) actually had
to supply both.  The tell is the same one: two premises written by different
tiers, one of them a sealed `_res`.  The fix is the same shape too -- the
entry opens the page out of the residue ITSELF and takes a CLOSER
(`31 cells -∗ Rut pt`) where the naked `Rut pt` used to be, so the bundle is
completed at the one point the slots are back in hand.  **A `-∗` premise is
how a linear resource that a callee borrows and returns should be threaded;
a bare conjunct beside it is how it gets claimed twice.**

## A CLAUSE ABOUT **NAMES** MUST TAKE THE WRITE'S ATOMICITY; ONE ABOUT
## INUMS OR INDICES NEED NOT

A payload invariant crossing a byte-range write is usually priced by
looking at the WINDOW: does the write touch the records the clause speaks
about?  That is the right question for a clause about a record's INUM
(`DirView.dir_ok`: the mod-256 argument covers a one-byte write) or about
an INDEX (`dir_dots_ix`: `dir_slot` keeps the window away from records 0
and 1).  It is the WRONG question for a clause about NAMES, and the
failure is silent until the proof.

The reason is the on-disk format: xv6's unlink zeroes only the inum
halfword, so **a free record still carries the name bytes of whatever was
deleted from it**.  A PARTIAL `dirlink` write (`0 < tot < 16`) puts a live
inum into such a record while leaving some of those stale name bytes in
place — so the record goes live under a name nobody chose, which may
duplicate a live one.  `FsTree.dir_uniq` is false there; so is any future
clause of the form "the live names are …".

**The fix is free and already in the contracts**: `SpecWritei`'s
`wi16_atomic` (`wi_blocks off n = 1 -> tot = 0 \/ tot = n`) is relayed by
`SpecDirlink`'s `dl_post` as `tot = 0 \/ tot = 16`, and every caller
destructs it already.  Take it as a premise of the preservation lemma.
The same clause is what `DirLinks.dir_link_at`'s re-park needed for an
unrelated reason (there is no ticket for a half-written record), so a
walk that has one has the other.

Corollary for reviewers: when a new pure conjunct is proposed for
`ic_loaded`, ask *"is it about names?"* before believing a "free at
dirlink" estimate.  (Cost: one design revision in the `dir_uniq`
increment, which had been priced as free off a landed lemma.)

## A WEAKENING IS CHEAP TO PROVE AND EXPENSIVE TO USE — plan the sweep accordingly

Strengthening a lemma's HYPOTHESIS weakens the lemma, so it stays provable from
the existing proof by instantiating the stronger hypothesis at whatever the old
one supplied.  That is genuinely free.  **What is not free is every CONSUMER**,
which must now establish the stronger form — and that obligation propagates up
the whole tier, not one level.  Both halves showed up in the same change:
wrapping `WpIntrInv.wp_exec_step_intr`'s σ-callback in `WpNext.wp_next` costs the
engine's own proof one `iApply … $! cpu_id` with the guard closed by
`reflexivity`, and costs its consumers `wp_instr_s_intr` → `wp_instr_s_sconf` →
~60 leaf proofs, because each in turn has to invoke ITS caller's callback at the
rebound hart.  **There is no independent half of such a change**: if you are
tempted to land "just the bottom lemma", check whether its immediate consumer can
still call its own continuation.  (`completed/explicit-cpuid.md` made exactly this
trade one tier lower, and its Stage-1/Stage-2 split is the same observation.)

Two mitigations worth reaching for before budgeting the full sweep:

- **A consumer that can DISCHARGE the stronger form pays nothing.**  For
  `wp_next`, `wp_next_off_intro` (interrupts off) and `wp_next_idle` (no current
  proc) collapse the obligation outright, so the interrupts-off-only leaves — the
  ones threading per-hart registers, which would have been the hard cases — are
  free.  Look for the collapse lemma first and count what it covers.
- **IF THE CONE ALREADY THREADS A PERSISTENT BUNDLE, PUT THE NEW AMBIENT
  CREDENTIAL IN THE BUNDLE.** Threading `kernel_data` + `panic_env` down to
  kexec's panic arm would have meant two more premises on each of that cone's
  dozen block lemmas — ~40 edits — against one conjunct added to
  `SpecKexec.fs_fabric`, which every one of them already carries as a single
  hypothesis, plus one extra name in each `iDestruct "Hfab"` pattern. Nothing
  is hidden by it as long as the new conjunct is NAMED in the bundle and the
  obligation it feeds is still discharged explicitly at the arm. The test for
  whether this is bundling or burying: does a reader of the arm still see
  which resource paid for it?
- **Widen an EXISTING premise slot instead of adding one.**  A new premise changes
  arity and therefore every call site; widening what an existing slot MEANS costs
  nothing wherever the slot is discharged by an opaque `ltac:(…)`.  Measured on
  this tree: `IntrDefs.rd_ok` → `ops_ok` over the read operands touched 33 leaves
  and 4 engines and **zero of 1192 call sites**, because all 1192 fill that slot
  with the positional `ltac:(rdok)`.  This is the second time the trick has paid
  (`rd_ok` itself replaced an older `rd <> csp_rs1` the same way), so it is worth
  designing FOR: keep such side conditions in one named, Ltac-discharged
  predicate rather than as loose conjuncts.

**The mirror-image plan — "the POSTCONDITION gains a conjunct, so no premise
moves and no call site changes" — is only free if the callee's own premises
already imply the conjunct, AND THE ARM TO CHECK IS THE ONE THAT RETURNS ITS
INPUTS UNTOUCHED.**  An early-return arm typically answers with the caller's
own record (`dn' = dn`, `data' = data`), so a new postcondition conjunct about
the OUTPUT is, on that arm, a claim about the INPUT — which the callee was
never given.  Both of `SpecWritei`'s two added `inode_ok` conjuncts failed
exactly there (and the size cap failed on the writing arm too, because
`max(old, new)` is unbounded when the old one is), and stating them
unconditionally would have forced them to become premises and rippled into
`SpecDirlink` and every caller below.  **When the consumer that wants the fact
already holds it going in — which it does whenever the fact is a conjunct of
an invariant it is about to REBUILD — state the PRESERVATION,
`⌜P input -> P output⌝`, not the fact.**  It is provable, it is genuinely
additive, and the consumer discharges the antecedent from the bundle it
already opened.  Budget a postcondition strengthening only after checking it
against every arm that returns an input verbatim.

**WHEN A CONTRACT RELAYS A CALLEE'S EXPOSED CLAUSE, RELAY ITS GUARD
VERBATIM — never re-state it at the arm you happen to need.**  A relayed
clause costs the same whatever its guard says (the proof is one `exact`
either way), so narrowing it buys nothing and silently deletes the OTHER
arms from every downstream ledger — and the deletion is invisible until
some caller has to pay for an arm the guard no longer covers, which can be
stages later and in a different file.  `SpecDirlink.dl16_post` relayed
`SpecWritei.wi16_post` under `tot = 16` where writei's own guard is
`0 < tot`; the short write vanished from the contract, and create's whole
failure arm turned out to be unprovable because of it
(`CreateBudget.cr_fail_counted_busts`).  **And where the callee's guard
excludes an arm the caller must still price, that is a finding about the
CALLEE's post, not something the caller's proof can repair**: what it can
relay there is only the coarse counted bound, and stating that honestly —
with the figure the walk actually proves, not the one the ledger wants —
is what turns the gap into a sized stage instead of a wrong number.

**AN AMORTIZED LOOP'S "CREDIT" IS A FUNCTION OF THE SET THE CONTRACT
ALREADY THREADS — DO NOT ADD A BOOLEAN FOR IT.**  Where a cost is carried as
held-back POTENTIAL over a set (`WriteiBudget.bm_pot`: one unit iff the
bitmap block is already in the op's logged set), the invariant computes the
credit itself with a `bool_decide (… ∈ SI)`, and its entry lemma holds at
*any* entry set.  Adding a `cr` parameter on top duplicates that device,
re-introduces the case split the potential was built to remove, and gives
callers two ways to say the same thing — a caller that has already logged
the block simply gets a call that spends one less than its budget allowed.
Reach for a `cr` boolean only where the callee is STRAIGHT-LINE (iupdate,
log_write) or where the split is genuinely one-shot (bmap; itrunc's single
bitmap unit).  **Before adding a credit parameter, check whether the
callee's own invariant already derives it** — `SpecWritei`'s header and
`WriteiBudget.wi_inv_enter` are the worked statement of the rule, and a
whole planned stage was retired by reading them.

**A STRONGER CALLEE BOUND DOES NOT COMPOSE FOR FREE.**  When a callee is
generalized and its post gets *tighter* (`n - 2 <= n'` where the caller's
own lemmas are stated at `n - 3`), every caller lemma phrased at the coarse
constant stops typechecking — the error is a bare "The term … has type …
while it is expected to have type …" naming two bounds that differ only in a
literal, which reads like an arithmetic mistake. Weaken ONCE at the seam,
right after the callee's `iIntros`, and **keep the hypothesis's name**
(`assert (Hw : <coarse>) by (unfold …; lia). clear H. rename Hw into H.`) so
nothing downstream moves. Never loosen the callee's contract to match: the
strength is real and some other caller wants it.

**A GENERALIZED CONTRACT THAT THE OLD ONE MUST BE *DERIVED FROM* HAS TO BE
CHECKED AT THE OLD ONE'S CORNER BEFORE THE WALK IS WRITTEN.**  When a
retrofit makes the general form the proven core and the landed form a seal
(the shape forced whenever the resource has no auth-monotone shadow — an
exclusive `ghost_map` element hands back a value at an unrelated
existential, and nothing recovers a relation to the caller's), every clause
of the general post must *instantiate to the landed clause*, not merely to
something true.  A bound that is honest but loose at the uncredited corner
does not weaken the new contract — **it makes the old one unprovable**, and
the retrofit stops being additive.  The instance: itrunc's credited post was
designed with `u' <= it_entry crb u`, which at the uncredited corner reads
`u' <= S (S u)` where the landed contract says `u' <= S u`; the fix was to
notice that the tail flush ALWAYS runs, so its unit is spent
unconditionally, and to state `u' + it_iu cru <= it_entry crb u`.  Cheap to
check (instantiate the clause at the corner and compare syntactically),
very expensive to discover after the walk.

Corollary on picking the premise: **guard a side condition on the index that makes
it necessary.**  `src_ok b rs := b = true -> Regidx rs <> Regidx Rtp` is provable
at every site, whereas the unguarded `rs <> Rtp` is UNPROVABLE at the three places
that legitimately read `tp` (all of which run interrupts-off, where the condition
is not needed).  An unguarded side condition that is false somewhere real forces a
duplicate leaf family; a guarded one is discharged by `discriminate`.

## Write the checker for a refactor's SILENT failure mode, before the sweep

If a change has a way of going wrong that still compiles, that way WILL be
taken, and no build will tell you. A checker exists because of exactly that,
and it is cheap enough to run on every touched file:

- **A `Local Lemma` is INVISIBLE to every other file, and the error names the
  USER, not the definition.** `ProofBallocParts.bal_pow_mod8_small` was
  `Local`, so `ProofBalloc.v` failed with *"The variable bal_pow_mod8_small was
  not found"* — which reads like a typo in the caller. Before hunting a
  misspelling, `grep -rn "<name>"` and check for `Local`; a helper that a
  sibling proof file needs must not be `Local`, and the proof that it is needed
  is that the sibling names it.

- **A PREMISE-DELETING SWEEP LEAVES TWO KINDS OF WRECKAGE, AND NEITHER IS
  FINDABLE BY GREPPING FOR THE DELETED NAME** — the name is gone; only the
  hole it left is still there. (a) If the deleted conjunct was the LAST one,
  the definition loses its closing `)%I.` and runs into the next sentence;
  the error is a syntax error tens of lines later, in code that is fine.
  (b) If the deleted conjunct was the WHOLE body, you get `Definition f … :=`
  with nothing after `:=`, reported as *"Syntax error: [reduce] expected after
  ':='"* at the FOLLOWING `Definition`. Both happened in one sweep
  (`SpecFileclose.fileclose_fs_env`, `ProofKwait.kw_rt`). Grep afterwards for
  a `:=` followed by a blank line and for a `∗` immediately before a blank
  line. Related, on the proof side: a sweep that edits STATEMENTS leaves every
  `iIntros`/`iApply` name in place, so strip the token from multi-line
  proofmode strings AND from `&`-separated destructuring patterns — a
  per-line, space-separated regex misses both and quietly leaves `(A & & B)`.

- **RETIRING A RESOURCE THAT 200 FILES NAME HAS FOUR SHAPES, AND ONLY THE
  FIRST IS A ONE-LINER.** Deleting `PanicStub.panic_wp_any` (207 files, 264
  changed) took five build rounds, and every failure after the first was one
  of the last three:
  (a) **the premise has three spellings** — alone on a line, mid-line after
  another premise, and at end-of-line with the continuation below. A
  line-anchored regex sees one of them; miss the others and the next full
  build reports them one file at a time.
  (b) **the hypothesis name is not uniform** — `Hpanic` in almost every file,
  but `Hpany` in `ProofMain`/`ProofMainSecondary` and `Hpanicany` in
  `ProofBwrite`. Enumerate the names before writing the regex
  (`grep -ho '#H<stem>[a-z0-9]*' *.v | sort | uniq -c` prints the roster).
  (c) **dropping a conjunct from a BUNDLE renumbers every POSITIONAL
  projection downstream of it.** Seven bundles carried this one, and
  `UsertrapRes.ut_caps`' consumers project by position
  (`iDestruct "Hcaps" as "(_ & _ & $ & _)"`), so five of those had to lose
  exactly one `_`. **The error is `iAndDestruct: cannot destruct` and it
  names the SURVIVING conjunct, not the missing one** — it reads like the
  bundle is the wrong shape rather than one short.
  (d) **a CONSTRUCTION site loses a tactic, not a name.**
  `iFrame "… Hx"` merely shortens, but `iSplitR; [iExact "Ha" | iExact "Hx"]`
  has to lose the whole `iSplit`: the bundle is one conjunct shorter, not one
  name shorter.
  **And do not normalise whitespace while doing any of it.** Collapsing runs
  of spaces on every touched line reflowed alignment inside `iIntros` patterns
  across 190 files and made the diff unreadable — back out with
  `git checkout -- <dir>` (never `reset --hard` in a shared tree) and redo it
  removing the token plus exactly one adjacent space.
- **`tools/lemma_diff.py [--ref REF]`** — reports top-level declarations that
  VANISHED relative to a git ref, plus `Admitted`/`admit`/`Abort` and any new
  `Axiom`/`Parameter`/`Hypothesis`. **Until 2026-08-10 its regex was anchored
  at column 0 and therefore blind to every Section-indented declaration —
  i.e. to essentially all of the Iris layer — and it reported CLEAN across
  real deletions.** The guard against silent sweeps was itself silently
  failing, which is this section's lesson eating itself: when a checker's
  verdict surprises you in the GOOD direction, check the checker. A sweep's characteristic failure is not a
  red build; it is a file that compiles because something was quietly dropped —
  a lemma deleted instead of restated, a `Module Type` that lost a `Parameter`.
  Every line it prints is a thing to justify, not necessarily a bug (a
  deliberate rename shows up as one `GONE`), which is the point.

The definitive soundness check for a whole cone is still
`Print Assumptions <the linked top-level theorem>` — it is the only one that
sees through every functor and seal. Do it once at the end of any interface
change and diff the axiom list against what the coverage report says should be
assumed; anything else is a regression.

## Three ways a build check can LIE about being green

The failure mode of each is a green-looking ANSWER, not an error.

- **A `.v`-vs-`.vo` mtime sweep is not a staleness check.** The obvious loop
  `for f in *.v; do [ "$f" -nt "${f%.v}.vo" ] && echo STALE $f; done` compares
  each file against ITS OWN `.vo` and misses TRANSITIVE staleness entirely: edit
  `SpecFoo.v`, rebuild it alone, and every `.vo` above it is stale while the
  sweep reports the tree clean, because none of those `.v` were touched. Only
  `make` knows the dependency graph. **The cheap correct check is `make -f
  CoqMakefile -q`** (or a plain `make`, which prints `Nothing to be done` when
  genuinely up to date); the cheap correct SPOT check is `find . -name '*.vo'
  ! -newer <the .vo you just rebuilt>` restricted to the files that Require it.
  Never report a build state from mtimes alone.
- **A PER-FILE `coqc` loop is a check of the FILE, never of the TREE — and a
  correct `.vo` COUNT does not contradict that.** A mirror reported the expected
  `.vo` count and every single-file `make -f CoqMakefile <t>.vo` passed in
  minutes; the first full `make` then recompiled from the bottom, because a base
  `git checkout` had refreshed every `.v` mtime and each per-file build had only
  brought ITS OWN dependency chain up to date. **And `make -q` is not the tell
  here**: it exits 1 on the phony `pre-all`/`real-all`/`post-all` targets even
  when nothing needs building. The cheap correct probe is **`make -f
  CoqMakefile -n` and look for `COQC` lines**; the authoritative one is a full
  `-k` build. Budget for that full build at the START of a stage rather than
  discovering it at the gate.
- **`make … | grep -E … | head -N` truncates the CHECK, not just the output.**
  Once `head` has its N lines it closes the pipe, so any later error is never
  seen — and `echo $?` after the pipeline reports the LAST command's status, not
  make's. Capture make's own exit status (`make proofs > log 2>&1; echo $?`) and
  grep the file afterwards.
- **A green build BEFORE a rebase says nothing about the tree AFTER it, and the
  commit most likely to break you cannot conflict textually.** The nightly
  dead-import sweep (`.github/workflows/dead-imports.yml`) removes and RE-POINTS
  imports across ~100 files at a time. It changes no statement and no proof, so
  the rebase is always clean — but it changes which names arrive TRANSITIVELY,
  and its likeliest victim is a brand-new file, whose own import list nobody has
  ever pruned and which therefore names half its vocabulary through chains that
  happen to carry it. **Rebase, THEN build, THEN push** — never push while the
  verification build is still running, however small the incoming delta looks.
  The fix is always the same: add the requires explicitly; the next sweep prunes
  whatever is genuinely unused.
- **A SENTINEL WAIT LOOP READS A LOG THAT IS ALREADY THERE.** The recommended
  "have the build write its own sentinel and wait on `grep EXIT` of the log"
  becomes an instant false green when a *previous session* left that log on the
  box: `until grep -q PAEXIT /tmp/pa4.log; do sleep 20; done` returned at once
  against a file two days old, and the axiom list read out of it belonged to
  another cone entirely (it named `consoleread`, which the cone under test
  cannot reach — that mismatch is the tell, and it is the only one). **`rm` the
  log in the same command that starts the job**, and check the file's mtime
  before believing its contents. Shared `/tmp` on a long-lived mirror is full of
  other agents' leftovers with exactly the names you would pick.

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
- **A FILE DELIBERATELY OUT OF THE BUILD IS DESCOPED BY A COMMENTED ROW, and a
  bare `# Foo.v` is the syntax the check recognizes.** Leaving a `.v` on disk
  while dropping it from the build is legitimate — a descoped tier kept for a
  later revival, a retired de-risk kept as the worked provenance its neighbours
  cite — but *silently* dropping it is the accident the check exists to catch,
  and the two look identical from outside the project file. So the intent is
  recorded in the project file, beside the rows it sits among, where the
  reviver looks: comment the row out to a bare filename (prose above it
  explaining why is ignored by the parser, and is the point of the block).
  Then reviving the file is uncommenting one row. Two new drift errors keep
  that honest: a `# Foo.v` naming a file that no longer exists (it promises the
  reviver a row that cannot come back), and a name both listed and commented
  out. In the tree today: the descoped Umode tier (~41 rows) and
  `EscrowRegionA.v`.
- **THE PROOF FUNCTOR NEEDS ITS `: <MODTYPE>` ASCRIPTION, and without it the
  function reads `assumed` with the build green.** `module_status` matches a
  `Link` instance to a spec through `Module <F>Proof (…) : <MODTYPE>.`; a
  functor with no ascription is never connected to anything, and the `Link`
  that applies it type-checks anyway (the signature is checked at the
  CONSUMER's functor application instead — `LinkUartintr.v` for consoleintr).
  So the report is the only thing that notices. Ascribe the functor.
- **AND SPELL THE `Link` INSTANTIATION UNQUALIFIED.** The script matches a
  functor application with `^\s*Module\s+(\w+)\s*:=\s*(\w+)((?:\s+\w+)*)\s*\.`,
  and `(\w+)` does not match a DOTTED name — so
  `Module Kfork := ProofKforkMain.Kfork Myproc ….` makes a proven, linked,
  axiom-clean function read **`assumed`**, with no error anywhere. Follow the
  tree's convention: name the functor `<F>Proof` in the proof file, `Require
  Import` it, and write `Module <F> := <F>Proof …` with a bare name. (Cost
  one debugging round on kfork; the same trap is one character away from
  every new `Link` file.)
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
  contracts (`kerneltrap`) in `MANIFEST_ASSUMED`. Every
  entry is verified against the tree and a stale one is reported as a manifest
  error rather than silently counted — fix those when they appear.

## Proofmode & bitvector gotchas (recur across files)

- **AN `=`-EQUATION BETWEEN TWO `iProp`s DOES NOT RELIABLY `rewrite` INSIDE THE PROOFMODE, AND THE ERROR NAMES A TERM THAT PRINTS AS THE GOAL.** A mover stated as `f x = (if b then P else Q)` (both sides `iProp Σ`) fails with *"Found no subterm matching …"* against a goal whose printed form IS that RHS — because the goal's copy was elaborated through an `iExists`-instantiated `∃`/`∗` skeleton and is not syntactically the same term. No stronger rewrite fixes it. **State the mover as a WAND in each direction and `iApply` it**; keep the equation only as the reading. (`DirLinks.dlc_tick_dot_out`/`_in`, `_name_out`/`_in` are written that way after the equations `dlc_tick_dot`/`_name` failed at exactly one of their four use sites.)

- **AN `own`-GHOST-STEP WHOSE FRAGMENT IS AN OP-TERM MUST BE STATED AS A GOAL AND `iApply`ed, NEVER `iMod`ed WITH EXPLICIT ARGUMENTS — the failure is a silent divergence, not an error.** Minting two fragments in one step (`link_update_alloc z a a' (b1 ⋅ b2)`) via `iMod` with every argument explicit spins forever at the `iMod` sentence (>14 min at 100 % CPU, stable RSS, no message); the IDENTICAL proof stated as `iAssert (|==> auth' ∗ frag (b1 ⋅ b2))%I … as ">[Hauth Hfr]"` with `iApply (link_update_alloc with "Ha")` inside — unification against the stated goal instead of elaborated arguments — completes in seconds. `iCombine "H1 H2" as "H"` on two `own`s of singleton auth-maps over a wide product CMRA diverges the same way (its `IsOp`/`CombineSepAs` search); combine with `iDestruct (own_op with "[$H1 $H2]") as "H"` + `iEval (rewrite singleton_op -auth_frag_op) in "H"` (all `=`-rewrites, no setoid search). And a `≡`-split of a fragment (`full ≡ half ⋅ half`) must NOT be setoid-rewritten under `own` inside `iEval` (fails fast with *"setoid rewrite failed: UNDEFINED EVARS"*) — do the `rewrite -Hsp` in the PURE local-update subgoal, where `local_update_proper` carries it. (All three found landing V5''s fractional parent register in `IcacheRef.link_mint_linkdp`/`link_spend_linkdp`.)
- **A `prod_local_update'` CHAIN OVER A WIDE NESTED `prodUR` COSTS SECONDS PER `apply` — ~8 s each at a 7-component element, and in a long Section EVERY apply pays it** (in a small scratch file only the first does). A file with a dozen movers over such an element takes minutes for the algebra section alone. When widening a ledger element, budget for it — or fold the per-component chain into ONE composed helper lemma so each mover pays the elaboration once. (`IcacheRef.v` after the V4+V5' widening.)
- **A STALE `iDestruct` PATTERN CAN SPLIT A NESTED CONJUNCTION AND BIND THE WRONG RESOURCE — silently, and it surfaces far away.** When a bundled predicate loses a conjunct, an intro pattern with the OLD arity does not necessarily fail: if one of the remaining conjuncts is itself a separating conjunction, the extra slots happily split IT instead. A four-slot `"(_ & _ & #Hdev & _)"` against a now-three-conjunct bundle bound `#Hdev` to the FIRST COMPONENT of the third conjunct (itself a 4-way `∗`) with no arity error, and failed eight lines later at an application wanting the whole thing — reported as "cannot instantiate … with (uart_inv γd)". **When you change the shape of a bundled predicate, grep for every `iDestruct` of it and re-count**; the error, when it comes, names the consumer and not the pattern.
- **TWO `bv` BYTES WITH THE SAME VALUE NEED NOT BE THE SAME TERM, AND THE ERROR PRINTS THEM IDENTICALLY.** Reading an IMAGE byte into a `uM_bytes` window fails with *"Unable to unify \"Some 54%bv\" with \"Some 54%bv\""* — the two really are equal as bitvectors, but one is `Z_to_bv 8 0x36` (what the dump holds) and the other is `nth_byte w 0` (what the window wants), and they carry DIFFERENT `bv_is_wf` proofs. `vm_compute; reflexivity` cannot bridge it, and the message gives you nothing to work with because both sides print as their common value. The route: get `M !! k = Some (Z_to_bv 8 …)` from `sh_data_sub` first, `rewrite` it, then close with `f_equal; apply bv_eq; vm_compute; reflexivity` — `bv_eq` is what discards the proof component. (Hit reading `runcmd`'s jump table out of `ShData.sh_data`; a byte introduced EXISTENTIALLY never hits it, which is why most image reads in this tree do not.)
- **`vm_compute` INSIDE AN `ltac:(…)` WHOSE ARGUMENT POSITION IS STILL AN EVAR HANGS; `lia` THERE FAILS WITH A MISLEADING MESSAGE.** `exact (some_lemma _ ltac:(vm_compute; reflexivity))` — where the `_` is inferred from the goal only AFTER the `ltac:` runs — spins forever rather than erroring, and costs you the "is this a slow proof or a hang?" question. `coqc -time` localises it in one run; reach for that before bisecting. In the same position `lia` does fail, but it reports **"Cannot find witness"**, which reads like an arithmetic gap and is not one — it means the goal still had an evar in it. In both cases the fix is to name the value: `assert (H : …) by (vm_compute; reflexivity)` and pass `H`, or supply the `_` explicitly. (Cost 22 minutes once and recurred three more times, once per `_`-inferred address, while proving `nulterminate`.)
- **A `*)` INSIDE A COMMENT SILENTLY CLOSES IT, AND THE ERROR APPEARS SOMEWHERE ELSE ENTIRELY.** Quoting C in a comment is enough to do it: `a5 := *(int*)(0x13b0 …)` ends the comment at `t*)`, and the rest of the intended comment becomes code. The symptom is `Nested proofs are discouraged` reported many lines later, at a `Lemma` that is perfectly fine — and every `Proof.`/`Qed.` pair still balances, so bisecting on `Qed.` lines finds nothing. The mirror case, a stray `(*` inside a comment (`(*eargv[i] = 0)`), gives `Unterminated comment` at EOF. **Write a comment-nesting checker and run it first**; a dozen lines of Python finds both in seconds. This tree has now been bitten by the pair three times (once mangling a comment via a careless regex substitution).
- **`split_and!` on `0 <= x < N` produces TWO goals, not one.** The conjunction is `0 <= x /\ x < N`. Any following bullet list is then off by one, and the error surfaces as a *rewrite* failure inside the next bullet ("The LHS of Hend (S i) does not match any subterm") rather than as a goal-count complaint. Count the goals after `split_and!` on any range hypothesis.
- **A CALLER'S `uM_only_in` WINDOW MUST COVER THE LOCALS IT PASSES DOWN, NOT JUST THE CALLEE'S FRAME.** The instinct "everything below my sp" is wrong for any function that hands a callee the address of one of its OWN locals. `parseexec` passes `&q`/`&eq` to `gettoken`; those cells live at `sp0-120`/`sp0-128`, inside parseexec's frame but ABOVE the region the callee carves — so the arg loop's window is `(uint sp0 - 320, 208)`, not 192. It must reach 16 bytes further up than the callee's frame, and still stop short of the caller's own spill slots, or the epilogue loses `ra`/`s0`. Get this wrong in either direction and the failure is a `uM_only_in` that cannot be established, reported at the caller.
- **A `rewrite` BETWEEN A `bv ?n` AND AN `mword 64` FAILS SAYING IT CANNOT FIND A TERM THAT IS PLAINLY THERE.** `rewrite <- H` with `H : m1 !!! Regidx r = m !!! Regidx r` fails with *"Found no subterm matching `m !!! Regidx ra_idx`"* inside a `uM_bytes M a 8 (m !!! Regidx ra_idx)` goal — because `uM_bytes`' value argument is a `bv ?n` with the width still an evar, while the equation is at `mword 64`, and **the two width indices print identically**. No stronger rewrite helps. State the whole spill/reload tower at the SOURCE file's spelling (`m1 !!! r`, `f1 !!! r`) and convert once at the end, in the final `ucallee_saved`, where both sides are honestly `mword 64`. Same family as the `Some 54%bv` / `Some 54%bv` unification failure above: when a message shows you two identical-looking terms, suspect an index or a proof component, not the values.
- **Some files are deliberately ssreflect-FREE, and that decides where a definition may live.** `Pt4kWalk.v` has 27 vanilla `rewrite … by …` rewrites, so it cannot `Require` anything that pulls in the iris proofmode — which `PageGeom.v` does (it needs ssreflect's `rewrite … in H |- *` for the two `uint`/`bv_unsigned` bridges it inherited from `KallocInv.v`). So a `page_base`-spelled restatement of a `Pt4kWalk` fact has to live in `PtBuild.v`, not in `Pt4kWalk.v`, even though there is no dependency CYCLE. Before planning a relocation into a low file, check whether that file uses `rewrite … by …`; the failure mode is a parse error at the first such rewrite, far from the import you added.
- **BUILD A CALLEE'S PRECONDITION BUNDLE WITH A NAMED `assert`, NEVER AN INLINE `ltac:`.** A conjunctive premise like `init_layout pt /\ init_text_sub M /\ is_aligned_vaddr (Virtaddr (mreg !!! Regidx ra_idx)) 2 = true` supplied as `(conj Hlay (conj Htext ltac:(rewrite Hmra; vm_compute; reflexivity)))` fails with *"The LHS of Hmra (mreg !!! Regidx ra_idx) does not match any subterm of the goal"* — by the time the `ltac:` runs, elaboration has zeta-expanded the `set`-bound register file, so the goal names the raw insert tower and the rewrite has nothing to hit. `assert (Hpre : <the whole conjunction>). { split_and!; [ … | … | rewrite Hmra; vm_compute; reflexivity ]. }` and pass `Hpre` works every time. Hit four times across UProofInitLib.v / UProofInit.v; the same shape is why `wp_init_write`'s three pure premises are named asserts too.
- In iris proofmode: `rewrite a b c` uses SPACES not commas (`rewrite H1, H2.` fails) — and a comma list is not rescued by the modifiers either: `rewrite H1, !H2` and `rewrite H1, <- H2` die with *"Syntax error: [ltac_use_default] expected after [tactic]"*, pointing at the `!`/`<-` rather than at the comma. Split them. `rewrite lem by tac` does NOT parse (ssreflect clash) — use `rewrite lem; [|tac]` / `rewrite (lem args ltac:(tac))` / `assert … by tac`. iris-FREE files can use `rewrite … by`. Rewrite a proofmode HYP with `iEval (rewrite H) in "Hpc"` — bare `rewrite H` rewrites the WHOLE `envs_entails Δ P` (hyps AND goal) and desyncs them.
- `iDestruct (lem with "…") as %pure` keeps the spatial inputs when the conclusion is pure (relied on by fetch/config lemmas) — a plain `iDestruct` of a pure-conclusion wand CONSUMES its premises. `big_sepM`/`big_sepL` byte extraction needs an EXPLICIT Φ (underscores leave TC evars unresolved).
- Value/frame binders must be `mword 64` (annotate; `add_vec` demands `mword n` and won't unify a `bv 64` binder even though `mword 64 ≡ bv 64`). Same trap for a value introduced from an EXISTENTIAL resource (`iDestruct "HR" as (t) "Hcell"` on a `∃ t : mword 32, a ↦₄ t` invariant body): `t` arrives as `bv 32`, so `sign_extend' 64 t` fails with "has type bv 32 while it is expected to have type mword ?n" — ascribe `(t : mword 32)` at every use (the ascription leaves no mark, so `change`/`set` terms still match the leaf's output). Decode-fact immediates must be the decoder's POSITIVE RESIDUE (−2016 → 2080; the signed literal fails `bv_is_wf`). Model names need `Defs.` qualification (`Defs.bind`/`Defs.read_reg`/`Defs.assert_exp'`; `rv64d_types.Read_plain`) or they resolve to raw Prompt_monad versions that won't unify with `M = Defs.monad`. A `.` immediately before `(*` parses as `.(` projection — leave a space.
- **A `nat`-ASCRIBED `Definition` WHOSE BODY IS AN `if`/`match` DOES NOT PUSH THE SCOPE INTO ITS BRANCHES.** Under the tree's usual `Local Open Scope Z_scope`, `Definition c (b : bool) : nat := if b then 0 else 1` fails with *"The term `0` has type `Z` while it is expected to have type `nat`"* — the return ascription constrains the `if` as a whole, but each branch is elaborated in the ambient scope first. Write the literals `0%nat` / `1%nat` per branch, and `(… + …)%nat` on any arithmetic. The same definition written with a bare literal body (`:= 3`) is fine, which is what makes this look arbitrary.
- `lia` cannot evaluate `2^n`/`bv_modulus`/`bv_half_modulus` — `assert (… = <literal>) as -> by (vm_compute; reflexivity)` first. In heavy-import WP files (WpSmodeGpr+SmodeCore+program_logic) `bitvector.tactics` sets a zify hook that makes `lia` return "Cannot find witness" on trivial bounds — prefer explicit `Z.le_lt_trans`/`Z.add_le_mono_r`/`Nat2Z.is_nonneg`. The hook arrives TRANSITIVELY (dropping `bitvector.tactics` from your own imports does not help), and what trips it is a goal mentioning `bv_unsigned`: so when a proof needs real arithmetic, factor the arithmetic into a lemma over plain `Z` variables and feed it the `bv_unsigned` values (`ProofMemmove.mm_overlap_arith`), where `lia` works normally. Widths appear as `MachineWord.Z_idx n`, so `change (Z.sub 57 12) with 45` (or `change (bv_modulus 27)` won't match `bv_modulus (Z_idx 27)`) before a rewrite; conversion beats rewrite for closed masks; `and_vec` needs `unfold word_binop, with_word', with_word` before `bv_and_unsigned` matches. Use `apply f_equal` (single-arg) not `f_equal` on `add_vec` bv-address equalities (over-splits into the wf proof); same for `mword_of_int a = mword_of_int b` — `f_equal` there leaves a goal `lia` then fails on, so `assert (a = b) by lia; rewrite` it instead. Regidx disequality: `intro He; injection He as He2; vm_compute in He2; congruence`.
- **TWO `bv_signed`s WHOSE WIDTH INDICES DIFFER ONLY UP TO CONVERSION ARE DISTINCT ATOMS TO `lia`.** `bv_signed (w : mword (MachineWord.Z_idx (31 - 0 + 1)))` and `bv_signed (w : mword (Z_idx 32))` are the same type up to conversion and print identically, but zify abstracts them as two unrelated atoms, so a hypothesis that IS the goal yields "Cannot find witness". Close it with `exact` (or `change` the width first) — reaching for a stronger arithmetic tactic never helps, because the arithmetic was never the problem. Its sibling: an `(MachineWord.Z_idx a <= MachineWord.Z_idx b)%N` side condition is opaque to `lia` for the same reason; close it with `apply N.leb_le; vm_compute; reflexivity`.
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
- **`set_solver` on a `gset Arch.pa` goal does not terminate** — and this is one of the two traps `iris/FastSetSolver.v`'s override does NOT fix, because the cost is in the GOAL's own instances rather than in the context. Even `{[a]} = {[a]} ∪ ∅` ran >10 min (the address `EqDecision`/`Countable` instances are enormous). Discharge such goals algebraically — `union_empty_r_L`, `dom_union_L`, `dom_singleton_L`, a `_dom` lemma for whatever built the map — and finish with `reflexivity`/`exact`. `set_solver` on a `gset nat` is fine. Same reflex for `decide`-heavy tactics over address sets.
- **`iFrame` never discharges a RUN of separate pure conjuncts `⌜A⌝ ∗ ⌜B⌝ ∗ …`**, and the reflex `iSplitR; [iPureIntro; split_and!; assumption|]` handles only the FIRST — `split_and!` then fails with *"No matching clauses for match"* on the second, because what follows is a `∗`, not a `∧`. An invariant body that opens with N pure conjuncts (DiskInv's `disk_res` has seven) is re-closed with N lines of `iSplitR; [iPureIntro; exact H|]` followed by one `iFrame` for the spatial rest. Related: `split_and!` DOES split `a <= x < b` (it is a conjunction), so a range-discharging tactic must not run after a `split_and!` that already peeled it.
- **Reading a `ghost_map_lookup` against an auth over a UNION** (`ghost_map_auth γ 1 (m1 ∪ m2)`) is `lookup_union_Some_raw`: it yields exactly `m1 !! p = Some v ∨ (m1 !! p = None ∧ m2 !! p = Some v)`. Do not `rewrite lookup_union` and `cbn` — `union_with` leaves a two-way match to case on by hand.
- **`iFrame` does not close a goal `[∗ list] m ∈ [m1; …; mk], P m` over a LITERAL list.** It leaves goals and the closing `}` then fails far away with *"This proof is focused, but cannot be unfocused this way"*. A cons big-op IS a nest of `∗`, so a chain of `iSplitL "Hk"; [iExact "Hk"|].` ending in `done.` works and is fast.
- **`big_sepL_cons` does not elaborate when two `big_sepL`s are in scope** — its `Φ` is left as an evar and ssreflect reports "_pattern_value_ is used in conclusion". You almost never need it: `big_opL` on a cons IS a separating conjunction, so `iDestruct "H" as "[Hh Ht]"` and `iSplitL "Hh"` work directly on `[∗ list] j ∈ (x :: l), …`. Peel the list with `rewrite (seq_cons off rem)` and then destruct. When only ONE hypothesis should be unfolded, scope it: `iEval (rewrite (seq_cons 0 len)) in "Hdst"` — a bare `rewrite` hits every occurrence, including the sibling buffer that a later lemma still needs in `seq 0 len` form.
- **`iApply (big_sepS_subseteq …)` SHELVES its `Affine` side condition, and the failure has no goal attached.** Nothing errors at the `iApply`; the `Qed` reports *"Attempt to save an incomplete proof"* and `Show` says "All the remaining goals are on the shelf". Fix: `Unshelve. intros ?. apply _.` (Found selecting a covered subrange out of a whole-disk big-op in `FsBoot.v`.)
- **A bare `rewrite !big_sepS_sep` in proofmode does not come back**: it rewrites the whole `envs_entails` — hypotheses AND an existentially-quantified conclusion. Scope it (`iEval (rewrite big_sepS_sep) in "H"`, then `iDestruct "H" as "[A B]"`), one split at a time. Same family as the `iEval … in "Hdst"` note above.
- **`++` IN A LEMMA *STATEMENT* PARSES IN `string_scope`** in the usual import set (proofmode's string scope under `Local Open Scope Z_scope`): `disk_read dk o n ++ …` fails with *"has type list (bv 8) while it is expected to have type string"*. Annotate `(… ++ …)%list`. This is the statement-position twin of the recorded local-hypothesis `++` trap.
- **A DOUBLE-QUOTED PHRASE IN A HEADER COMMENT MUST NOT SPAN LINES.** The `*)` ending an intervening line lands inside the string, Coq warns *"Not interpreting `*)` as the end of current non-terminated comment"*, and swallows the rest of the file. (Live example: `FsCrash.v`'s line-260 warning.)
- **`cbn` with NO delta list next to a definition that expands into a 1024-element list is seconds per use.** `fs_blocks` unfolds into a `disk_read` of 1024 bytes and a following `injection` then walks it — measured ~7 s per `cbn` in `FsBoot.v`. Give `cbn` its delta list (`cbn [mbind option_bind]`); `coqc -time` pins it instantly.
- **A `bv 8` VALUE DOES NOT UNIFY WITH AN `mword 8` PARAMETER, though the two are convertible.** `mword` is a `match` on its `Z` index, so `mword ?n =?= bv 8` is not solvable by unification and a `b : bv 8` handed to a lemma expecting `mword ?n` fails with *"has type `bv 8` while it is expected to have type `mword ?n`"*. Image bytes come out of a `gmap Z (bv 8)` and go into width-generic model operations (`zero_extend'`, `nth_byte`), so this hits any proof that reads a byte: write the binder as **`(b : mword 8)`** and the map lookup's result coerces by conversion. (Found proving `strlen`'s `lbu`.)
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
- **A `={E}=∗` LEMMA CANNOT BE `iMod`-ed DIRECTLY ONTO A `WP (Loop) {{Φ}}` GOAL** -- it fails with *"cannot eliminate modality"* on a goal that is visibly a weakest precondition. The idiom that works is **`iApply fupd_wp. iMod (…) as "…". iModIntro.`** (`ProofInitlog.v` lines 665 and 1410 are the precedent). This bites the FIRST caller of any accessor stated as a fancy update -- `FileOff.off_checkout` / `off_checkin` were written long before `fileread` existed, so the seam had never been exercised and the lemma statements looked fine in isolation. **A fancy-update lemma with no caller is an untested lemma**; when you add one, add its call site or at least a two-line consumer.
- **`rget` IS INDEXED BY THE AMBIENT `CpuId`, AND AN EXPLICIT `rget_ne D R pf` DOES NOT SURVIVE A `wp_next` BOUNDARY.** A term produced by a leaf carries the `CID` in force at the `iApply`; an `assert` written *after* the following `iIntros (CIDn …)` elaborates its `rget` at `CIDn`, and the two do not unify -- the error reads *"does not match any subterm"* on a term you can see in the goal, which sends you hunting for an address mismatch that is not there. **Use `rgne` / `iEval (rgne) in "H"` and let unification pick the instance**; reserve explicit `rget_ne` for facts that never cross a boundary. Cost three debug rounds on `ProofFileread.v`. Same family as the "post-resume half must be its OWN lemma with `CID` as a BINDER" rule below.
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
- **`iNext` DESCENDS INTO A PERSISTENT HYPOTHESIS AND STRIPS A LATER THAT IS NOT AT ITS TOP — which BREAKS the hypothesis, because the result is STRONGER and no longer matches the definition by name.** `intr_handler_avail := ∃ h, intr_inv h ∗ ▷ intr_handler_spec h`: after any branch's `iNext`, the context holds `∃ h, intr_inv h ∗ intr_handler_spec h`, and passing it where the DEFINITION is expected fails with *"iSpecialize: cannot instantiate … with (∃ x, intr_inv x ∗ intr_handler_spec x)"* — an error that reads like a resource is missing when in fact you have too much. `MaybeIntoLaterN`'s structural instances go through `∃`, `∗` and `□`, so nothing about persistence or about the later being nested protects it. Two escapes, and pick by whether you own the definition site: (i) **keep an index symbolic** so the `if` guarding the later never reduces — `ProofAcquiresleep` deliberately does not `subst eb`, because with `eb` literal `intr_count`'s `if eb` reduces and `iNext` can then reach inside; (ii) **re-seal at the point of use**, the repair `IntrDefs.intr_restore_intro` exists for:
  ```coq
  iAssert (intr_handler_avail) as "#Havz".
  { iDestruct "Havail" as (hz) "[#Hiz #Hsz]".
    iExists hz. iFrame "Hiz". iNext. iExact "Hsz". }
  ```
  **That inner `iNext` is what makes ONE tactic cover BOTH forms** — it strips the GOAL's later and leaves an already-stripped hypothesis untouched — so you never have to work out which use sites sit behind a branch `iNext` and which do not. A top-level persistent premise has no version of escape (i), so (ii) is the only route there.
- **A STATEMENT MAY SHADOW A SECTION VARIABLE'S NAME; A PROOF MAY NOT — but `rename` frees the name, and that is the difference between a 3-line-per-site sweep and a 500-annotation one.** `wp_next b p (fun (CID : CpuId) => …)` deliberately names its binder `CID` so it shadows the section's `Context `{CID : CpuId}`, and every hart-indexed resource in the body then retargets by instance resolution with no annotation — which is why restating ~150 leaf CONCLUSIONS that way was free. The mirror-image proof step `iIntros (CID Hs …)` fails with **`Error: CID is already used.`** — `intros` will not shadow a section variable. **The fix is `rename CID into CID0.` first**: inside a proof a section variable is an ordinary context entry, so it can be moved aside, after which `iIntros (CID …)` succeeds and the body below is UNCHANGED. Two things make this strictly better than introducing the new hart under a fresh name:
  - **The STATEMENT never sees the rename**, so the implicit-argument name stays `CID` and every caller that writes `(CID := X)` on the lemma keeps working. Renaming the section *variable* would break them — in this tree that was **184 call sites across 14 files**. Check that count before reaching for the other option.
  - Introducing `CIDn` instead forces `(CID := CIDn)` on every hart-indexed term the body writes out (`tp_pin m`, `rget m rs`); here ~200 + ~280 occurrences.
  **`rename` must come AFTER any application of a SIBLING lemma from the same Section**, because such a reference resolves through the section variables BY NAME (they are not generalized until the Section closes) and fails with *"<lemma> depends on the variable CID which is not declared in the context"*. Lemmas from other files are already generalized and take the hart as an instance argument, so they are unaffected. Note the entry hart must stay nameable anyway whenever the proof RELATES the two harts (`rget_next_indep : rget (CID := CIDn) m rs = rget (CID := CID) m rs`), which is what `CID0` is for.
- **WHAT SUCH A SWEEP CANNOT FIX BY PLUMBING: a leaf that FRAMES A PER-HART RESOURCE ACROSS ITS OWN STEP.** Once a step's continuation is rebound to another hart, anything the proof obtained *before* the step is about the wrong hart, and the failure is loud but misleading — `iSpecialize: cannot instantiate (?r ↦ᵣ{?dq} ?v -∗ ⌜register_lookup ?r (sregs σ) = ?v⌝) with (mcounteren ↦ᵣ□ mcen)`, or `iFrame: cannot frame hw_config`, i.e. it reads as a MISSING resource when the real problem is that you have the wrong hart's. Persistence does not help (`↦ᵣ□` is still per-hart). The fix is a design call per leaf, not a tactic: either the leaf is `b = false`-only — and then `assert ((CID : CpuId) = CID0) as -> by exact (Hs (or_introl eq_refl)).` collapses the two harts and the conversion is free — or the resource belongs in the ambient bundle rather than in a caller frame. Budget the sweep as "mechanical part + one decision per leaf that frames anything", and identify the framers up front by grepping for caller-supplied `↦ᵣ` premises and for regime/invariant arguments.
- Section gotchas: a lemma using NO section vars is not generalized over them; `intros ->` on a section-variable equation BREAKS references to sibling section lemmas (state such wrappers outside the section); `Proof using All` generalizes over ALL context vars (callers must then pass them). A section `Variable` (e.g. `root_ppn`) auto-threads intra-file but external callers pass it as the LEADING argument.
- **REASSEMBLING A RECORD AFTER AN `upd_*` FUNCTIONAL UPDATE: `iFrame`/`cbn` CAN HANG EVEN THOUGH EVERY UNCHANGED FIELD IS DEFEQ, AND THE FIX IS NOT MORE REDUCTION.** Closing over `proc_priv γf pa pid (upd_tf V ws')` — `upd_tf` only touches `pv_tf`, so every other projection is DEFINITIONALLY the same as under `V` — looks like it should be one `iFrame` away, but five attempts hung or missed before it worked (`claude-notes/completed/usertrap.md`, "THE TRAPFRAME BORROW" has the full blow-by-blow): a bare `cbn` (no delta list) hangs chasing the unfold through every field's own definition (the existing `cbn`-with-no-delta-list bullet above, but easy to not recognize in THIS shape); a SECOND `rewrite` once the pattern is already exhausted also hangs (an empty search is not a fast search); a correctly TARGETED `cbn [f g h …]` can itself return instantly and the VERY NEXT bare `iFrame` still hangs. The fast, diagnosable move that actually cracks it: **`assert (Heq : proj (upd_tf V ws') = proj V) by reflexivity`, one per projection, then `rewrite` them in by name** — instant, and a genuine mismatch now fails FAST ("LHS does not match any subterm") instead of hanging, which is what actually surfaces the real bug (here: one field, `proc_fields`, takes the WHOLE record as its argument rather than a projection, so no per-projection equality ever reaches it — needs its OWN whole-argument `reflexivity` equality). Even after every equality is proven and rewritten in and the goal is fully reduced, a bare `iFrame` can STILL hang — apparently `iFrame`'s own typeclass-based `Frame` search turns pathological in a section with many ambient typeclass parameters (14+ in the observed case), independent of whether the goal matches. **Final fix: bypass `iFrame` with explicit `iSplitL "…"; [iExact "…" | …]` chains** — purely structural, no typeclass search, and it is what actually terminated. Reach for this — per-projection `reflexivity` assertions, then explicit `iSplitL`/`iExact` — on the FIRST unexplained hang after a record `upd_*`, rather than iterating on `cbn`/`iFrame` variants.

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
- **STATE A HARDWARE-ATTRIBUTE OBLIGATION AS WHAT THE CONSUMER CONSUMES — AND *MEASURE* WHAT THAT IS BEFORE WEAKENING IT.** Two instances, and they came out opposite ways. `RiscvLang.reset_regs`' PMP clause used to pin a 64-entry `pmpcfg_boot`; every consumer (`SpecEntry.wp_entry_boot`, `BootBridge.boot_bridge`) already quantified over the value and took only `pmp_all_off` of it, so the clause became `pmp_all_off (register_lookup pmpcfg_n rs)` and the ripple was three lines. The sibling `mseccfg = 0` pin looks identical — architecturally only PMM and MLPE matter — but the grep says the WHOLE 64-bit value is consumed, by a *proof-engineering* artifact: the fast concrete-state decode bridge's read-frame congruence (`WpDecodeBridge.exec_goodb_congr`) transports a decode from a reference state on the condition that the two states AGREE on every register the program reads, and `goodb` cannot express "reads it but the value cannot matter" — so 1220 per-word decode lemmas rest on the pin. **A read-frame/agreement bridge is whole-value by construction; a field-wise obligation above one is unprovable until the bridge itself changes.** So before restating an over-claiming conjunct field-wise, follow the pin to its LEAF consumers (`grep` the premise, not the register), and if a congruence bridge is one of them, price that out first (measured: running the bridge at a symbolic reference value costs 15× on the `goodb` obligation and does not return at all on the concrete-decode one — a single symbolic leaf inside a `regstate` field function is enough, the open-register-file rule above in miniature). Full account: `claude-notes/completed/crash.md`, "MSECCFG / MENVCFG PATCH SHARPENING".
- **STATE A HARDWARE-ATTRIBUTE OBLIGATION AS WHAT THE CONSUMER CONSUMES, NEVER AS A PINNED ENUM LEVEL.** `RiscvFetchExec.pma_allows_ram` used to pin `PMA_atomic_support = AMOSwap`; the U-mode AMO classifier then *concluded a fault* for a user-mode `amoadd`, i.e. the pinned level leaked into a theorem about the machine and made it FALSE (the real DRAM is AMOCASQ). The conjunct is now `∀ op n, Z.leb n 16 = true → pma_allows_atomic_op … op n = true` — "every AMO the decoder can produce is permitted" — which every consumer instantiates and no consumer can over-read. Two shape rules that came with it: make such a conjunct a `∀` rather than a conjunction (a `∀` survives the `repeat split; assumption` that config-bundle preservation proofs end with), and state the side condition as a **`Z.leb … = true`** so a literal call site discharges it with `eq_refl` (`Hatomic AMOSWAP 4 eq_refl`).
- **WHEN A RESOURCE APPEARS ON BOTH SIDES OF A CONTRACT, A DISJUNCTION IN IT IS NOT A GENERALIZATION — IT IS A LOSS. INDEX THE CHOICE INSTEAD.** Generalizing `copyout` to tables that are not the running process's meant replacing its `p_sz ∗ p_pagetable` premises with "those cells, OR a proof the destination is already mapped". Written as `A ∨ B` that is strictly WEAKER than what it replaced: the resource is returned in the POSTCONDITION too, so a caller who hands in `A` gets back `A ∨ B` and cannot recover its own cells — nothing refutes `B`, because `B` is pure. The old contract then stops being an instance of the "general" one, and you end up inventing a Module Type whose only job is to prove both side by side. The fix is a ghost `arm : bool` and an `if`: `COPYOUT` is `COPYOUT_GEN` at `arm := true`, derived, and no caller moves. The tell that you are about to make this mistake: the disjunction you are adding also has to appear in the post.
- **GENERALIZING A CALLER CAN REQUIRE MAKING A CALLEE'S *FAILURE* ARM INFORMATIVE, and an uninformative failure arm is unrefutable by construction.** `SpecWalkaddr`'s was a bare `a0 = 0`, deliberately contents-free ("four reasons, one answer, and every caller reacts the same way"). But a bare `a0 = 0` is permitted UNCONDITIONALLY, so no amount of knowledge about the map rules the branch out, and the fault path stays alive in the proof even where it is dead in the machine — which is exactly what a caller trying to prove a call unreachable needs. Making the arm report which test failed cost three `destruct` patterns downstream. Before concluding a branch is dead, check that the callee's contract lets you SAY so.
- **A 32-BIT ARGUMENT'S REGISTER PREMISE IS THE ABI'S WORD, NOT THE VALUE'S.** RV64 passes a 32-bit argument SIGN-EXTENDED, `uint` included, so a contract pinning `m a3 = mword_of_int (Z.of_nat off)` silently confines `off` to `[0, 2^31)` — and does so in a way no caller can work around, because no compiled caller ever puts the zero-extended word there. Pin `sign_extend' 64 (mword_of_int (Z.of_nat off) : mword 32)` and export the "below 2^31 it is the plain literal" bridge for callers whose argument is small (`SpecReadi.rd_arg32_small`; readi's four call sites cost one `assert` each). **The widening is usually cheap in the PROOF, and for a reason worth expecting:** the 64-bit `bltu`/`bgeu` a compiler emits for a 32-bit unsigned compare are correct exactly BECAUSE a sign-extended-negative word is above every small bound, so the newly admitted arguments land on an exit the proof already had; and a `*w` instruction truncates its operands, so only the SUM of two arguments ever needs a bound (readi's joint `off + n < 2^32`, used at one instruction). What can move is the POSTCONDITION, if the wrapping arm becomes reachable — check that before starting (readi's `rd_clamp` is already 0 past the file's end, so it did not).
- A `stack_own` (or any) resource bound must be the function's own max depth as a CONSTANT, stated `∀ n, (K ≤ n) → … stack_own sp n` — never a value coupled to the function's arguments.
- **A WRONG WP APPLICATION DOES NOT FAIL, IT HANGS — SO PROFILE BEFORE YOU CHANGE ANYTHING.** Applying a spec whose regfile/parameter you guessed wrong sets the unifier an unsatisfiable problem (`m =?= <[r := v]> m`) and `iSpecialize` never returns; an unbounded `coqc` then teaches you nothing for twenty minutes. The tools that work, together: a hard `timeout 260` on `coqc`, `coqc -time` for per-statement costs, and Rocq's **`Timeout n <tactic>`** combinator to bound ONE step — bisect an `iApply` into `iPoseProof` plus per-hypothesis `iSpecialize` and each run finishes in ~2 minutes naming the exact offender. Get the true baseline by timing the unmodified HEAD version of the same file: the checked-in `.v.timing` files go stale (ProofDirlink's said 130s; the real figure was 48s). Measured instance: three changes made before profiling, two of them real defects that were NOT the cause, and the third became the new bottleneck (100s in a `rewrite upd_ne`, 110s more at its `Qed`). See claude-notes/projects/panic.md, "HOW TO PROFILE ONE OF THESE".
- **A CREDENTIAL THAT APPEARS IN A SPEC FILE IS NOT NECESSARILY IN SCOPE ON THE ARM YOU NEED IT ON.** Picking the cheap call sites for a splice by `grep`ping their specs for the credential is unsound when the spec bundles it behind a CONDITIONAL: `SpecFilewrite` contains both `kernel_data` and `printk_env`, but inside `filewrite_fs_env`, which is the FD_INODE branch — and filewrite's panic arm is the "neither pipe, nor device, nor inode" branch, where the bundle reduces to `emp`. The test is whether the credential is in scope AT THE ARM, which means reading the branch, not counting grep hits. Cost of getting it wrong: a full conversion written and then reverted.
  The same trap with a different shape: **a bundle indexed by an OPTION is `emp` in one mode**, so a credential inside it is unavailable exactly where that mode is taken. `ProofBmap.bm_prk ak γu γd` is `kernel_data ∗ printk_env …` at `ak = Some a` and `emp` at `None` — the NOALLOC mode — so bmap could not source `kernel_data` from the bundle it already carried, and `SpecBmap`'s noalloc body had to gain the premise outright while its two siblings gained only the other half.
- **THE REGFILE A CALLEE'S SPEC WANTS IS THE POST-`jal` ONE.** `wp_jal_s_sconf` hands back `sie_cap_gpr (<[Regidx rd := regval_into_reg (add_vec_int pc 4)]> m) n b p`, so the register file to pass is the one posed before the jump WITH `rd` written — not the posed one. Passing the latter is the hang above. A spec that INFERS its regfile from the capability hypothesis hides this (`PanicStub.panic_wp` did); one that takes it as a parameter exposes it at every call site. Carry any register fact across the write by re-proving it on the post-jal file with `pcw`, stated in the goal's `!!!` form — `rget f r` is a definition and `rewrite` will not match it against `f !!! Regidx (mword_of_int 10)` however convertible, and deriving it with `rewrite upd_ne` instead costs two orders of magnitude more.
- **A STACK-BUDGET CONSTANT IS A `Notation … (only parsing)`, NEVER A `Definition`.** All ~102 of them (`K_*`, `*_stack`, `kv_frame_slots`, `boot_stack_depth`) expand at parse time, so `lia` sees the literal and NO proof has to know which callee dominates a derived budget. Adding one as a `Definition` re-introduces the churn this replaced: raising a constant then breaks every `unfold`/`rewrite /` list that names it, and moving a derived budget's dominating callee (e.g. `fileclose_stack` going `8 + K_iput` → `8 + K_end_op`) breaks them all again. Three traps when adding one: (1) **a `Notation` inside a `Section` does NOT survive its `End`** — declare it above the `Section`; (2) the `: nat` ascription is gone, so **the body needs an explicit `%nat`** or a bare numeral parses in the ambient scope (`Z_scope` in most of these files) and you get a `Z`; (3) `rewrite /X` is ssreflect's unfold and fails as "**The term S is not unfoldable**" once `X` is a numeral — the message names neither the constant nor the file's real problem.
- **A NUMERAL IN A PROOF THAT SILENTLY ENCODES ANOTHER CONSTANT'S VALUE IS THE DOMINANT FAILURE MODE OF ANY BUDGET CHANGE — and it is ungreppable, because the constant's NAME never appears.** Raising the stack budgets to cover `panic()` took six build rounds, and after the first every failure was this: `(50 <= n)` was `K_userinit`, `(60 <= av)` was `K_iput`, `(74 <= K)` was `6 + fileclose_stack`, `(46 + av)` was `kv_frame_slots - 32`, `trap_res true = 78` was `kv_frame_slots`, and two `Lemma … = <literal>` pins (`cr_K_value`, `boot_stack_slots_main`) restated a budget outright. The `Notation` rule above does NOT fix this class. **When you write a numeral into a budget goal, write the constant instead if it is in scope; if pulling in the `Require` is the worse trade, say so in the comment and name what the number is derived from.** Only the build finds these, so expect to iterate rather than to predict.
- **THE PROOFS ARE A BETTER ORACLE FOR BUDGETS THAN THE DISASSEMBLY.** Frames read off the prologue (`addi sp,sp,-N`) are reliable — they match the `K - n` the proofs name. Whole-function DEPTHS are not: `syscall()` dispatches indirectly through `syscalls[]`, so no static `jal` edge exists for any of the 22 `sys_*`, and a call-graph model silently under-reads `K_syscall`/`K_usertrap` by ~250 slots. Compute a ripple as an ABSOLUTE monotone fixpoint seeded at the current spec values, fed by both the constraints the proofs state outright (`(K_f <= K)%nat -> (K_g <= K - n)%nat`) and the static edges — never as a DELTA between two fixpoints of the model added onto the spec values, which does not compose wherever the model's baseline already disagreed.
- **A spec whose function ACQUIRES a lock and then calls a callee that itself acquires must state `Z.of_nat n + 2 < 2^31`, not `+ 1`.** The callee runs at level `S n`, its own premise becomes `n + 2`, and the `+1` form is unobtainable at the call site — `cpu_cells`' own `⌜n < 2^31⌝` at level `S n` gives back only `+1`, and nothing else carries a nesting bound. The gap compiles and surfaces only at the callee application, far from the spec. Precedents: SpecPipeclose, SpecConsoleintr, SpecDevintr, SpecUartintr, SpecVirtioDiskIntr, SpecLogWrite.
  **And `+3` when the callee is reached from INSIDE the function's own critical section.** A panic (or any nested-acquire) arm that fires while the function still holds the lock it took itself runs at `S n` with the held set `{[<that lock>]} ∪ lks`, so it wants `S n + 2`, i.e. the CALLER must state `n + 3`. `SpecIget` is the worked instance (iget panics holding `itable.lock`), and `SpecNamex`/`SpecNamei`'s `namex_root` had to follow because they hand their `n` to iget. Two things move together here and only one is arithmetic: the held set also grows, so the `locks_below` obligation is discharged by `LockRank.locks_below_union_singleton` over `rank(<that lock>) < rank(<the callee's own top lock>)` — which is why `LockRank.v` ranks `itable`(14) and `bcache`(2) below `pr`(16) and says so at the table. **Before adding an arm under a lock, check that edge exists; if it does not, the arm is not dischargeable at all and the ranking, not the proof, is what has to change.**
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
- **AN EXISTENTIALLY-INDEXED PAYLOAD ERASES ITS INDEX AT EVERY RE-SEAL, so two writes that share a unit of SLACK must be crossed by ONE lemma.** A payload that carries `∃ F, ⌜bound F …⌝ ∗ <big-op indexed by F>` is opened at "SOME `F` with the bound" and re-sealed the same way — which is strictly weaker than what the opener knew ("THIS `F`, and the record at `k0` is set"). So a walk that establishes the slack at instruction A and spends it at instruction B cannot seal the payload in between, however natural the intermediate re-park looks: the sealing step is where the fact dies. Cross A and B with one lemma that takes both, and let the walk carry the raw fragment across the instructions between. (`DirLinks.dir_links_dirlink_d` crosses create's `dirlink(dp,…)` at +0x12c and its `dp->nlink++` at +0x134 together; the four-lemma open/deposit/open/seal chain that preceded it could not.) The tell is a re-seal whose next step needs a number the seal just quantified away.
- **STATE A COUNTING INVARIANT AS AN INEQUALITY AND THE MACHINE'S `++` CROSSES IT FOR FREE.** `bv_unsigned (add_vec h 1) <= bv_unsigned h + 1` holds UNCONDITIONALLY at any width — the wrap lands at zero, which is below every bound — so a `<=` invariant over a machine counter needs no range fact and no kernel guard to survive an increment. The corresponding EQUALITY needs the range invariant open at the record, which a walk usually cannot name (fs-sysfile.md's twelfth stop bought exactly that lesson at the price of a region-invariant increment). Ask what the consumer actually needs before choosing: a consumer that reads "at most one" is happy with `<=`.
- Avoid ad-hoc argument couplings in preconditions (e.g. a precondition like `eq_vec (m0!!!a2) zero_reg = Nat.eqb N 0` that ties an argument to a branch condition). Prefer deriving branch conditions internally / a natural contract; if a coupling is genuinely unavoidable, flag it and confirm the form before building it out.

## IMAGE CONSTANTS ARE GENERATED — do not transcribe one by hand

A handful of files need an image constant as a Coq **term** rather than as an
`instr` fact, because a spec unifies on the term: `ProcGeom.mycpu_ret` (the
closed form of `&cpus` that every per-CPU cell address and every
acquire/release/push_off/pop_off/myproc contract is stated in),
`ProofMyproc.mp_A4C`, `WpDecode.w_ld`, `BootChain.entry_got`, and the
hand-written `Code*Aux.v` files. Each used to be a transcribed literal, and
**each went stale on every image bump** — surfacing not at its own definition
but as an unhelpful failure in whatever consumer compiled first (a bare `lia`
"Cannot find witness" inside `BootCarve.v`; `Unable to unify "2147558352" with
"2147558212"` inside `ProcGeom.v`). The diagnosis is nowhere near the defect,
which is what made them expensive.

**The same rule covers a `.rodata` STRING address used in a proof, and there
the transcription is even easier to get wrong because nothing checks it until
a `vm_compute` fails.** Derive it: `site + (auipc_imm << 12) + addi_imm`, then
read the bytes out of `kernel-rocq/KernelData.v` to confirm the string and its
length (the `*_msg_bytes` lemma's `do N (destruct j …)` wants length + 1 for the
NUL). A hand-kept table of panic-message addresses in `claude-notes` had one
entry pointing into the MIDDLE of a different string, and the only symptom was
`congruence failed` inside the bytes lemma.

They are all generated now. **`iris/KernelConsts.v` is produced by
`tools/gen_consts.py` (hooked into `make gen-code`)** from the same dump the
rest of the decode layer comes from; adding one is a row in its `CONSTS`
table, which names the symbol, the offset and the field kind (`word32` /
`imm_i` / `imm_u` / `imm_jal` / `pcrel`, the last being the address an
`auipc`/`addi` pair computes). If you find yourself about to write a hex
literal that came out of `kernel.asm`, add a row instead.

Three constants are NOT routed through the generator, because the dumper
already emits exactly them and a generator would be a second copy:
`RiscvLang.img_end` (the single PT_LOAD's `vaddr + filesz`, from
`KernelData.kernel_segments`), `RiscvLang.rodata_end` (the read-only/writable
boundary, from `KernelData.kernelRodataEnd` — see "A PERSISTENT POINTS-TO AT A
WRITABLE IMAGE BYTE") and `PageGeom.kmem_lo` (the `end` symbol, from
`KernelSyms.end_`).

**Both use `Definition c : Z := ltac:(let x := eval vm_compute in <e> in exact x).`
and that form is load-bearing, not stylistic.** Defining `kmem_lo` as
`KernelSyms.end_` directly compiles, but `unfold kmem_lo` then leaves a
constant `lia` cannot see through, and all six downstream `unfold kmem_lo;
lia` sites break — measured, not hypothetical. Computing the value at
definition time leaves a plain `Z` literal in the body, so every existing
consumer works unchanged. It is the same "compute the result ONCE into its own
Definition" idiom as `ColdBoot.v`'s, used for a different reason.

## A paren-splice bug that DUPLICATES rather than truncates

A rewriter over Coq source that walks outward for an enclosing `(` must handle
"there isn't one".  Python's `rstart`-style scan returns `-1` there, and
`s[:lo] + rep + s[hi:]` with a negative `lo` silently emits the file's tail
TWICE instead of failing.  Eight files came back at ~2x their length with two
copies of their `Module <X>Proof`, and the only visible symptom was a single
odd line at the seam (`End EndOpProof.lkbelow : ...`).

Two habits that catch it immediately:

* after any bulk rewrite, check STRUCTURE, not just syntax -- `grep -c '^Module '`
  per file, and compare line counts against the previous commit.  A file that
  doubled is not a subtle bug.
* make the matcher fail loudly on `-1` instead of indexing with it.

The line-count check is also what distinguishes "my rewriter ate this" from
"someone else's work landed here", which is worth being sure about before
reverting anything.

## `make -k` leaves the stale `.vo` AND skips the dependents silently

When a file fails to compile, its previous `.vo` is not necessarily removed,
and `make -k` then builds nothing downstream of it while reporting only the
one failure.  Counting `*** [X.vo] Error` lines therefore measures "files that
fail to compile", NOT "everything else is verified" -- the layer below a
failure can be sitting on artifacts from before whatever change you are
testing.

The tell is a timestamp comparison, not `ls`: any `.vo` OLDER than a root
dependency you edited (`LockRank.vo`, `CpuOwn.vo`) was built against the old
version and was not rebuilt.

    stat -c "%y %n" LockRank.vo <suspect>.vo

Before trusting a failure count after a semantic change, `rm` the failing
files' `.vo` and the `.vo` of everything that requires them, then rebuild.
The number goes up; that is the real one.

- **Contract ownership across the two lines (from the GR-33 sys_unlink
  collision, 2026-08-16):** the first syscall BOTH lines specified went
  red on main — each line independently made `SpecSysUnlink` "real", in
  incompatible shapes, in the same window (their dispatch arm vs our
  walk's contract), and the merge could keep only one. CONVENTION: a
  syscall's contract is OWNED by whichever line has started its walk
  (a Proof*/Budget file in tree beats a dispatch arm's expectation);
  the other line consumes or stubs, never respecifies. A dispatch arm
  written against a stub must be re-pointed when the real contract
  lands — the arm is one iApply, the walk is a campaign. The open
  cross-line item this leaves: whether the dispatch site can supply
  our fs contracts' disk-fabric resources (gu/gd/gk) at index 18 —
  the shape decision is the user's conversation with the other line,
  with both parameter lists side by side in the GR-33 ledger entry.

- **THE MIRROR-ONLY RULE ERODES ACROSS RELAY HANDOFFS (2026-08-16
  incident, second occurrence of the violation class):** compressed
  relay briefs said "lane tree, -j3" without the EC2 ssh recipe, and
  successive walk/ledger agents drifted onto the local laptop ("-j3 at
  15 GB" in several gate reports WAS the laptop; the mirror is 32
  cores/246GB). RULE: every brief that authorizes a compile must carry
  the full recipe VERBATIM — ssh -i /shared/xv6iris/aws/ags-fk.pem
  ubuntu@<mirror-host>, checkout /shared/xv6iris, scp+md5 as a block,
  build there — and a lane tree is a MIRROR-side object. A gate that
  ran locally is still a sound gate (a green compile is host-independent);
  the rule protects the user's machine, so relocation forward suffices —
  no re-verification owed.

## The adequacy-print baseline (GR-36, 2026-08-16)

`Print Assumptions xv6_power_adequacy_xv6Σ` (SystemAdequacy.v, printed by
every CI build since 85c21e9f) must show EXACTLY these eight, and merge
rounds diff against this list textually, not by count:

1. `LinkNameiRootBoot.NameiRootBoot.wp_namei_root_boot`  (assumed-Link)
2. `LinkForkretPark.ForkretPark.forkret_park`            (assumed-Link)
3. `FunctionalExtensionality.functional_extensionality_dep`
4. `valid_reservation`    (rv64d extern)
5. `plat_term_write`      (rv64d extern)
6. `match_reservation`    (rv64d extern)
7. `load_reservation`     (rv64d extern)
8. `cancel_reservation`   (rv64d extern)

**IT WAS SEVEN UNTIL 2026-08-19, AND THE SWAP IS THE POINT.** What stood at
(1) was `LinkUserinit.Userinit.wp_userinit_sconf` — userinit's WHOLE BODY,
assumed. userinit is now PROVEN (`ProofUserinit.v`, linked in
`LinkUserinit.v`), and the two entries above are what its proof rests on:

- (1) is `namei("/")` at the boot client's premises — the same corner
  `ProofNameiRoot.v` already PROVES, minus the four persistent inode-cache
  rows main cannot produce (`SpecNameiRootBoot.v`'s header is the
  inventory). Retiring it is boot wiring, not proof work.
- (2) is the RUNNABLE park, and it is **not new to the tree** — `kfork` and
  `sys_fork` have carried it all along. It is new to the BOOT cone only
  because the old axiom hid it: `SpecForkretPark.v`'s header said userinit
  "sidesteps the question entirely by being a wholesale Axiom", and it no
  longer does. The paid form (`SpecForkretParkPaid`, PROVED) is not
  available to userinit either: its `forkret_park_pkg` wants the trap
  loop's kernel-side bundle for the new process, which is the same
  "where does a new process's half of the kernel environment come from"
  question kfork owes.

So the count went up by one while the assumed SURFACE went down by a whole
function: prefer that trade, and do not read the count alone.

`LinkPanicStub.PanicAssumed.panic_wp_holds` was an earlier assumed Link and
is gone: `panic()` is proven and every arm links against `SpecPanic`, so the
placeholder was deleted outright (`claude-notes/projects/panic.md`).

A NEW entry = an axiom leaked into the boot cone: stop and investigate.
A MISSING assumed-Link = someone proved it: celebrate, then update this
list in the same commit.  Remember the print's honest scope: cones not
wired into boot (create's, syscall dispatch) do not appear here, so
absence from this list is not absence from the tree.

## Gate grep: match "ROCQ compile", NOT "COQC" (false-green trap)

This tree builds with Rocq 9.0.1, whose build recipe prints `ROCQ compile
<f>.v`, not `COQC <f>.v`.  A gate check like `make -n | grep -c COQC` reads
**0** on a tree that still has hundreds of files to compile — it looks
green when it is not.  Grep case-insensitive `compile` (or `ROCQ compile`)
for the pending-compile check, never `COQC`.  (Caught mid-GR-38, 2026-08-16;
the older durable-notes guidance that said to look for COQC lines is wrong
for this switch.)
