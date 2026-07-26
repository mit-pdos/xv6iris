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
- Never `git add -A` from a parent dir (sweeps sibling untracked trees `coq-sail-stdpp*/`, `lean/`, `rocq/`, `sail-riscv/`); use `git add -A .` from `iris/`.
- Build is **critical-path bound**, not core-bound (~426s path ≈ wall even at -j32). A chain of monolithic 40–74s Iris files dominates; each pays a ~12s `Qed` kernel-typecheck. For iterative re-checking, a `-vos`/`-vok` two-phase build drops the Qed off the critical path (no proof changes) — but interactive tactics still run, so a vos build is still >2min.
- **opam switch:** everything builds in the project-local switch `/shared/xv6rocq` (Rocq 9.0.1, coq-iris 4.4.0, coq-stdpp/-bitvector 1.12.0, coq-sail-stdpp 0.20.1). `eval $(opam env --switch=/shared/xv6rocq)` is mandatory in any raw `coqc` invocation — a fresh shell defaults to the wrong switch (→ "Cannot find SailStdpp.*"). Rocq ≥9.1 is not an option (coq-sail-stdpp 0.20.1 is capped `< 9.1~`).
- The generated Sail model (`Riscv.rv64d`, defines `try_step`) is NOT an opam package — rebuild from `/shared/xv6rocq/model-xv6iris/` in order `rv64d_types.v → riscv_extras.v → rv64d.v`.
- **Stale `.vo` trap:** compiling a new file against stale sibling `.vo` produces *impossible-looking* arity/alignment/"expected X" errors, and every address `vm_compute`s to an OLD literal after a `kernel-rocq` image regen. Whenever an argument-count or address error looks impossible, check `.v -nt .vo` and `make proofs` to resync first.
- **Fork/parallel discipline:** `make clean-proofs` nukes the shared `.vo` tree and breaks concurrent siblings — a fork must `coqc` only its OWN file, one compile at a time. Never `pkill -f coqc` (the pattern matches the killer's own shell → kills Bash, exit 144; and kills sibling compiles) — use `pkill -x coqc` or kill the `rocqworker` by PID.
- **Profiling:** per-file times via `make TIMED=1` (or `make proofs TIMING=1 JOBS=32` → per-sentence `*.v.timing`, parse `Chars A-B [snip] T secs`, map offset→line); per-command via `coqc -time` (a stall right after a lemma's last tactic = stuck in `Qed`). Optimize the longest Require chain, not `-j`. Delete `*.v.timing` after (don't commit). Measure any `vm_compute`/decode tactic ONE variant per `coqc` process — the 2nd variant in a process wins ~35% from bytecode-cache reuse (fabricates false savings).
  - **`tools/proof_profile.py` does all of this in one pass** and runs in CI on every checkin (`.github/workflows/ci.yml`): the iris build there is `make … TIMED=1 TIMING=1` (`tee`d to a log), and the profiler consumes that log + the `*.v.timing` files + coqdep's `.CoqMakefile.d` + `.vo` mtimes to emit most-expensive statements/files, the weighted critical path (+ other deep chains), and a parallelism-over-time chart. All of it — tables + an inline Unicode block-chart of concurrent compiles — lands in the job's **step summary** and nowhere else (no artifact upload): GitHub sanitizes raw SVG/`<img>`/`data:` out of the summary, so the chart is drawn in text. The tool still writes a higher-res `parallelism.svg` + full `report-full.txt` to its `--out-dir` for local runs. Stdlib-only, `continue-on-error`, so it never fails a green build. Run it locally the same way: `python3 tools/proof_profile.py --build-log <TIMED-log> --iris-dir iris --out-dir /tmp/prof --jobs $(nproc)`.
- **`coqc` offloads `Qed` kernel-checking to an async `rocqworker` subprocess, and `coqc -time` does NOT count that worker's time.** So `-time`'s per-sentence sum can be tiny (e.g. 14 s) while the real `/usr/bin/time` wall is minutes — the gap is the async `Qed`, NOT machine contention. A pathological `Qed` (e.g. a whole-function proof term over a transparent, eagerly-reducible register-map tower) hides this way. To see it: `/usr/bin/time -v coqc …` (wall + RSS), not `-time`. Also: a killed/`pkill`-ed `coqc` can leave orphan/zombie `rocqworker`s (`ps -eo pid,ppid,stat,comm | grep rocqworker`; `Z`/defunct = harmless, a live orphan holds a worker slot and can stall the next build) — reap them before re-measuring, and prefer `pkill -x rocqworker`/kill-by-PID over `pkill -f coqc`.

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
  `pc_is` is `KernelSyms.<f>` at offset 0 and whose continuation `pc_is` is the
  ra-derived return address is a whole-function spec; it counts as proven once
  a `Link*.v` instantiates a functor sealed by its `Module Type`. **So keeping
  a new proof in that shape is what keeps it visible to the report** — nothing
  needs to be registered.
- The whole-function proofs that predate the shape (M-mode boot and the
  assembly: `_entry`, `start`, `timerinit`, `spin`, `swtch`, `kernelvec`,
  `userret`) name their entry pc through a local `Definition`, so they are
  listed in the script's `MANIFEST_PROVEN`, as are the deliberately-assumed
  contracts (`myproc`, `panic`, `kerneltrap`) in `MANIFEST_ASSUMED`. Every
  entry is verified against the tree and a stale one is reported as a manifest
  error rather than silently counted — fix those when they appear.

## Proofmode & bitvector gotchas (recur across files)

- In iris proofmode: `rewrite a b c` uses SPACES not commas (`rewrite H1, H2.` fails); `rewrite lem by tac` does NOT parse (ssreflect clash) — use `rewrite lem; [|tac]` / `rewrite (lem args ltac:(tac))` / `assert … by tac`. iris-FREE files can use `rewrite … by`. Rewrite a proofmode HYP with `iEval (rewrite H) in "Hpc"` — bare `rewrite H` rewrites the WHOLE `envs_entails Δ P` (hyps AND goal) and desyncs them.
- `iDestruct (lem with "…") as %pure` keeps the spatial inputs when the conclusion is pure (relied on by fetch/config lemmas) — a plain `iDestruct` of a pure-conclusion wand CONSUMES its premises. `big_sepM`/`big_sepL` byte extraction needs an EXPLICIT Φ (underscores leave TC evars unresolved).
- Value/frame binders must be `mword 64` (annotate; `add_vec` demands `mword n` and won't unify a `bv 64` binder even though `mword 64 ≡ bv 64`). Same trap for a value introduced from an EXISTENTIAL resource (`iDestruct "HR" as (t) "Hcell"` on a `∃ t : mword 32, a ↦₄ t` invariant body): `t` arrives as `bv 32`, so `sign_extend' 64 t` fails with "has type bv 32 while it is expected to have type mword ?n" — ascribe `(t : mword 32)` at every use (the ascription leaves no mark, so `change`/`set` terms still match the leaf's output). Decode-fact immediates must be the decoder's POSITIVE RESIDUE (−2016 → 2080; the signed literal fails `bv_is_wf`). Model names need `Defs.` qualification (`Defs.bind`/`Defs.read_reg`/`Defs.assert_exp'`; `rv64d_types.Read_plain`) or they resolve to raw Prompt_monad versions that won't unify with `M = Defs.monad`. A `.` immediately before `(*` parses as `.(` projection — leave a space.
- `lia` cannot evaluate `2^n`/`bv_modulus`/`bv_half_modulus` — `assert (… = <literal>) as -> by (vm_compute; reflexivity)` first. In heavy-import WP files (WpSmodeGpr+SmodeCore+program_logic) `bitvector.tactics` sets a zify hook that makes `lia` return "Cannot find witness" on trivial bounds — prefer explicit `Z.le_lt_trans`/`Z.add_le_mono_r`/`Nat2Z.is_nonneg`. Widths appear as `MachineWord.Z_idx n`, so `change (Z.sub 57 12) with 45` (or `change (bv_modulus 27)` won't match `bv_modulus (Z_idx 27)`) before a rewrite; conversion beats rewrite for closed masks; `and_vec` needs `unfold word_binop, with_word', with_word` before `bv_and_unsigned` matches. Use `apply f_equal` (single-arg) not `f_equal` on `add_vec` bv-address equalities (over-splits into the wf proof). Regidx disequality: `intro He; injection He as He2; vm_compute in He2; congruence`.
- The Sail model (`Import Defs` / `Riscv.rv64d`) SHADOWS `filter` (a bool list filter) and `not` (bool negation): in model-importing files write `base.filter` for the stdpp map filter and `¬` (never `not`) for Logic negation, or the elaborator demands `bool`. Similarly, do NOT `Require Import SailStdpp.Values` just to name `mword` in a type annotation — it leaks typeclass instances that break unrelated Iris proofs ("Unable to find an instance"); reference it qualified (`SailStdpp.Values.mword`) instead.
- Section gotchas: a lemma using NO section vars is not generalized over them; `intros ->` on a section-variable equation BREAKS references to sibling section lemmas (state such wrappers outside the section); `Proof using All` generalizes over ALL context vars (callers must then pass them). A section `Variable` (e.g. `root_ppn`) auto-threads intra-file but external callers pass it as the LEADING argument.

## Spec-design preferences (durable)

- **Cleaner specs and abstractions beat avoiding rework** (see the guiding principle at the top of this file). Refactor or rewrite freely to reach a better shape; do NOT keep near-duplicate lemma families, awkward interfaces, or leaky abstractions merely because they already compile. Prefer one parametric lemma over a cross-product of special cases.
- A `stack_own` (or any) resource bound must be the function's own max depth as a CONSTANT, stated `∀ n, (K ≤ n) → … stack_own sp n` — never a value coupled to the function's arguments.
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
  it the driver's obligation. Worked example: `claude-notes/projects/virtio-disk.md`.
- Avoid ad-hoc argument couplings in preconditions (e.g. a precondition like `eq_vec (m0!!!a2) zero_reg = Nat.eqb N 0` that ties an argument to a branch condition). Prefer deriving branch conditions internally / a natural contract; if a coupling is genuinely unavoidable, flag it and confirm the form before building it out.
