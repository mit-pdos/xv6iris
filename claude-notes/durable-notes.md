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

## Proofmode & bitvector gotchas (recur across files)

- In iris proofmode: `rewrite a b c` uses SPACES not commas (`rewrite H1, H2.` fails); `rewrite lem by tac` does NOT parse (ssreflect clash) — use `rewrite lem; [|tac]` / `rewrite (lem args ltac:(tac))` / `assert … by tac`. iris-FREE files can use `rewrite … by`. Rewrite a proofmode HYP with `iEval (rewrite H) in "Hpc"` — bare `rewrite H` rewrites the WHOLE `envs_entails Δ P` (hyps AND goal) and desyncs them.
- `iDestruct (lem with "…") as %pure` keeps the spatial inputs when the conclusion is pure (relied on by fetch/config lemmas) — a plain `iDestruct` of a pure-conclusion wand CONSUMES its premises. `big_sepM`/`big_sepL` byte extraction needs an EXPLICIT Φ (underscores leave TC evars unresolved).
- Value/frame binders must be `mword 64` (annotate; `add_vec` demands `mword n` and won't unify a `bv 64` binder even though `mword 64 ≡ bv 64`). Decode-fact immediates must be the decoder's POSITIVE RESIDUE (−2016 → 2080; the signed literal fails `bv_is_wf`). Model names need `Defs.` qualification (`Defs.bind`/`Defs.read_reg`/`Defs.assert_exp'`; `rv64d_types.Read_plain`) or they resolve to raw Prompt_monad versions that won't unify with `M = Defs.monad`. A `.` immediately before `(*` parses as `.(` projection — leave a space.
- `lia` cannot evaluate `2^n`/`bv_modulus`/`bv_half_modulus` — `assert (… = <literal>) as -> by (vm_compute; reflexivity)` first. In heavy-import WP files (WpSmodeGpr+SmodeCore+program_logic) `bitvector.tactics` sets a zify hook that makes `lia` return "Cannot find witness" on trivial bounds — prefer explicit `Z.le_lt_trans`/`Z.add_le_mono_r`/`Nat2Z.is_nonneg`. Widths appear as `MachineWord.Z_idx n`, so `change (Z.sub 57 12) with 45` (or `change (bv_modulus 27)` won't match `bv_modulus (Z_idx 27)`) before a rewrite; conversion beats rewrite for closed masks; `and_vec` needs `unfold word_binop, with_word', with_word` before `bv_and_unsigned` matches. Use `apply f_equal` (single-arg) not `f_equal` on `add_vec` bv-address equalities (over-splits into the wf proof). Regidx disequality: `intro He; injection He as He2; vm_compute in He2; congruence`.
- Section gotchas: a lemma using NO section vars is not generalized over them; `intros ->` on a section-variable equation BREAKS references to sibling section lemmas (state such wrappers outside the section); `Proof using All` generalizes over ALL context vars (callers must then pass them). A section `Variable` (e.g. `root_ppn`) auto-threads intra-file but external callers pass it as the LEADING argument.

## Spec-design preferences (durable)

- **Cleaner specs and abstractions beat avoiding rework** (see the guiding principle at the top of this file). Refactor or rewrite freely to reach a better shape; do NOT keep near-duplicate lemma families, awkward interfaces, or leaky abstractions merely because they already compile. Prefer one parametric lemma over a cross-product of special cases.
- A `stack_own` (or any) resource bound must be the function's own max depth as a CONSTANT, stated `∀ n, (K ≤ n) → … stack_own sp n` — never a value coupled to the function's arguments.
- Avoid ad-hoc argument couplings in preconditions (e.g. a precondition like `eq_vec (m0!!!a2) zero_reg = Nat.eqb N 0` that ties an argument to a branch condition). Prefer deriving branch conditions internally / a natural contract; if a coupling is genuinely unavoidable, flag it and confirm the form before building it out.
