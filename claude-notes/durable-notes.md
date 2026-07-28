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
- **A FAILING TACTIC IN A WHOLE-FUNCTION WP LOOKS LIKE A HANG.** Rocq prints the entire goal with the error, and a syscall-altitude goal contains `ProcInv.tf_page`'s **4096-conjunct** big-op plus every `iAssert`ed continuation; formatting that takes tens of minutes, so a one-line mistake reads as an infinite loop and every "where did it stall?" reading is wrong. Put **`Set Printing Depth 40.`** at the top of any file that proves over `proc_priv` (ProofSysPipe.v does) — it turns a 40-minute non-answer into a 30-second error message. Corollary: before hunting a "hang", check that the proof is not simply *wrong*.
- **`timeout N coqc` does NOT kill the worker, and `pgrep -x coqc` does NOT find it.** `coqc` runs as `rocqworker --kind=compile`, so an exact-name wait loop returns while the compile is still going (giving truncated logs and phantom "stalls"), and `timeout`'s SIGTERM reaps only its direct child. The orphan then spins at 100% and **holds a worker slot, stalling the next build at a random point** — which is what makes the stall location look non-deterministic. Wait on `pgrep -f "rocqworker --kind=compile"`, or better, have the compile print its own sentinel (`bash -c 'coqc …; echo EXIT=$?'`) and wait for that; and `pkill -f rocqworker` before re-measuring.
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
  `pc_is` is `KernelSyms.<f>` at offset 0 and whose continuation `pc_is` leaves
  the function — the ra-derived return address, or (for one that never returns,
  like the boot path) a `let` bound to ANOTHER `KernelSyms` symbol — is a
  whole-function spec; it counts as proven once
  a `Link*.v` instantiates a functor sealed by its `Module Type`. **So keeping
  a new proof in that shape is what keeps it visible to the report** — nothing
  needs to be registered.
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

- In iris proofmode: `rewrite a b c` uses SPACES not commas (`rewrite H1, H2.` fails); `rewrite lem by tac` does NOT parse (ssreflect clash) — use `rewrite lem; [|tac]` / `rewrite (lem args ltac:(tac))` / `assert … by tac`. iris-FREE files can use `rewrite … by`. Rewrite a proofmode HYP with `iEval (rewrite H) in "Hpc"` — bare `rewrite H` rewrites the WHOLE `envs_entails Δ P` (hyps AND goal) and desyncs them.
- `iDestruct (lem with "…") as %pure` keeps the spatial inputs when the conclusion is pure (relied on by fetch/config lemmas) — a plain `iDestruct` of a pure-conclusion wand CONSUMES its premises. `big_sepM`/`big_sepL` byte extraction needs an EXPLICIT Φ (underscores leave TC evars unresolved).
- Value/frame binders must be `mword 64` (annotate; `add_vec` demands `mword n` and won't unify a `bv 64` binder even though `mword 64 ≡ bv 64`). Same trap for a value introduced from an EXISTENTIAL resource (`iDestruct "HR" as (t) "Hcell"` on a `∃ t : mword 32, a ↦₄ t` invariant body): `t` arrives as `bv 32`, so `sign_extend' 64 t` fails with "has type bv 32 while it is expected to have type mword ?n" — ascribe `(t : mword 32)` at every use (the ascription leaves no mark, so `change`/`set` terms still match the leaf's output). Decode-fact immediates must be the decoder's POSITIVE RESIDUE (−2016 → 2080; the signed literal fails `bv_is_wf`). Model names need `Defs.` qualification (`Defs.bind`/`Defs.read_reg`/`Defs.assert_exp'`; `rv64d_types.Read_plain`) or they resolve to raw Prompt_monad versions that won't unify with `M = Defs.monad`. A `.` immediately before `(*` parses as `.(` projection — leave a space.
- `lia` cannot evaluate `2^n`/`bv_modulus`/`bv_half_modulus` — `assert (… = <literal>) as -> by (vm_compute; reflexivity)` first. In heavy-import WP files (WpSmodeGpr+SmodeCore+program_logic) `bitvector.tactics` sets a zify hook that makes `lia` return "Cannot find witness" on trivial bounds — prefer explicit `Z.le_lt_trans`/`Z.add_le_mono_r`/`Nat2Z.is_nonneg`. The hook arrives TRANSITIVELY (dropping `bitvector.tactics` from your own imports does not help), and what trips it is a goal mentioning `bv_unsigned`: so when a proof needs real arithmetic, factor the arithmetic into a lemma over plain `Z` variables and feed it the `bv_unsigned` values (`ProofMemmove.mm_overlap_arith`), where `lia` works normally. Widths appear as `MachineWord.Z_idx n`, so `change (Z.sub 57 12) with 45` (or `change (bv_modulus 27)` won't match `bv_modulus (Z_idx 27)`) before a rewrite; conversion beats rewrite for closed masks; `and_vec` needs `unfold word_binop, with_word', with_word` before `bv_and_unsigned` matches. Use `apply f_equal` (single-arg) not `f_equal` on `add_vec` bv-address equalities (over-splits into the wf proof); same for `mword_of_int a = mword_of_int b` — `f_equal` there leaves a goal `lia` then fails on, so `assert (a = b) by lia; rewrite` it instead. Regidx disequality: `intro He; injection He as He2; vm_compute in He2; congruence`.
- **`bv_unsigned` silently elaborates at the wrong width over `Arch.pa`.** `pa_add` lands in `Arch.pa`, whose width is an unreduced `Z_idx (if xlen =? 32 then … else …)` match, so an `assert` stated as `bv_unsigned (pa_add p j) = …` gets `bv_unsigned` at THAT width and then fails to `rewrite` in a goal stated at width 64 — the two print identically, so the error reads "Found no subterm matching" on a term you can see in the goal. Ascribe: `bv_unsigned (pa_add p j : mword 64)`.
- **A stored value that itself contains an insert-lookup derails `rewrite upd_ne`/`upd_eq`.** Several leaves write a value computed from the same map (`c.addi4spn`'s `add_vec (m1 !!! Regidx csp_rs1) …`, an slli's `shift_bits_left (m2 !!! Regidx a2_idx) …`), so the NEW map contains `(<[k := v]> f) !!! j` inside itself; ssreflect then matches that occurrence instead of the peel you meant, and you get an unprovable side goal (`Regidx 2 <> Regidx 2`) or a `discriminate` failure ("No primitive equality found"). Two fixes, both worth preferring to a bare peel: pass the value to the leaf as its explicit `wval` (`wp_slli_s_sconf`/`wp_add_s_sconf` take one) so the stored term is closed, or `iEval (rewrite <the lookup fact>) in "Hcg"` BEFORE naming the map with `set`. Pinning the instance (`rewrite (upd_ne _ (Regidx k) (Regidx j))`) also works.
- **`reg_lookup` is not always the faster discharge.** It is one `vm_compute` over the whole tower, which is the right call for a deep whole-function map — but on a small tower under a full `sie_cap_gpr` context it can fail to come back at all (observed: >3 min on `m2 !!! Regidx csp_rs1 = pa_stk sp0 2`, two inserts deep, in ProofMemmove). If a `by reg_lookup` hangs, peel insert by insert instead; `coqc -time` pins it immediately (the log's last sentence is the one before the hang).
- **`big_sepL_cons` does not elaborate when two `big_sepL`s are in scope** — its `Φ` is left as an evar and ssreflect reports "_pattern_value_ is used in conclusion". You almost never need it: `big_opL` on a cons IS a separating conjunction, so `iDestruct "H" as "[Hh Ht]"` and `iSplitL "Hh"` work directly on `[∗ list] j ∈ (x :: l), …`. Peel the list with `rewrite (seq_cons off rem)` and then destruct. When only ONE hypothesis should be unfolded, scope it: `iEval (rewrite (seq_cons 0 len)) in "Hdst"` — a bare `rewrite` hits every occurrence, including the sibling buffer that a later lemma still needs in `seq 0 len` form.
- The Sail model (`Import Defs` / `Riscv.rv64d`) SHADOWS `filter` (a bool list filter) and `not` (bool negation): in model-importing files write `base.filter` for the stdpp map filter and `¬` (never `not`) for Logic negation, or the elaborator demands `bool`. Similarly, do NOT `Require Import SailStdpp.Values` just to name `mword` in a type annotation — it leaks typeclass instances that break unrelated Iris proofs ("Unable to find an instance"); reference it qualified (`SailStdpp.Values.mword`) instead.
- **`repeat split` CLOSES an equality goal whose sides are convertible** (`split` is `constructor 1`, and `eq`'s only constructor is `eq_refl`), so on a `sp_base`-style record of register equalities it silently discharges some conjuncts and every following bullet lands on the WRONG goal — the error surfaces far away as "`H` has type … while it is expected to have type …". It also splits nested `/\`s you meant to keep whole (a `sp_hi m M` conjunct destined for a transport lemma). Use stdpp's **`split_and!`**, which only splits conjunctions, whenever the leaves are equations. (`repeat split` is still fine for a flat conjunction you intend to prove leaf-by-leaf with matching bullets.)
- **Write `bv_unsigned_in_range _ x`, never `bv_unsigned_in_range 64 x`.** The explicit `64` elaborates the width as `64%N`, while everything else in the tree carries `MachineWord.Z_idx 64`. The two print IDENTICALLY, so `remember (bv_unsigned x) as v` silently fails to abstract the hypothesis, and every later `lia` then still sees a `bv_unsigned` and answers "Cannot find witness". The general escape from that hook when the goal is pure `Z` but the context is full of `bv_unsigned`s is **`clear - H1 H2; lia`**.
- **An `Ltac` body cannot reference a hypothesis by literal name.** `Ltac t := subst c; vm_compute in Hc; rewrite Hxx in H.` resolves those names at *definition* time and errors "Hypothesis c was not found". Worse, a `subst`-based variant can silently fail to peel in a large context while passing in a small standalone test, and the symptom surfaces as a confusing `apply` unification error one line later. Write the tactic name-free (`first [ … ; assumption | congruence ]`, `lazymatch goal with H : … |- _ => … end`); `congruence` sees through `Regidx`'s injectivity, so no `injection`/`subst` is needed for a register disequality. But see optimization.md before putting `congruence` in a peel loop.
- Section gotchas: a lemma using NO section vars is not generalized over them; `intros ->` on a section-variable equation BREAKS references to sibling section lemmas (state such wrappers outside the section); `Proof using All` generalizes over ALL context vars (callers must then pass them). A section `Variable` (e.g. `root_ppn`) auto-threads intra-file but external callers pass it as the LEADING argument.

## Reusable recipes (validated; reuse verbatim)

- **WRAPPER RECIPE — generalizing a lemma without churning call sites.** The generic lemma gets the NEW name; the old name becomes a RESTATEMENT `Lemma` with the verbatim original statement, closed by `exact (<generic> <instance> <explicit binders>)`. NEVER make the old name a `Definition`/notation alias — an implicit argument (`dq`, a section variable) becomes positional and every call site churns. This is how the whole S-mode leaf layer went regime-generic (`R : s_regime`) with zero consumer edits.
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
- **A CODE BLOCK gcc EMITTED TWICE IS ONE LEMMA, PARAMETERIZED BY ITS PCs AS LITERALS.** sys_pipe has two copies of "close both files, return −1" and three of "p->ofile[fd] = 0"; each is one section lemma taking the block's `instr` facts and pc-successor equations as premises. Parameterize by the **pcs themselves** (`za zb zc … : Z`, instantiated `(SP + 0xc4) (SP + 0xc8) …`), never by an entry offset `a` with `a + k` arithmetic: an `instr` fact whose address must be *converted* to match (`0xb8 + 2` against `0xba`) makes every `iApply` reduce a `Z_to_bv` over a kernel address. Discharge the pc equations as named `assert`s once, outside the WP goal, and pass the names. Worked example: `ProofSysPipe.sp_close2` / `sp_ofile_null` (`claude-notes/projects/sys-pipe.md`).
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
- **A caller obligation that the caller cannot actually discharge is a design smell — absorb the arm with the contract of the code that handles it.** xv6's `acquire` re-checks `holding(lk)` and panics; a non-holder provably knows nothing about `lk->cpu`, so proving that arm dead would need callers to thread a per-(lock,hart) "I don't hold it" ticket. The right shape is the `panic_wp` convention (SpecPanic.v): `panic` never returns, so a `□`-persistent safety WP for it closes the arm at zero cost to callers, and the spec honestly reads "acquires, or panics".
- Avoid ad-hoc argument couplings in preconditions (e.g. a precondition like `eq_vec (m0!!!a2) zero_reg = Nat.eqb N 0` that ties an argument to a branch condition). Prefer deriving branch conditions internally / a natural contract; if a coupling is genuinely unavoidable, flag it and confirm the form before building it out.
