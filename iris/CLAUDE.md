# xv6iris — Rocq/Iris proof development notes

Weakest-precondition proofs for a RISC-V (rv64) xv6 kernel, in Iris. This file
holds durable, forward-looking guidance distilled from past work.

## Build

- Working dir: `/shared/xv6rocq/iris`.
- Single file: `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden <file>.v`
- Full build: `make -f CoqMakefile -j16` (CoqMakefile auto-regenerates from `_CoqProject`; coqdep decides order).
- ALWAYS grep the build log for `Error` — `make …; echo $?` masks make's exit via the echo.
- Never `git add -A` from a parent dir (sweeps sibling untracked trees `coq-sail-stdpp*/`, `lean/`, `rocq/`, `sail-riscv/`); use `git add -A .` from `iris/`.
- Build is **critical-path bound**, not core-bound (~426s path ≈ wall even at -j32). A chain of monolithic 40–74s Iris files dominates; each pays a ~12s `Qed` kernel-typecheck. For iterative re-checking, a `-vos`/`-vok` two-phase build drops the Qed off the critical path (no proof changes) — but interactive tactics still run, so a vos build is still >2min.

## Proof performance rules (apply proactively when writing new proofs)

- **Never `set_solver`** (or `naive_solver`) inside a large Iris WP context — it rescans the whole hypothesis context: **100–190 s per call**. Instead:
  - register-membership `mword_of_int N ∈ [concrete list]`: `ltac:(compute_done)` (context-free, instant).
  - domain `r ∈ dom (<[k:=v]> … M)` from `Hr : r ∈ dom M`: `rewrite !dom_insert_L. repeat apply elem_of_union_r. exact Hr.`
- **Order `repeat (first [ … ])` rewrite loops** so cheap structural rewrites come first and broad whole-goal normalisation (e.g. boolean-identity cleanup) comes LAST — the loop re-tries its first branch after every success, so a broad first branch re-scans the whole goal every iteration. Profile hot branches with `Set Ltac Profiling. … Show Ltac Profile.`.
- **CSR nested-if dispatch** (`read_CSR`/`write_CSR`, ~90 clauses): use the batched peel lemmas from the start — `skip_csr_false_clauses` (writes) / `drive_csr` (reads, WpGprCsrrCommon.v), built on `exec_if_false_g16`/`_g4` (WpLeafCommon.v). Do NOT peel one clause per `erewrite exec_if_false_g` — it's O(tail) retyping per clause and dominates whole files.
- **iApply/iSpecialize cost** in the big Wp files is *structural*: lemma addresses stated as `let a := add_vec … (sign_extend' …) in …` zeta-expand into big trees that every `pm_reduce` traverses. Do NOT retry the "bare-name framing swap" fix (`iEval (rewrite -Hacpu) in "Hcpu"`) — it has been shown to break (let-bound vars ssreflect can't reverse-rewrite). The only real fixes are larger (make addresses opaque `Definition`s; or the `-vos/-vok` split) and are not currently done.

## Code organization

- **Per-instruction WP leaf lemmas** live in `Wp<Mode><Family>.v`, where Mode is `Smode`/`Mmode` by whether the precondition assumes `smode_config`/`Supervisor` vs `mmode_config`, and Family is the decode AST constructor (Itype, Rtype, Btype, Utype, Jal, Jalr, Load, Store, Shiftiop, Addiw, Mul, Csr, Amo, Fence, Sret, Mret). Shared bases: `WpMmodeLeafBase.v` (pure exec/value facts — `gpr_*_val`, `exec_execute_*_gpr`) and `WpSmodeLeafBase.v` (S-mode tactics `mk_base`/`mk_rvc2`/`mk_rvc4` + the generic gpr-write engine). Old `WpGpr*.v` are `Require Export` shims. (M-mode `Csr` is the one aggregator, not a physical merge: its read/write value-helpers appear in leaf post-conditions shared by value with boot code.)
- **Import discipline (critical):** reorg/base files `Require Import` low-level primitives — NEVER `Require Export` them. `Require Export` of Sail/stdpp modules transitively propagates an ssreflect `by` notation that breaks `rewrite … by lia` in far-off files. `Require Import` is non-transitive for the Import part, so importing a base pulls in its own definitions but not its imports' notations. Shims `Require Export` only their OWN reorg definitions.
- `Import Defs` ordering: `Require Import Riscv.rv64d` exposes the *instantiated* `Defs`; `SailStdpp.ConcurrencyInterfaceBuiltins` brings a *functor* `Defs` that shadows it ("Cannot import functor"). Put rv64d (re-)required last before `Import Defs.` so the instantiated one wins.
- Visibility = short-name scope: `Import` is NOT transitive, so a lemma "defined somewhere" is only usable if its file is in the current file's actual import closure. Check the closure, not just that it exists.
- Pure register-generic execute facts (`gpr_*_val` + `exec_execute_*_gpr`) belong in `WpMmodeLeafBase.v` (the shared exec base), NOT in high-level function-proof files — otherwise family files can't reuse them without an import cycle.

## Specific-vs-generic leaf lemmas

- The generic gpr-write **engine** (`wp_gpr_write_s_config*`, in `WpSmodeLeafBase.v`) takes an arbitrary `instr` + an `exec (execute i)` obligation. It is *internal plumbing* — call it only from within family-file specific lemmas, never from a higher-level function proof.
- **Specific per-instruction leaf lemmas** fix the decode family/op in their `instr` precondition and take a pure **map-form value hypothesis** (`<op>(m !!! rs…) = wval`) instead of an `exec` obligation — e.g. `wp_addi_s`, `wp_cli_s`, `wp_sltiu_s`, `wp_add_s`/`wp_sub_s`/`wp_sltu_s`/`wp_cor_s`, `wp_slli_s`, `wp_clui_s`. When wval is exactly the map-form the value hyp is `reflexivity`; otherwise it is the instruction-specific arithmetic (e.g. `sltu_false_zero`). New higher-level proofs should call these, not the engine.

## S-mode config convention

- Kernel WP proofs hold `smode_config γ dq` end-to-end (do NOT `smode_config_unbundle` at entry). Each straight-line leaf has a `_scfg` wrapper that unbundles once internally: extract `mstatus0 mie_v mdv0 menvcfg0` + the config facts, call the raw `wp_X_s (dq:=dq)`, then `smode_config_rebuild`. Non-config side conditions (rd≠0, cmp, align, value hyps) stay explicit wrapper args.
- A `_scfg` wrapper's section MUST have `Context {!sieG Σ}` or you get undefined evars.
- **sstatus reads** (csrrci/csrr on `csr_sstatus`) go through the SIE ghost: `wp_csrrci_sstatus_scfg`/`wp_csrr_sstatus_scfg` yield `∃ ms, ⌜SIE ms = false⌝ ∗ …`; introduce `ms` and re-derive interrupt-off facts from its SIE hyp.
- The **mycpu call** needs raw cells + the SIE ghost half → wrap just that call in an unbundle→raw-call→rebundle island (fine: these posts are existential).
- Raw "engine" layers (`wp_mycpu_words`, `wp_vc_block_s_aux`, the amoswap retry loop) take raw cells and are the intended bottom layer — leave them raw; the `_scfg`/`_config_scfg` wrappers sit above them.

## Recurring technique: recover a concrete register map from a VCgen block

`wp_vc_block_s`'s continuation gives an abstract `mf` + `gpr_matches` facts. To hand back a concrete `gpr_file`: use `agree_off st'.(vregs) mf m0` (2nd conjunct — pins every reg the block didn't write to its pre-block value) together with `gpr_file_ext` (two *total* maps that agree on every `!!!` are equal gmaps, so `gpr_file m1 -∗ gpr_file m2`). Store-only blocks give `mf = m` generically; K-write blocks: prove `mf = <the K-insert chain>` by ~K `decide`-cases (`regval_into_reg` is the identity, so raw block values line up by conversion). Extract `∀ r, r ∈ dom m` at the TOP before the block consumes `gpr_file m`.
