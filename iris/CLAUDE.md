# xv6iris — Rocq/Iris proof development notes

Weakest-precondition proofs for a RISC-V (rv64) xv6 kernel, in Iris. This file
holds durable, forward-looking guidance distilled from past work.

## Maintaining this file

Any project memory worth keeping goes HERE, committed in the repo — not in local
per-session memory files. Record only what is useful for **future** development:
architecture, conventions, gotchas, and techniques that will recur. Do NOT record
narratives of refactorings or code changes that are already finished and no longer
bear on future work — once a change has landed and its lessons are captured as a
forward-looking convention, drop the play-by-play.

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

## Multi-CPU model (ambient hart)

- Multi-hart execution uses an AMBIENT hart: `CPU := fin NCPU`, `Class CpuId := cpu_id : CPU` (RiscvLang.v). `Notation Loop := (LoopE cpu_id)` keeps WP statements spelled exactly as single-CPU.
- Per-file contract: add `Context `{CID : CpuId}.` after every `Context `{!riscvGS Σ}.`, and use the single-hart view `mstate_interp σ` (= `reg_interp σ.(sregs) ∗ gen_heap_interp σ.(mem)`) in leaf lemmas — never the global `state_interp`. The one per-hart framing point is `gregs_interp_acc` inside `wp_exec_step`.
- The older explicit-`cpu` design lives on branch `backup-explicit-cpu`; do not resurrect it.

## U-mode execution theorem (WpUserExec.v)

The end-to-end theorem `wp_user_exec_v1`: from a `user_frame` (config cells + upt_inv + arbitrary GPRs/pc), the machine runs arbitrary user code with continuations only at stvec. Built as: per-shape **arms** (`ustep_*`) → a pure classification `ustep_case` (one disjunct per arm = exactly that arm's pure premise bundle) → `user_step_holds` destructs + dispatches → Löb loop in `wp_user_exec`.

- **Later convention:** the Löb obligation provides continuations under `▷`; every arm's final continuation premise is `▷ (...)` (proof-free for arms whose engine has an internal `iNext`; `ustep_ecall` needed one explicit `iNext`).
- **Adding an arm family is scripted, not hand-written.** Extract the closest proven arm's text from the file and constructor-swap it (e.g. RTYPE→RTYPEW + `rop`→`ropw`; RTYPE→MUL + `mul_op` param). Same for its `ustep_case` disjunct and dispatch case. Scripted swaps of proven text compile first try; hand-built premise bundles don't.
- **Disjunct paren discipline:** a base disjunct's trailing execute-fact text ends with the disjunct's own closing paren — copying it verbatim and appending `)` gives +1 imbalance. Before compiling, split the `ustep_case` body on `\n    \/\n` and balance-check each disjunct's parens; check the destruct intropattern has N−1 `[` and `]` for N disjuncts.
- **Arm placement:** compressed/late arms must sit AFTER the base arms — some (jalr) use helpers (`exec_cE_zicfilp_false_u`) defined mid-file.
- **Pure-classification boundary:** `ustep_case` is a `Prop`; mutable-memory loads/stores (`ustep_ld_data`, `ustep_sd`) take spatial premises and stay standalone theorems by design. `ustep_ld_code` folds in because the code image is immutable.
- Register-generic execute facts follow the `exec_execute_*_gpr` pattern (`exec_rX_bits_gpr`/`exec_wX_bits_gpr` chains; values packaged as `gpr_*_val` in the two-value shape). `execute_RTYPEW` is op-generic — one lemma covers all five W-ops; prefer that shape where the model allows.

## Decode totality and the user-mode instruction set (DecodeTotalU.v / DecodeSetU.v)

- `decode_total_u`: every 32-bit word decodes at the U-mode reference state; `decode_total_u_set` / `decode_total_c_set`: the decode images are the EXPLICIT sets `decodable_u` (54 constructors) / `decodable_c` (44). Machine-discovered, not guessed.
- **Technique** (reuse for any exec-totality/classification goal): reduce to a boolean `goodb`/`goodbP` traversal at the concrete `dstateU`. `goodb D m s = true` alone implies exec success with state unchanged; `exec_goodb_congr` transports to agreeing states. The bind rule with a ∀-quantified continuation makes the traversal LINEAR in decoder size (the abandoned exec-threading peel was per-clause × per-guard: 35min/28GB vs ~10s).
- `goodbP` adds a leaf predicate; classification flows through the clause spine via `goodbP_bind_Q` (head's leaf predicate becomes the continuation's hypothesis). The decoder's LAST clause uses a pure-match tail — needs `goodbP_spine_pure`.
- **vm_compute trap:** never `eval vm_compute in` a term whose value can be stuck (readback of a stuck normal form costs minutes). Decide value-pins by vm-ing only the closed gate (`currentlyEnabled e`); goal-level `vm_compute; reflexivity` is safe even with symbolic bits in dead branches (discarded during evaluation, never read back). `bval` (value-only exec mirror) exists because an exec equation's readback contains the whole normalized register file.
- **Discovery recipe:** run the traversal with an opaque predicate variable; the unsolved leaves are exactly the reachable constructors.
- Config at dstateU: only Zba/Zbb/Zbs/Zicfilp gates are OFF; Zicfiss is ON but `senvcfg.SSE=0` kills SSPUSH/SSPOPCHK/SSRDP at decode (SSAMOSWAP's xSSE check is execute-time, so it IS in the image). Neither decoder emits any FP instruction in this model build.

## Compressed (RVC) layer (UmodeFetchC.v + WpUserExec.v)

- Every retiring compressed instruction executes as `ExecuteAs` of its base expansion (pure `reflexivity` lemmas, UmodeFetchC §5) — so compressed arms reuse the base execute-lemma layer unchanged. Exceptions: C_NOP/C_NTL/ZCMOP retire directly, C_ILLEGAL is directly illegal, C_NOT/C_ZEXT_B compute inline (own `_gpr` facts, §6).
- The RVC dispatch writes `nextPC := pc+2` BEFORE execute, so JAL/JALR link values come out right with no new jump lemmas.
- Two fetch modes, packaged as ONE disjunctive premise (`c_fetch_mode`): 4-aligned pc → Ziccif reads a full 4-BYTE window (code map must cover pa..pa+3; F_RVC is the low half); pc ≡ 2 (mod 4) → single 2-byte fetch (the align check reads Zca). Engines: `wp_instr_c_hit` (ExecuteAs) / `wp_instr_c_hit_direct`; step dispatch via `exec_hart_active_progress_RVC_gen` (SmodeCore, privilege-generic) / `_RVC_direct_gen` (UmodeFetchC).
- For a dual-mode arm with a long tail (the trapish ones): hoist width-independent facts before `destruct Hmode`, copy the two fetch-construction blocks from `wp_instr_c_hit` verbatim, duplicate the tail per branch.

## Kernel-side proof architecture notes

- **swtch / contexts:** `valid_context sc E Φ P c` (WpSwtchVc.v) = c's 14 saved-register cells + wand to WP; config abstracted as one resource `sc` (instantiated at the `smode_config γc dq ∗ SIE-ghost ∗ tlb_inv` bundle). The resumer is EXISTENTIAL with a caller-chosen ▷-guarded predicate `P` (fixpoint) — multi-CPU: never pin a partner.
- **proc locks / wakeup:** `proc_lock_res` owns state@24 + chan@32 (+ `proc_ctx` when parked); `contains_lock` hands the spinlock token through the sleep/wakeup swtch handoff; `procs_inv` = 64 `is_lock`s. Wakeup's content is `proc_lock_res_wakeup` (SLEEPING→RUNNABLE carries the context untouched).
- **Bounded loops: fuel induction, NOT iLöb.** Packaged S-mode leaves strip the step's `▷` internally and never expose a `▷` goal, so an iLöb IH under `▷` can never be applied. `iAssert` a fuel-indexed loop lemma and `iInduction fuel`.
- **Genuine branches: `destruct (eq_vec ..) eqn:` + taken/fall leaves, NOT the split leaf** — the split leaf forces both continuations from disjoint resources; destruct duplicates the full Iris context.
- **Callee-saved pins:** call specs (acquire/release/push_off/pop_off/holding/mycpu) pin s2–s5 (x18–x21) across calls; when a new loop keeps another callee-saved live, extend the pins bottom-up (the `lookup_total_insert_ne` peel pattern; `po_mycpu_out_s*` clones).

## U-mode worklist (state as of the 32-disjunct assembly)

Covered: all integer compute incl. RTYPEW/MUL/ZIMOP, control flow, ECALL, illegal-trap, fetch faults, NOP-likes, width-8 loads/stores, and the compressed layer (every non-memory `decodable_c` constructor except C_EBREAK). Open, roughly in order:
1. MULW/DIV/DIVW/REM/REMW + SHIFTIWOP: one `_gpr` lemma each (fold div-by-zero into the value fn), then the scripted 4-swap (base arm, c-instances where applicable, disjunct, dispatch).
2. C_EBREAK / base EBREAK: trap template = ustep_c_illegal recipe with E_Breakpoint cause (`Hdel_break` hypothesis already in the section).
3. Illegal-in-U instances: SRET/MRET/WFI/SFENCE*/SINVAL*/CSR*/SSAMOSWAP/ZICBOM/ZICBOZ (CSRs need mcounteren/scounteren pinned; cbo needs the MENVCFG_S CBIE/CBCFE/CBZE bits).
4. Width-1/2/4 loads/stores (unlocks the 13 compressed memory ops), then LR/SC/AMO (reservations).
5. F_Base fetch at pc ≡ 2 (mod 4) (32-bit instr at odd halfword: two 2-byte fetches; M-mode template `FetchFBase2` exists); C-enabled JAL/JALR/BTYPE target-alignment lemmas (current ones demand bit-1-clear targets).
6. Hclass discharge: connect `decode_total_u_set`/`decode_total_c_set` to `ustep_case` (per-decoded-instruction execute classification).
