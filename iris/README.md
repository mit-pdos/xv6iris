# Iris weakest-precondition for `add` through the real Sail RISC-V `try_step`

This directory contains a machine-checked Iris weakest-precondition showing that
the xv6/Sail RISC-V model's **actual `try_step`** (one fetch–decode–execute cycle),
run on a register-type instruction `add a2, a0, a1`, behaves as expected:
starting from a booting-Machine-mode state with the instruction in memory at the
PC, one step writes `a0+a1` to `a2` and advances the PC by 4.

## Files

The development is split into focused modules (compiled in this dependency
order; `make proofs` computes the order automatically from `_CoqProject`):

| File | What it is |
|---|---|
| **`RiscvModelBytes.v`** | An **iris-free** bitvector/byte-arithmetic prelude (`read_bytes`, `assemble_bytes`, `bv_eq_of_bytes`, `pa_add`, `nth_byte`, …). Kept separate **on purpose**: it uses vanilla Coq `rewrite … by …`, which `ssreflect` (pulled in by `iris`) forbids. |
| **`RiscvLang.v`** | The Iris `language` over the real Sail monad: the machine state `mstate`, the one-program expression `Loop`, `prim_step`, and `riscv_lang`. |
| **`RiscvPtsto.v`** | The program-logic / points-to layer: `riscvGS`, register points-to `↦ᵣ`, the **RAM-constrained** memory points-to `↦ₘ` (bundles `⌜addr_is_ram a⌝` = the byte is outside the CLINT/SIG ranges), the `regstate`↔points-to bridge (`reg_valid`/`reg_update`/`mem_valid`/`mem_ram`), and the `irisGS` state interpretation. |
| **`RiscvExec.v`** | The exec bridges: the relational interpreter `run` and its functional twin `exec`, the determinism bridge (`exec_run_det`/`run_to_exec`), the reusable one-step rule `wp_exec_step`, and the `bind`/`bind0`/leaf reduction lemmas (incl. the `Base`/`TypeCasts` import boundary). |
| **`RiscvExtras.v`** | Additional reduction helpers shared by the `try_step` machinery (boolean-monad combinators, register/exec leaves). |
| **`RiscvTryStep.v`** | The common `try_step` reduction machinery used by every opcode: `fetch` (address translation, the PMP loop, PMA, multi-byte read), `currentlyEnabled` (the `Acc` recursion), the MR / early-return monad, the pending-interrupt keystone, and the `minstret`/`hart_state`/`tick_pc` wrapper — plus the `add` datapath reductions interleaved here. |
| **`RiscvFetchExec.v`** | The functional `exec`-level fetch (`exec_fetch_done`) and the conditioned progress fact `exec_hart_active_done`. |
| **`WpAdd.v`** | The **`add`** opcode WP: `forward_exec_final` + the capstone `wp_add_real_final` (`add a2,a0,a1` through one real `try_step`, exactly the 5 model axioms). |
| **`WpAuipc.v`** | The **`auipc`** opcode WP: `exec_execute_UTYPE_AUIPC`, `forward_exec_auipc`, and the single-step rule `wp_step_auipc`. |
| **`WpLoad.v`** | The **`ld`** opcode WP: the 8-byte data-memory path (the doubleword `read_ram`/`pmaCheck`/`mem_read` chain, `translateAddr` for `Load Data`, the address transform, and `vmem_read` through the model's **`untilMT` byte-loop** via `execR_untilMT_1`), the `mword`/`bv` identity lemmas, `exec_execute_LOAD_8`, `forward_exec_ld`, and `wp_step_ld`. |
| **`WpFetch.v`** | The separation-logic **fetch** lemma `fetch_from_pts`: owning the 4 memory bytes at `fetch_pa pc` (as `↦ₘ`) + `PC ↦ᵣ pc` + the fetch CSRs (with the boot/geometric/PMA/PMP facts) ⊢ `⌜exec (fetch tt) s = Some (F_Base w, s)⌝`, i.e. `fetch` returns exactly those 4 bytes assembled into `w`. The wrapper turns the pure `exec_fetch_done` into an owned-memory statement: the bytes supply fetch's reads (`mem_valid`) **and**, being RAM-constrained, discharge `within_clint`/`within_sig` (`mem_ram`); `within_htif` from an owned `htif_tohost_base ↦ᵣ None`. Also provides `fetch_from_pts_minstret`, the variant concluding at `set_reg s minstret_increment b` (the state where `try_step` actually fetches). **This is now wired into all four WPs**: `wp_step_auipc`/`wp_step_ld`/`wp_add_real_final`/`wp_kernel_first_two` own the instruction's 4 bytes and discharge fetch via it, so none of them carry an abstract fetch hypothesis any more. |
| **`WpDecode.v`** | The separation-logic-free **decode** lemmas `decode_auipc` / `decode_ld`: for the **concrete** kernel encodings `w_auipc = 0xa117` / `w_ld = 0x1d813103`, `cur_privilege = Machine ⊢ exec (ext_decode w) s = Some (<AST>, s)` — i.e. the bytes decode to `UTYPE (…,AUIPC)` / `LOAD (…,false,8)`. The Sail decoder (`encdec_backwards`, ~4000 lines) is **not** `vm_compute`d whole (that's the "decode wall"); instead it is **stepped clause-by-clause** through `exec`: each pure opcode guard `vm_compute`s to a bool (`skip_pure_clause`), and the `currentlyEnabled`-gated `PAUSE`/`LPAD` clauses reduce via the `Acc` recipe (`exec_cE_pause`, and `exec_cE_zicfilp_M` — which needs `cur_privilege = Machine` because `get_xLPE` `throw`s an `internal_error` in the Virtual privileges). Axiom-free. |
| **`KernelBoot.v`** | The top: imports the real xv6 kernel image (the dumped `Kernel.*` modules) and **proves `wp_kernel_first_two`** — a WP for executing the kernel's **first two instructions** (`auipc sp,0xa`; `ld sp,472(sp)`) through the real `try_step`. Owning the booting-Machine state with PC at the entry point (and the 8 `ld` data bytes), two `Loop` steps leave PC at entry+8 and `sp` holding the loaded value. Built from `wp_step_auipc` + `wp_step_ld`. `Print Assumptions wp_kernel_first_two` = **exactly the 5 model platform axioms**; **zero `Admitted`**. **All** `exec`-conditions are now **discharged** into initial-state ownership / concrete computation: `should_inc_minstret` (owns `mcountinhibit`/`minstretcfg`; the counter flag is computed); the MMIO checks (`within_clint`/`within_sig` from the RAM-constrained `↦ₘ` bytes; `within_htif` from an owned `htif_tohost_base ↦ᵣ None`); **`fetch`** (owns the two instructions' 4-byte encodings and discharges via `fetch_from_pts_minstret`); and — **new** — **`decode`** itself: the instruction words are the concrete `w_auipc`/`w_ld`, and the two `ext_decode` side-conditions are discharged by `decode_auipc`/`decode_ld` (the `uint i = 2` / `isRVC = false` facts compute by `vm_compute`). So **the theorem carries no fetch and no decode hypothesis** — the two `encdec_backwards` "decode walls" are gone. The surviving hypotheses are the genuine boot frontier: the boot-CSR config (`mstatus`/`mseccfg`/`elp`) and the per-instruction PMA/PMP/alignment geometric facts at the concrete kernel PCs. **Memory precondition: the whole ELF text image.** Instead of hand-listing the two instruction byte-blocks, the WP now takes a single `kernel_text` predicate — `[∗ list] k ∈ KernelInstrs.kernel_instrs, kinstr_bytes k` — asserting that *every* dumped instruction's little-endian bytes are resident at the fetch-translation of its ELF address (`kinstr_bytes k` owns `ki_width/8` bytes of `ki_enc` at `fetch_pa (mword_of_int (ki_addr k))`). `kernel_text_first_two` extracts the auipc/ld blocks (the first two `kernel_instrs` entries, in the per-opcode WPs' form) and returns a wand to restore the full image (fetch leaves memory unchanged), so `kernel_text` is both consumed and handed back to the continuation. This directly wires the WP to the dumper's image rather than to two ad-hoc points-to facts. |
| `model-xv6iris/` | The generated Sail RISC-V model (`Riscv.rv64d` / `rv64d_types`), a separate compiled dependency (≈43k generated lines — not inlinable). |
| **`VcGen.v`** | The straight-line **VCgen**: deep-embedded symbolic values/heap, the computable symbolic executor `vc_step`/`vc_block`, and the single generic block WP **`wp_vc_block`** (one `vm_compute` + one `iApply` per block instead of one leaf-WP `iApply` per instruction). See the "straight-line VCgen" section below. |
| **`VcGenDemo.v`** | The VCgen applied to a real kernel block: the 4-instruction timerinit prologue, re-derived as `wp_timerinit_prologue_vc` with ordinary `↦₈` pre/posts. |
| **`VcGenS.v`** | The **S-mode** instantiation of the VCgen: the RVC-shape alphabet `vop_s` (c.addi / c.addi4spn / c.sdsp / c.ldsp), the executor `vc_block_s`, and **`wp_vc_block_s`** — the same one-`vm_compute`-per-block lifting over the S-mode leaf WPs (Supervisor config + `tlb_inv` threaded through). |
| **`WpMycpuVc.v`** | `wp_mycpu` **re-proved with the VCgen**: mycpu's 4-instruction prologue and 3-instruction epilogue are each one `wp_vc_block_s`; only the 6 value-computing middle instructions and the `c.ret` keep per-instruction leaves. Statement identical to `WpMycpu.wp_mycpu`. |
| **`WpPopOffVc.v`** | `wp_pop_off` **re-proved with the VCgen**, callee included: pop_off's prologue and (per bnez branch) epilogue are `wp_vc_block_s` applications — the epilogue's symbolic run is `vm_compute`d ONCE and reused in both branches — and the `jal mycpu` call composite is rebuilt on `wp_mycpu_vc`. Statement identical to `WpPopOff.wp_pop_off`; same 5 platform axioms. |
| `kernel-rocq/` | The dumped xv6 kernel image (`Kernel.KernelInstrs` / `KernelData` / `KernelSyms`), produced by `tools/dump_kernel.py`; a separate compiled dependency consumed by `KernelBoot.v`. |
| `archive/` | The original ~35-file modular development this was consolidated from, plus dead-ends (the mock `RiscvIris*`, superseded `ADDwp*`/`WPAdd`, the abandoned `ChooseFree2`/`Step`). Kept for reference; not needed to build. |

## The main results (in `WpAdd.v` and `KernelBoot.v`)

- **`wp_add_real_final`** — the capstone weakest-precondition. Owning the
  booting-Machine-mode machine state as points-to (the GPRs `a0`/`a1`/`a2`,
  `PC`/`nextPC`, `minstret`/`minstret_increment`, and the relevant CSRs), one
  `Loop` step of the real `try_step` yields `a2 ↦ a0 + a1` and `PC ↦ pc + 4`.
  Beyond the owned points-to it carries **three functional hypotheses** plus a
  few register/config facts: the **decode equation** `Hdec_exec_gen` ("the bytes
  at the PC decode to `add …`"; the model's `encdec_backwards` does not reduce,
  so this is a principled, unavoidable assumption); a **conditioned fetch** fact
  `Hfetch_exec_gen` (`PC=pc → cur_priv=Machine → exec-fetch = F_Base w`); a
  conditioned `should_inc_minstret` fact `Hsi_gen`; and the register-index/config
  facts `Hrs1`/`Hrs2`/`Hrd`, `Hrvfi`, `mstatus0`, `elp0`. The earlier *relational*
  twins `Hfetch_gen`/`Hdec_gen` were **removed** — they are derived on the spot
  from the `exec` versions via the determinism bridge `exec_run_det`. `Hcycle`,
  `Hstep`, and `Hne` (`Choose`-freeness) are likewise **gone — discharged into
  proven lemmas, not carried**.

  The conditioned `Hfetch`/`Hsi` are *not* further discharged here, on purpose:
  the standalone fetch reduction `run_fetch_F_Base` / `exec_fetch_done` (kept in
  the file as evidence the hypotheses are sound) needs ~13 facts that, at an
  **abstract** `pc`, are irreducible geometric properties (pc 4-aligned, `pc[0]=0`,
  not-MMIO, not-compressed) — so "discharging" the one bundled fetch hypothesis
  would replace it with ~8 geometric conditions plus more owned cells, i.e. *more*
  surface, not less. Those facts only compute away at a **concrete** `pc` (e.g.
  the kernel entry point); wiring fetch end-to-end there is sensible future work,
  not a cleanup.
- **`wp_exec_step`** — the reusable, proven one-step rule and the actual engine
  `wp_add_real_final` is built on: given `exec riscv_step σ = Some (tt, σ')` for
  the current state, it produces the WP for one `Loop` step. Instruction-agnostic;
  `wp_add_real_final` plugs the `add` reduction into it.

`Print Assumptions wp_add_real_final` reports **exactly five model platform
axioms** — `rv64d.{valid_reservation, plat_term_write, match_reservation,
load_reservation, cancel_reservation}` (the Sail backend's `--dcoq-undef-axioms`
LR/SC-reservation and terminal-I/O hooks). There are **zero metatheory axioms**
(no `proof_irrelevance`/`classic`/`JMeq`/`admit`): no `Hcycle`, no determinism
assumption, no over-strong fetch hypothesis — those were all discharged into
machine-checked lemmas. (`get_config_rvfi`, which appears in the `Hrvfi`
hypothesis, is a plain model *definition* — `fun 'tt => false` — not an axiom.)

What makes this notable: the model's `currentlyEnabled` uses `Acc`
well-founded recursion that segfaults `vm_compute` (the reason this project once
left Rocq for Lean). Here it is reduced **symbolically and axiom-free** through
the relational `run` interpreter — Iris reasons about the step, it never computes
it.

## Building

From the **repository root** (`/shared/xv6rocq`):

```sh
make            # build the model, dump the kernel, and compile all proofs
make proofs     # just the Iris proofs (iris/) + their dependencies
```

`make` runs every Rocq command inside the project-local opam switch
(Rocq 9.0.1 + coq-iris 4.4.0 + coq-sail-stdpp 0.20.1), so you do **not** need to
`eval $(opam env …)` first. Dependency order within `iris/` is computed
automatically by `coq_makefile` from `iris/_CoqProject`, and each Coq sub-make
runs with `-j$(JOBS)` (defaults to `nproc`; override with e.g. `make JOBS=1
proofs` to force serial). A clean `make proofs` takes **~30 s**. See the **root
`README.md` → Build** for the full pipeline (Sail model, xv6 kernel, dumper) and
for regenerating the Sail model.

> **Build-perf note.** `WpLoad.v` once took ~23 min to compile — traced (via
> `coqc -time`) to a single `iApply fupd_mask_intro; [set_solver|]`. The mask
> side-goal is the trivial `∅ ⊆ E`, but `set_solver` runs `set_unfold` over the
> whole context, and `wp_step_ld`'s context holds `Hexec_spc` whose type embeds
> the dependent-width `update_subrange_vec_dec`/`extend_value` term — normalizing
> it cost the 23 min. Discharging the mask with `apply empty_subseteq` (which
> never touches the context) cut that one step from 1383.6 s to 0.03 s. **Never
> use bare `set_solver` for a trivial subset/mask goal when heavy generated Sail
> terms are in scope.**

> **Build-perf note (decode/dispatch walks).** Stepping a concrete instruction
> through one of the model's giant nested-`if` decision trees — the ~4000-clause
> `ext_decode` or the ~90-way `read_CSR`/`write_CSR` CSR-address dispatch — must
> *not* be done with the naive
> `repeat (match goal with |- context[if ?g then _ else _] => replace g with false
> by (vm_compute; reflexivity) end; cbn match)`.
> That idiom is **O(#clauses²)**: each iteration re-scans the whole (huge) goal for
> `context[…]` and then `cbn match`-traverses it. Two cheaper shapes:
> * **Peel at the head, no scan.** `exec_if_false_g : g = false → exec (if g then A
>   else B) s = exec B s` lets `repeat (erewrite exec_if_false_g by (vm_compute;
>   reflexivity))` drop one guard per step with no goal-wide `context` match and no
>   `cbn match`. Used for the `write_CSR`/`read_CSR` walks (`WpGprCsrw`, `drive_csr`
>   in `WpGprCsrrAny`); `WpGprCsrw` 105 s → 82 s.
>   **…and peel in BATCHES.** Ltac profiling (2026-07-02) showed even the head-peel
>   walk dominating its files (68 % of `WpGprCsrwB`): every `erewrite` re-types the
>   O(#clauses) *tail* of the dispatch, so a per-clause walk is still O(n²) in
>   retyping. `exec_if_false_g16`/`_g4` (WpLeafCommon.v, plain-`if` form) and
>   `skip_clause_head16`/`4` (WpDecode.v, decoder `bind`-form) collapse 16/4 clauses
>   per rewrite; the wrappers `skip_csr_false_clauses` / `skip_pure_clauses` try
>   16 → 4 → 1 (a batch whose window covers the TRUE guard just fails its side
>   condition and backtracks). WpGprCsrwB 27 s → 13 s, WpGprCsrwA 22 s → 16 s,
>   WpGprMretWp 13 s → 2 s. (Do NOT try to collapse the guards by conversion with
>   `cbv -[…]` instead: the negative delta form unfolds some Sail definition with a
>   huge normal form and OOMs the machine.)
> * **Collapse a read-free tail in ONE `vm_compute`.** Once the *gated* prefix
>   (`currentlyEnabled` PAUSE/Zicfilp, which read state) is peeled by
>   `decode_pause_prefix`, the rest of a CSR/ITYPE decode is a pure function of the
>   concrete word, so `decode_finish` (vm-compute the decoder term + `change_no_check`
>   splice + closing `vm_compute`) finishes it whole. Replacing the old
>   `csr_prefix … ; csr_body/itype_body …` clause-walk pairs (≈8.5 s each, 24 sites)
>   with `decode_pause_prefix s Hpriv. decode_finish s.` (≈1.8 s each) cut
>   **`WpStart2` 184 s → 87 s, `WpStartChain` 187 s → 140 s**. (`Zicsr` is pure-true
>   in this model, so it survives the `vm_compute`; only the `Zihintpause`/`Zicfilp`/
>   `Zca` gates — which read `misa`/privilege — must be peeled by hand first.)
>   That `decode_pause_prefix s Hpriv. decode_finish s.` pair is packaged as a
>   single tactic **`decode_any s Hpriv`** (WpDecode.v): it decodes *any* 32-bit
>   word in base RV64I + Zicsr — lui/auipc, loads/stores, branches, jal/jalr, the
>   OP-IMM/OP arithmetic family, csrr/csrw/csrrs — in one line with no per-opcode
>   stepping (e.g. `decode_auipc`/`decode_ld` are now one-liners; the 24 CSR/ITYPE
>   decode lemmas in the start chains use it too). The ONE thing it can't do is an
>   instruction sitting behind a *misa-gated* extension clause (M `mul`/`div`, A
>   atomics, C compressed, F/D): their `currentlyEnabled Ext_*` reads `misa`, so
>   `vm_compute` gets stuck on it exactly like `Zicfilp`, and the gate must be
>   peeled by hand with the relevant misa hypothesis first.

> **Build-perf note (extract `iApply`/`iDestruct` of heavy lemmas out of big
> proofs).** In `WpKernelMret`, discharging the per-instruction fetch windows
> *inline* — `iDestruct (kernel_window … ltac:(kwin4) with "Htext") as "#K"` —
> cost **~22 s each** (3 of them ≈ 57 s of the file). The `kernel_window`
> application and its `kwin4` side-condition are trivial in isolation (~0.2 s,
> measured), so the blow-up is entirely the *large surrounding proof context*:
> elaborating/`iDestruct`ing over a goal whose hypotheses embed heavy
> dependent-width Sail terms is super-linear (the same effect as the `set_solver`
> note above). Fix: extract each window into its own tiny lemma proved in an
> empty context (`k60_window`/`w61_window`/`k62_window`, exactly like
> `kernel_mret_window` and KernelBoot's `auipc_get`), then `iDestruct` the
> *already-proved* wand in the big proof. **`WpKernelMret` 73 s → 14 s.**
> Rule of thumb: if an `iApply`/`iDestruct` of a reusable lemma is slow, prove
> it standalone and apply the result, rather than re-elaborating it in context.
>
> (Counter-example worth recording: the `read_CSR`/`write_CSR` head-rewrite trick
> does **not** port to the RVC walk `open_rvc`/`cstep`. `repeat (erewrite
> skip_clause_head …)` over the *compressed* decoder fails to converge — the
> lemma's `c`/`REST` evars let `erewrite` match non-productively — so that walk
> keeps its clause-by-clause `cstep`. Always run a new walk tactic under a
> `timeout`.)

> **Build-perf note (bundle the immutable config into one persistent fact —
> `hw_config`).** Every WP threads a cluster of *configuration-register* points-to
> facts that never change (misa, mseccfg, the counter config, the PMA regions, the
> HTIF base, …) plus their well-formedness side-conditions (`pma_allows_all`,
> `_get_Misa_S`). Carried per-register and *re-listed in every continuation*, this
> bloats every WP statement and feeds the per-step Qed conversion cost. Foundation
> (built, validated): the boot never writes these, so own them **persistently**
> via `r ↦ᵣ□ v` (`RiscvPtsto.v`: `reg_pointsto_persist`, `reg_valid_dq`, the
> `Persistent` instance — mirroring `↦ₘ□`) and bundle them in one persistent
> proposition **`hw_config misa0 mseccfg0 mc mcfg pmar0`** (`RiscvFetchExec.v`),
> which subsumes the `pma_allows_all`/`_get_Misa_S` macros. Because it is
> `Persistent`, a WP that only *reads* config takes `hw_config` in its precondition
> and **need not return it** — config drops out of every continuation entirely.
> (Reads are non-destructive — `iDestruct … as %` keeps the resource — so the only
> reason config was re-listed in continuations was the linear `↦ᵣ`; persistence
> removes it.) `fetch_from_pts_minstret` (the shared fetch helper) is already made
> dfrac-generic so persistent config can flow through it. The mutable config
> (pmpcfg_n, mstatus, mie, elp, pmpaddr, …) genuinely changes and stays linearly
> threaded. ROLLOUT (green-incremental, three phases — a WP that drops config from
> its postcondition forces every caller up to a no-caller "top" to change in the
> same commit, so we stage it):
> * **Phase A** — make the shared *leaf* per-opcode WPs **dfrac-generic** in the
>   config registers (`reg_pointsto X dqc v` + `reg_valid_dq`). Backward-compatible
>   (existing callers unify `dqc := DfracOwn 1`), so the build stays green; this
>   merely lets a leaf also accept *persistent* config.
> * **Phase B** — convert each top-unit (a no-caller top theorem + its exclusive
>   chain WPs) to take `hw_config` and **drop config from its own postcondition**,
>   passing persistent config down to the (dfrac-generic) leaves. Tops have no
>   callers, so each unit is independent and the build returns to green after it.
>   Establish persistence once per top via `reg_pointsto_persist`.
> * **Phase C** — once *all* top-units are converted (so no caller ever needs
>   config back from a leaf), switch each shared leaf to a `hw_config` precondition
>   and **drop config from the leaf postconditions** too. Now config is threaded
>   nowhere and returned nowhere.

> **Build-perf note (never `vm_compute`/`reflexivity` an equality whose RHS is a
> well-founded-recursion term — target-unfold the LHS's dispatch instead).**
> Ltac profiling (2026-07-02) found `is_CSR_accessible csr Machine Acc =
> currentlyEnabled Ext_U`-style asserts costing **~1.7 s each** (`by (vm_compute;
> reflexivity)`, or bare `reflexivity`) — ~35 % of `WpGprCsrrA`/`WpGprCsrrB`.
> `currentlyEnabled`/`hartSupports` are defined as `_rec_currentlyEnabled ext
> (measure ext) (Zwf_guarded _)`: a well-founded fixpoint over an `Acc` proof
> witness, which neither the tactic-level `vm_compute` nor the kernel's
> `Qed`-time conversion check (invoked again by `reflexivity`) reduce cheaply —
> so with an *identical* subterm on both sides of the equality, you pay for
> normalizing that same expensive recursor roughly twice over. But
> `is_CSR_accessible`'s OWN dispatch on the concrete CSR address is a plain
> (non-well-founded) `eq_vec`/`if` chain — so a delta-list `cbv` that unfolds
> only the guard-deciding primitives (`eq_vec`, `get_word`,
> `MachineWord.MachineWord.eqb`, `bool_decide`) — and nothing else, so
> `currentlyEnabled`/`hartSupports`/`and_boolM`/`or_boolM` stay folded and
> untouched — selects the matching clause and lands on a goal that's
> syntactically `RHS = RHS`, closed by a free `reflexivity`. Packaged as
> `csr_dispatch_eq` (WpLeafCommon.v). Measured **~1.7 s → ~0.02 s per call**
> (`WpGprCsrrA` 11.3 s → 7.4 s, `WpGprCsrrB` 12.9 s → 6.9 s). General lesson: a
> positive `cbv delta [...]` whitelist is always safe (nothing outside the list
> can be touched); the WRONG shape to reach for here is a *negative* `cbv
> -[preserve-list]`, which unfolds everything else and can OOM the machine (see
> the batched-peel note above) — and bare `simpl`/`cbn` (no restriction) is
> *not* safe either: it still ends up reducing through the Acc recursor
> (measured no faster than the original `vm_compute`).

> **Build-perf note (never case-split inside a heavy proof context — pre-prove
> the split as a standalone lemma).** Ltac profiling (2026-07-02) showed `reg_ne`
> — the side-condition solver for `tmig`/`irrelevant_register_set` — as the top
> cost of `WpGprLoad`/`WpGprRvc`/`WpGprLogic` (74 %/54 %/45 %): its fallback
> `unfold gpr_of_Z; repeat case_match` runs ~32 `destruct`s, and **each `destruct`
> re-types the entire proof context**, which in a WP proof embeds huge Sail terms
> (one inline `reg_ne` = 6.6 s / 853 destructs). The same 32-way split done in a
> *standalone lemma* (empty context) costs ~1 ms/case. Fix: the recurring shapes
> are pre-proved once in WpGpr.v (`regbeq_nextPC_gpr`, `regbeq_gpr_PC`, `…minstret…`,
> `…minc…`) and `reg_ne` now `apply`s them first, keeping the inline split only as
> a last-resort fallback. `WpGprLoad` 12 s → 5 s, `WpGprMretWp` 13 s → 2 s (with
> the batched peel below). Generally: `destruct`/`case_match` cost is proportional
> to the whole context, so hoist any fixed finite case analysis out of WP proofs.

> **Build-perf note (rebuild a destructed persistent bundle by NAME, never by
> pieces).** Profiled 2026-07-01: rebuilding `mmode_config` for the continuation
> with the piecewise
> `iExists misa0, …, elp0. iFrame "Hmisa Hmseccfg Hpma Hhtif Help %"`
> cost **2.5–8 s per call site** — ~50 % of the compile time of `WpGprCsrw` /
> `WpGprCsrr` / `WpGprRvc1` (≈ 90 s of the whole build). Each named `iFrame` hyp
> triggers a goal-wide search whose match is *up to conversion*, and the `%`
> pure-framing pass retries every pure hypothesis against every pure conjunct —
> all over goals embedding heavy Sail terms (the same super-linear effect as the
> `set_solver` note). Since `hw_config` is `Persistent`, the fix is to keep the
> *undestructed* bundle alive and hand it back whole:
> `iPoseProof "Hhw" as "#Hhwc"; iDestruct "Hhwc" as (…) "(…)"` for the pieces,
> then rebuild with `iFrame "Hhw …"` — one exact-name match, ~0 s. The same
> applies to `iFrame "… %"`: with heavy hypotheses in the Coq context the `%`
> pass costs ~1.3 s per site (it conversion-tests *every* pure hypothesis
> against every pure conjunct), so close the pure tail explicitly instead:
> `iPureIntro. exact (conj HmIE (conj HMPRV HSXL))`. Applied to
> `InstrBytes`, `WpGprCsrw`, `WpGprCsrr`, `WpGprRvc1`, `WpGprLoad`, `WpGprStore`,
> `WpGprJalr`: clean-build wall time 168 s → 128 s (→ ~100 s together with the
> `WpLeafCommon.v` split below).

> **Build-perf note (keep slow files off the leaves' import path —
> `WpLeafCommon.v`).** With 32 cores the clean build is *critical-path bound*
> (wall ≈ the longest `Require` chain, everything else overlaps). The leaves all
> imported `WpEntry.v` (30–40 s) for ~23 tiny helper lemmas
> (`exec_if_false_g`, `exec_jump_to`, `exec_execute_JAL`, the csrr cluster, …),
> which put `infra → WpEntry → WpGpr → leaf` on every leaf's path. Those helpers
> now live in `WpLeafCommon.v` (~2 s); leaves and `WpGpr` import it instead, and
> `WpEntry` re-`Export`s it, so only `WpEntryNew` still waits for `WpEntry`.
> When adding a leaf-shared helper, put it in `WpLeafCommon.v` (or another cheap
> early file), never in a file with expensive proofs. Three more instances of the
> same rule: `decode_auipc`/`decode_ld` moved from `WpDecode.v` (every leaf's
> prefix) to `KernelBoot.v` (their only user); `subrange_id`/
> `exec_ext_data_get_addr_gpr` moved from `WpGprLoad.v` to `WpGpr.v` so
> `WpGprStore` need not wait for `WpGprLoad`; and the two ~25–47 s terminal poles
> `WpGprCsrw.v` / `WpGprCsrr.v` were each split into `*Common.v` + two balanced
> per-CSR-cluster halves `*A.v` ∥ `*B.v` (the original filename remains as a
> `Require Export` shim so importers are unaffected).

To compile a single file by hand:

```sh
eval $(opam env --switch=/shared/xv6rocq)
cd iris
coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel <File>.v
```

## Module-structure note

The files above are organized so each respects two import-scope subtleties (the
same ones that once forced a single-file consolidation):
1. `mstate.mem`'s `Countable Arch.pa` must agree with `RiscvModelBytes`'s
   `read_bytes` (stdpp's `bv_countable`). So the "front" modules
   (`RiscvLang`, `RiscvPtsto`, and the early part of `RiscvExec`) import **neither**
   `SailStdpp.Base`/`TypeCasts` **nor** `SailStdpp.Values`; the modules from
   `RiscvExec`'s `Base`/`TypeCasts` boundary onward import `Base`/`TypeCasts` and
   then **re-import the model** (so the model's `read_kind` shadows `Base`'s).
   `SailStdpp.Values` is never imported (it provides competing
   `Countable`/`read_kind`/`Forall2_length` homonyms).
2. No global `Set Default Proof Using "Type"` — some lemmas use bare `Proof.` and
   rely on Coq generalizing over the section hypotheses actually used.

(`archive/` holds the original ~35-file development this layout descends from.)

## The straight-line VCgen (`VcGen.v` / `VcGenDemo.v`)

An experiment in replacing hand-chained per-instruction WPs with a
**reflective verification-condition generator** for sequential blocks.

**Problem.** A straight-line block is verified today by one
`iApply (wp_<op>_gpr …)` per instruction, manually re-threading
`mmode_config` / `pmpcfg` / `pc_is` / `gpr_file` / points-to through every
step (WpTimerinit / WpStartNew / WpPushOffTop are 20–35 such steps and
1–3 kloc each).  The plumbing is identical per instruction shape; only the
data differ.

**Design (`VcGen.v`).**  A block is described in a small deep-embedded
language and *executed symbolically by computation*:

- `sval` — symbolic 64-bit values: a constant `SC z` or a variable plus
  concrete offset `SX x off`, offsets canonicalized mod 2⁶⁴.  This normal
  form makes address matching *decidable* (syntactic equality), which is
  what lets the executor resolve loads/stores against the footprint.
- `vop` — the instruction alphabet (currently `addi`/`add`/`lui`/`ld`/`sd`,
  covering the RVC forms through the `instr` ExecuteAs indirection).
  Extending it = one constructor + one `vc_step` case + one `wp_vc_block`
  case.
- `vstate` — concrete pc + symbolic register file (`gmap regidx sval`) +
  symbolic word heap (`list (sval * sval)` of 8-byte cells).  **The heap is
  the block's memory footprint**: exactly the `a ↦₈ v` facts (full
  ownership — sequential code) the block needs.
- `vc_step` / `vc_block` — the symbolic executor; for a concrete block it
  runs by `vm_compute`.

The single Iris lemma **`wp_vc_block`** (proved once, by induction over the
program, dispatching to the existing leaf WPs) turns a successful symbolic
run `vc_block st prog = Some st'` into a WP for the whole block: resources
in = the denotation of `st` (via a valuation `ρ : nat → mword 64` for the
symbolic variables), resources out = the denotation of `st'`.  Per-block
cost is therefore: the `instr` decode facts (needed by any approach) + one
`vm_compute` + one `iApply` — no per-instruction Iris reasoning.  The
per-step Iris plumbing was paid once, inside the (Qed-opaque) induction.

**Why it lifts into Iris cleanly.**  `wp_vc_block` is an ordinary `WP Loop`
lemma in the same CSL as everything else: its pre/post are plain `↦ᵣ`/`↦₈`
resources, so a client can extract the footprint from an invariant/lock
before the block and return the updated footprint afterwards — concurrent
reasoning composes before/after the block exactly as with hand-chained
proofs.  Determinism is only assumed *inside* the block (full ownership of
the touched cells for its duration), matching the sequential-code premise.
Aliasing needs no side conditions: distinct heap cells are separately owned
`↦₈` facts, so separation (plus the 8-alignment carried by `word_pointsto`)
already guarantees their disjointness; the executor only ever *matches*
addresses syntactically and fails (returns `None`) on anything it cannot
resolve.

**Demo (`VcGenDemo.v`).**  The 4-instruction timerinit prologue
(`c.addi sp,-16; c.sdsp ra,8(sp); c.sdsp s0,0(sp); c.addi4spn s0,sp,16`) —
a block WpTimerinit steps through by hand — is re-derived as
`wp_timerinit_prologue_vc` with ordinary `↦₈` pre/posts.  The whole
symbolic execution is the one-line `demo_run` (`vm_compute`), which also
computes `s0 = (sp−16)+16 = sp` by canonical offset arithmetic.
`vregs_den_init` bridges the canonical initial symbolic register file
(`vregs_init`: x0 ↦ `SC 0`, xk ↦ `SX k 0`) to an arbitrary complete runtime
`gpr_file m` by choosing `ρ k := m !!! xk`.

**The S-mode VCgen and the pop_off()/mycpu() example
(`VcGenS.v` / `WpMycpuVc.v` / `WpPopOffVc.v`).**  The same design
instantiated for S-mode kernel code: the alphabet `vop_s` mirrors the RVC
shapes the S-mode leaf WPs are stated for (`c.addi`, `c.addi4spn`,
`c.sdsp`, `c.ldsp` — exactly the prologue/epilogue instructions of the
kernel's S-mode functions), and `wp_vc_block_s` threads the S-mode machine
configuration (Supervisor privilege, mstatus/mie/mideleg/menvcfg, the
PMP-TOR-covers-RAM geometry, `tlb_inv root_ppn`) through the induction.
`wp_mycpu_vc` and `wp_pop_off_vc` re-prove `wp_mycpu` and `wp_pop_off`
*verbatim* (same statements, same 5 platform axioms) with every
straight-line stack-frame run as a VCgen block: 7 of mycpu's 14
instructions and 10 of pop_off's own 19-instruction path come from four
`wp_vc_block_s` applications backed by one-line `vm_compute` runs — and
pop_off's epilogue run is computed once and reused in both `bnez`
branches.  Two things the example makes explicit:

- *Mid-proof seams.*  Entering a block from an abstract `gpr_file m`
  mid-chain uses `vregs_den_init_agree` (choose the valuation
  `ρ k := m !!! xk`); exiting converts the denoted post-state back to the
  surrounding proof's spelling with `vregs_den_insert` + a few
  `add_vec_off2`/`bv_eq; vm_compute` value equalities.  That glue is the
  honest cost of dropping a computational block into a hand proof — a
  dozen `assert`s per seam, all mechanical.
- *Division of labor.*  Branch conditions, CSR reads, and 32-bit
  sign-extending arithmetic (`c.lw`/`c.addiw`/`c.sw`) stay on the existing
  per-instruction leaves by design: their values live outside the VCgen's
  symbolic domain (`var + concrete offset`), and the VCgen honestly
  returns `None` rather than approximating.

**4-byte (word) cells and 32-bit tracking.**  The symbolic domain has a
second layer for `lw`/`sw`/`addiw`: `sval32` (32-bit constant, or "low
word of variable x plus offset") and a register shape `S32` denoting a
sign-extended word — so `lw` loads a cell's word into a register, `addiw`
does the arithmetic *in the 32-bit domain* (`vc_step` computes, e.g.,
"low word of a5, minus one" as `SX32 15 (2³²−1)`), and `sw` stores
`sval_trunc32` of any register back into a cell.  Cells live in a second
heap (`vheap4`, one `word4_pointsto` each — the 4-byte `↦₈` analogue,
alignment bundled).  The bv layer behind it is the `trunc32` algebra
(`trunc32_sext`, `trunc32_add`, `trunc32_subrange`, …): truncation
commutes with the model's sign-extensions and sums, which is exactly why
the ADDIW leaf's `sext64 (subrange (x + imm) 31 0)` normalizes into the
symbolic form.  The `wp_clw_s_ram`/`wp_csw_s_ram` wrappers derive the ten
per-address translation/PMP geometry facts of the underlying leaves from
the cell's RAM-ness + alignment, so word cells need no side conditions
either.  In `WpPopOffVc.v` this absorbs three more of pop_off's
instructions: `c.lw a5,120(a0)` is a one-instruction block, and
`c.addiw a5,-1; c.sw a5,120(a0)` is a single block whose `vm_compute` run
carries the decrement symbolically into the stored word.  64-bit offset
arithmetic on `S32` registers is guarded off (`sval_is64`) — the executor
fails rather than approximates.

**Performance: the agreement interface and the kernelvec blocks
(`VcGenS.v` / `WpKernelvecVc.v`).**  Profiling showed the first-cut VCgen
was compile-time-neutral: symbolic runs `vm_compute`d 32-entry
mword-keyed register maps (~2s per run lemma), the seams materialized
`vregs_den ρ vregs_init` (a term bigger than the hand proofs' maps), and
the per-cell `big_sepL_cons` *setoid* rewrites at the heap seams cost
~0.5s each.  Three fixes:

- **`gpr_matches`, the agreement interface** — `wp_vc_block_s` now takes
  an abstract `gpr_file m` plus a pointwise pure fact
  `gpr_matches ρ vr m` relating a *partial* symbolic map (just the
  registers the block touches or observes) to `m`; the continuation gets
  the stepped file abstractly (`∀ mf` + post-agreement).  `gpr_file` is
  never rewritten, seeding a register is a one-line `gpr_matches_ins`,
  and exit facts are `vm_compute`d symbolic-map lookups.  Small maps also
  make the run lemmas ~0.1–0.4s (the old cost was normalizing the
  32-entry map on both sides of the equation).  The old total-map
  denotation interface survives as `wp_vc_block_s_den` (used by
  `wp_mycpu_vc`, whose statement demands an exact concrete output map).
- **`pose`, not `set`, for valuations** — `set (ρ := …)` scans the whole
  (late-proof, huge) goal for occurrences to abstract; two such `set`s
  cost 3.3s each in pop_off.
- **`cbn [big_opL]`, not `rewrite !big_sepL_cons`** — unfolding a literal
  cell list by setoid rewriting pays a Proper-instance search per cons
  (~16s of the 17-cell kernelvec blocks); one structural `cbn` pass is
  free.

Measured effect (per-lemma coqc time, same statements):
`wp_pop_off` 23.4s hand → 17.0s VCgen (+1.3s for all four run lemmas,
was 8.2s); and on the block shape the VCgen is built for — kernelvec's
17-instruction register-save/restore runs (`WpKernelvecVc.v`) — the
VCgen block lemmas cost 4.4s / 5.9s (+ ~2s runs + ~1.5s instr bundles)
against 18.1s / 23.9s for the hand-chained `wp_kv_prologue` /
`wp_kv_epilogue`: **roughly 3× faster**, with the block programs and
footprints as data and the seam glue mechanically generated.

**Future work.**  Byte-width cells for `lb`/`sb` (memset); more `vop`s
(shifts, logic ops, `mv`); an M-mode/S-mode-generic induction to avoid the
duplicated per-mode lemma; porting the M-mode `wp_vc_block` to the
agreement interface; and a footprint-*inference* pre-pass (run the
executor with a fresh-variable-on-miss heap to *emit* the needed cells —
it needs no soundness proof, since its output is re-checked by the
verified `vc_block`).
