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
