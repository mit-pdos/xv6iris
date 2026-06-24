# Iris weakest-precondition for `add` through the real Sail RISC-V `try_step`

This directory contains a machine-checked Iris weakest-precondition showing that
the xv6/Sail RISC-V model's **actual `try_step`** (one fetch–decode–execute cycle),
run on a register-type instruction `add a2, a0, a1`, behaves as expected:
starting from a booting-Machine-mode state with the instruction in memory at the
PC, one step writes `a0+a1` to `a2` and advances the PC by 4.

## Files

| File | What it is |
|---|---|
| **`RiscvAddTryStep.v`** | The entire development, consolidated into one file: the Iris `language` over the real Sail monad, the program-logic layer (`gen_heap` register/memory points-to + the `regstate`↔points-to bridge), the relational interpreter `run` and its functional twin `exec`, the determinism bridge + reusable `wp_exec_step`, the full reduction of `try_step` (fetch incl. address translation / the PMP loop / PMA / MMIO / multi-byte read, `currentlyEnabled`, `execute`, and the `minstret`/`hart_state`/`tick_pc` wrapper), and the capstone WPs. |
| **`RiscvModelBytes.v`** | A small **iris-free** bitvector/byte-arithmetic prelude (`read_bytes`, `assemble_bytes`, `bv_eq_of_bytes`, `pa_add`, `nth_byte`, …). It is kept separate **on purpose**: it uses vanilla Coq `rewrite … by …`, which `ssreflect` — pulled in transitively by `iris` — forbids. `RiscvAddTryStep.v` imports it. |
| **`KernelBoot.v`** | Imports the real xv6 kernel image (the dumped `Kernel.*` modules) and **proves `wp_kernel_first_two`** — a weakest-precondition for executing the kernel's **first two instructions** (`auipc sp,0xa`; `ld sp,472(sp)`) through the real `try_step`: owning the booting-Machine state with PC at the entry point (and the 8 data bytes the `ld` reads), two `Loop` steps leave PC at entry+8 and `sp` holding the loaded value. The entry address and both encodings are checked against the dump. Built from the proven single-step rules `wp_step_auipc` and `wp_step_ld` (each `wp_exec_step` + `forward_exec_auipc`/`forward_exec_ld`), and `exec_execute_LOAD_8` (the full 8-byte `ld` execute). `Print Assumptions wp_kernel_first_two` = **exactly the 5 model platform axioms**; **zero `Admitted`**. The `should_inc_minstret` `exec`-conditions have been **discharged** — instead of assuming them, the theorem owns the `mcountinhibit`/`minstretcfg` cells and the retired-instruction-counter behaviour `b` is *computed* from them (`exec_should_inc_M`). The surviving hypotheses are the legitimate frontier — the two decode walls (`encdec_backwards` for AUIPC/LOAD), the fetch facts, and the `ld`'s memory/PMA/PMP/MPRV/PMM boot conditions — exactly the kind of hypotheses the proven ADD `wp_add_real_final` carries. |
| **`LoadProof.v`** | The machine-checked 8-byte `ld` data-memory path that `KernelBoot.v` builds on (23 lemmas): the doubleword `read_ram`/`pmaCheck`(readable)/`checked_mem_read`/`mem_read` chain, `translateAddr` for `Load Data`, the `transform_effective_address`/`get_pmlen` address transform, the `vmem_read_addr`/`vmem_read` reduction through the model's **`untilMT` byte-loop** (via `execR_untilMT_1`, an axiom-free `Acc (Zwf 0)` unfolding like `currentlyEnabled`), and the `mword`/`bv` identity lemmas (`zero_extend'_id`, `autocast_id` — `mword n = bv (Z_idx n)`, so these reduce to stdpp `bv` facts). |
| `model-xv6iris/` | The generated Sail RISC-V model (`Riscv.rv64d` / `rv64d_types`), a separate compiled dependency (≈43k generated lines — not inlinable). |
| `kernel-rocq/` | The dumped xv6 kernel image (`Kernel.KernelInstrs` / `KernelData` / `KernelSyms`), produced by `tools/dump_kernel.py`; a separate compiled dependency consumed by `KernelBoot.v`. |
| `archive/` | The original ~35-file modular development this was consolidated from, plus dead-ends (the mock `RiscvIris*`, superseded `ADDwp*`/`WPAdd`, the abandoned `ChooseFree2`/`Step`). Kept for reference; not needed to build. |

## The main results (in `RiscvAddTryStep.v`)

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

```sh
eval $(opam env --switch=/shared/xv6rocq)        # Rocq 9.0.1 + coq-iris 4.4.0 + coq-sail-stdpp 0.20.1
cd /shared/xv6rocq/iris
coqc -R . xv6iris -R /shared/xv6rocq/model-xv6iris Riscv RiscvModelBytes.v
coqc -R . xv6iris -R /shared/xv6rocq/model-xv6iris Riscv RiscvAddTryStep.v
```

(The model in `model-xv6iris/` must already be compiled against the same switch;
see the project root for how it was generated from the Sail sources.)

## Consolidation note

This was assembled from a modular development (now in `archive/`). The merge had
to respect two import-scope subtleties that the per-file structure handled
implicitly, both documented inline near the top of `RiscvAddTryStep.v`:
1. `mstate.mem`'s `Countable Arch.pa` must agree with `RiscvModelBytes`'s
   `read_bytes` (stdpp's `bv_countable`), so `SailStdpp.Base`/`TypeCasts` and the
   model are (re-)imported **after** the `Lang`/`Iris`/`Exec` sections, not at the
   top — and `SailStdpp.Values` is not imported at all (it provides competing
   `Countable`/`read_kind`/`Forall2_length` homonyms).
2. No global `Set Default Proof Using "Type"` — some sections use bare `Proof.`
   and rely on Coq generalizing over the section hypotheses actually used.
