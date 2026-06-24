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
| **`KernelBoot.v`** | The top: imports the real xv6 kernel image (the dumped `Kernel.*` modules) and **proves `wp_kernel_first_two`** — a WP for executing the kernel's **first two instructions** (`auipc sp,0xa`; `ld sp,472(sp)`) through the real `try_step`. Owning the booting-Machine state with PC at the entry point (and the 8 `ld` data bytes), two `Loop` steps leave PC at entry+8 and `sp` holding the loaded value. Built from `wp_step_auipc` + `wp_step_ld`. `Print Assumptions wp_kernel_first_two` = **exactly the 5 model platform axioms**; **zero `Admitted`**. Two families of `exec`-conditions are **discharged** into initial-state ownership: `should_inc_minstret` (owns `mcountinhibit`/`minstretcfg`; the counter flag is computed) and the MMIO checks (`within_clint`/`within_sig` from the RAM-constrained `↦ₘ` bytes; `within_htif` from an owned `htif_tohost_base ↦ᵣ None`). The surviving hypotheses are the legitimate frontier — the two decode walls (`encdec_backwards`), the fetch facts, and the `ld`'s PMA/PMP/MPRV/PMM/alignment boot conditions. |
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
automatically by `coq_makefile` from `iris/_CoqProject`. See the **root
`README.md` → Build** for the full pipeline (Sail model, xv6 kernel, dumper) and
for regenerating the Sail model.

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
