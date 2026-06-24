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
| `model-xv6iris/` | The generated Sail RISC-V model (`Riscv.rv64d` / `rv64d_types`), a separate compiled dependency (≈43k generated lines — not inlinable). |
| `archive/` | The original ~35-file modular development this was consolidated from, plus dead-ends (the mock `RiscvIris*`, superseded `ADDwp*`/`WPAdd`, the abandoned `ChooseFree2`/`Step`). Kept for reference; not needed to build. |

## The main results (in `RiscvAddTryStep.v`)

- **`wp_add_real_final`** — the capstone weakest-precondition. Owning the
  booting-Machine-mode machine state as points-to (the GPRs `a0`/`a1`/`a2`,
  `PC`/`nextPC`, `minstret`/`minstret_increment`, and the relevant CSRs), one
  `Loop` step of the real `try_step` yields `a2 ↦ a0 + a1` and `PC ↦ pc + 4`.
  Beyond the owned points-to it carries: the **decode equation** (`Hdec_gen` /
  `Hdec_exec_gen` — "the bytes at the PC decode to `add …`"; the model's
  `encdec_backwards` does not reduce, so this is a principled, unavoidable
  assumption); a **conditioned fetch** fact (`Hfetch_gen`/`Hfetch_exec_gen`, of
  the form `PC=pc → cur_priv=Machine → fetch = F_Base w`); a conditioned
  `should_inc_minstret` fact (`Hsi_gen`); and register-index/config facts
  (`Hrs1`/`Hrs2`/`Hrd`, `Hrvfi`, `mstatus0`, `elp0`). The conditioned
  `Hfetch`/`Hsi` are **dischargeable from owned CSR cells** using lemmas already
  in this file (`run_fetch_F_Base` / `run_fetch_F_Base_from_cells` /
  `exec_fetch_done` / `run_pmpcfg_all_off` / `run_pma_match_ram` /
  `run_should_inc_minstret_red`); doing so — the one remaining cosmetic step —
  would leave only the decode wall + reducible geometric facts. Crucially, `Hcycle`,
  `Hstep`, and `Hne` (`Choose`-freeness) are **gone — discharged into proven
  lemmas, not carried**.
- **`wp_add`** — a reusable, generic one-step rule (`wp_exec_step`-style): it
  takes the `run riscv_step` reduction as hypotheses and produces the WP. It is
  the engine `wp_add_real_final` is built on, not itself instruction-specific.

`Print Assumptions wp_add_real_final` reports **only the model's own platform
axioms** — `rv64d.{valid_reservation, plat_term_write, match_reservation,
load_reservation, cancel_reservation}` (the Sail backend's `--dcoq-undef-axioms`
LR/SC-reservation and terminal-I/O hooks). Nothing in this development adds any
axiom: there is **no `Hcycle`, no determinism assumption, no over-strong fetch
hypothesis** — those were all discharged into machine-checked lemmas.

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
