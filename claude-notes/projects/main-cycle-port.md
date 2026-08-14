# main-cycle-port — worklist

Design: [`design/main-cycle-port.md`](../design/main-cycle-port.md) — read it
first; the settled decisions (per-node semantics, batching as a theorem, the
self-enforcing batch boundaries, the tick-family shape) live there, not here.

## What exists (pointers, not status)

- `iris/RiscvLang.v` — `HartE gen cpu m`; `LoopE` a Definition; `mnode_step`
  (hart-local, on `mstate`) + `hart_node_step` (focus/step/write-back);
  the fused-AMO window (`silent1`/`silent_run`/`wr_node`, `ak_excl`); per-arm
  `prim_step` inversion; `prim_step_hart_regs_frame` (the batching licence:
  plic's `sig_seip` wire is the only cross-thread register write).
- `iris/HartBlock.v` — the solo-block bracket, sound direction
  (`mblock` ⇒ `run`); closed against `exec` by `RiscvExec.hart_block_exec`.
- `iris/RiscvExec.v` — `wp_dead` + device rules re-derived; `wp_hart_step`
  (the per-node framing point) + `wp_hart_restart` (the ∀-tick boundary).
- `iris/HartLift.v` — the reflective silent stepper (`hsil_node` /
  `hrun_silent` / cursor `hcur` / projections + inversions), `hreg_frame`,
  and the batched rule `wp_hart_batch` (equation-free, F8 form).
- `iris/HartEvents.v` — per-memory-event rules (RAM read/write, MMIO
  read/write), fupd σ-callback currency.
- `iris/HartAmo.v` — the fused-AMO rule `wp_hart_amo` (∃-`w` inside the
  fupd; window data a function of `w`) + the pure window layer.
- `iris/HartRegNode.v` — single-node RegRead/RegWrite fupd rules (the escape
  hatch for invariant-held cells and the wire).

## Left

1. **The pinned-text fetch rule** (spike F7): derive from
   `wp_hart_ram_read` + `↦ₓ□` facts (`text_valid` per byte → `read_bytes`
   via `read_bytes_ne`/`read_bytes_spec`/`bv_eq_of_bytes`).  Shape it
   against the pilot's real fetch plumbing (`instr`/`fetch_from_pts_*`),
   not speculatively.
2. **The certification adapter + pilot** (Phase B's gate):
   - port `WeakEvStarted` §5a's measurement scaffolding: the footprint
     collector (`erun_any`/`erun_regs` → computed `D : gset register`), the
     cursor compositions, the `vm_cast_no_check` per-site facts;
   - ONE pilot leaf + ONE small whole-function proof re-established at
     parity; per-lemma `coqc -time` vs the originals (target ≤ ~1.2×).
   - The tick is a certification FAMILY uniform in `(w, tick)` — design doc
     §5's 5b; only reach for `hsil`-commutes-with-`bind` if measurement says.
3. **Phase B′ — reconnect the tree** (971 files behind `MinstretInv.v`):
   rebuild `wp_exec_step` / `_clock` / `_minstret` / `_hart_active(_inv)` /
   `_decode_execute_inv` and `InstrBytes.wp_instr` on the adapter, statements
   intact — the footprint argument lives at `wp_instr`, the first altitude
   where the caller's ownership of the read set is known.  The clock/minstret
   absorption rebuilds on `HartRegNode`'s single-node rules.
4. **Phase C — the leaf sweep**, spec-identical; whole-function proofs must
   re-check unedited (a failure is a finding, not a patch).
5. **Phase D — adequacy + capstones** (`RiscvAdequacy`/`SystemAdequacy`
   mention `LoopE` by name — the Definition keeps statements elaborating;
   proofs that invert `prim_step` need the new inversion lemmas);
   `proof_coverage.py` parity; `Print Assumptions` unchanged.
6. **The §4 audit items**, resolved and recorded: (a) invariants opened
   across a whole instruction to LINK two accesses — candidates: the
   page-walker's read-then-A/D-update (`CommonWalk`) and the
   interrupt-absorbing step engines (`sr_absorb` family); (b) mid-cycle
   interrupt delivery — the model's check reads `sig_seip`/mip at its own
   node, `WpIntrCore`/`WpIntrInv` already ∀-quantify those off σ.

The tree is RED from `MinstretInv.v` up (971 files) until item 3 lands —
this is by design (design doc §6); iterate with single-file `coqc` /
`make -f CoqMakefile <one>.vo` chains, not full builds.
