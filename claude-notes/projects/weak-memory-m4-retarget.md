# The M4 RETARGET — porting the weak tier to the event language (worklist)

**Status (2026-08-17): PLANNED from a full survey; spike M4-S1 dispatched.**
Design of record for the language: `design/weak-memory-event-granular.md`;
the WP-package obligation it discharges is the one premise of
`WeakEvCapstone.xv6_ev_weak_robust` besides `main_premises`
(`design/weak-memory-premise-discharge.md`).  The old recipe
`weak-memory-porting.md` is for the instruction-atomic tier and stays as
history.

## What the survey found (2026-08-17; file:line in the survey commit)

The instruction-atomic weak tier is unusually well funnelled:
- `wp_lift_step` is used in ONE file (`WeakExec.v`, 4 sites); `WWP` (`wwp_triv`)
  is never unfolded outside `WeakGhost.v`; no leaf/function proof mentions
  `wprim_step`/`weak_riscv_lang` (three binding points only: `wwp_triv`'s
  argument type, the `Loop` notation, `WeakExec`'s `(Λ := …)`).
- NINE Iris chokepoints; `WeakFunnel.wwp_instr`/`wwp_cb` (C4) alone carries
  48 of the 49 instruction-granular call sites and ~140 leaf lemmas; the
  three straight-line function proofs (`WkStartNew`, `WkTimerinit`,
  `WkMemmoveLoop`, 2 159 lines) are pure CPS chains of `_run` leaves +
  `cobj` — no `wwp_seq`, no Löb — and would RE-CHECK VERBATIM if the leaf
  statements survive.  The σ-altitude resource layer (~11 000 lines:
  `WeakStarted/Store/Word8/Fence/Ctx*/Kpt*/PtPub/ViewMono/ViewRacy/VProp/
  Mem/Bridge`) mentions neither `WWP` nor `Loop` — untouched.
- Five files sit BELOW leaf altitude and must be rewritten: `WkEntryNew`
  (8 inline `wwp_instr`), `WkYieldFrame`, `WkOwnPingPong`, `WkCtxSurface`,
  `WkWalkCapstone` (5 556 lines).  `WeakRacy` (C5) is superseded by
  `ewp_ev_load` (`WkStartedLoad`'s leaves already re-proven in
  `WeakEvStarted`); the walk rule (C6: `WkWalkRule`+`WkStepPeel`+`WeakStale*`)
  DISSOLVES; `WeakCert`/`WeakVarCert` (whole-instruction totality) are
  superseded by per-node reducibility.
- THREE design items, not ports:
  - **B1** `wwp_instr` holds `minstret_inv` (and `clock_inv` on the tick
    branch) ACROSS the whole instruction; at event granularity those
    registers are written by silent nodes mid-instruction.
  - **B2** the register interface differs: curried `↦ᵣ` + `pc_is` +
    `gpr_file m` (leaves) vs `ereg_frame c rs D` + a whole-regstate cursor
    (event rules) — same ghost elements (`reg_pointsto = reg_pointsto_at
    cpu_id`), different packaging; an adapter is owed.
  - **B3** the event tier has NO SYMBOLIC discharge route: the spike's node
    projections were `vm_cast` at ONE concrete post-boot register file, while
    the leaves/functions are generic over `m : regfile`; the reflective
    stepper `esil` is stuck at the first symbolic `RegRead`, and the 17 189
    lines of symbolic `exec_eff` mirrors (`WeakEff*`, `WeakFetch*`,
    `WeakLeafBase4`, …) have no bridge to the cursor world.

## THE DECISION (orchestrator, 2026-08-17): bridge from `exec_eff`, not from the cursor

`WeakCert.exec_eff m t = Some (y, t', es)` is a COMPLETE description of the
monad's run from SC state `t` (regs, memory, device): every `RegRead` is
answered from `t.sregs`, every RAM read from `t.mem`, and `es` lists the
memory effects in order.  The event language runs the same monad node by
node.  So ONE derived rule, proven ONCE by induction on `m`,

    ewp_ev_exec_eff :  exec_eff m t = Some (y, t', es)  →  (resources) -∗
                       EWP (Sail gen c m None)

turns every existing symbolic `exec_eff` certificate into an event-tier
whole-instruction WP with obligations only at the memory events of `es`
(owned window: discharged inside the rule from `↦w`; racy/fetch: the client's
callback), registers via the client's `reg_pointsto`s.  Consequences:
- **B3 dissolves**: no node projection is ever computed at proof time; the
  residual monads are bound variables of the once-proven induction; the
  17 189-line mirror library is CONSUMED, not redone.  (The reflective
  cursor interface of the spike stays for concrete instantiations.)
- **B2 shrinks** to stating the rule over the SAME `↦ᵣ` points-tos the leaves
  hold (a footprint = the registers the run reads or writes; agreement with
  σ comes from ownership), so `wwp_instr`'s twin can keep `wwp_cb`'s
  interface as closely as the per-event contract allows.
- **B1 becomes local**: the rule steps node by node, so at a `RegWrite` of an
  invariant-owned register (`minstret`, the clock cells) the rule may open
  the invariant AT THAT NODE — the whole-instruction hold is not needed.
- **THE ONE GENUINELY NEW SEMANTIC ITEM — VOLATILE REGISTERS.**  `sig_seip`
  is written by the PLIC thread at ANY time, including mid-instruction, and
  every instruction's interrupt check may read it.  A certificate at a fixed
  `t` cannot describe both outcomes.  The rule therefore takes certificates
  for EACH valuation of a declared volatile set (`sig_seip`), reads the live
  value at the node (from the wire's invariant), and continues with the
  matching certificate.  For MIE-off code both certificates agree on
  everything but the seip cell.  Measure how many boot-cone instructions
  read `sig_seip` in the spike.

## Stages

- **M4-S1 (spike, dispatched)** — `WeakEvExecEff.v`: `ewp_ev_exec_eff` for
  memory-free, device-free runs (`es = []`, no device node) with the
  register footprint owned by the client (twin of `wwp_instr_conf` /
  `wcert_regonly`); then the OWNED-WINDOW extension (RAM reads/writes at
  bytes the client holds `↦w` for; the barrier arm).  Report the register
  footprint of the boot-cone instructions and whether `sig_seip` is read.
- **M4-1** the funnel twin: `ewp_instr` with `wwp_cb`'s interface (fetch
  through `ewp_ev_fetch`/`etext_word` from `winstr`'s text resource; the
  minstret/clock cells per B1-local; `mmode_config`), so `WeakLeafM`'s 34
  hoisted leaves and `WeakLeafO`'s 65 wrappers re-check with `WWP Loop`
  re-bound to `EWP (ELoop gen_id cpu_id)`.
- **M4-2** the racy/lock/release rules: `ewp_ev_load` (exists), the fused
  RMW `ewp_ev_rmw` (exists) as `wacq_cb`'s twin, `wrel_cb`'s twin,
  `wwp_spin_loop` (pure Löb, re-checks).
- **M4-3** the five below-altitude files rewritten; the walk cone re-done
  without the stale mirror.
- **M4-4** `WWP := EWP` rebinding, `WeakAdequacy` → `WeakEvAdequacy` as the
  system theorem, the WP package of `xv6_ev_weak_robust` discharged for the
  boot cone (+ the disk thread via `WeakEvDisk` once the driver proof
  lands).
