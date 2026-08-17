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

- **M4-S1 — DONE (2026-08-17, `iris/WeakEvExecEff.v` `bbca8853`): THE BRIDGE
  WORKS.**  `epure D m t` (= `exec_eff` with the RAM/MMIO/barrier arms deleted
  and register arms guarded by `r ∈ D`) and
  `ewp_ev_exec_eff_pure : epure D m t = Some (y,t') → ereg_frame c (sregs t) D
  -∗ (ereg_frame c (sregs t') D -∗ EWP (ELoop gen c)) -∗ EWP (ECycle gen c m
  None)` — `▷`-FREE (laters are weakening on the continuation), no
  vm_compute anywhere, applied to a real boot-cone leaf mirror at an
  ARBITRARY register bank in 0.04 s.  B3 is closed.  `epurew` (RAM arms
  against the run's own byte map, emitting the `weff` trace) is proven equal
  to the certificate run; its Iris side is M4-1.  FINDINGS: (i) `Choose` is
  never reached by a certified run (both `exec_eff` and `esil_node` are
  `None` there); (ii) there is NO free device-free detector (every
  `dev_state` answers UART reads), so device-freedom rides in `epure`
  structurally; (iii) **`sig_seip` IS READ BY EVERY INSTRUCTION, ungated by
  `mstatus.MIE`** (`getPendingSet` reads `read_mip` → `sig_meip`/`sig_seip`
  BEFORE the MIE test) — the volatile-register treatment is MANDATORY for
  M4-1; (iv) B1's register list per instruction is recorded in the file
  header (`minstret_increment`/`nextPC` writes before `execute`; `PC`,
  conditionally `minstret` after; tick branch writes `mcycle`/`mtime`/`mip`).
  ORIGINAL BRIEF: — `WeakEvExecEff.v`: `ewp_ev_exec_eff` for
  memory-free, device-free runs (`es = []`, no device node) with the
  register footprint owned by the client (twin of `wwp_instr_conf` /
  `wcert_regonly`); then the OWNED-WINDOW extension (RAM reads/writes at
  bytes the client holds `↦w` for; the barrier arm).  Report the register
  footprint of the boot-cone instructions and whether `sig_seip` is read.
- **M4-1 — FIRST SLICE LANDED (2026-08-17, `iris/WeakEvFunnel.v` +
  `iris/WeakEvWire.v`, `1d9cee32`).**  `erun Dr Dw m t` (the mirror with
  READ and WRITE register footprints split), `ereg_fr c rs Dr q` (dfrac a
  FUNCTION of the register — needed because `try_step` reads `misa`/
  `mseccfg`/`pma_regions`/`htif_tohost_base`/`elp` which `hw_config` holds
  persistently, and `cur_privilege`/`mstatus`/`hart_state` at a fraction:
  `DfracOwn 1` over the footprint is unobtainable, so `WeakEvLift`'s
  `ereg_frame` is the constant-1 instance), `ewp_ev_one_fetch`/
  `ewp_instr_pure` (one `▷`, as `wwp_cb`), the demonstration
  `ewp_lui_leaf_ev` = `WeakLeafUtypeShift.wwp_lui_leaf` restated at the
  event tier (statement delta recorded in the file §6b: the register bundle
  becomes one `ereg_fr`; the decode/pmp/alignment premises are absorbed by
  the run certificate), `wire_inv` + **`ewp_plic`** (the PLIC thread's WP,
  by Löb — an obligation of the WP package that had no rule before) and
  `ewp_instr` with the wires OUT of the owned frame (a wire read needs no
  resource: the certificate branches at the node, `ewrun`).  FINDINGS:
  (1) **THE MIRROR GAP** — the tree's existing whole-instruction `exec_eff`
  certificates do NOT transfer to `erun`/`epure`: `exec_eff` consults
  `dev_read`/`dev_write` at a device access and RECORDS NOTHING, so a
  successful `exec_eff` run cannot witness device-freedom.  The agent's
  estimate for re-mirroring the `try_step` spine at `erun` is ~2 800 lines
  of mechanical script; THE ORCHESTRATOR'S ALTERNATIVE (do this instead):
  make `WeakCert.exec_eff` RECORD device accesses in its trace (two new
  `weff` constructors `WEdevr`/`WEdevw`); the existing certificate library
  never reaches a device arm, so its lemma statements (traces of RAM
  effects only) re-check with the same scripts, and a certificate's trace
  then witnesses device-freedom by inspection — the mirror re-do collapses
  to adding two arms to `weff_apply`/`weff_quiet`/`weff_touches` and their
  lemma families.  (2) B1 dissolves: the `minstret`/clock cells are
  hart-local and go into `Dw`.  (3) `leaf_hide` needs no adapter; the
  `mmode_config` adapter (`hw_config`'s five registers at
  `DfracDiscarded` in `ereg_fr`) is the next packaging item.
  ORIGINAL BRIEF: the funnel twin: `ewp_instr` with `wwp_cb`'s interface (fetch
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
