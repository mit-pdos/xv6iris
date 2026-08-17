# The one-machine soundness capstone — worklist (Phase B: the instance; Phase C: M5 device views)

**Status (2026-08-17): PLAN OF RECORD, user-approved; work starting.**
Supersedes the open tail of
[`weak-memory-fabric.md`](weak-memory-fabric.md) (G6b) — read that file's
G5c2/G6 findings first; nothing there is retried here.

## The theorem this effort closes

```
(1) event-language adequacy  ──►  φ at every reachable σ        DONE  WeakEvAdequacy.weak_ev_adequacy_phi
(2) φ  ──►  epf_violation_free_hart  (over epf_run)               DONE  WeakEvAdequacy.weak_ev_pf_violation_free
(3) Layer 1: robust_main  (over wp_pf_run pstep pcls, any instance) DONE  WeakRobustMain.robust_main
(4) full promising machine ⊇ hardware                             NOTE  WeakCompose §6(5) (PARM containment)
```
MISSING: (2)→(3), i.e. `epf_step` as a Layer-1 INSTANCE in the ⇒
direction (every `wp_pf_run` of the instance is an `epf_run`, because
`pf_violation_free_hart` quantifies over ALL pf runs).  G5c2 named three
over-approximation points; after G6a the remaining ones are the `pcls`
arity (mechanical), the PLIC hart index (trivial) and THE DISK'S DMA READ.

## Two findings that fix the plan (2026-08-17, orchestrator analysis)

- **`ev_dma_harmless` (G6a2's fallback packaging) is FALSE for xv6.**  With
  an existential DMA memory the pf disk agent may take `WDiskStepDma`
  against a fictional `mv` in which `avail_idx ≠ v_seen` and the descriptor
  chain points anywhere, so whenever the queue is live it writes disk
  data/status bytes to ARBITRARY addresses (and `WDiskStepWild` writes
  arbitrary bytes under a fictional stall).  Such configurations are not
  reachable by the flat-faithful machine, and garbage in a page table
  steers a foreign hart's loads onto another hart's owned-unpublished bytes
  — a real hart violation.  So neither a reachability-inclusion premise nor
  "violation-freedom of the over-approximating machine" is honest.  There
  is NO cheap packaging of the disk arm.
- **The flat DMA read is a HARDWARE-FIDELITY gap, not proof plumbing.**
  `edisk_burst` reads `wflat img log` — the device can never see stale
  ring memory — which is STRONGER than hardware (design Decision 6: a
  missing I/O fence before `QUEUE_NOTIFY` lets real DMA read the ring
  stale).  The only honest theorem covering the disk makes the DMA read a
  VIEW-BASED read: M5 ("disk DMA gets a view"), already the design of
  record.  A "latest-as-of-T" Layer-1 label was considered and rejected:
  it forces from-read edges into the replay graph, the device-epoch rank
  does not survive them, and the exact-value form is refuted by xv6's
  `avail->idx` (a second hart bumps it after the burst reads it, unordered
  in the graph — harmless for the device, fatal for a value-exact replay).

## Phase B — the hart-side instance (unblocked; subagent work)

- **B1 — DONE (2026-08-17).**  `pcls : P → wlabel → wstate → wm_class`,
  pinned at the FULFILLING agent's pre-step `pa_st`: `PFStore`/`PFRmw` now
  read `k = pcls (pa_st ag) l (pa_ws ag)`.  Threaded through Bridge →
  Robust → Trace → Sim → Cone/Blocks/Graph → Main → Retag, and the archive
  is instantiated at the program-blind wrapper `WeakSailLTS2.lbl_class_p`
  (`lbl_class_p _ l ws := lbl_class l ws`), so the archive's coverage
  restriction `wrun_plainw` is untouched.  `cls_canonical` /`pcls_obl` gained
  the argument (`pcls_obl` quantifies it per fixed `p`).  Three places where
  the argument was NOT merely carried, all recorded in the commit message:
  `WeakSailLTS`'s ⇒-bracket premise `Hpcls` became `∀ p, …`;
  `WeakSailComplete.wp_pf_step_inv`'s re-take clause gained
  `pcls (pa_st agd) l (pa_ws agd) = pcls (pa_st ag) l (pa_ws ag)` (the
  register-file twin `cfg_eqv` changes the program state); and the reverse
  bridge's `exec_cls_ok` is now indexed by the initial program list `ps`.
  Print Assumptions on the six capstones byte-identical; `lemma_diff` clean.
- **B2** `WeakEvPf`: `pexv6.PHart` gains the CPU; `pstep_ev`/`pcls_ev`/
  `pdev_ev` over `D := dev_state`; `pcls_ev` reads the access kind off the
  `MemWrite` node (`wm_class_of (classify ak) ws`), `WCexcl` at `LRmw`,
  `WCplain` for the disk.  Disk burst arm = the archived existential-memory
  form FOR NOW (Phase C replaces it).
- **B3.1** DONE (2026-08-17) the LANGUAGE-SIDE factorization
  (`WeakEvInst`): `ecycle_step_factor`, `eplic_step_factor`,
  `euart_step_factor`, `edisk_step_factor` — all ↔, all arms.
- **B3.2** DONE (2026-08-17, `WeakEvCapstone` §§0–6) the INSTANCE:
  * ⇒ `wp_pf_step_epf_step` : `ethread_live σ (ep_gen P) → wp_pf_step
    pstep_ev pcls_ev i l (ecfg_of P σ) c' → ∃ P' σ', epf_step i l (P,σ)
    (P',σ') ∧ ecfg_of P' σ' = c'` — EVERY arm, no exception (M5 removed the
    disk-burst one), plus the run level `wp_pf_rtc_epf_rtc`.
  * ⇐ `epf_run_wp_pf_run` / `epf_rtc_wp_pf_rtc` : `epf_run ρ ρ' →
    wp_pf_run pstep_ev pcls_ev (ecfg_of ρ) (ecfg_of ρ')`, and the step form
    `epf_step_wp_pf_step` with an EXISTENTIAL label.  **FINDING (recorded,
    not a gap): the per-label ⇐ is FALSE, and that is a property of
    `WeakEvPf.epf_step`, not of the instance** — its label is only
    constrained by `elabel_ok`, which under-determines it.  Witness:
    `fence.i`, whose language arm re-inserts the hart's `wstate` unchanged,
    so `elabel_ok σ c LSilent σ'` holds there while the program half emits
    the inert `LFence false false false false`.  Every consumer of
    `epf_step` quantifies the label existentially (`epf_run`,
    `epf_violation_free_hart`, `epf_step_erased`), so the run-level form is
    the exact statement and nothing needs the other.
  * the uniform shape of a pf step (`pf_ok`/`pf_log`/`pf_ws`/`pf_cfg` +
    `wp_pf_step_intro`/`wp_pf_step_inv`), which is what collapses "six pf
    arms × two agent kinds" to one shape — and which IS `WeakEvInst`'s
    memory half at the projection (`pf_ok_hart`/`pf_log_hart`/`pf_ws_hart`,
    `pf_ok_disk`/`pf_log_disk`/`pf_ws_disk`).
  * the layout (`eags_lookup_inv`, `eags_upd_hart`, `eags_upd_disk`,
    `eags_eq`, `ecfg_of_hart_upd`, `ecfg_of_disk_upd`, `ecfg_of_dev`,
    `ecfg_of_reg`, `ecfg_of_hset`).
  * the initial configuration: `eps_init σ` and `ecfg_of_init : wglog σ = []
    → (∀ c, wgws σ c = ws_init) → ecfg_of (ep_init gen) σ = wp_init
    (img_z (wgimg σ)) (wgdev σ) (eps_init σ)`.
  * the Layer-1 side conditions: `pstep_ev_lat_free_prog`,
    `pstep_ev_ts_oblivious`, `pcls_ev_obl`, `WeakEvInst.pdev_ev_ok`; and the
    transport `epf_pf_violation_free : epf_violation_free_hart (ep_init gen,
    σ) → pf_violation_free_hart cls_of pub_of n_disk pstep_ev pcls_ev …`.
- **B4** DONE (2026-08-17) **THE ONE-MACHINE CAPSTONE**
  `WeakEvCapstone.xv6_ev_weak_robust`, verbatim:

  ```coq
  Theorem xv6_ev_weak_robust Σ `{!riscvGpreS Σ, !weakGpreS Σ}
      (gen : nat) (σ0 : wgstate) (D : CPU -> gset register)
      (c : wpcfg pexv6 dev_state)
      (Hgen : gen = 0%nat)
      (Hpow : wgpow σ0 = true) (Hgen0 : wggen σ0 = 0%nat)
      (Hlog : wglog σ0 = [])
      (Hws : forall cc : CPU, wgws σ0 cc = ws_init) :
    (forall (HR : riscvGS Σ) (HW : weakGS Σ),
       ⊢ ([∗ set] cc ∈ (fin_to_set CPU : gset CPU),
            [∗ set] r ∈ D cc,
              reg_pointsto_at cc r (DfracOwn 1)
                (register_lookup r (wgregs σ0 cc))) ∗
         ([∗ map] a ↦ b ∈ wgimg σ0,
            wlat_pointsto (pa_z a) (DfracOwn 1) 0%nat b) ∗
         ([∗ set] cc ∈ (fin_to_set CPU : gset CPU), hart_view cc) ∗
         wlog_lb [] ∗
         uart_frag (wgdev σ0).(duart) ∗ plic_frag (wgdev σ0).(dplic) ∗
         virtio_frag (wgdev σ0).(dvirtio)
         ={⊤}=∗ ([∗ list] e ∈ epower_fork gen, EWP e @ ⊤)) ->
    wp_behavior pstep_ev (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0) c ->
    (forall cb mid TS DS,
       wp_behavior pstep_ev (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0) cb ->
       rtc (wp_promise_step (P:=pexv6) (D:=dev_state))
         (wp_init (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)) mid ->
       ptraces_dev_of pstep_ev pdev_ev TS DS mid cb ->
       cls_canonical pcls_ev TS ->
       main_premises n_disk TS DS) ->
    exists cf,
      rtc (wp_pf_run pstep_ev pcls_ev)
        (wp_init (img_z (wgimg σ0)) (wgdev σ0) (eps_init σ0)) cf /      prog_of cf = prog_of c /\ (forall a, mem_of cf a = mem_of c a) /      exists P' σ', rtc epf_run (ep_init gen, σ0) (P', σ') /                    ecfg_of P' σ' = cf.
  ```

  **THE PREMISE LEDGER, in full** — and nothing else:
  1. four machine facts about a booted σ0 (fresh era, power on, empty log,
     fresh views);
  2. THE WP PACKAGE (the only Iris-side obligation), verbatim
     `WeakEvAdequacy.weak_ev_pf_violation_free`'s;
  3. the behavior under consideration;
  4. `WeakRobustMain.main_premises n_disk TS DS` served at CANONICAL traced
     bundles of any behavior of the same program — the genuine Layer-1
     robustness content (per-edge split, bad-SCC residue, E-edge
     obligation, device-epoch residue, byte classification), whose
     exhibit-level discharge is `weak-memory-premises.md` phase 2;
  5. the 5 `rv64d` axioms (machine-checked: `Print Assumptions
     xv6_ev_weak_robust` = exactly those five, nothing else).

  GONE relative to the archived instruction-atomic capstone
  (`WeakComposeLang.xv6_weak_robust_lifted`): `rv64d_axiom_shapes`,
  `rv64d_live_residue`, `img_total`, `xv6_cone_premises`, `cone_liftable`,
  `Hcq`, `Hseip`, `Hpriv`, `sail_shaped`, `sail_live`, the oracle streams —
  and `cls_canonical`, which the retag discharges inside the proof.

  TWO SHAPE DEVIATIONS FROM THE COMMISSIONED SKETCH, both forced and both
  matching the archive: (i) the `main_premises` supplier is quantified over
  the behavior `cb` as well, because the capstone RETAGS the behavior
  before running Layer 1 on it (`cls_canonical` is obtainable only for a
  bundle one already holds, so the bundle Layer 1 consumes belongs to
  `retag_cfg _ c`); in exchange the supplier MAY ASSUME canonicity.
  (ii) `WeakRobustMain` gained `robust_main_bundle` — `robust_main`'s body
  with the traced decomposition as an ARGUMENT rather than produced
  internally — because `robust_main`'s own `cls_canonical` hypothesis
  quantifies over EVERY bundle of the behavior, which no retag can supply.
  `robust_main` is unchanged in statement and is now derived from it in
  three lines.  `WeakRetag` gained `ptraces_dev_of_retag` (the witness is a
  pure order on trace positions, so the retag leaves it alone).

## Phase C — M5: the disk as a weak-memory AGENT (design: `design/weak-memory-m5.md`)

DECIDED 2026-08-17 (the orchestrator's design; the "fabric view" sketch of
this file's first draft is WITHDRAWN — no fabric view, no view-carrying
label, no replay change): the virtio device becomes a small PROGRAM in a
read/write/fence monad (`VirtioModel.DM`, `virtio_prog`) that acquire-loads
`avail->idx`, plain-loads the ring/descriptors/header/buffer at the acquired
view, stores the completion, FENCES, stores `used->idx` — one event per
node at the disk agent's own `dws`, with the hart's labels.  Driver/device
synchronization is message passing through the rings (the virtio spec's own
barrier protocol); QUEUE_NOTIFY/ISR are hints (the device polls — a
superset).  Layer 1's ONLY change is the fabric-marker label `LDev`.  The
FENCE I/O-bit issue (Sail drops the bits) is MOOT for safety under this
model; recorded as assumption 3 of the design.
- **C1** `VirtioModel`: `DM`, `dres`, `virtio_prog`, and the equivalence
  lemma with `virtio_req_step`/`virtio_stalled` over a flat `mv`.
- **C2** DONE (2026-08-17) `WeakEvLang`: `EDisk gen (dp : option (DM dres))
  dws`; the eight arms of the design (start / `DRead` / `DWrite` / `DFence`
  / commit / `DWild` / `DIdle` / latch), each fabric-touching one its own
  disjunct; the store class spelled once as `ddev_class = wm_class_of
  ddev_ak` (a PLAIN EXPLICIT store, hence `WCrel` exactly when the disk's
  own `w_relp` is armed by its `DFence`).  `wflat`/`wdisk_step`/
  `wmsgs_of_map`/`pend`/`edisk_burst`/`edisk_emit`/`epend_canon` left the
  event language; `edp_wf`/`edisk_step_wf` and a `DRead`-excepting
  `eprim_step_disk_reducible` took their place (a `DRead` with no
  admissible timestamps is legitimately STUCK — the driver's WP
  obligation).  `WeakEvPf` followed (`ep_dp`, `PDisk dp`, `EPFDisk`,
  `edlabel_ok` at `LLoad`/`LFence`, `edisk_step_label`); `EPFUart`/
  `EPFPlic`/the MMIO branches relabelled `LDev`; `WeakEvAdequacy`/
  `WeakEvLift`/`WeakEvStarted` needed NO change.
- **C3** DONE (2026-08-17) `WeakEvInst`: `pstep_disk = pdisk_prog ∨
  pdisk_uart` with one disjunct per arm and NO memory existential anywhere
  (`pdisk_burst`/`pstep_disk_at`/`pstep_disk_of_at`/`pdisk_emit` deleted);
  the hart's MMIO arms and `pstep_plic` relabelled `LDev`; `pcls_ev (PDisk
  _) (LStore …) ws := ddev_class ws`; `pdev_ev _ l _ := (l = LDev)` with
  `pdev_ev_ok : WeakPromiseFact.pdev_ok pstep_ev pdev_ev`; a new
  `edisk_step_factor` covering all eight disk arms in BOTH directions,
  plus `euart_step_factor`, `ecycle_step_factor`, `eplic_step_factor`
  re-proved at the new labels, and the lat-freedom / ts-obliviousness
  lemmas extended to the disk's loads.  RECORDED DECISION: the `DWild`
  arm's label is `LSilent`, not `LDev` (it reads and moves nothing, so it
  is fabric-blind and `pdev_ok` holds; `LDev` would only add a spurious
  device event to the replay order).  The remaining step to the capstone is
  the pf-side WRAPPER (`epf_step` ⇄ `wp_pf_step pstep_ev pcls_ev`), which
  is B3's ⇒/⇐ statement — now with NO named exception.
- **C4** (later, M4-port track): per-node EWP rules for the disk thread; the
  driver proof that `DWild` is unreachable.

## After the capstone

Phase-2 discharge of `main_premises` (`weak-memory-premises.md`, exhibit
level); the RVWMO axiomatic containment (`WeakAxiomatic*`) as the upgrade
of §6(5); the M4 leaf retarget (separate volume track).
