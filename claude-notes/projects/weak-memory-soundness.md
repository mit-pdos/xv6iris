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
- **B3** the factorization, arm by arm: ⇐ (`epf_step i l ρ ρ' → wp_pf_step
  pstep_ev pcls_ev i l (ecfg_of ρ) (ecfg_of ρ')`) for ALL arms, and ⇒
  (`wp_pf_step … i l (ecfg_of P σ) c' → ∃ ρ', epf_step i l (P,σ) ρ' ∧
  ecfg_of ρ' = c'`) for every arm EXCEPT the disk burst, which is the one
  named exception in the statement.  Plus `lat_free_prog`, `ts_oblivious`,
  `pdev_ok`, `pcls_obl` for the instance, and `ecfg_of (ep_init gen) σ0 =
  wp_init …` at a fresh era.
- **B4** the capstone STATED with the burst arm as its single open case.

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
- **C2** `WeakEvLang`: `EDisk gen (dp : option (DM dres)) dws`; the arms of
  the design; `wflat`/`wdisk_step`/`pend` leave the event language.
- **C3** `WeakEvInst`/`WeakEvPf`: the disk arms as `PFLoad`/`PFStore`/
  `PFFence`/`PFSilent(LDev)`; ⇒ holds for the disk; the capstone closes.
- **C4** (later, M4-port track): per-node EWP rules for the disk thread; the
  driver proof that `DWild` is unreachable.

## After the capstone

Phase-2 discharge of `main_premises` (`weak-memory-premises.md`, exhibit
level); the RVWMO axiomatic containment (`WeakAxiomatic*`) as the upgrade
of §6(5); the M4 leaf retarget (separate volume track).
