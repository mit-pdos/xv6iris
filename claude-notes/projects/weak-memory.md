# Project: weak memory (RVWMO) — staged worklist

Design: [`design/weak-memory.md`](../design/weak-memory.md) (PROPOSAL).
Nothing landed. Branch: `weak-memory`.

## M0 — model spike (no Iris)

Validate the operational design before anything depends on it.

- [ ] `WeakMem.v`: `wmsg`, `wstate`, the log (`gmem0` + `glog`), per-byte
      readability, the load/store/AMO/fence update functions. Pure stdpp.
- [ ] Modified `run`/`exec` on a COPY (`WeakLang.v` scratch): MemRead/
      MemWrite/Barrier arms consult `wstate` + log; `exec` takes the read
      oracle χ; `exec_run` bridge per oracle.
- [ ] Litmus suite as executable lemmas (SB, MP±fences, CoRR, IRIW,
      MP+amoswap.aq; LB must be unobservable — documents the promise-free
      gap). Verdicts cross-checked against riscv.cat/herd expectations.
- [ ] Spike report: does the oracle shape hold up? is the per-byte View
      workable as a monPred index? Feed corrections back into the design.

## M1 — language + base logic

- [ ] Swap `gstate`/`prim_step` to the log + `gws` (the real `RiscvLang.v`);
      device arms; crash reset of log/views per generation.
- [ ] Base state interpretation: `mono_list` log auth, per-hart `wstate`
      auth, per-byte history auth; base points-to and seen-assertions.
- [ ] `wp_exec_step` tower re-derived (oracle-∀ form); adequacy skeleton
      (`riscv_system_adequacy` restated over log-initial resources).

## M2 — the vProp surface

- [ ] `View`, `vProp = monPred`, `⊒V`, `@V`, `objective`, split axiom;
      `Objective` instances for registers/devices/ghosts/`↦□` family.
- [ ] `↦ₘ{dq}` redefinition + its SC-shaped load/store leaf rules; the
      `↦₈`/`↦₄`/`↦ₛ` towers on top; fence modalities + fence leaf WPs;
      AMO leaf WPs.

## M3 — vertical slice (the interface test)

- [ ] `WpLock.v` rework: objective `lock_inv` with `@V R` deposit;
      acquire/release re-proven; `locked` token unchanged.
- [ ] One lock-client cone re-proven unchanged-in-statement (candidate:
      kinit/kfree — small, pure lock+memory).
- [ ] `StartedInv.v` escrow → view-transferring form; ProofMainSecondary's
      spin+fence path over the new leaves.
- [ ] Porting guide written from what the slice taught (the
      explicit-cpuid-porting-guide precedent).

## M4 — the sweep

- [ ] File-by-file port of the leaf libraries, then function proofs
      (subagents, batched; `lemma_diff.py`/`spec_vacuity.py` per batch).
- [ ] Final `Print Assumptions` diff: baseline axioms + the four declared
      weak-memory assumptions (LB-gap, MMIO-ordering, coherent-ifetch,
      SC-walker) and nothing else.

## M5 — devices

- [ ] Disk-agent view; notify-carries-view MMIO coupling; `DiskStepDma`
      through the device view; virtio cone re-proof (the 4 fence sites).

## M6 — closing the LB gap (research)

- [ ] Robustness theorem (preferred): for the release-fenced/lock-mediated
      store discipline the kernel obeys, full Promising-RISC-V behaviors =
      promise-free behaviors. Operational-level, no Iris. Retires the
      store-reordering-gap assumption.
- [ ] Axiomatic characterization of the promise-free machine (the PS1
      Thm 5 analog): promise-free ≡ RVWMO ∧ acyclic(po ∪ rf) ∧
      (po ∩ W×W) ⊆ gmo. Pins exactly what the interim assumption says.
- [ ] Fallback: promises in the semantics + SLR-style logic (transfinite
      Iris territory — only if robustness fails).

## Open questions (resolve by end of M0/M3)

- Oracle granularity: per-MemRead per-byte timestamp list vs one global
  choice sequence; what shape keeps leaf statements smallest.
- View index: full `gmap Arch.pa nat` vs (scalar vrNew + sparse coh deltas);
  monPred index must be a join-semilattice either way.
- Forward-bank view: store-time `w_vwNew` vs 0 (both sound; pick the one
  that never surfaces in leaf statements).
- Whether `wp_dead`/corpse arms and the power thread need any view plumbing
  at all (expected: no — they never read memory).
- Where the MMIO/ifetch/walker declared assumptions live so
  `proof_coverage.py`/`Print Assumptions` surface them honestly.
