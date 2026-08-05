# Project: weak memory (RVWMO) — staged worklist

Design: [`design/weak-memory.md`](../design/weak-memory.md) (PROPOSAL).
Branch: `weak-memory`. Landed: M0 (`iris/WeakMem.v`, `iris/WeakLitmus.v`)
and M1a (`iris/WeakInterp.v` + fwd-bank wire-in). Next: M1b.

## M0 — model spike (no Iris)

Validate the operational design before anything depends on it.

- [x] `WeakMem.v`: `wmsg`, `wstate`, the log (`gmem0` + `glog`), per-byte
      readability, the load/store/AMO/fence update functions. Pure stdpp.
- [x] Modified `run`/`exec` on a COPY: done as M1a's `WeakInterp.v`.
- [x] Litmus suite as executable lemmas (SB, MP±fences, CoRR, IRIW,
      MP+amoswap.aq; LB must be unobservable — documents the promise-free
      gap). Verdicts cross-checked against riscv.cat/herd expectations.
- [x] Spike report: fed back into the design (AMO side condition, fwd-bank
      decision, gap-witness framing).

### What M0 established (read before M1)

- **`readable` wants ONE workhorse lemma, not a monotonicity theory.**
  `readable img log ws vpre a t := t writes a ∧ ¬ writes_in log a t (vpre ⊔ coh(a))`
  is anti-monotone in `vpre` and has NO monotonicity in `t` in either
  direction (both directions are the coherence constraint). Every forbidden
  litmus proof goes through exactly one corollary,
  `readable_not_init : readable … → writes_in log a 0 vpre → t ≠ 0` — "if my
  pre-view already covers a write to this byte, the era-initial image is no
  longer readable". Expect the Iris load leaf to be built on that shape.
- **`writes_in log a lo hi` is the right primitive**, and it is what makes the
  invariants stable: monotone in the log (`writes_in_app`), invertible below
  the old length (`writes_in_app_inv`), and clippable to `min hi (length log)`
  — the last one is what lets a *negative* fact ("no write to y below my
  view") survive later appends, which is the whole IRIW proof.
- **`coh` with a `default 0` lookup never had to be reasoned about
  pointwise** — only `t ≤ coh (load_post …) a` and the insert/lookup pair.
- **Each hart's stores enter the log in program order BY CONSTRUCTION**
  (a store appends at `S (length log)` and the hart cannot reach its next
  store first), so no invariant is needed for it — which is precisely why the
  machine is stronger than RVWMO on W→W (gap witness #2 below).
- **Two documented over-strengthenings**, both proven as unreachability
  theorems in `WeakLitmus.v`: `lb_forbidden` (the LB gap, Decision 1) and
  `mp_reader_fence_only_forbidden` (MP with no writer fence — RVWMO allows
  it, this machine does not). Plus one M0-local simplification: `load_post`
  ignores the forward bank and always uses `t` for `vpost`, so `w_fwd` is
  written and never read. DECIDED: wire it into the load rule at M1 (design doc, Decision 3).
- **Instantiating addresses at `Arch.pa`** needs only `EqDecision` +
  `Countable` + "byte i of a message" arithmetic; the spike keeps addresses
  as `Z` under `Z.le`/`Z.sub` and as `gmap` keys only. Mind the
  `gmap Arch.pa _` Countable-instance trap in the durable notes when the real
  file also imports `SailStdpp.Values`.

## M1 — language + base logic (ALL in parallel files; existing tree untouched)

- [x] **M1a — the weak interpreter** (`WeakInterp.v`, + WeakMem fwd-bank
      wire-in): DONE. `wrun`/`wexec` with the `list (list nat)` oracle
      (validated, unchanged), `wexec_wrun` per-oracle soundness (closed),
      `wexec_det`, `wread_bytes_complete` (the per-read converse M1c
      consumes; full completeness blocked only by `Interface.Choose`,
      TODO comment names the `choice_free` fix). Access-kind reality:
      kinds come from the aq/rl/reserved flags ALONE — plain `.aq` loads
      are internal_error (acquire arrives only on exclusives, i.e.
      amoswap.w.aq), AMOs use exclusive/conditional kinds (never
      AV_atomic_rmw), fetch and walker emit plain reads (see design doc
      Decision 6 — SC-walker assumption dropped). Byte j of an access is
      at `uint pa + j` (`acc_addr`), wrap-freedom isolated in `pa_z_add`
      for the M2 bridge. Image is a function `Z → option (bv 8)`; the
      `gmap Arch.pa` img converts at the seam (`img_z`). Forwarding is
      disabled for acquire loads (PARM read_view side condition), coh
      still joins the raw timestamp — all 11 litmus verdicts unchanged,
      plus `fwd_selfread_*` witnesses so the wire-in can't go vacuous.
      Sanity: `wrun_v_disk`, `wrun_img`, `wrun_log_app` (append-only —
      M1c's mono_list premise), SC-degeneracy `wread_all_seen`.
      NOTE for M1b: `wm_tid` is stamped None inside `wrun` — make
      wrun/wexec tid-parametric so the language layer stamps hart ids.
- [ ] **M1b — the language** (`WeakLang.v`): `wgstate`, prim_step arms
      (hart via `wrun`, uart/disk/plic/power; disk reads coherent-latest
      as an interim until M5's device views), boot/crash reset of
      log+views per generation, language mixin.
- [ ] **M1c — base logic**: state interpretation (`mono_list` log auth,
      per-hart `wstate` auth, per-byte latest-write auth), base points-to
      + seen-assertions, `wp_exec_step` tower analog (oracle-∀ form),
      adequacy skeleton over log-initial resources.

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
      weak-memory assumptions (store-reordering gap, MMIO-ordering,
      no-icache) and nothing else (SC-walker dropped at M1a).

## M5 — devices

- [ ] Check how the generated Sail model decodes/executes FENCE words with
      I/O bits (barrier_kind is memory-only — see design doc); recover the
      I/O bits at the `run` layer if the model drops them.
- [ ] **Patch xv6 virtio_disk.c to emit the architecturally correct
      fences** (`fence w,o` before QUEUE_NOTIFY, `fence i,r` after the
      MMIO status read) + re-dump; the model classifies MMIO by the I/O
      fence bits strictly, no accommodation of the old driver (decided
      2026-08, design doc Decision 6).
- [ ] Disk-agent view; notify-carries-view MMIO coupling; `DiskStepDma`
      through the device view; virtio cone re-proof (the fence sites).

## M6 — closing the store-reordering gap (research)

Two-layer proof plan (the quantification over all executions is the one
the Iris proof already pays for — no separate whole-kernel analysis):

- [ ] **Layer 1, program-independent operational lemma** (once, about the
      machine; no xv6/Sail in the statement): if no promise-free execution
      of P reaches the violation pattern, then every full-machine
      execution of P is matched by a promise-free one (same observable
      states + reducibility). Proof = delay-simulation: a promise matters
      only if read by another agent before fulfilment; unread promises
      commute forward to their fulfilment point; an early read implies the
      violation pattern back in the PROMISE-FREE semantics. Precedents:
      PS1 DRF-Promise (same structure at language level), Shasha–Snir /
      Bouajjani–Derevenetc–Meyer (TSO) / Lahav–Margalit (RA) robustness.
- [ ] **Layer 2, the premise, extracted from the WP proofs**: per-store
      protection certificates emitted by the store leaf rules — every
      store either consumes `↦ₘ` (exclusively owned ⇒ promise unreadable)
      or is an enumerated fenced sync-site leaf (certification arithmetic
      pins the promise: fulfilment po-after `fence rw,w` forces the
      timestamp above everything the fence covers). Adequacy exports the
      certificate fact alongside reducibility; Layer 1 consumes it.
- [x] **RESOLVED (2026-08, read from snu-sf/promising-arm sources): the
      PARM base machine has NO certification at all.** `Machine.step`
      lifts `state_step ∪ promise_step` with promising unconditional;
      doomed threads are trivially reachable and are pruned only EX POST —
      "behavior" (`Machine.exec`) is a run whose FINAL state satisfies
      `no_promise` (all promise sets ⊥). Both axiomatic-equivalence
      directions and Thm 7.1 quantify over `Machine.exec` only. The
      certified machine (`lcertify/Certify.v`) checks only the STEPPING
      thread post-step; `certify` = the thread alone, from current
      memory, reaches promises = ⊥ (its `write_step`s append but each
      promise made in certification is fulfilled in the same step).
      All-threads-certified is preserved only via `interference_certify`
      (`certify` survives arbitrary memory extension), which exists ONLY
      for RISC-V (`arch == riscv` hypothesis) — hence Thm 6.3 deadlock
      freedom being RISC-V-only. Coq 8.15 + sflib + hahn, ~17k lines;
      architecture is a parameter, not a separate RISC-V file.
      CONSEQUENCES for us: (a) full-machine adequacy must be stated over
      completable prefixes (prefixes extendable to a `no_promise`
      completion) — doomed runs are model artifacts hardware never
      exhibits, exactly what `Machine.exec` already prunes; (b) **their
      Thm 7.1 (`promising_to_promising_pf`, PtoPF.v) is a reusable
      Layer-1 skeleton**: every behavior = a promise PHASE from init,
      then per-thread `state_step`s against FROZEN memory (`pf_exec`) —
      so robustness reduces to "for our kernel, a nonempty front-loaded
      promise set admits no `no_promise` completion beyond what the
      empty phase admits", a statement over frozen-memory per-thread
      runs, far more tractable than arbitrary interleavings.
- [ ] OPEN TENSION to resolve when M6 starts: `interference_certify`
      as paraphrased (certification survives ANY memory extension,
      RISC-V) seems to contradict the CS-store scenario — a thread that
      promised a critical-section store while the lock was free looks
      uncertifiable after another hart's acquire lands (its cert-run AMO
      must read the new lock=1 and spin). Read the lemma's exact side
      conditions in CertifyProgressRiscV.v; the resolution determines
      the robustness invariant. Also still open: the exact sufficient
      violation pattern (the fenced empty-predecessor-set wrinkle — a
      release-fenced store with nothing to order CAN be promised and
      must commute harmlessly), and byte-granularity/mixed-size care.
- [ ] Axiomatic characterization of the promise-free machine (the PS1
      Thm 5 analog): promise-free ≡ RVWMO ∧ acyclic(po ∪ rf) ∧
      (po ∩ W×W) ⊆ gmo. Pins exactly what the interim assumption says.
- [ ] Fallbacks, in order: ship the interim theorem (unconditional for
      Ztso hardware, explicit assumption otherwise); promises in the
      semantics + SLR-style logic (transfinite Iris — only if robustness
      fails).

## Open questions (resolve by end of M0/M3)

- Oracle granularity: per-MemRead per-byte timestamp list vs one global
  choice sequence; what shape keeps leaf statements smallest.
- [x] View index: DECIDED `View := nat * gmap Z nat` (scalar ⊔ sparse,
  pointwise floor order) — see design doc Decision 5. Validate at M2.
- Forward-bank view: store-time `w_vwNew` vs 0 (both sound; pick the one
  that never surfaces in leaf statements).
- Whether `wp_dead`/corpse arms and the power thread need any view plumbing
  at all (expected: no — they never read memory).
- Where the MMIO/ifetch/walker declared assumptions live so
  `proof_coverage.py`/`Print Assumptions` surface them honestly.
