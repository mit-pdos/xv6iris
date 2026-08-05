# Project: weak memory (RVWMO) — staged worklist

Design: [`design/weak-memory.md`](../design/weak-memory.md) (PROPOSAL).
Branch: `weak-memory`. Landed: M0 (`iris/WeakMem.v`, `iris/WeakLitmus.v`),
M1a (`iris/WeakInterp.v` + fwd-bank wire-in), M1b (`iris/WeakLang.v`),
M1c (`iris/WeakGhost.v`, `iris/WeakExec.v`, `iris/WeakAdequacy.v`),
M2a (`iris/WeakView.v`, `iris/WeakVProp.v`).
Next: M2b.

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
- [x] **M1b — the language** (`WeakLang.v`, 778 lines): DONE. Reuses
      RiscvLang's CPU/mexpr/device-relations/reset definitions wholesale
      (no instance clash — both cones stay off SailStdpp.Base); the
      interpreter is now tid-parametric and stamps hart ids on messages.
      Disk arm: thin `wdisk_step d m d' w` exposing the WRITE MAP (the
      reused relation only exposes `w ∪ m`, unrecoverable), proven
      equivalent to `RiscvLang.disk_step` both ways; DMA appends
      `wmsgs_of_map w`. `wflat` (coherent flat projection) characterized
      against `latest`/`log_byte` under `wlog_wf` (needed: `z_pa` wraps,
      keys don't round-trip without it). Boot anchor reused verbatim
      (register-only program), so `reset_regs_of_run` and consumers
      apply to a weak boot unchanged. Mixin's axiom footprint =
      byte-identical to RiscvLang's (the 5 platform axioms).
      **SEAM FACTS for M1c:** (1) log append-only holds for every arm
      EXCEPT PowerOn (`wprim_step_log_app` carries that side condition;
      `wprim_step_poweron_log` states the reset) — the mono_list log
      auth is a PER-ERA resource, reallocated at reboot like the era
      gen_heap in the fixed/era riscvGS split; (2) `ws_le` monotonicity
      is per-hart and also broken by PowerOn (reset to `ws_init`);
      (3) the five inversion lemmas are uniform, `whart_view`/
      `whart_write` + peel lemmas are the destructing shape.
      Gotchas recorded: conditional-`rewrite` side-goal ORDER flips
      between implicit/explicit-P spellings (fully apply or pre-assert);
      `lia` dies with an mword in context (hoist to mword-free Local
      Lemmas); `Forall_singleton` mis-elaborates (use `Forall_inv`).
- [x] **M1c — base logic** (`WeakGhost.v` 429 / `WeakExec.v` 358 /
      `WeakAdequacy.v` 211 lines; 2.8 / 3.8 / 4.4 s): DONE.
      `weakGS` = mono-list log + `ghost_map Z (nat * bv 8)` latest-write map
      + a PER-HART `ghost_var wstate` family; registers and devices are
      `riscvGS`'s, reused verbatim (its `gen_heap` and the whole crash
      apparatus go unused). `weak_system_adequacy` is CLOSED at the baseline
      5 platform axioms (no funext).
      **SEAM FACTS for M2:**
      (1) **The leaf-facing rule is `WeakExec.wp_wexec_step`**, whose
      continuation is `∀ tick χ σ' χ', ⌜wexec (Some (fin_to_nat cpu_id))
      (riscv_step tick) χ σ = Some (tt, σ', χ')⌝ ={∅,⊤}=∗ wmstate_interp σ'
      ∗ WP Loop`, and whose premises are ONE reducibility witness
      (`∃ χ σ0 χ', wexec … false … = Some …`) plus the pure bridge
      obligation `wexec_covers` (below). It is derived from the PRIMITIVE
      `wp_wrun_step`, whose continuation quantifies over `wrun` successors
      and which has NO bridge premise — a leaf that cannot discharge
      `wexec_covers` can always drop to it.
      (2) **The `wrun`→`wexec` bridge is NOT a theorem, and this is
      structural.** `wexec` rejects `Interface.Choose` (as `RiscvExec.exec`
      does) while `wrun` branches over it, and — unlike the SC tree — the
      caller's exec witness does NOT pin the path: a `wrun` may read a
      different admissible value and descend into a different subtree, which
      may contain a `Choose`. rv64d has 54 `undefined_bitvector` sites, each
      a `Choose`, so this is not a technicality. What IS proven:
      `WeakExec.wrun_wexec` — the bridge on the choice-free fragment
      (`mchoice_free`, a recursive predicate on `M X`), axiom-free — plus
      `wread_coh_ts` (a coherent read's timestamp is forced to `coh_ts`, the
      `ak_coh` twin of `wread_all_seen`). So `wexec_covers` is a caller
      obligation with a proven sufficient condition.
      (3) **γlat updates happen in the CALLBACK**, not in the rule: the
      continuation must re-establish `wmstate_interp σ'`, whose
      `wlat_interp (wm_img σ') (wm_log σ')` conjunct is exactly the "every
      element is still the latest write" obligation. `WeakGhost` supplies
      the algebra for it: `latest_val` (= `WeakMem.latest` + the value),
      `wlat_lookup` (auth+elem ⇒ the element IS the latest — what collapses
      the ∀-oracle to one VALUE), `latest_val_app` / `wlat_agree_app`
      (an element survives an append that does not write its byte),
      `wlat_agree_insert`, `wlat_interp_acc`, and
      `writes_in_app_new`/`not_writes_in_app_new` for the "which new message
      wrote this byte" side.
      (4) **`ghost_map CPU wstate` was REJECTED for a per-hart `ghost_var`
      family**: a single map authority cannot be focused on one hart the way
      `gregs_interp_acc` focuses one hart's registers (the rule would have to
      expose the whole map to say the other cells did not move). The halves
      pattern makes it one `big_sepS_delete` (`wws_interp_acc`), exactly like
      `era_strans_name`/`era_sie_name`.
      (5) **Single-era simplifications, all noted in the file headers**: the
      state interp pins `⌜wgpow g = true ∧ wggen g = 0⌝` (`wgen_pin`) instead
      of the generation/started/registry/FS-tie tower, the rules take
      `gen_id = 0` as a premise (so no corpse arms — `wp_dead` has no
      analogue yet), and the pool excludes `PowerLoopE`. The era indirection
      slots in at `weak_state_interp`, in `RiscvPtsto.power_interp`'s shape.
      The unused `riscvGS` gnames (heap/meta, kmap, kpt, strans, sie, park,
      disk, gen, start, registry, fstie) get `1%positive` placeholders —
      nothing owns anything at them.
      (6) Also landed: the three DEVICE lifting rules (`wp_wuart_step` /
      `wp_wdisk_step` / `wp_wplic_step`), each handing the caller the whole
      `weak_state_interp` and taking it back at its arm's successor
      (`wg_dev` / `wg_regs` / `wg_dma`), so the adequacy premises are not
      vacuous. The disk's is where M5's log-append obligation lands.

## M2 — the vProp surface

- [x] **M2a — the vProp core + the two memory rules**
      (`WeakView.v` 479 / `WeakVProp.v` 672 lines; 2.6 / 5.5 s): DONE.
      `View`, `vProp = monPred`, `⊒V`, `P @@ V`, the split axiom, the
      `Objective` inventory; the byte points-to `↦w`, the `vwp_hold`
      discipline, the load and store rules at the event altitude + their
      monPred restatements, and an access-altitude demo.
      Two forced extensions to existing files:
      `WeakMem.readable_latest_pin` (the collapse lemma; `readable_top_unique`
      is now its `vpre = 0` corollary) and `WeakGhost.wlat_agree_store`.
- [ ] **M2b** — the `↦₈`/`↦₄`/`↦ₛ` towers on `↦w`; the fetch/`instr`/decode
      bridge onto `wpt_img`; the `wexec`↔`exec` pinned-read transfer (see
      the seam facts below); fence modalities + fence leaf WPs; AMO leaf WPs.

### What M2a established (read before M2b/M3)

- **The vProp core is 95 % INHERITED from `iris/bi/monpred.v`.** The `biIndex`
  is the whole added content: `Record view := View { v_scl : nat; v_map :
  gmap Z nat }`, `flr V a := v_scl V ⊔ default 0 (v_map V !! a)`, order
  pointwise on `flr` (a PREORDER — deliberately unquotiented, `biIndex` asks
  for no more), join componentwise, `BiIndexBottom view_bot`. Everything
  else — the BI structure, `BiAffine`/`BiBUpd`/`BiFUpd`/`BiEmbed`, `⊒V`'s
  persistence and anti-monotonicity (`monPred_in`), the `Objective` class and
  its ~20 connective instances, the proofmode — comes for free.
  **`⊒V` IS `monPred_in V`**; do not hand-roll it.
- **`P @@ V := ⎡ monPred_at P V ⎤` is the right view-at, and Iris does not
  name it.** It is objective by `embed_objective` with NO proof obligation,
  and every embedding lemma applies. `<obj> P` ("P at every index") is the
  wrong object and much too strong. The split axiom is then Iris's own
  `monPred_in_intro`/`monPred_in_elim` modulo ∧↔∗ — but BOTH are proved here
  index-wise (`constructor => V; rewrite monPred_at_…`), because rewriting
  with `monPred_in_intro` in a goal that mentions `P` twice dies with
  *"_pattern_value_ is used in conclusion"*, and `bi.sep_and`/
  `persistent_and_sep_1` leave TC side goals that a following `rewrite` then
  lands on. **Index-wise proofs are the reliable idiom for anything
  structural about `⊒`/`@@`.**
- **ONE objectivity instance covers the whole design doc's list.**
  `embed_objective` (⎡P⎤ for any `iProp`) makes every register/CSR
  assertion, every device assertion, all ghost state and the whole base layer
  objective at a stroke — nothing per-family had to be added.
- **THE vwp_hold DISCIPLINE WORKS, AND ITS SEAM IS `wpt_at`.** The design
  call (no new WP connective; the vProp layer is a discipline over the base
  logic) landed: `vwp_hold P ws := monPred_at P (ws_view ws)` with
  `ws_view ws := View (w_vrNew ws) (w_coh ws)` — and `flr (ws_view ws) a =
  w_vrNew ws ⊔ coh ws a` holds by `reflexivity`, `ws_le ws ws' →
  ws_view ws ⊑ ws_view ws'` in three lines. Two facts make it pay:
  (1) `vwp_hold_mono` carries EVERY untouched premise across a step for
  free, out of `WeakInterp`'s own `wread_post_ws_le`/`wwrite_post_ws_le`,
  so a leaf rule's side conditions are only ever about the byte it touches;
  (2) `wpt_at : vwp_hold (a ↦w{dq} v) ws ⊣⊢ ∃ t, wlat_pointsto a dq t v ∗
  ⌜t ≤ flr (ws_view ws) a⌝` decodes the points-to into base-logic terms,
  after which BOTH rules are pure `WeakMem`/`WeakGhost` reasoning with no
  monPred in sight. The monPred altitude is re-entered in exactly two
  three-line lemmas (`wpt_load_vprop`, `wpt_store_vprop`). Verdict: keep
  both altitudes; state leaves at `vwp_hold`, publish `@@`-forms for M3.
- **The points-to is `a ↦w{dq} v := ∃ t, ⎡wlat_pointsto a dq t v⎤ ∗
  ⊒(view_byte a t)`** — the base element (objective) plus the receipt (the
  entire subjectivity). Fractions/agreement/persist all lift from
  `ghost_map`; `wlat_pointsto_agree` (t AND v agree) is the base-altitude
  lemma the vProp-level `wpt_agree`/`wpt_split` are built on — and note that
  the ← direction of `wpt_split` is NOT free, two points-to for one byte may
  a priori carry different timestamps and it is element agreement that
  forces them equal.
- **OBJECTIVITY OF THE ERA IMAGE.** `view_byte a 0 ⊑ view_bot`, so a
  points-to whose latest write is timestamp 0 has NO receipt: `wpt_img a dq v
  := ⎡wlat_pointsto a dq 0 v⎤` is objective, and `wpt_img_wpt` turns it into
  an ordinary `↦w`. This is the resource `kernel_text`/`instr`/the `↦□`
  family port onto at M2b. **The converse is false**: a `↦w□` at t > 0 is
  persistent but NOT objective — putting one in an invariant is unsound.
  Persistence and objectivity are independent here.
- **THE COLLAPSE LEMMA IS `WeakMem.readable_latest_pin`:**
  `latest img log a t → t ≤ vpre ⊔ coh ws a → readable img log ws vpre a t' →
  t' = t`. The floor premise must be at `Nat.max vpre (coh ws a)` (not at
  `coh ws a`, which is all `readable_top_unique` gave) because the floor the
  vProp layer owns is the hart's index `w_vrNew ⊔ coh(a)`; `load_vpre_vrNew`
  is what bridges it. Feed it `wlat_lookup` (my element IS the latest) and
  the ∀-over-oracles quantifier of `wp_wexec_step` collapses: **the timestamp
  still varies, the VALUE cannot.**
- **The store rule's whole content is `wlat_agree_store`** — a message that
  writes exactly byte `a` keeps every other element accurate by
  `latest_val_app`, and `a`'s new element is a fresh top so nothing can be
  above it. The post-view premise is the honest one (`S (length log) ≤
  flr (ws_view ws') a`), discharged at the machine's own `store_post` by
  `flr_store_post`.
- **THE DEMO REACHED THE ACCESS ALTITUDE, NOT THE INSTRUCTION ALTITUDE.**
  `wpt_wread_word` : owning the `n` bytes at the hart's index pins the whole
  word `wrun`/`wexec` returns for a single `Interface.MemRead`, at any width
  (`w = Z_to_bv (8*n) (assemble_bytes bs)`); `wpt_wwrite_byte` runs the store
  rule through `wwrite_post` for a 1-byte store. Recipe worth reusing: a
  "for every byte" pure conclusion is obtained WITHOUT induction by making
  `j` a Coq-level parameter and, where the ∀ is really needed,
  `rewrite bi.pure_forall; iIntros (j)` — the `wlat_interp` authority is
  consumed once and the ∀ is introduced before it is spent.
- **WHERE THE INSTRUCTION ALTITUDE FIGHTS BACK (shapes M2b).** It is NOT
  views. An SC leaf (`WpMmodeLoad.wp_ld_gpr`, ~130 lines) spends ONE line on
  memory — `∀ j, σ.(mem) !! pa_add ea j = Some (nth_byte v j)` — and all the
  rest on `wp_instr` (fetch + decode bridge), the
  `mmode_config`/`hw_config`/PMP/PMA/clint/htif tower, and one
  `exec_execute_LOAD_8_gpr`. The blocker is that that whole layer is stated
  over `RiscvExec.exec` / `RiscvLang.mstate` (with a flat `mem` map), while
  the weak side is `wexec` / `wmstate`: a PARALLEL type, so none of the
  ~1220 decode lemmas or the execute lemmas apply. The config tower itself
  is register-side and therefore objective — it rides through `⎡·⎤` with no
  view plumbing at all. **Recommended M2b shape: a `wexec`↔`exec` transfer
  lemma on the PINNED-READ fragment** — if every read of a run is pinned
  (owned `↦w` at the hart's index, or timestamp-0 text), the collapse lemma
  says it returns `WeakLang.wflat`'s value, so `wexec tid m χ σ = Some
  (x, σ', χ')` corresponds to `exec m (MState (wm_regs σ) (wflat …)
  (wm_dev σ))`. That single bridge transfers EVERY existing exec-level leaf;
  racy sites (the lock word, `started`) drop to the weak arm, which is
  exactly the design's split. Do that before porting any leaf by hand.
- Axiom footprint: `view_at_intro`/`view_at_elim`/`view_at_split`,
  `wpt_load_rule`, `wpt_store_rule`, `wpt_load_vprop`, `wpt_store_vprop`,
  `wpt_wread_word`, `wpt_wwrite_byte` are ALL **closed under the global
  context** — the vProp layer adds nothing, not even the 5 platform axioms
  (it never touches `try_step`).

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
  pointwise floor order) — see design doc Decision 5. **VALIDATED at M2a**
  (`WeakView.view`): the scalar/map pair is exactly `(w_vrNew, w_coh)`, so
  `flr (ws_view ws) a = w_vrNew ws ⊔ coh ws a` is `reflexivity` and
  `ws_le → ⊑` is three lines; a points-to needs only `view_byte a t` and a
  release will need only `view_scl t`. No quotient was needed.
- Forward-bank view: store-time `w_vwNew` vs 0 (both sound; pick the one
  that never surfaces in leaf statements).
- Whether `wp_dead`/corpse arms and the power thread need any view plumbing
  at all (expected: no — they never read memory).
- Where the MMIO/ifetch/walker declared assumptions live so
  `proof_coverage.py`/`Print Assumptions` surface them honestly.
