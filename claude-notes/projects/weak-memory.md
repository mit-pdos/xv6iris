# Project: weak memory (RVWMO) — staged worklist

Design: [`design/weak-memory.md`](../design/weak-memory.md) (PROPOSAL).
Branch: `weak-memory`. Landed: M0 (`iris/WeakMem.v`, `iris/WeakLitmus.v`),
M1a (`iris/WeakInterp.v` + fwd-bank wire-in), M1b (`iris/WeakLang.v`),
M1c (`iris/WeakGhost.v`, `iris/WeakExec.v`, `iris/WeakAdequacy.v`),
M2a (`iris/WeakView.v`, `iris/WeakVProp.v`),
M2b (`iris/WeakBridge.v`, `iris/WeakFence.v`, + `ws_bounded`),
M3a (`iris/WeakInstr.v`), M3b (`iris/WeakStore.v`, `iris/WeakCert.v`,
`iris/WeakLock.v`, `iris/WeakStarted.v`), M3c (`iris/WeakAcquire.v`, the
`wstep_cert` Q-type fix, `WeakCert`'s effect-trace certificates),
M4-prep (`iris/WeakFunnel.v`, `iris/WeakEff.v`, `iris/WeakBranch.v`,
`iris/WeakRacy.v`, `iris/WeakWord8.v`),
the WIDTH GENERALIZATION (`WeakStore.winsw` & co., `WeakInstr`'s `_w`
family — see the block below), **M4 batch 0a** (`iris/WeakEffSkel.v`),
**batch 0b** (`WeakPmpEff.v`, `WeakTickEff.v`, `WeakFetchEff.v`,
`WeakFetchRvc.v`), **batch 1** (`WeakLeafEff8.v`, `WeakLeafEff8s.v`,
`WeakLeafBase4.v`, `WeakLeafAmo4.v`, over the shared
`WeakLeafEffCommon.v`), and **batch 2's first leaf**
(`iris/WeakLeafLd8.v`, the `ld`-class 8-byte load, end to end) — whose two
funnel seams have since been fixed, so its 472-line/3.1× figure IS the
sweep's unit price.
**M3 and M4-prep are DONE.**  Next: M4's remaining leaves — read
[`weak-memory-porting.md`](weak-memory-porting.md) first (§2g is the leaf
recipe at its post-fix shape), then the batch blocks below.

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
- [x] **M2b — the pinned-fragment transfer bridge, the fence frontier and
      the AMO read half** (`WeakBridge.v` / `WeakFence.v`, + `ws_bounded` in
      `WeakMem`/`WeakInterp`/`WeakGhost`/`WeakExec`): DONE, with cuts (see
      the block below). NOT done, and deliberately deferred: the `↦w₈`/`↦w₄`
      multi-byte towers and the `↦ₛ` string family (M4-adjacent, no design
      content), and the fetch/`instr`/decode restatement onto `wpt_img` —
      which the bridge SUPERSEDES for the exec-level library (the decode
      lemmas transfer as-is; only the WP-level `instr` resource still has to
      be restated, at M3/M4).

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

### What M2b established (read before M3)

- **Inventory**: `WeakBridge.v` 686 lines / 2.7 s, `WeakFence.v` 414 lines /
  2.1 s (both new); `WeakMem.v` +187, `WeakInterp.v` +93,
  `WeakGhost.v` +19/−6, `WeakExec.v` +19/−3, `WeakAdequacy.v` +3 (all
  `ws_bounded`). Everything in `WeakFence.v` and every bridge lemma is
  **closed under the global context** — the vProp/view layer still adds no
  axiom; only the PoC transfer, which mentions the model's `execute`,
  inherits the usual rv64d platform axioms.
  `weak_system_adequacy`'s footprint is byte-identical before and after.

- **THE BRIDGE IS `WeakBridge.v`, AND ITS OBJECT IS `wflat_st`.**
  `wflat_st σ := MState (wm_regs σ) (wflat (wm_img σ) (wm_log σ)) (wm_dev σ)` —
  registers and devices are literally the same objects, memory is the
  coherent flat projection. Two directions, BOTH proved, over the same
  run predicate:
  - `exec_of_wexec_pinned : pinned_exec tid m σ → wlog_wf (wm_log σ) →
    wexec tid m χ σ = Some (x,σ',χ') → exec m (wflat_st σ) = Some (x, wflat_st σ')`
    — **the consumption direction**, and the one M3's leaves need: inside
    `wp_wexec_step`'s ∀-oracle continuation a leaf is HANDED a `wexec` fact
    at an oracle it did not choose, and this turns it into an `exec` fact
    that the leaf's EXISTING library lemma pins by `exec`'s functionality.
  - `wexec_of_exec_pinned : … → exec m (wflat_st σ) = Some (x,t') →
    ∃ χ σ' χ', wexec tid m χ σ = Some (x,σ',χ') ∧ wflat_st σ' = t'` — the
    **reducibility** direction, which discharges the same rule's
    `∃ χ σ0 χ'` premise out of the exec witness the leaf already carries.
  - `wexec_pinned_agree` packages both against ONE `exec` fact and is what
    a leaf actually applies: "the machine can step, and however it steps,
    the value, the registers, the devices and the flat memory are the SC
    ones". The TIMESTAMPS still vary; nothing observable does.
  - `wexec_pinned_wlog_wf` re-establishes `wlog_wf` for the next
    instruction. (`wlog_wf` is currently a threaded premise, NOT a state-
    interpretation conjunct — see the cuts.)
- **THE PINNED PREDICATE'S FINAL SHAPE.**
  `pinned_read σ a := latest_ts (wm_log σ) a ≤ w_vrNew (wm_ws σ) ⊔ coh (wm_ws σ) a`
  — the hart's own logical index (`WeakVProp.ws_view`/`WeakView.flr`) covers
  the latest write to the byte. Three ways a read is pinned, and taking ALL
  THREE is what makes the bridge worth having:
  (1) the ACCESS KIND forces it — `ak_coh` (fetch/walker) or `ak_latest`
  (every exclusive/AMO read half), whose admissibility condition IS
  `WeakMem.latest`. **So an `amoswap` read transfers with NO ownership and
  no view hypothesis at all**;
  (2) the byte is OWNED at the hart's index (`WeakBridge.wpt_pinned_read`:
  `wpt_at` + `wlat_lookup` + `latest_val_ts`, six lines);
  (3) the byte was NEVER WRITTEN this era (`latest_ts = 0`, so
  `pinned_read_unwritten` closes it) — **all kernel text and rodata, hence
  the whole fetch/decode path, for free** (`wpt_img_pinned_read`).
  `wpt_pinned_acc` converts an owned `n`-byte footprint into the read arm's
  whole obligation.
- **`pinned_exec` is a `Fixpoint` over the monad in `wexec`'s own shape**
  (the `mchoice_free` idiom), collecting per-ACCESS: `acc_wf` (wrap-freedom
  of the range) and, only where `ak_pins ak = false`, pinnedness of the
  read footprint. Its recursive successors are the CANONICAL ones (reads at
  `coh_ts`); `wread_pinned_ts` is what says the actual run cannot use any
  others. NOTE for M3: a leaf must discharge BOTH `pinned_exec` and
  `WeakExec.wexec_covers` (via `mchoice_free`) over the peeled instruction —
  the same peel, done twice. Merging them into one predicate is the obvious
  future cleanup.
- **WRAP-FREEDOM IS NOT BUREAUCRACY.** `wflat` is `Arch.pa`-keyed and the
  log is `Z`-keyed, so a message that wraps the address space is genuinely
  not described by `wflat` (`wflat_lookup` needs `wlog_wf`). `acc_wf pa n :=
  pa_z pa + n ≤ 2^64` is discharged from `RiscvPtsto.addr_is_ram`. The
  WRITE arm needs no wrap side condition for the memory correspondence
  itself — `z_pa (acc_addr pa j) = pa_add pa j` is UNCONDITIONAL (both sides
  wrap identically), and `bytes_map`'s insert chain IS `write_bytes`' foldr —
  only `wlog_wf` for the NEXT access needs it.
- **PROOF OF CONCEPT: `wexec_execute_ITYPE_ADDI` is one `apply` of
  `wexec_pinned_agree` over `ExecCommon.exec_execute_ITYPE_ADDI`.** No view
  reasoning, no re-peeling of the model, no new proof about the instruction.
- **`ws_bounded` (WeakMem) IS the enabler of VA-based transfer**: every view
  a hart holds is a real timestamp of the current log —
  `ws_bounded ws n := the five scalars ≤ n ∧ (∀ a, coh ws a ≤ n) ∧ (∀ a tv,
  w_fwd ws !! a = Some tv → tv.1 ≤ n ∧ tv.2 ≤ n)`. Three things to know:
  it is stated over a NAT bound (always used at `length log`, and monotone
  in it, which is what the non-stepping harts need after a log append);
  **the FORWARD-BANK conjunct is not optional** — `fwd_view` puts a banked
  view into a load's post-view, so without it `load_post` would not preserve
  boundedness; and the payoff is the one-line `ws_bounded_scl`.
  `WeakInterp.wrun_ws_bounded` is the preservation theorem (+ the
  `wexec_ws_bounded` corollary), and it lands in BOTH state interpretations:
  `⌜∀ c, ws_bounded (wgws g c) (length (wglog g))⌝` as the SECOND conjunct of
  `weak_state_interp` — deliberately after `⌜wgen_pin g⌝`, because the three
  device rules destruct only the first conjunct and pass the rest along as
  one hypothesis, so they compiled unchanged — and
  `⌜ws_bounded σ.(wm_ws) (length σ.(wm_log))⌝` as the FIRST conjunct of
  `wmstate_interp`. Only `wp_wrun_step` had to be reproved (+19/−3: hand the
  fact out, and on the way back re-establish it for the stepping hart from
  the continuation and for every other hart by `ws_bounded_mono` over
  `wrun_log_app`); `wp_wexec_step` and the device rules needed nothing.
  Two gotchas found doing it: stdpp's `Forall_cons` (the biimplication)
  fails to elaborate under `apply … in` here (*"Unable to find an instance
  for the variable x"*) — use `Forall_cons_1`; and `Forall_lookup_total_2`
  cannot resolve its `Inhabited` instance in `WeakInterp.v`, so go through
  `Forall_lookup_2` + `list_lookup_total_correct`.
- **THE FENCE MODALITY IS A DISCIPLINE OPERATOR, NOT A vProp CONNECTIVE,
  AND THAT IS A FINDING.** `WeakInterp.barrier_post` with `rw,rw` moves the
  hart's index to `acq_view ws := View (vrNew ⊔ vrOld ⊔ vwOld) (w_coh ws)`
  — EXACTLY: `ws_view (fence_post ws true true true sw) = acq_view ws` is
  `reflexivity`. But `vrOld`/`vwOld` are NOT part of the `biIndex`
  (`WeakView.view = (vrNew, coh)`), so "the frontier" is not a function of
  the index and `∇ P` cannot be a `vProp → vProp`. iRC11 pays for a real
  `∇` with a THREE-view index (cur/acq/rel); that upgrade is deferred.
  Delivered instead: `vwp_acq P ws := monPred_at P (acq_view ws)` at the
  `vwp_hold` altitude, with `vwp_acq_fence`/`vwp_acq_barrier` (the rule),
  `vwp_acq_intro` (a `P @@ V` with `V ⊑ acq_view ws` enters), the
  structural laws, and the pred-R-only twin `acq_view_r`. **Δ is NOT a
  modality here**: promise-free, a predecessor-W fence constrains nothing,
  and what the writer side actually needs is the timestamp-domination
  LEMMA — `ws_view_store_dom`/`release_deposit`.
- **THE HANDOFF, in two lemmas, is the M3 skeleton** (`WeakFence.v` §5):
  `release_acquire_transfer : ws_bounded ws_r (length log) →
   vwp_hold P ws_r ⊢ vwp_hold P (load_post_at ws_a true vpre a' (S (length log)))`
  (the spinlock: whatever the releaser held at its index when its store took
  the log's fresh top, the acquirer holds after an acquire-AMO that reads
  that timestamp — no invariant, no ghost state, no fence), and
  `release_fence_transfer` (the same through a plain read plus a succ-R
  fence — the `started`/MP shape, premise `S (length log) ≤ w_vrOld ws_a`,
  which `load_post_vrOld_nofwd` supplies). Both are pure view arithmetic
  over `release_deposit` (writer) and `amo_acq_gain` (reader).
- **THE AMO READ HALF NEEDS NO VIEW.** `wamo_read_latest` : `ak_latest ak =
  true → wbyte_ok σ ak a t' b → wlat_interp -∗ wlat_pointsto a dq t v -∗
  ⌜t' = t ∧ b = v⌝` — the element pins the value AND the timestamp with no
  hypothesis about the reader, so the rule fires off an element held in an
  INVARIANT (elements are `iProp`s, hence objective), which is the
  M3-relevant form. `wpt_amo_read` is the owned restatement;
  `amo_acq_gain : view_scl t ⊑ ws_view (load_post_at ws true vpre a t)` is
  the index gain — note the SCALAR, which is the entire difference between
  an acquire and a plain load (`load_byte_gain` gives only `view_byte a t`),
  and the reason the release deposit is a scalar view.
- **CUTS (from the bottom of the M2b list, as instructed):** the `↦w₈`/`↦w₄`
  multi-byte towers and `↦ₛ` (item 3) — no design content, M4-adjacent
  bookkeeping over `wpt_wread_word`; `wlog_wf` as a state-interpretation
  conjunct (it is a threaded premise with a preservation lemma —
  `wexec_pinned_wlog_wf` — so nothing is unprovable, but M3 will probably
  want it next to `ws_bounded`); and the three-view `biIndex` upgrade that
  a genuine `vProp`-level `∇`/`Δ` pair would need.

## M3 — vertical slice (the interface test) — **DONE** (M3a/M3b/M3c)

- [x] **M3a — the weak instruction-leaf layer** (`iris/WeakInstr.v` 800 lines /
      9.1 s; + the two M2b-queued cleanups): DONE, with cuts (see the block
      below).  Scope delivered: the merged peel `wstep_ok`, `wlog_wf` in both
      state interpretations, the flat-lookup resource bridge, `↦w₄`,
      `wkernel_text`, the per-instruction step CERTIFICATE `wstep_cert`, the
      instruction rule `wp_winstr`, the four leaves' P/Q pairs and their
      resource-side lemmas (load, store/release-deposit, the amoswap acquire
      in its INVARIANT form, fence), and two leaf-composition smoke tests.
- [x] **M3b — the vertical slice** (`WeakStore.v` 435 / `WeakCert.v` 505 /
      `WeakLock.v` 353 / `WeakStarted.v` 194 lines; 6.7 / 3.1 / 3.3 / 1.9 s):
      DONE, with cuts (see the block below).  The `↦w₄` store-window update,
      the `wstep_cert` discharge (as a SINGLE instruction-independent
      theorem — see below), the lock library core (objective `wlock_inv`,
      `wis_lock`, `wlocked`, acquire/release cores) and the started escrow.
- [x] **M3c — closing the vertical slice** (`iris/WeakAcquire.v` NEW;
      `WeakInstr.v`/`WeakCert.v`/`WeakLock.v`/`WeakStarted.v` touched):
      the `wstep_cert` Q-type fix, the WP-level composition of the lock
      (acquire + spin loop + release), the `started` setter, and a
      two-instruction smoke test.  See "What M3c established" below.
- [ ] One lock-client cone re-proven unchanged-in-statement. **TARGET
      CORRECTED (2026-08 tier audit)**: the original candidate kinit/kfree
      is at the SCONF (S-mode) tier — 42 distinct `wp_*_s_sconf` leaves,
      every instruction through `WpSmodeIntr.wp_instr_s_sconf`, whose fetch
      IS the page-table walk; it consumes ZERO M-mode leaves, so batch 2
      does not unblock it. Its specs thread `sie_cap_gpr`, which smuggles
      `stack_own` (a mechanical `↦w₈` respell) and `strans_inv`, whose KPT
      arm names `tlb_res_pt` — whose weak twin is batch-6 P4. The kinit
      cone is therefore the VALIDATION CAPSTONE OF BATCH 6c, not an M4
      item. The correct vertical slice for the M-mode stack is the
      `_entry`→`start` boot cone (`WpEntryNew.v` — the sole SC consumer of
      the M-mode memory leaves; straight-line M-mode, module-shaped).
- [x] Porting guide written from what the slice taught:
      [`weak-memory-porting.md`](weak-memory-porting.md); refined at M3c with
      the composition/mask pattern (§2b), the `Q`-half recipe (§2c) and the
      racy-load finding (§3).

### What M3a established (read before M3b)

- **Inventory**: `iris/WeakInstr.v` (new, ~800 lines / 9.1 s);
  `WeakBridge.v` +150 (§11, the merged peel); `WeakGhost.v` +2,
  `WeakExec.v` +3, `WeakAdequacy.v` +2 (all `wlog_wf`).  Full build green.
  `proof_coverage.py --check`, `lemma_diff.py`, `spec_vacuity.py` all clean.
  **Axiom footprint**: everything that does not mention `riscv_step` —
  `wexec_leaf_agree`, `wwp_lw4`, `wwp_amoswap_w_aq_inv`, `wwp_fence_deliver`,
  `wwp_release_deposit`, all the bridges — is **closed under the global
  context**; `wp_winstr` carries exactly the 5 rv64d platform axioms, and
  `weak_system_adequacy`'s footprint is byte-identical to M2b's.

- **THE PEEL IS MERGED, AND THE MERGE IS ALSO A WEAKENING.**
  `WeakBridge.wstep_ok` = `pinned_exec` with the `Choose` arm turned from
  `True` into `False`.  It is strictly WEAKER than `pinned_exec ∧
  mchoice_free`: `mchoice_free`'s memory arms quantify over EVERY possible
  read result, whereas on the pinned fragment `wread_pinned_ts` forces the
  run's timestamps to the canonical ones, so choice-freedom is only needed
  along the successors `wstep_ok` already speaks about
  (`wrun_wexec_wstep_ok`).  ONE lemma consumes it:
  `wexec_leaf_agree tid m s x0 t0 : wstep_ok → wlog_wf → exec m (wflat_st s) =
  Some (x0,t0) → wexec_covers ∧ reducibility ∧ (∀ oracle, value/regs/dev/flat
  agreement ∧ `wlog_wf` of the successor)`.

- **`wlog_wf` IS NOW A STATE-INTERPRETATION CONJUNCT**, third in
  `weak_state_interp` (after `wgen_pin`, `ws_bounded` — the device rules
  destruct only the first and were unaffected) and second in
  `wmstate_interp`.  Unlike `ws_bounded` its preservation is NOT a theorem
  about `wrun` (a wrapping write is genuinely not `wflat`-describable), so it
  is passed OUT to the caller and taken back from the caller's re-established
  interpretation — which a leaf discharges from its own peel via
  `wexec_leaf_agree`.  Only `wp_wrun_step` needed touching (+3 lines).

- **THE CONFIG-TOWER VERDICT: REUSABLE AS-IS, and nothing had to move.**
  `hw_config`, `mmode_config`, the sconf bundles and `kmap_static_claims` are
  conjunctions of REGISTER points-to, pure facts and ghost state — `iProp`s
  over `riscvGS`, which the weak side carries unchanged — and
  `wmstate_interp σ` contains `reg_interp (wm_regs σ)` with
  `wm_regs σ = sregs (wflat_st σ)`, so `reg_valid`/`reg_valid_dq`/`reg_update`
  apply verbatim and the exec-facts they feed are facts about a state whose
  registers ARE the weak hart's.  Embedded into `vProp` they are objective by
  `embed_objective`: no view plumbing anywhere.  The ONLY non-transferring
  lemmas are the ones that consume `RiscvPtsto.mstate_interp` AS A BUNDLE
  (`fetch_from_instr_bytes`, `instr_lift`, `dispatchInterrupt_none_from_regs`,
  `state_interp_reg_dq`, `wp_instr`), because that bundle contains
  `gen_heap_interp`; each is a mechanical restatement with the memory
  hypothesis taken as the pure fact §1 of `WeakInstr.v` produces.

- **THE RESOURCE→FLAT BRIDGE IS ONE LINE OF CONTENT**: a `γlat` element says
  its byte's LATEST write is `(t,v)` and `WeakLang.wflat_latest` says the flat
  projection holds the latest write, so an element AT ANY TIMESTAMP determines
  the flat byte — `wlat_flat_lookup`, with no hypothesis about the reader's
  views.  Corollaries: `wpt_flat_lookup` (owned), `wpt_img_flat_lookup_gen`
  (also returns `latest_ts = t`), `wpt4_flat`.  This is what makes the whole
  fetch/decode side a statement about `wflat_st`.

- **`wkernel_text bs := [∗ map] a↦b ∈ bs, wlat_pointsto (pa_z a) □ 0 b`** —
  an `iProp`, i.e. objective and unconditionally shareable; `wkernel_text_v`
  is the `wpt_img`-spelled `vProp` twin and `wkernel_text_at` identifies them
  at any `ws`.  `wkernel_text_flat` gives the two facts a fetch reduction
  takes (the flat byte, and `latest_ts = 0`), and `wkernel_text_pinned` turns
  a window of text into the `pinned_read` obligation for free.

- **`↦w₄` (`wpt4 a dq w`)**: 4-alignment ∗ `acc_wf a 4` (wrap-freedom —
  carried IN the bundle, because it is what lets `acc_wf_byte` convert between
  the log's `Z` key `acc_addr a j` and the flat map's `pa_add a j` wherever
  the bundle is) ∗ four explicit `↦w` bytes at `acc_addr a j`.  Deliberately
  NOT a `big_sepL`: the four-fold `∗` makes every extraction a `destruct j as
  [|[|[|[|]]]]` and dodges the `big_sepL`/`monPred_at` elaboration traps.
  With `wpt4_split`/`wpt4_agree`/`wpt4_flat`/`wpt4_pinned`/`wpt4_mono`.

- **THE INSTRUCTION RULE, AND THE ONE THING THAT DID NOT TRANSFER.**
  `wp_winstr Φ pc P Q` takes `gen_id = 0`, `acc_wf pc 4`, a
  `wstep_cert (fin_to_nat cpu_id) pc P Q`, and a callback that — given
  `wmstate_interp σ` — returns `PC = pc`, the text-pinnedness of the four
  fetch bytes, `P σ`, and the SAME `exec` facts today's
  `wp_exec_step_decode_execute_inv` takes but **over `WeakBridge.wflat_st σ`**
  (both tick values), plus a continuation over `(tick, σ')` receiving
  `wstep_post σ σ'` and `Q σ (wm_ws σ')`.  `wstep_post` is the successor
  contract: registers/devices/flat memory are the SC ones, the image is
  unchanged, the log only grew, **`ws_le (wm_ws σ) (wm_ws σ')`** (this is what
  `vwp_hold_mono` consumes, so every untouched resource crosses for free), and
  `wlog_wf`/`ws_bounded` are re-established.
  **THE GAP, and it is the honest one:** `wstep_ok` for the WHOLE
  `riscv_step tick` is a STRUCTURAL peel of `try_step`/`run_hart_active`/
  `fetch`/decode/`execute` — the same walk `RiscvExec.exec_riscv_step_hart_active`
  and `RiscvFetchExec.exec_hart_active_progress` do for `exec`, and of the same
  size (it needs an `execR`-level analogue and mirrors of the three
  `exec_fetch_*` reductions).  There is no way around it: pinnedness is
  per-ADDRESS, so the read footprint must be identified structurally, and no
  state-level condition weaker than "my view covers the whole log" implies it.
  It is therefore PACKAGED as a per-instruction pure obligation of the same
  nature as a decode fact — `wstep_cert cid pc P Q` — whose hypotheses (`PC =
  pc`, text unwritten, `P σ`) the resource-side lemmas discharge, and whose
  second component `Q` also carries the instruction's WEAK-MEMORY EFFECT (that
  the fence really moved the index, that the acquire really took the read
  timestamp).  **Building the certificates for concrete instructions is the
  first task of M3b or an M3a follow-up**; `wstep_cert_mono` is the
  contravariant/covariant weakening.

- **THE FOUR LEAVES**, as `P`/`Q` pairs plus their resource-side lemmas:
  - `lw`/`ld` (4-byte): `wP_load ea = acc_wf ea 4 ∧ ∀ j<4, pinned_read σ
    (acc_addr ea j)`, `Q = wQ_none`.  `wwp_lw4` : from `wlat_interp` and
    `vwp_hold (wpt4 ea dq w) (wm_ws σ)` — `⌜wP_load ea σ ∧ ∀ j<4, wflat … !!
    pa_add ea j = Some (nth_byte w j)⌝`, i.e. the peel obligation AND the
    premise `exec_execute_LOAD_*` takes, verbatim.  `wwp_lw4_carry` frames the
    word across the step.
  - `sw`/`sd`: `wP_mem ea = acc_wf ea 4` (a store has no read to pin),
    `wQ_store ea σ ws' = ∀ j<4, S (length (wm_log σ)) ≤ flr (ws_view ws')
    (acc_addr ea j)`.  **The store's timestamp is `S (length (wm_log σ))` and
    it is visible to the caller because `σ` is** — no `Q` needed to expose it.
    `wwp_release_deposit R σ : ws_bounded (wm_ws σ) (length (wm_log σ)) →
    vwp_hold R (wm_ws σ) ⊢ monPred_at R (view_scl (S (length (wm_log σ))))` is
    the composition `release` needs (the objective payload for the invariant);
    `wwp_sw4_post` is the byte-view form.
  - `amoswap.w.aq`, INVARIANT FORM — `wwp_amoswap_w_aq_inv R σ ws' ea dq t w`:
    `wlog_wf → acc_wf ea 4 → wQ_amo_aq ea σ ws' → wlat_interp -∗ wlat4 ea dq t w
    -∗ monPred_at R (view_scl t) -∗ ⌜wP_mem ea σ⌝ ∗ ⌜∀ j<4, wflat … !! pa_add ea
    j = Some (nth_byte w j)⌝ ∗ ⌜view_scl t ⊑ ws_view ws'⌝ ∗ vwp_hold R ws'`.
    `wlat4` is a bare four-element bundle of `wlat_pointsto`, i.e. an `iProp`,
    i.e. OBJECTIVE — so it lives in the lock invariant, and the rule fires off
    it with NO ownership and NO view hypothesis about the acquirer (the read
    half is `ak_latest`, whose admissibility condition IS `WeakMem.latest`).
    The `⌜…⌝`s are the peel obligation and the SC premise; the last conjunct
    is the THAW of whatever the releaser deposited at `view_scl t`.
  - `fence`: `wP_none`, `wQ_fence b σ ws' = ws_le (barrier_post (wm_ws σ) b)
    ws'`.  `wwp_fence_deliver` : `vwp_acq R (wm_ws σ) ⊢ vwp_hold R ws'` for
    `rw,rw`; `wwp_fence_scl` : an assertion deposited at a scalar view the
    hart has READ (`t ≤ w_vrOld`) is delivered; `wwp_fence_rw_w` for the
    release kind (promise-free, it carries no read-side content — the
    writer's content is `wwp_release_deposit`).  The two kernel kinds
    instantiate directly; full `barrier_kind` genericity was CUT.

- **CUTS**, from the bottom as instructed (the amoswap invariant form was
  never at risk): (i) the `↦w₄` UPDATE across a store — a 4-byte message needs
  `WeakGhost.wlat_agree_store` generalised from one byte to a window, which is
  ~40 lines of `<[…]>`-chain bookkeeping and is the first thing to add;
  (ii) the fence leaf's full kind-genericity; (iii) the smoke test is at the
  LEAF-COMPOSITION altitude (`wwp_smoke_sw_fence` = release-deposit then
  fence, `wwp_smoke_amo_lw` = acquire-thaw then carry) rather than a literal
  double `wp_winstr` application; (iv) `wstep_cert`'s discharge (above).

- **WHAT M3b CONSUMES.** Re-proving `acquire`/`release` needs: (a) a
  `wstep_cert` per instruction of the two functions — the outstanding work;
  (b) the lock invariant holds `∃ t v, wlat4 lk □/frac t v ∗ R @@ view_scl t`,
  which is objective because `wlat4` is an `iProp` and `@@` is objective by
  construction; (c) `acquire` = `wwp_amoswap_w_aq_inv` (thaws `R` at the
  acquirer's index) + `wwp_lw4` for the spin re-read; (d) `release` =
  `wwp_release_deposit` at `S (length (wm_log σ))` (the store's timestamp),
  put back into the invariant; (e) the `started` handoff = `wwp_release_deposit`
  on the writer and `wwp_fence_scl` on the reader
  (`WeakMem.load_post_vrOld_nofwd` supplies the `t ≤ w_vrOld` premise);
  (f) every register/config resource is unchanged in statement.

### What M3b established (read before M4)

- **Inventory**: four NEW files, nothing existing touched.
  `iris/WeakStore.v` 435 lines / 6.7 s (the `↦w₄`/`wlat4` store-window
  update), `iris/WeakCert.v` 505 / 3.1 (the step certificate),
  `iris/WeakLock.v` 353 / 3.3 (the lock), `iris/WeakStarted.v` 194 / 1.9 (the
  handoff).  Full build green; `proof_coverage.py --check`, `lemma_diff.py`,
  `spec_vacuity.py` clean.  **Axiom footprint**: `wstep_ok_confined`,
  `wacquire_core`, `wrelease_core`, `wlat4_store`, `wpt4_store` and every
  other lemma that does not mention `riscv_step` are **closed under the
  global context**; only `wstep_cert_conf`/`_none` (which do) carry the 5
  rv64d platform axioms.  `weak_system_adequacy`'s footprint is unchanged.

- **THE `wstep_cert` PEEL DOES NOT HAVE TO BE WALKED, AND THIS IS THE M4
  PRICING DATUM.**  M3a estimated the per-instruction peel at the size of
  `exec_riscv_step_hart_active` + `exec_hart_active_progress_base_gen` + the
  three `exec_fetch_*` mirrors, plus an `execR`-level analogue — i.e. a
  four-figure line count of model walking, per instruction.  That is wrong.
  `WeakBridge.wstep_ok`'s content is entirely "WHICH BYTES does this step
  touch", and `RiscvExec.exec`'s RAM read arm RETURNS `None` on a byte the
  memory map does not contain.  So **run the SC interpreter on a memory
  RESTRICTED to the instruction's window** and every read of the run is
  inside that window by construction; writes are confined by the domain of
  the FINAL memory (`exec_dom_mono`: memory only grows along a run); the
  restriction agrees with the real memory, so the confined run IS the real
  run; and a `Choose` is impossible because `exec` is stuck there — which
  discharges the `wexec_covers` half of the merge for free.
  `WeakCert.wstep_ok_confined` is that theorem (one induction, the shape of
  `WeakBridge.exec_of_wexec_pinned`), and `wstep_cert_conf_none` is it
  packaged: **for EVERY instruction at every pc, the `wstep_ok` half of the
  certificate holds under one predicate, `wP_conf`.**  Shared skeleton: 505
  lines / 3.1 s, ONCE.  Per-instruction marginal cost: the window `W` (the
  text word + the data word), plus the leaf's OWN SC library lemma
  instantiated at a SECOND state whose memory is `wmem_restrict σ W` —
  ~20–40 lines, no model reduction, no `vm_compute`, nothing new about the
  instruction.  Wrap-freedom (`acc_wf`) comes from the window for free
  (`acc_wf_window`: a wrapping range passes through address 0, and RAM does
  not contain it).

- **WHAT THE CERTIFICATE STILL CANNOT GIVE, and why it is not a shortcut.**
  `wstep_cert`'s second component `Q` — the instruction's WEAK-MEMORY EFFECT
  (the `.aq` raised the scalar floor; the fence moved the index; the store
  appended THIS message) — is invisible to `exec`, which ignores access kinds
  and barriers entirely.  No semantic argument over `exec` can produce it, so
  it stays a per-instruction ISA obligation of the same nature as a decode
  fact — but only the three sync instructions have one worth stating, and a
  plain load or ALU instruction takes `wQ_none`, where the certificate is
  UNCONDITIONAL.

- **CORRECTION TO M3a'S INTERFACE: `wstep_cert`'s `Q` must be
  `wmstate -> wmstate -> Prop`, not `wmstate -> wstate -> Prop`.**  Found by
  the release core, and it is not about views at all: the lock invariant OWNS
  the lock word's latest-write ELEMENTS, and any step that writes those bytes
  invalidates them, so re-establishing `wmstate_interp σ'` requires
  RETARGETING them at the message the step appended — i.e. the certificate
  must say WHICH message that was, which is a statement about `wm_log σ'`.
  `wstep_post` says only `∃ l, wm_log σ' = wm_log σ ++ l`, so a STORE leaf
  built on `wp_winstr` as it stands is unprovable.  The fix is one type, after
  which `wQ_store`/`wQ_amo_aq` become `WeakLock.wstore_eff`/`wamo_eff` and
  `wp_winstr`'s proof is unchanged apart from passing `σ'` instead of
  `wm_ws σ'`.  The M3b cores are stated at the post-fix shape, so landing it
  is a substitution, not a re-proof.

- **THE LOCK, AS LANDED.**  The invariant is kept ENTIRELY AT THE `iProp`
  ALTITUDE (the Cosmo pattern) and the `vProp` surface appears only in the
  payload:

      wlock_inv γ lk R := ∃ st t v, wlat4 lk (DfracOwn 1) t v ∗ lock_auth γ st ∗
                            ( ⌜st = None⌝ ∗ ⌜v = 0⌝ ∗ lock_frag γ None ∗
                              monPred_at R (view_scl t)
                            | ⌜st ≠ None⌝ ∗ ⌜v ≠ 0⌝ )
      wis_lock γ lk R := ⎡inv wlockN (wlock_inv γ lk R)⎤   (persistent AND objective)
      wlocked γ i     := ⎡WpLock.locked γ i⎤               (today's token, verbatim)

  Objectivity is free three times over: `wlat4` is an `iProp` (M3a),
  `monPred_at R V` is objective by construction for ANY `vProp` `R`, and the
  ghost state is `WpLock`'s own `excl_auth` — so `lockG`, `lock_state`,
  `lock_auth/frag` and all four transition lemmas are REUSED, not cloned, and
  a client's holder token is unchanged in statement.  **The number that links
  the two halves is the timestamp**: the payload is frozen at `view_scl t`
  with `t` the timestamp `wlat4` carries, the releaser deposits at the
  timestamp its own store takes (`wwp_release_deposit`, resting on
  `ws_bounded`), and the acquirer's `amoswap.w.aq` reads THAT timestamp and
  gains `view_scl t ⊑ ws_view` — so the thaw is one `monPred_mono` and no
  view ever crosses the invariant boundary.
  Kept: the lock WORD, the ghost layer, the holder token, the transfer of
  `R`.  Deferred (M4 bookkeeping, no design content): the `lk->cpu` and
  `lock_name` fields, both 8-byte cells needing the `↦w₈` tower M2b cut — so
  `lock_state` only ever takes `None` and `Some (i, true)` here, and the
  intermediate state is passed through by composing `WpLock`'s own two
  transitions.

- **THE CONTENDED ARM OF THE ACQUIRE IS NOT A NO-OP ON THE WEAK STATE.**
  `amoswap` writes 1 back even when it read 1, so the invariant's elements are
  retargeted at the new message in BOTH arms — which is why the bundle is held
  at FULL fraction in the invariant and why `WeakStore.wlat4_store_gen` is
  needed on the acquire path and not only on the release path.

- **THE STARTED ESCROW NEEDED ONE THING THE SC VERSION DID NOT.**  The writer
  is structurally identical to the release (deposit at the store's own
  timestamp, retarget the elements) and the reader is `wwp_fence_scl` over
  `load_post_vrOld_nofwd`.  But a PLAIN load may read a stale message, so "I
  read a nonzero flag" does not identify WHICH message was read; the escrow
  therefore carries `wstarted_oneshot` (every non-clear write to the byte is
  the setter's message, the era image holding the flag clear), which is
  preserved by every append that does not write the byte —
  `wstarted_oneshot_app`.  The payload is persistent, as today, and for the
  same reason (up to NCPU−1 readers take a copy).

- **CUTS**, from the bottom as instructed: (i) the spin-loop composition (the
  iLöb over `wp_winstr`) — the single-step cores are the floor and they
  landed; (ii) the WP-level composition of the cores THROUGH `wp_winstr` (they
  are stated at the `σ`/`σ'` altitude `wp_winstr` hands a leaf, and the `Q`
  type correction above must land first); (iii) the lock's `cpu`/`name`
  fields; (iv) the certificate's `Q` half for the four concrete instructions
  (the `wstep_ok` half is discharged for ALL instructions at once, which is
  the part that was estimated as expensive).

### What M3c established (read before M4)

- **THE Q-TYPE FIX COST 40 LINES AND BROKE NOTHING** (item 1).
  `wstep_cert`/`wp_winstr`/`wstep_cert_conf`/`wstep_cert_of_conf` now carry
  `Q : wmstate → wmstate → Prop`; `wp_winstr`'s proof changed by one token.
  The view-level predicates the LEAF lemmas consume are now spelled `wV_fence`
  / `wV_store` / `wV_amo_aq` / `wV_load` (the old `wQ_*` statements, renamed),
  and the certificate-level `wQ_fence` / `wQ_store tid ea v` /
  `wQ_amo_aq tid ea v` / `wQ_load` / `wQ_none` are built on them.
  `WeakLock.wstore_eff`/`wamo_eff` MOVED to `WeakInstr` under those names —
  they always were the certificate's `Q`. Files touched: `WeakInstr.v` (+93/−36),
  `WeakCert.v` (2 signatures), `WeakLock.v` (−2 definitions), `WeakStarted.v`
  (2 renames). **The lesson generalises: put the instruction's whole
  weak-memory effect in `Q`, and keep the view-only part as a separate
  predicate the leaf lemmas take.**

- **THE `Q` HALF IS AN EFFECT-TRACE PROBLEM, AND THAT MAKES IT ONE THEOREM
  PLUS ARITHMETIC** (item 2; `WeakCert.v` 505 → 1160 lines / 4.2 s).  The
  route that works is the confinement trick's twin: INSTRUMENT the SC
  interpreter with the trace of its memory effects (`exec_eff`, an arm-for-arm
  mirror of `RiscvExec.exec` emitting `WEread`/`WEwrite`/`WEbar`), and prove
  once that under the SAME confinement premises the weak successor's log AND
  views are the FOLD of that trace over the pre-state
  (`wstep_eff_confined`, ~195 lines; `wstep_ok_confined` is re-derived from it
  with a byte-identical statement).  Then:
  - **the two halves of the certificate MERGE into one per-instruction
    obligation**, `WeakCert.wP_eff tid es σ` = "`wlog_wf`, and the confined run
    succeeds with trace `es`" — strictly stronger than the old `wP_conf`, of
    exactly the same NATURE (an `exec`-level fact at a second state whose
    memory is `wmem_restrict σ W`), and it is the only thing a leaf still owes;
  - **every `wQ_*` is then view arithmetic over a 2- or 3-element list.**
    `wcert_fence` is 6 lines, `wcert_store` 13, `wcert_load` 14,
    `wcert_amo_aq` 30 — plus ~60 lines of shared helpers (`fence_post_mono`,
    `barrier_post_mono`, `load_post_run_gain`).  **That is the M4 per-sync-
    instruction price for the `Q` half: well under an hour each.**
  - **EVERY instruction's trace begins with the FETCH read** (rv64d emits
    `Read_plain` for instruction fetch, so it is an ordinary weak read that
    raises views), and the certificates leave it generic in kind/address/width
    so a compressed 2-byte fetch instantiates them unchanged.
  - `wcert_amo_aq`/`wcert_load` need `ak_coh … = false` as well as
    `ak_sync = true`: with `ak_coh` set, `wread_post` is the IDENTITY and the
    view gain is simply false.  Both hold for every `AK_explicit`, i.e. for
    everything rv64d emits.
  - **What was tried and does NOT work** (record, so it is not re-tried):
    deriving the appended message from the SC successor's memory.  `mem t'`
    pins the final VALUE of every byte but not how many messages wrote it; a
    domain-growth argument only sees writes to bytes absent from the confined
    map, so it can never exclude a value-preserving write to the TEXT — which
    is exactly what would invalidate the `wkernel_text` elements.  Something
    structural about the run is genuinely required, and `exec_eff` is the
    cheapest structural thing that is not a model walk.

- **THE COMPOSITION IS `iris/WeakAcquire.v` (618 lines / 5.9 s), AND IT WENT
  THROUGH WITH NO NEW MACHINERY** — every M3b core applied as stated. What it
  contains, and the four moves that recur, is written up as §2b of the porting
  guide; the statements are `wwp_acquire_swap` (one `amoswap.w.aq` at a
  caller-supplied pc + certificate, `wis_lock`'s invariant opened at ⊤ and
  held across the `▷`), `wwp_spin_loop` + `wwp_acquire_loop`,
  `wwp_release_store`, `wwp_started_set`, `wwp_fence_step`, and the smoke test
  `wwp_release_seq` (`fence rw,w ; sw` as two `wp_winstr` applications).
  **§9 then re-states the four rules with the certificate DISCHARGED**
  (`wwp_acquire_swap_cert` / `wwp_release_store_cert` /
  `wwp_started_set_cert` / `wwp_acquire_loop_cert`, over `WeakCert`'s
  `wcert_amo_aq` / `wcert_store`), so per instruction nothing is left but the
  `exec_eff` fact inside the caller's own σ-callback.
  Three things worth carrying forward:
  - **`wmstate_rest` is the right seam.** A racy leaf borrows exactly ONE
    conjunct of the state interpretation — `wlat_interp` — and the caller
    keeps and updates the other six with the SC register tower it already has.
  - **The shared word must be read out of the invariant's ELEMENTS BEFORE the
    step** (`wlat4_flat_gen`, no view hypothesis), because the caller's `exec`
    fact is a statement about `wflat_st σ` and can only be supplied at a known
    word. The post-step branch is then on the same `v`.
  - **The spin loop has NO weak-memory content**: a failed `amoswap` leaves
    `⌜v ≠ 0⌝` and no resource, so the loop is the plain Löb rule
    `□ (K -∗ ▷ (K -∗ WP) -∗ WP) -∗ K -∗ WP` over the `▷` every `wp_winstr`
    provides. The retry edge (the branch instructions, which have no weak leaf
    yet) is a premise; when the branch leaves land, the body becomes
    `attempt ; branch` and the loop's statement does not change.

- **THE ONE THING THAT DID NOT COMPOSE, AND IT IS A RULE-LEVEL GAP:
  `wp_winstr` CANNOT RUN A RACY PLAIN LOAD**, so the `started` WAITER's `lw`
  is out of reach (its setter and its fence are done). The rule rests on the
  pinned-fragment bridge, whose read arm demands that the hart's index already
  cover the latest write to every byte read; a waiting hart legally reads the
  era image while `wflat_st σ` already holds the setter's 1, so no `exec` fact
  about the flat projection describes the step. **The AMO is unaffected** —
  its read half is `ak_latest`, whose admissibility condition IS "read the
  latest" — which is exactly why the spinlock composes and the escrow's reader
  does not. What is needed is a load rule quantifying over the ADMISSIBLE READ
  RESULTS (one `exec` fact per admissible value; two for a one-shot flag),
  over `WeakExec.wp_wrun_step` — the primitive lifting rule, which has no
  bridge premise. Recorded in `WeakAcquire.v`'s closing note and in the
  porting guide §3.

- **`tools/spec_vacuity.py` NEVER SCANNED A `Weak*.v`** (M3b's suspicion,
  confirmed): it took no arguments and looked only for `Definition …_body` in
  `Spec*.v`/`Wp*.v`/`Code*.v`, so the entire weak layer — whose contracts are
  plain lemmas — sat outside a run that still reported CLEAN. Patched: file
  arguments + a `--lemmas` mode that scans top-level statements; the default
  run is byte-identical to the old one, and `--lemmas iris/Weak*.v` is clean.
  Hygiene from now on: `tools/spec_vacuity.py --lemmas iris/Weak*.v` per batch.

- **WHAT SHIPPED FOR THE SMOKE TEST, AND WHAT DID NOT** (item 4).  Shipped:
  `WeakAcquire.wwp_release_seq`, the FALLBACK altitude — `fence rw,w ; sw` as
  two `wp_winstr` applications meeting with no adapter, the first step's
  successor being the second's pre-state.  NOT shipped: the two-hart
  `weak_system_adequacy` Example.  It is blocked by the same residue as
  everything else — the theorem's premise is `WP (LoopE gen_id c) {{_, True}}`
  per hart, which cannot be proved for a concrete hand-assembled program until
  that program's instructions have their `exec_eff` facts, i.e. until the
  first M4 batch. Nothing about adequacy itself is in the way (its footprint
  is unchanged and its premises are the same ones M1c validated).

- **M4 READINESS.  Missing before the sweep can start, in order:**
  (i) the weak analogue of the per-instruction FUNNEL — `wp_instr_s_sconf` /
  `wp_exec_step_decode_execute_inv_priv` restated over `wflat_st σ` (the five
  bundle-consuming lemmas M3a listed; everything else in the config tower
  transfers verbatim), because every leaf goes through it;
  (ii) the `exec_eff` instantiation per instruction shape — the SC library
  lemma re-run at the instrumented interpreter, which is the ONLY remaining
  model work and the thing to price first on a real leaf;
  (iii) the BRANCH leaves (`bnez`/`j`), which cost `wQ_none` and turn
  `wwp_acquire_loop`'s retry-edge premise into a proof;
  (iv) the racy-load rule for `started` (above);
  (v) the `↦w₈` tower (M2b's cut), needed for the lock's `cpu`/`name` fields
  and for every 8-byte kernel cell.

- **Axiom footprint unchanged**: every WP-level lemma of `WeakAcquire.v` —
  including `wwp_spin_loop`, which mentions no instruction but does mention
  the WP of `weak_riscv_lang`, whose `prim_step` reaches `riscv_step` —
  carries exactly the 5 rv64d platform axioms and nothing else;
  `wmstate_interp_split` (no WP) is closed under the global context.
  `weak_system_adequacy`'s footprint is byte-identical to M3b's.

## M4-prep — the five M3c readiness items — **DONE** (one cut, below)

Branch `weak-memory`.  Five NEW files, nothing existing touched:

| item | file | lines / single-file compile |
|---|---|---|
| (i) the weak per-instruction FUNNEL | `iris/WeakFunnel.v` | 807 / 8.1 s |
| (ii) the `exec_eff` toolkit | `iris/WeakEff.v` | 809 / 3.0 s |
| (iii) the BRANCH leaf + the real-shape acquire loop | `iris/WeakBranch.v` | 252 / 2.3 s |
| (iv) the RACY-LOAD rule | `iris/WeakRacy.v` | 994 / 3.4 s |
| (v) the `↦w₈` tower | `iris/WeakWord8.v` | 752 / 20.6 s |

Full `make -f CoqMakefile -j16` green; `proof_coverage.py --check`,
`lemma_diff.py`, `spec_vacuity.py` and `spec_vacuity.py --lemmas iris/Weak*.v`
all clean.  No `Admitted`/`admit`/new `Axiom`.

### What M4-prep established (read before the sweep)

- **THE FUNNEL IS `WeakFunnel.wwp_instr`, AND THE PIECE WORTH REUSING IS THAT
  THE FETCH LEMMA IS NOW PURE.**  `InstrBytes.fetch_from_instr_bytes` consumed
  `mstate_interp` for exactly two things — `reg_valid` on registers, and
  turning `↦ₓ` byte ownership into `mem !! pa = Some b` — so restated over
  pure register lookups plus pure byte/`addr_is_ram` facts
  (`WeakFunnel.exec_fetch_flat`, all three alignment arms) it has no Iris in
  it at all and serves both tiers; the `kmap_static`/`text_ident_phys` VA→PA
  machinery DISAPPEARS, because weak addresses are already physical.  The
  other four bundle-consumers M3a listed are then trivial
  (`dispatchInterrupt_none_from_regs` and `state_interp_reg_dq` are `reg_valid`
  against `reg_interp`; `instr_lift` and `wp_instr` are the funnel).
- **`winstr` REPLACES `instr`, AND THE DECODE FACTS TRANSFER VERBATIM.**
  `InstrBytes.instr` cannot be reused: its `instr_bytes` half is gen_heap
  ownership (the weak `riscvGS` heap gname is an unused placeholder) and its
  decode field is a wand over `mstate_interp`.  `WeakFunnel.winstr` keeps the
  decode field as a plain `Prop` over an arbitrary `mstate` — which is what
  every existing decode lemma already proves — and replaces the bytes with
  timestamp-0 `wlat_pointsto` text elements, i.e. an `iProp`: objective,
  persistent, and `pinned_read` for free (`winstr_pinned`, via
  `pinned_read_unwritten`).  **The footprint is always the FOUR bytes of one
  word**, even for a compressed instruction, because `wp_winstr`'s
  text-pinnedness obligation is over the four-byte window; that deletes the
  2-byte RVC case from both `fetch_flat_ok` and `winstr_bytes` and is free for
  kernel text.
- **THE FUNNEL OWNS THE WRAPPER AND THE REGISTER BOOKKEEPING; A LEAF STILL
  OWES ONE `execute` FACT.**  Two things are forced and are worth knowing
  before writing a leaf: (1) `wp_winstr` demands the `exec` fact at the state
  the WEAK machine holds, so the `minstret_increment` pre-write is INSIDE the
  run and the leaf's execute fact is instantiated at
  `set_reg (wflat_st σ) (R_bool minstret_increment) b` with `b` funnel-chosen
  — free, since every SC execute lemma is state-generic; (2) the two register
  facts about `s_exec` that the SC funnel reads off `mstate_interp s_exec` are
  NOT premises here, because the weak funnel holds those ghost cells itself.
  The seam is `wmstate_norg` (`wmstate_rest` minus `reg_interp`).
- **THE sconf TIER DOES NOT TRANSFER, AND THE REASON IS THE PAGE-TABLE WALK.**
  `WpSmodeIntr.wp_instr_s_sconf`'s fetch is `SmodeCorePt.tlb_inv_pt_fetch`,
  which consumes AND RETURNS `mstate_interp` as a bundle, opens the kpt tree
  invariant, walks the page table and may write A/D bits back.  Four things
  it needs, none of them a restatement: (a) the kernel-page-table invariant at
  the weak altitude, with the walk's footprint PINNED — and PTE bytes are
  written this era (`kvminit`), so `pinned_read_unwritten` does NOT apply and
  the tree invariant has to carry views or the PTEs have to become a one-shot
  escrow like `started`; (b) a decision on the A/D writeback — either prove
  the walk write-free (the kernel PTEs have A/D preset), after which
  `WeakEff.wcert_*_gen`'s write-free surroundings apply verbatim, or give it a
  `Q`; (c) three extra PTE words per translated access in the confinement
  window `W`; (d) the `mstate_interp`-in/out shape restated as
  `wlat_interp`-in/out.  What is NOT a problem: the S-mode fetch returns a
  CHANGED state (`tlb`), and the weak assembly already supports that
  (`exec_hart_active_progress_base_gen` takes `s_f ≠ s`).
- **THE GENERAL exec→exec_eff LEMMA LANDED, AND IT IS THE EMPTY-MEMORY
  DETECTOR.**  `exec_exec_eff` (M3c) only gives `∃ es`, which is useless: the
  `wQ_*` arithmetic needs the trace.  `WeakEff.exec_eff_quiet_of_empty` is the
  usable one — **`exec` fails on an absent byte and GROWS the domain on a
  write, so a program that completes at the EMPTY memory with an empty final
  domain performed no RAM access of positive width**, and (by the memory frame
  `exec_eff_mem_frame`) it then runs identically at any memory with the same
  QUIET trace.  Obtaining it is one `apply` of the SC library lemma one
  already has, at `MState rs ∅ d`.  **So the decoder, every register-only
  `execute` (branch/jump/ALU) and every memory-free sub-call (`pmpCheck`,
  `translateAddr`, `within_clint`, `currentlyEnabled`) are FREE at `exec_eff`
  — no mirroring, no model walk.**
- **WHAT THE DETECTOR CANNOT SEE IS A ZERO-WIDTH ACCESS, AND THAT IS HONEST.**
  A zero-width read reads nothing and a zero-width write writes nothing, so
  neither is visible to `exec` and no argument over `exec` can exclude one.
  `weff_quiet` therefore ADMITS them and `wQ_quiet` is stated to tolerate them
  (they append a message that writes no byte, which changes no latest write:
  `wlat_interp_quiet_app`).  The strict predicate `nowrite_trace` and
  `wQ_pure` are what the store/AMO certificates need, and the gap between them
  is exactly the zero-width residue — which a SYNTACTIC bind-peel avoids
  entirely, since those arms simply are not in the program.
- **THE MIRRORING COST WAS MEASURED, NOT ESTIMATED.**
  `WeakEff.exec_eff_bind_nil`/`_bind0_nil` are drop-in replacements for
  `RiscvExec.exec_bind_Some`/`exec_bind0_Some` (every register step has an
  empty trace), and `WeakEff.exec_eff_riscv_step_hart_active` is
  `RiscvExec.exec_riscv_step_hart_active` — the whole `try_step` wrapper —
  replayed line for line: **65 lines of SC script became 68, in 45 seconds of
  wall time including two failed compiles.**  Differences: the lemma names,
  and three `app_nil_r`/`cbn` adjustments where the trace concatenates.
- **THE CERTIFICATES NO LONGER PIN THE FETCH ELEMENT BY ELEMENT.**
  `WeakEff.wcert_fence_gen` / `_store_gen` / `_load_gen` / `_amo_aq_gen`
  surround the instruction's own access with ARBITRARY WRITE-FREE traces:
  reads and barriers only raise views and leave the log alone, and all four
  `wQ_*` are monotone in exactly that direction.  `wcert_nowrite` /
  `wcert_quiet` are the memory-effect-free certificates.
- **A BRANCH IS NOT `wQ_none`.**  It performs no memory access, but a leaf
  must give the state interpretation back, and `wlat_interp` says every
  latest-write element is still the latest write — unprovable from
  `wstep_post`'s `∃ l, log' = log ++ l`.  The branch's `Q` is `wQ_pure` (image
  and LOG unchanged, views grew) or `wQ_quiet`; both are free from
  `wcert_nowrite`/`wcert_quiet`.  `WeakBranch.wwp_branch_step` is
  `WeakAcquire.wwp_fence_step` with the effect predicate ABSTRACTED, so one
  rule serves the branch, the jump and every ALU instruction.
- **THE REAL-SHAPE ACQUIRE LOOP IS `WeakBranch.wwp_acquire_loop_real`**
  (`amoswap.w.aq` at `pca`, branch at `pcb`), with two persistent premises of
  one instruction each — the attempt, whose failure arm hands back the loop
  head's resources one instruction later, and the retry edge.  **The Löb
  induction did not change, and the reason generalises: the LATER the loop
  spends is the AMO's own `wp_winstr` later, stripped inside the AMO's
  continuation, which is where the branch runs — so the branch's own later is
  never needed for the induction.**  Adding an instruction to a loop body
  therefore never changes the loop's shape.
- **THE `↦w₈` TOWER WAS MOSTLY INSTANTIATION, AND IT EXPOSED THREE
  GENERALISATIONS.**  `WeakStore.wlat_agree_store_win` was already
  window-generic.  What was not is stated generically in `WeakWord8.v` (and
  is a recommended follow-up refactor of the width-4 files, not yet applied):
  `winsw` (WeakStore's `wins4` family is its `n := 4` instance);
  `wP_load_w`/`wV_store_w`/`wQ_store_w`/… (WeakInstr's whole P/V/Q family
  hardcodes the 4 in its BODY — six lemmas prove the width-4 originals are the
  `n := 4` instances ON THE NOSE, so the refactor is a rename plus a notation
  with no call-site churn); and `wpt_byte_flat_pin`/`wlat_byte_flat_gen`, the
  one-byte argument that `wpt4_flat`, `wpt4_pinned`, `WeakLock.wlat4_flat_gen`
  and `WeakInstr.wwp_amoswap_w_aq_inv` each open-code four times.
- **Axiom footprints.**  `wwp_instr` is **byte-identical to
  `InstrBytes.wp_instr`** (the 5 rv64d platform axioms + the funext already in
  `MinstretInv`'s cone) — no new axiom.  `exec_fetch_flat` carries one of the
  five.  `exec_eff_quiet_of_empty`, the whole `↦w₈` tower and everything else
  that does not mention `riscv_step` is **closed under the global context**;
  `wcert_nowrite`/`wcert_store_gen`/`wcert_amo_aq_gen`,
  `wwp_acquire_loop_real` and `wwp_branch_step_cert` carry exactly the 5
  platform axioms.

- **THE RACY-LOAD RULE IS `WeakRacy.wp_wracy_load`, AND ITS ∀-ORACLE SURFACE
  IS ONE BINDER.**  `wstep_ok_racy` generalises `WeakBridge.wstep_ok` at one
  designated window: a RAM read DISJOINT from it keeps `wstep_ok`'s arm
  (pinned, canonical successor), a read of EXACTLY the window drops pinnedness
  and quantifies over every admissible timestamp list, and partial overlap is
  `False`.  `exec_of_wrun_racy` is then "for the run that happened there EXISTS
  an admissible `w` such that the SC correspondence holds at the flat memory
  PATCHED at the window with `w`" — reads outside the window still agree
  because the patch only touches the window, and writes are disjoint from it so
  the patch commutes.  **The caller's PRE-step obligation is its ordinary
  `exec` fact about `wflat_st σ`** (reducibility is built at the canonical,
  hence pinned, value, where the patch is the identity); only the continuation
  sees `∀ w, ⌜wadm σ rak ra rn w⌝ -∗ …`, and for a one-shot flag
  `wadm_two_valued`/`wadm_started_lw4` collapse that to `w = 0 ∨ w = 1`.
  Three things to know before using it: (a) a RAM WRITE BEFORE the racy read is
  forbidden by a phase bit — transporting admissibility back across an
  intervening write needs "the appended messages do not write the window"
  reasoning, whereas without one the pre-racy states differ only in VIEWS and
  the transport is ten lines (an `lw`'s trace is `[fetch; data read]`, so
  nothing is lost, and writes AFTER the racy read are supported); (b) the
  bridge needs "the window is readable at all" for its `Ret` case — a run that
  never takes the racy read must still exhibit SOME admissible `w`, and the
  canonical one is it; (c) disjointness is stated ARITHMETICALLY on `pa_z`,
  never as `gset` disjointness (`set_solver` does not terminate on a
  `gset Arch.pa`).
- **THE ONE CUT: `wwp_started_wait`, AND IT IS BLOCKED ON THE ESCROW, NOT ON
  THE RULE.**  The collapse needs `WeakStarted.wstarted_oneshot`, which
  `wstarted_at` does not carry — latest-write ELEMENTS pin the latest message,
  not the absence of an earlier non-clear one — and which, being a statement
  about the whole log, cannot be a persistent pure fact: it has to become a
  conjunct of the escrow INVARIANT with a preservation step
  (`wstarted_oneshot_app` is that argument's byte-level half).  That is a
  change to `WeakStarted.v` and is the first thing to do before
  `ProofMainSecondary`.  Also open: `WeakCert`'s confinement machinery does not
  yet produce a `wstep_ok_racy`, so `WeakRacy.wracy_cert` is a per-instruction
  premise the way `wstep_cert` was before `WeakCert`.

### The WIDTH GENERALIZATION (landed after M4-prep; read before adding a width)

M4-prep found three families that were the `n := 4` instances of width-generic
statements ON THE NOSE.  They are now generalized, with the GENERIC statement
primary and both widths as instances — measured call-site churn **ZERO** (every
downstream `Weak*.v` compiled unchanged, including the ten `rewrite /wQ_store`-
style sites, because a `Definition wQ_store … := wQ_store_w 4 …` is a delta
step the same tactics see through).

- **`WeakStore.winsw a T v n mm`** — the `n`-fold window insert, with
  `winsw_lookup_in` / `_out` proved once by induction, and
  `wlat_agree_store_w` (the store window's pure part at every width) over it.
  `wins4 := winsw a T v 4` and `WeakWord8.wins8 := winsw a T v 8`; both
  `wlat_agree_store4` / `_store8` are one `apply` each.
- **`WeakInstr.wpt_byte_flat_pin` / `wlat_byte_flat_gen`** — the ONE-BYTE
  flat/pinned bridges at an arbitrary access width.  Every N-fold bundle lemma
  is N one-line applications of one of them (`wpt4_flat_pin` — new, the merged
  pass — `wpt8_flat_pin`, `wlat4_flat_gen`, `wlat8_flat_gen`,
  `wwp_amoswap_w_aq_inv`'s inner block).
- **`WeakInstr`'s whole `P`/`V`/`Q` family** is now `wP_load_w` / `wP_mem_w` /
  `wV_store_w` / `wV_amo_aq_w` / `wV_load_w` / `wQ_load_w` / `wQ_store_w` /
  `wQ_amo_aq_w`, all taking `n : N`; the width-4 names are `_w 4` and
  `WeakWord8`'s width-8 names are `_w 8`.  `WeakWord8.wP_load_w_4` & co. are
  kept as `reflexivity` regression checks.

**WHAT STAYS WIDTH-SPECIFIC, and why** (do not "fix" these):
- the BUNDLES (`wlat4`/`wpt4` vs `wlat8`/`wpt8`).  They are deliberately N
  explicit `∗`s, not a `big_sepL` or a fold, so that byte extraction is
  `destruct j as [|[|…]]` with no `Φ` to elaborate.  A width-generic bundle
  would have to be a fixpoint and would then NOT be convertible to either
  instance (`emp ∗ …` and the associativity differ), so every proofmode
  pattern in four files would churn — the exact opposite of a clean shape;
- the ALIGNMENT conjunct (`is_aligned_paddr (Physaddr a) 4` vs `8`): it is the
  model's own per-width access check, carried inside the bundle;
- the store PRIMITIVES (`wlat4_store_prim` / `wlat8_store_prim`), which perform
  N `ghost_map_update`s over the bundle's N explicit elements.
- `wpt4_pinned` is deliberately NOT routed through the merged
  `wpt4_flat_pin`: pinnedness needs no `wlog_wf`, and a leaf that owes only
  the peel should not have to produce the log's well-formedness for it.
  (`WeakWord8.wpt8_pinned` still carries the premise; harmless, unused.)

### WHAT M4 STILL OWES (the shared `exec_eff` skeleton)

The one thing M4-prep did NOT build, and the only remaining model work.
**ALL FOUR ITEMS ARE NOW DONE** (1 and 2 at batch 0, 3 at batch 0b, 4 —
partly — at batch 1); the list is kept because its per-item estimates are
what the batch-0b/1 blocks below correct, and the correction is the durable
lesson:

1. `execR_eff` — the early-return interpreter instrumented, plus its ~8
   rewriting lemmas (`execR_eff_bind`/`_bind0`/`_liftR`/`_returnR`/
   `catch_early_return`).  `RiscvTryStep.execR` is a separate `Fixpoint` from
   `exec`, and `run_hart_active`'s reductions all go through it.  ~200 lines.
2. `exec_eff_hart_active_progress_base_gen` / `_RVC_gen` — mirrors of
   `SmodeCore`'s, ~40 lines each, replayed with the kit.
3. `exec_eff_fetch_done` / `_fetch_bytes_4` / `_mem_read_fetch` — the one
   place the fetch's `WEread` is emitted.  Everything under it (`pmpCheck`,
   `translateAddr`, `within_clint`/`_sig`/`_htif`, `currentlyEnabled`) is
   memory-free and therefore FREE via the detector; only the `MemRead` arm is
   explicit.  ~100–150 lines.
   → **WRONG ON BOTH COUNTS, and this is the correction to keep.** The
   detector is NOT usable there (it gives `quiet_trace`, the certificates
   need `nowrite_trace` — the zero-width residue), so `pmpCheck` and friends
   all had to be mirrored; and the *transitive* cone is what costs. Actual:
   **1867 lines** (batch 0b), of which the named chain itself was ~250, as
   estimated.
4. Per instruction SHAPE (not per call site), the memory-touching `execute`
   mirrored: the memory-free prefix by the detector, the one `MemRead`/
   `MemWrite` arm explicit.  ~40–60 lines each, ~9 shapes (LOAD/STORE at
   1/2/4/8 and the AMO).
   → same correction: the `vmem_read`/`vmem_write` cone under an `execute`
   is not detectable either, so a shape is **≈ 700 lines**, not 40–60.

Total ≈ 400–600 lines of shared skeleton plus ≈ 450 of per-shape mirrors, at
the measured replay rate of ≈ 1.05× the SC script's lines.
→ **the replay RATE was about right (measured 1.03–1.14× on scripts); the
LINE COUNTS were 4–10× low, because they priced the script in front of the
author rather than the transitive cone of lemmas it names.**

### What M4 BATCH 0 established (read before batch 1)

`iris/WeakEffSkel.v`, **834 lines / 3.9 s**.  Items 1 and 2 of the list above
are DONE; items 3 (the fetch) and 4 (the per-shape `execute` mirrors, = batch
1) are not, and the block below is what was learned pricing them.

- **`execR_eff` IS A SEPARATE FIXPOINT AND ITS KIT IS THE EXPENSIVE PART.**
  `execR` (RiscvTryStep) differs from `exec` in one arm — `ExtraOutcome`, the
  early return, which is a VALUE and carries the trace so far — so the
  instrumented twin cannot be an instance of `exec_eff`.  Landed:
  `execR_eff`, `execR_eff_execR` / `execR_execR_eff` / `execR_eff_None`,
  `execR_eff_bind` / `_bind0` and their UNCONDITIONAL equations
  `execR_eff_bind_eq` / `_bind0_eq`, `execR_eff_returnR`, `execR_eff_liftR`,
  `exec_eff_catch_early_return`, and the six forward forms
  (`_bind_cat` / `_bind_nil` / `_bind0_cat` / `_bind0_nil` / `_liftR_cat` /
  `_liftR_seq`).  `_nil` is the drop-in replacement for
  `execR_bind_Some` / `execR_bind0_Some` / `execR_liftR_seq`; `_cat` is for
  the one sub-run per instruction that touches memory.
- **THE REPLAY RATE IS NOT ONE NUMBER, and M4-prep's 1.05× is right only for
  the SCRIPTS.**  Measured here:
  - the two `run_hart_active` progress mirrors: **36 → 24 and 35 → 21 SC
    lines (0.65×)** — a replayed script gets SHORTER, because the SC runs of
    `cbn match` collapse into the trace-carrying equations;
  - the `execR` interpreter + kit: **78 → ~300 SC lines (3.8×)** — a mirrored
    INTERPRETER is much more expensive than a mirrored script, because the
    trace turns each unconditional equation into a case analysis and each
    rewriting lemma needs a `_cat` (trace-concatenating) and a `_nil`
    (trace-free) form side by side.
  **Rule for the rest of the sweep: price a mirrored SCRIPT at ~0.7× and a
  mirrored INTERPRETER/DEFINITION at ~4×.**
- **THE ASSEMBLY IS `exec_eff_riscv_step_base` / `_rvc`,** and it is the shape
  a leaf meets: given the fetch's and the `execute`'s `exec_eff` facts (plus
  the same register/config premises `WeakFunnel.wwp_instr` already collects),
  the whole step's trace is `es_fetch ++ es_execute` and nothing else
  contributes.  **So batch 1's per-shape deliverable is exactly "the
  `execute`'s `exec_eff` fact", with no plumbing above it.**
- **THE COMPLETENESS CHECK PASSED, WITH ONE HONEST RESIDUE.**
  `wcert_load_via_skeleton` / `_store_` / `_amo_aq_` re-derive `WeakCert`'s
  three certificates AT THE TRACE THE SKELETON PRODUCES — `es_f ++ es_x` at
  `es_f := [fetch read]` and `es_x := [the data access(es)]` is the
  certificates' own 2-/3-element list ON THE NOSE (`app` of singletons), so
  the two halves meet with no adapter and no peeling.  **Verdict: batch 2 is
  mechanical FOR THE TRACE JOIN and for the `Q` half; it is NOT yet
  mechanical end-to-end, because `wP_eff` still needs the two model
  reductions below.**
- **EXACTLY TWO THINGS STAND BETWEEN THE ASSEMBLY AND `wP_eff`** (written up
  in `WeakEffSkel.v` §6b):
  1. **the FETCH's own `exec_eff` reduction.**  This is unavoidable and the
     argument is worth keeping: `WeakEff`'s empty-memory detector does NOT
     apply (the fetch reads the text, so it fails at `∅`), and a
     domain-growth argument cannot exclude a value-preserving write to a byte
     the confined map already has — M3c's finding, at the fetch.  It is a
     syntactic replay of `exec_fetch_done` → `exec_fetch_bytes_4` →
     `exec_mem_read_fetch` → `exec_checked_mem_read_ram` →
     `exec_read_ram_plain_4` (≈ 110 SC lines for the 4-aligned `F_Base` path,
     ≈ 75 mirrored at 0.7×), **plus** the register-only sub-lemmas that chain
     names — `exec_translateAddr_identity` (14 SC lines) and its three
     `returnM` twins, `exec_pmpCheck_machine_unlocked_ifetch4` (11, over the
     much larger `exec_pmpCheck_machine_unlocked`),
     `exec_pmaCheck_ram` (20), `exec_currentlyEnabled_Ziccif` +
     `exec_hartSupports_Ziccif` (18), `within_clint_false` / `_sig_` /
     `_htif_` (24), and `or_boolM`/`and_boolM` eff variants (≈ 20).
     **Estimate: 250–350 lines for the 4-aligned `F_Base` arm alone**; the
     three other arms of `WeakFunnel.exec_fetch_flat` (2-aligned `F_Base`,
     `F_RVC` at 4 and at 2) roughly double it if all four are wanted, and
     for M-mode kernel text only the 4-aligned `F_Base` and the two `F_RVC`
     arms are actually reachable.
  2. **the `tick_clock` mirror** (`exec_riscv_step_tick` over
     `MinstretInv.exec_tick_clock`), which turns the assembly's
     `riscv_step false` fact into the `∀ tick` shape `wstep_conf_eff` asks
     for.  Register-only, so its trace is `[]`; ≈ 25 lines.
- **WHY EVERY REGISTER-ONLY SUB-LEMMA HAS TO BE MIRRORED RATHER THAN
  DETECTED — the zero-width residue, and it decides the whole shape.**  The
  detector (`exec_eff_quiet_of_empty`) gives `quiet_trace`, which ADMITS
  zero-width writes; `WeakEff.wcert_store_gen` / `_load_gen` / `_amo_aq_gen`
  need `nowrite_trace`, because a zero-width write still APPENDS a
  (byte-less) message and `wQ_store`'s `wm_log σ' = wm_log σ ++ [msg]` is
  then false.  Weakening the certificates to "up to `qmsgs`" was considered
  and REJECTED: the store's timestamp shifts by the length of the quiet
  prefix, so `wQ_store` would have to name the timestamp existentially and
  the change ripples through `WeakLock`/`WeakAcquire`/`WeakStarted`/
  `WeakStore` — a strictly uglier spec for a residue the model never
  exhibits.  **So: register-only sub-runs in a bind spine get a mirrored
  lemma with an EMPTY trace; the detector is for whole `execute`s that touch
  no memory at all (branch/jump/ALU), where `wQ_quiet` is the right `Q`
  anyway.**  Record this before re-deriving it.
- **A MIRROR FILE MUST IMPORT `iris.proofmode` EVEN WITH NO IRIS IN IT.**
  Every SC script in this cone uses ssreflect's space-separated
  `rewrite a b c` and `rewrite H /=`; without the import those are syntax
  errors reported at the `/=` (a five-minute trap).  Two smaller ones:
  stdpp's `by` does not parse inside `try (…; by tac)` in such a file (use
  `; tac; reflexivity`), and `mword` must be spelled
  `SailStdpp.Values.mword` (the durable notes' instance-leak rule).

### What M4 BATCH 0b established (read before batch 2)

Batch 0b is **DONE**: `iris/WeakPmpEff.v` (358 lines / 2.3 s),
`iris/WeakTickEff.v` (397 / 2.2 s) and `iris/WeakFetchEff.v` (1112 / 5.3 s).
`WeakEffSkel` §6b's two missing facts are both landed, and so is the recipe
they unlock.

- **THE FETCH'S TRACE IS ONE ELEMENT, AND THE MODEL DECIDES WHICH.**
  `WeakFetchEff.wak_plain = AkInfo false false false`: rv64d emits
  `AK_explicit {| variety := AV_plain; strength := AS_normal |}` for an
  instruction fetch — **not `AK_ifetch`** — so the fetch is an ORDINARY weak
  read that RAISES VIEWS (`ak_coh = false`), not a coherent one. The design
  doc's "instruction fetch is declared coherent" is about the *intended*
  model; the *generated* one does not say so, and every `WeakCert`
  certificate quantifies over the fetch's `akinfo`, which is why nothing
  breaks. Do not "fix" the certificates to pin `AK_ifetch`.
- **WHICH FETCH ARMS SHIPPED: the two 4-ALIGNED ones.** `F_Base` at a
  4-aligned pc (`WeakFetchEff` §4, `wP_eff_of_leaf_base`) and `F_RVC` at a
  4-aligned pc (`iris/WeakFetchRvc.v`, 405 lines, `wP_eff_of_leaf_rvc4`) —
  i.e. every instruction, compressed or not, whose pc is 4-aligned. **The
  compressed arm was nearly free (405 lines, of which ~130 is the `Ext_Zca`
  probe and ~90 the recipe), because a 4-aligned fetch reads the whole
  32-bit word whatever the instruction turns out to be: it reuses
  `exec_eff_fetch_bytes_4` unchanged and its trace is the SAME single
  element.** Every certificate in `WeakFetchEff` §9a therefore applies to it
  verbatim.
  **STILL NOT COVERED, and it is the whole remaining gap: the two 2-ALIGNED
  arms.** A pc that is 2- but not 4-aligned performs TWO 2-byte reads
  (`exec_fetch_F_Base_2` / `exec_fetch_RVC_2`), so its trace has two
  elements and a leaf over it needs a THREE-element `wcert_*` family that
  does not exist. Cost to add: ≈ 200 lines for the two arms (the width-2
  memory chain, `exec_read_ram_plain_2`, already exists) **plus** the
  3-element certificate family (≈ 120: `wcert_load`/`_store`/`_amo_aq` take
  the fetch's element as ONE `WEread akf pf nf`; generalising the prefix to
  a `nowrite_trace` list is `WeakEff.wcert_*_gen`, which already exists —
  so the real work is proving the split fetch's 2-element trace `nowrite`,
  which is immediate). **This is the first thing to do if a 2-aligned
  32-bit instruction blocks a batch-2 file.**
- **THE ACTUAL SIZE: 1112 lines for the 4-aligned arm, vs the 250–350
  estimate.** The estimate counted only the chain
  `exec_fetch_done → … → exec_read_ram_plain_4`; that part came in at ≈ 250
  as predicted (§2–§4 of the file). What it did NOT count is everything the
  chain *names*: the PMP cone had to be mirrored whole (358 lines, its own
  file), the interrupt gate `getPendingSet`/`currentlyEnabled Ext_S` cone
  (≈ 175), the `tick_clock` cone (397, its own file), and the register-only
  prefix (`translateAddr`, `pmaCheck`, `within_*`, `currentlyEnabled
  Ext_Ziccif`, ≈ 130). **Rule: when pricing a mirror, price the TRANSITIVE
  cone of named lemmas, not the script in front of you.**
- **THE DECODE FACTS TRANSFER FOR FREE, AND THIS IS THE FINDING THAT CHANGES
  BATCH 2.** `WeakEffSkel.exec_eff_riscv_step_base` wants
  `exec_eff (ext_decode w) s = Some (i, s, [])` while the decode library
  states the `exec` form — and the empty-memory detector cannot produce `[]`
  (zero-width residue). Restating the ~1220 per-word decode lemmas looked
  like the price. **It is not owed.** `WpDecodeBridge.goodb` is ALREADY a
  syntactic witness that a run performs no memory outcome — a fixpoint over
  the monad along the path the state resolves, `vm_compute`d at a concrete
  reference state (`dstateM`/`dstateS`) by every decode call site through
  `WpDecodeBridge.decode_bridge`. Its one gap is the `Barrier` arm, which
  `goodb` accepts (a barrier is read-only) but which emits a `WEbar`.
  `WeakFetchEff.goodb0` closes that arm; `goodb0_goodb` shows it is strictly
  stronger, so nothing already proved is lost; and
  `WeakFetchEff.exec_eff_decode_bridge` is `decode_state_bridge`'s twin with
  the EMPTY trace. **A leaf's decode obligation at `exec_eff` is therefore
  the same `apply` and the same two `vm_compute`s the SC leaf already does,
  plus one more `vm_compute`** (`Ltac decode_bridge_eff`). Generalise the
  lesson: *before mirroring a register-only cone, look for an existing
  syntactic read-frame witness over it* — `goodb` was written for a
  completely different purpose (the concrete-state decode bridge) and turned
  out to be exactly the certificate the trace argument needed.
- **`wP_eff_of_leaf_base` IS THE BATCH-2 RECIPE, AND IT PEELS NOTHING.**
  Premises: the window's three obligations; the M-mode config tower (the
  SAME register facts `WeakFunnel.wwp_instr` already collects); (a) the four
  text bytes IN THE CONFINED MEMORY at a 4-aligned pc; (b) the decode, in
  the shape the decode library states it (`agree_on` + `goodb0` +
  `exec (ext_decode w) dst = Some (i, dst)`); (c) the `execute`'s own
  `exec_eff` fact quantified over the `minstret_increment` flag, with its
  hart-state/flag frame and `dom (mem s_exec) ⊆ W`. Conclusion:
  `wP_eff (Some cid) ([WEread wak_plain pc 4] ++ es_x) σ`. The end-to-end
  check (`WeakFetchEff` §9) is TWO `exact`s: `wcert_load_base4` is
  `WeakCert.wcert_load` at `akf := wak_plain, pf := pc, nf := 4`, and
  `wP_load_of_leaf_base` is §8 at `es_x := [WEread akl ea 4]` — `[a] ++ [b]`
  IS `[a; b]`, so the certificate's `P` and the recipe's conclusion are the
  same term with no adapter. **Zero hand-peeling: confirmed.**
- **A `gset Arch.pa` BINDER IN A FILE THAT IMPORTS `SailStdpp.Base` IS THE
  INSTANCE TRAP** (durable notes, binder position). `WeakFetchEff` must
  import `Base` (`'b"1"` notation, `Ok`, `generic_eq`), so
  `wP_eff_of_leaf_base`'s window is spelled `(W : _)` and let
  `wmem_restrict σ W` pin the type. A `Section Context` cannot do that (it
  will not accept a hole), which is why the recipe is one `Lemma` with a
  commented premise list rather than a Section.
- **THE `Print Assumptions` FOOTPRINT GREW BY ONE, AND IT IS PRE-EXISTING.**
  `wP_eff_of_leaf_base` rests on the 5 rv64d platform axioms **plus
  `functional_extensionality_dep`** — inherited from `MinstretInv`'s
  regstate helpers (`register_set_bv64_id` / `_overwrite` update a *function*
  field), i.e. exactly the SC `exec_tick_clock`'s assumption set. Not a
  regression; anything that reaches the clock tick has always carried it.
  Sub-lemmas below the fetch carry FEWER than five (the LOAD-8 execute
  carries two; the PMP cone is closed under the global context) — the five
  arrive with `riscv_step`.

### What M4 BATCH 1 established (read before batch 2)

- **THE REPLAY RATE ON A TRACE-CARRYING SCRIPT IS ≈ 1.1×, NOT 0.7×.**
  Measured: LOAD 8 **1.14×** (263 → 299 SC proof lines), STORE 8 **1.12×**
  (286 → 319), the PMP cone **1.05×**, the tick cone **1.03×**. Batch 0's
  0.65× was measured on the two `run_hart_active` mirrors, where SC runs of
  `cbn match` collapse into trace-carrying equations; that does not
  generalise. The +10 % is structural: a trace-carrying bind must use the
  CONCATENATING form (`exec_eff_bind_Some` / `execR_eff_liftR_cat`), which
  leaves a `match` plus an `es ++ []` residue, so each lemma on the
  trace-carrying path costs one extra line. Every register-only lemma OFF
  that path replays at exactly 1.00× by name substitution.
  **Revised rule: mirrored SCRIPT ≈ 1.1×, mirrored INTERPRETER ≈ 4×.**
- **Two call-site rules for the mirror kit**, both learned by paying:
  - **prefer `WeakEff.exec_eff_bind_Some` over `exec_eff_bind_cons` for the
    ONE memory-touching bind.** `_bind_cons` pins the continuation through
    its second premise and then fails to match whenever the continuation is
    not literally `returnM` (it is usually `fun res => returnM (Ok res)`);
    `_bind_Some` reads `f` off the goal, exactly as SC `exec_bind_Some` does.
  - **`read_ram`'s mirror is the one script that is NOT a name swap.** The
    SC pins the read's value with a `run`-fact and then only has to show
    `exec ≠ None` (`discriminate`); the eff goal is a real equation, so the
    two interpreters must be peeled in LOCKSTEP (`pose proof` the SC lemma,
    run the same rewrites in `H |- *`, `destruct` the shared `read_bytes`
    scrutinee, close by `injection`; `congruence` fails on the `cast_N`
    dependency). Also: `cbn [Interface.ReadReq.pa]` alone leaves
    `Mem_read_request_pa {| … |}` unreduced, after which a `destruct` of the
    `read_bytes` scrutinee silently matches nothing — add
    `ConcurrencyInterfaceTypes.Mem_read_request_pa` / `_access_kind` to the
    `cbn` list, or grab the scrutinee from the goal with `match goal`.
- **THE DATA ACCESS KINDS, READ OFF THE MODEL** (all four traced to rv64d
  line numbers, none guessed):
  - a plain load/store (`Read_plain` / `Write_plain`) carries
    `AK_explicit {AV_plain; AS_normal}`, so `classify … = AkInfo false false
    false`. `ak_coh = false` is what `wcert_load`'s premise wants, so a plain
    leaf discharges it by `reflexivity`.
  - **`amoswap.w.aq`'s READ is `AkInfo false true true` — `ak_sync` is
    TRUE, and the acquire certificate applies.** `execute_AMO` issues its
    read as `mem_read … aq (aq && rl) true`, i.e. `(aq,rl,res) =
    (true,false,true)` at `.aq`; `read_kind_of_flags true false true =
    Read_RISCV_reserved_acquire`, whose `read_ram` arm builds
    `AK_explicit {AV_exclusive; AS_rel_or_acq}`. This is the one place where
    a "the model doesn't actually emit the ordering" surprise would have
    invalidated the whole lock proof, and it does not: `WeakCert.wcert_amo_aq`
    demands exactly `ak_coh aka = false /\ ak_sync aka = true` of the read.
  - the AMO's WRITE is `AkInfo false true false` (`Write_RISCV_conditional`
    → `AK_explicit {AV_exclusive; AS_normal}`): exclusive but NOT
    synchronising. Harmless — the certificate constrains only the read's
    kind, and the write's `ak_sync` enters only through
    `store_post_run_coh`, which is monotone in it.
- **THE SHARED `exec_eff` KIT IS `iris/WeakLeafEffCommon.v` (228 lines) —
  REQUIRE IT, DO NOT COPY IT.** Batch 1's four shape files each declared
  their own `exec_eff_returnM` / `_and_boolM_nil` / `_or_boolM_nil` /
  `_MemRead` / `_MemWrite` and their own copies of the width- and
  access-INDEPENDENT leaves (`exec_eff_rX_bits_gpr`, `_wX_bits_at`,
  `_wX_bits_gpr`, `_translationMode_M`, `_ext_data_get_addr_gpr`,
  `execR_eff_untilMT_1`, `_split_misaligned_aligned`) — 40 lemmas of
  duplication, identical modulo the `wl8_`/`wl8s_`/`wl4_`/`wa4_` prefix, and
  a fifth shape would have made a fifth copy. All of it now lives in
  `WeakLeafEffCommon`, which `WeakFetchEff` is routed through as well (it had
  four of the same lemmas, and `WeakLeafLd8` imports both cones).
  `split_misaligned` was generalised over the width while moving
  (`exec_eff_split_misaligned_aligned_w`, with the 8 and 4 spellings as
  instances, so no call site churned). Net −597/+161 across six files.
- **WIDTH IS NOT ALWAYS COSMETIC.** At width 8 a STORE's
  `subrange_vec_dec vrs2 63 0` is the whole register (`autocast_subrange_id`
  concludes `= vrs2`); at width 4 it is a genuine truncation, so the stored
  value is `subrange_vec_dec vrs2 31 0` and any `sw` WP must carry the
  truncation in its postcondition. Conversely the LOAD's sign flag is FREE
  (`LOAD (imm, rs1, rd, u, 4)` with `u` a variable), so one lemma covers `lw`
  and `lwu` — do that rather than pinning `u := false`.
- **`Read_plain` / `Write_plain` / `read_kind` ARE AMBIGUOUS** under
  `RiscvExtras` + `WeakMem` and must be spelled `rv64d_types.*`; the 8-byte
  mirrors escape it only because their import list is narrower.
- **DECOUPLING BY `exec_eff` PREMISE WORKS AND SHOULD BE THE HOUSE STYLE FOR
  PARALLEL MIRROR WORK.** Each shape file takes `pmpCheck` and the three
  `within_*` gates in their `exec_eff` form as hypotheses instead of proving
  them, exactly as the SC originals take the `exec` forms. Four agents built
  four files concurrently with no shared edit and no adapter at the seam.

### THE BATCH-2 UNIT PRICE, FINAL (read before batch 2)

`iris/WeakLeafLd8.v` is the FIRST COMPLETE WEAK LEAF — the `ld`-class 8-byte
load, from the `↦w₈` resource to `WP (Loop) {{ Φ }}` — and it exists to
produce this number. It landed at 967 lines / 43.7 s and, after the two
funnel seams below were fixed, is 791 lines / 35 s.

- **THE FINAL PRICE: 472 code lines per leaf, 3.1× the SC leaf**
  (`WpMmodeLoad.wp_ld_gpr` = 152 code lines by the same count — comments and
  blanks excluded, statements included; the batch-2 report quoted 128 for it,
  on a different count). It was **611 / 4.0×** when batch 2 landed.
  Breakdown, in the same units:

  | | at batch 2 | now |
  |---|---|---|
  | the width-generic certificate (§1) | 37 | 37 (**per FAMILY**, not per leaf) |
  | the window + its three obligations | 65 | 65 |
  | the `execute` lemma at a generic `s0` | 137 | 137 |
  | the `wP_eff` half | 102 | 102 |
  | the second replay, for the device frame | 116 | **0** |
  | the WP composition proper | 191 | 142 |
  | **per-leaf total** (all but the certificate) | **611** | **472** |

  The 65 is **exactly the porting guide's predicted 20–40 plus the membership
  lemmas**; the 137 is the SC leaf's own execute block hoisted to a generic
  `s0` (≈ 50 of which the SC leaf does inline). The genuinely new work in a
  leaf is 309 lines, half of it the WP composition.
- **SEAM 1, FIXED: the device frame.** `WeakFunnel.wwp_cb`'s continuation
  must hand back `wmstate_norg σ'`, whose `dev_interp (wm_dev σ')` conjunct
  needs to know what `wm_dev σ'` IS; `WeakInstr.wstep_post` gives only
  `wm_dev σ' = mdev t`, and `dev_interp` is an authoritative half that cannot
  be moved without its fragment. The funnel CONSTRUCTS `t` and then forgot
  it, so the leaf's only route was to re-derive the whole `riscv_step` at the
  FLAT state and identify the two successors by determinism of `exec` — 116
  lines duplicating, premise for premise, what `wP_eff_of_leaf_base` had just
  done at the confined state. `wwp_cb`'s post-step arguments now include
  **`⌜mdev t = mdev s_exec⌝`** — two `mdev_set_reg` rewrites in the funnel
  (it builds `t` out of `s_exec` by register writes only) and two lines at
  the leaf. **Stated against `mdev s_exec`, not against `wm_dev σ`**: same
  cost, but it does not bake in "the instruction touches no device", so an
  MMIO leaf can still use the funnel and update `dev_interp` from its own
  `execute` fact.
- **SEAM 2, FIXED: the config reads.** `wwp_cb` used to hand the leaf only
  `⌜register_lookup PC (wm_regs σ) = pc⌝`, although `wwp_instr` had just read
  the whole M-mode tower off the bundle it was given — so every leaf split
  `mmode_config` in half, kept one half to `reg_valid_dq` the same nine
  registers, transported all nine past the `minstret_increment` pre-write and
  recombined the halves at the end (43 lines). `wwp_cb` now also hands over
  **`⌜WeakFunnel.wcfg_regs σ pmpcfg0⌝`**: cur_privilege / hart_state / misa /
  mseccfg / pmpcfg_n / pma_regions / htif_tohost_base plus the misa.S,
  mstatus.MIE, mstatus.MPRV, mseccfg.PMM and elp bits, at `wm_regs σ` and in
  exactly the shape `wP_eff_of_leaf_base` and the `execute` lemmas consume
  (misa and mseccfg pinned to their WHOLE values, because that is what the
  concrete-state decode bridge compares). The funnel takes the whole
  `mmode_config (DfracOwn q)` and gives it back; the only register a leaf
  reads for itself is its own operand. **What this does NOT fix**, and it is
  not fixable at this altitude: the decode bridge's `agree_on D` premise is
  still ∀-over-register-files in a leaf's STATEMENT, because a leaf is stated
  before `σ` exists (`wwp_cb` quantifies over it). Instantiating it is now
  three `exact`s off `wcfg_regs`.
- **TWO CONVENTIONS EVERY LATER LEAF SHOULD FOLLOW**, both established here:
  - **state the leaf's `execute` lemma over an ARBITRARY `s0 : mstate`**, never
    over `MState (wm_regs σ) (wmem_restrict σ W) (wm_dev σ)`. That makes the
    confined and the flat instantiation literally the same lemma applied
    twice, and it dodges the `gmap Arch.pa` binder-instance trap outright;
  - **define any `gset Arch.pa` window ABOVE the `SailStdpp.Base` import**
    (`Base` re-exports `#[export] Countable_mword`, so a `gset Arch.pa`
    written after it elaborates against the wrong instance and
    `wmem_restrict` rejects it, printing two identical-looking types).
- **The certificate family is now width-generic.** `WeakLeafLd8.wcert_load_w`
  is `WeakCert.wcert_load` over an arbitrary `n` — its script was generic ON
  THE NOSE — with `wcert_load_w_4` as the subsumption check at the original's
  exact statement. `wcert_store` / `wcert_amo_aq` are still width-4-only;
  generalise them the same way when the first `sd`/`amoswap.d` leaf needs it.

### THE SECOND LEAF: sd (batch 2; read with the unit-price block)

`iris/WeakLeafSd8.v` (465 code lines, **433 per-leaf** after the 32-line
per-family width-generic certificate; 20.5 s single-file; green on the
FIRST compile — the leaf recipe is deterministic now). The first
STORE-class leaf: `wcert_store_w` (+ `wcert_store_w_4` subsumption,
`wcert_store8_base4`), `exec_eff_sd8_at` at an arbitrary `s0`,
`wP_eff_sd8`, and the leaf `wwp_sd8_leaf` — `ea ↦w₈{1} vold` in,
`ea ↦w₈{1} rs2v` at `ws'` + `monPred_at R (view_scl T)` out
(`T = S (length (wm_log σ))`, the `wwp_release_deposit` surface). FULL
fraction is forced (the element retarget is a `ghost_map_update`).
Cheaper than `ld` because the WINDOW KIT IS ACCESS-AGNOSTIC and was
imported from `WeakLeafLd8` (+16 lines for `wsd8_window_wdom`, the
write-domain confinement) and a store's execute has no data-byte
lookups. Corrections & follow-ups:
- **Axiom phrasing correction**: WP-altitude leaf lemmas carry the 5
  platform axioms **+ funext** (via `MinstretInv`'s cone) — true of
  `ld` too, verified byte-identical; `wcert_*` carries the bare 5.
- **Store/AMO-class successor is an `MState` LITERAL, not a `set_reg`
  tower** — state register facts at the tower only (`sd8_regs_facts`),
  consume by `exact`/`eq_trans` (conversion sees through
  `sregs (MState …)`); `iEval (cbn [sregs])` BEFORE any ssr rewrite of
  the funnel's PC hand-back.
- **The store Q-half is a fixed 4-move WP block** (reusable in §2g):
  `wpt8_at_elems` → `wlat8_store_prim` (retarget at `wQ_store8`'s
  message) → `WeakGhost.wlog_update` (the log AUTHORITY must grow —
  loads never touch it, every store leaf must) → `wlat8_wpt8` with
  `wQ_store8`'s `wV` conjunct as the floor.
- Hoist follow-ups (do when the third 8-byte leaf lands): the window
  kit → a shared `WeakLeafWin8.v`; `exec_eff_within_htif_w_false` (the
  `_writable` twin `WeakFetchEff` lacks) → `WeakFetchEff` §1; a generic
  `write_bytes_dom_sub` next to `WeakCert.write_bytes_dom`.
- `wcert_amo_aq` remains width-4-only; generalize with the first
  `amoswap.d` leaf.

### LEAVES 3–4: lw/lwu and sw (batch 2)

`iris/WeakLeafLw4.v` (439 code lines / 26.7 s; ONE parametric leaf
`wwp_lw4_leaf` covers `lw` AND `lwu` — the sign flag `u` free, as the
Base4 mirror leaves it) and `iris/WeakLeafSw4.v` (406 / 29.9 s;
`wwp_sw4_leaf`, stored value = the truncation, full fraction, the
release-deposit surface intact). Both green on the FIRST compile —
four-for-four; the leaf recipe is deterministic. Corrections:
- **A width-4 leaf has NO certificate section**: width 4 is `WeakCert`'s
  native width — `wcert_load_base4`/`wcert_store_base4` (WeakFetchEff)
  ARE the certificates on the nose; even `wcert_*_w` at n:=4 is not
  needed. That is where ~33–60 lines of the 472/433 price vanish.
- **The window kit is WIDTH-shaped, not access-shaped**: the 8-byte kit
  does not fit width 4 (a 4+4 clone lives in `WeakLeafLw4`, reused by
  `WeakLeafSw4`). Three copies of the family now exist — the
  width-parameterized hoist (`WeakLeafWin.v`) is DUE.
- `ld8_sexec_facts`/`sd8_regs_facts` ARE width-independent — reuse them.
- **`lw`'s value spelling**: `extend_value u (v : mword 32)` — the
  ascription is mandatory (`bv 32` vs `mword ?n` unification trap);
  `extend_value` is NOT identity at width 4; the bridge is
  `rewrite (data2_id_4 v)`, not `sign_extend'_id` (the width-8 move).
- **`sw`'s truncation as a TIE PREMISE**: `subrange_vec_dec rs2v 31 0 =
  vw` with `vw : bv 32` a binder, so trace/message/`↦w₄` rebuild all
  speak `vw`; goal-side `rewrite -Hvw -Hdata -Hpa` then `apply` (the
  `31` vs `(4*8-1)` gap is absorbed by conversion).
- `lemma_diff.py` must be passed the filenames EXPLICITLY for untracked
  files (bare invocation reports "no *.v differs from HEAD").
- Still-owed hoists: `exec_eff_within_htif_w_false` → `WeakFetchEff` §1
  (reused width-generically from Sd8); `write_bytes_dom_sub` generic.

### THE FIFTH LEAF: amoswap.w.aq (batch 2 COMPLETE)

`iris/WeakLeafAmo4Leaf.v` (1161 code lines / 35.2 s; green first
compile — five for five). ≈685 per-leaf-comparable + ~400 one-time
(the pin-refined certificate chain §1 + a 102-line run-assembly clone,
both hoistable). `wwp_amo4_acq_leaf` concludes `wacq_cb … (wP_eff_pin
…)` — i.e. it IS `WeakBranch.wwp_acquire_loop_real`'s attempt premise
DEFINITIONALLY; `wwp_amo4_acquire_loop` is the slot-in check with both
certificates discharged by `eq_refl` kind checks. The lock invariant is
NOT opened by the leaf (`wwp_acquire_swap` opens it and runs
`wacquire_core`), so the store Q-half block never appears here.
Axioms: bare 5 for the certificates/loop; 5+funext at WP altitude.

**THE HEADLINE CORRECTION — `WeakCert.wP_eff`'s whole-window pinnedness
is UNPROVABLE for the AMO leaf** (and the porting-guide §2.3 / WeakCert
§6 comment claiming an AMO data word "needs no pinnedness" is wrong
about the implementation): `wP_conf`/`wP_eff` demand `pinned_read` on
ALL of W, but a contended acquirer's index need not cover the lock
word. Both real consumers of pinnedness (`wstep_ok`'s read arm,
`WeakBridge.wread_pinned_ts`) only need it where `ak_pins ak = false`,
so the fix is TRACE-KEYED pinnedness: `trace_pin s es` (pin only the
reads whose kind doesn't self-pin) + `wstep_eff_confined_pin` (a
mechanical clone of the ~190-line induction) + `wP_eff_pin` /
`wstep_cert_eff_pin` / `wcert_amo_aq_pin`. **This is also exactly the
premise shape batch 6 wants** (walker RMW reads self-pin by kind;
translation reads get the variant treatment).

**CONSOLIDATION HOISTS: DONE** (2026-08-06, solo pass).  Raw-line deltas:
the five leaves 4087 → 3125 (−962; the amo file alone 1461 → 875), the
new shared `WeakLeafWin.v` +275, `WeakCert` +274 (absorbed the pin chain
+ its docs), `WeakFetchEff` +140 (the split + pin packaging + the two
hoisted §1/§9a lemmas) — **net −273** across the whole set, with every
duplicate retired.  Where things landed:
1. `trace_pin` + `wstep_eff_confined_pin` are `WeakCert` §5a/5b — THE
   confinement premise/theorem; `wP_eff_pin`/`wstep_cert_eff_pin`/
   `wP_eff_pin_of_window`/`wcert_amo_aq_pin` in §7/§8f.  The
   whole-window `wP_eff` form SURVIVES as the every-read-pinned instance
   (`exec_eff_reads_dom` + `confined_trace_pin` + `wP_eff_pin_of_eff`;
   `wstep_eff_confined`/`wstep_cert_eff` unchanged in statement), so the
   four owned-data leaves and WeakEff/WeakBranch/WeakAcquire kept
   compiling untouched.  The amo file's §1 pin chain, §2 window kit and
   §4a/§4b run-assembly clone are gone.
2. `WeakFetchEff` §8 = `exec_eff_step_of_leaf_base` (the pinnedness-free
   ∀-tick run assembly) + `wP_eff_of_leaf_base` (unchanged statement,
   now 5-line packaging) + `wP_eff_pin_of_leaf_base` (the pin variant —
   packaging only, no clone).
3. `iris/WeakLeafWin.v` (NEW, ~290 lines): `wwin pc ea n` (4 text + n
   data bytes) with membership/inv/nonzero/pinned/conf-text/conf-data/
   wdom lemmas, `addr_is_ram_pa_z_nz`, `set_lookup_ne`, the shared
   `leaf_peel` Ltac, `reg_at_flat`, `load_sexec_facts`/
   `store_regs_facts` (renamed from `ld8_sexec_facts`/`sd8_regs_facts`),
   `wpt8_align`/`wpt4_align`.  All five leaves instantiate it; no leaf
   imports another leaf anymore.  Widths are `N`; `N.to_nat 8` vs
   `8%nat` premise gaps close by conversion (`exact` accepts them).
4. `exec_eff_within_htif_w_false` is `WeakFetchEff` §1 (next to its
   `_readable` twin); `write_bytes_dom_sub` sits next to
   `WeakCert.write_bytes_dom` and `wwin_wdom` is its instance.
5. The unused `HP` argument is dropped from `wstep_cert_eff` (the pin
   precedent held: no Q-arithmetic used it); the ten `wcert_*` call
   sites just dropped one intro.
Other durable findings: an invariant-form leaf CANNOT use the funnel
(`wacq_cb` sits on `wp_winstr` directly so the lock library can open
`wlockN` around it; the leaf replays the funnel wrapper by hand —
`minstret_inv` opens at `⊤∖↑wlockN`, `clock_inv` inside the
▷-continuation; neither funnel seam arises — the ~250-line excess is
this replay, and it is FORCED); AMO-class register facts =
`amo4_sexec_facts` (peel rd write, `cbn [sregs]` the MState literal,
peel the tower).

### THE FIRST FUNCTION PORT: _entry (batch 4's vertical slice)

`iris/WkEntryEff.v` (492 code lines / 8.5 s — seven state-generic
trace-`[]` exec_eff mirrors incl. an `execR_eff` `jump_to`, + the
chain's static facts) and `iris/WkEntryNew.v` (1581 / 52.6 s —
`wwp_ld8_leaf_same`, `jal_sexec_facts`, and `wwp_entry`: the whole
8-instruction `_entry` chain as ONE Qed). Statement = SC `wp_entry`
under exactly the porting-table swaps (`kernel_text`→`wkernel_text` +
`wkb_covers`; `↦ₚ₈`→`hart_ws` + `vwp_hold (wpt8 …)`; continuation binds
`ws'` with `ws_le`); `m_*` output defs REUSED, not restated. Footprint
byte-identical to SC. First consumer of all four fetch-alignment arms.
**Total 2073 ≈ 9.8× the SC proof file**; per-instruction funnel blocks
150–220 lines inline — the argument for hoisting per-shape REGISTER-ONLY
weak leaf lemmas (weak `wp_addi_gpr`-style) before any bigger sweep.
Recipe findings:
- **Register-only instructions: the empty-memory detector (§2e) is
  UNUSABLE at the funnel altitude** (the fetch-arm premise fixes one
  `es_x` for all `b`; the detector's trace is existential per state).
  The syntactic trace-`[]` mirror is mandatory and cheap (10–40
  lines/execute; ~70 for CSRR). Then `wcert_nowrite` at the fetch-only
  trace + `wQ_pure`. Also: `wcert_quiet` cannot certify ANY real
  instruction (fetch reads are width 2/4, `quiet_trace` needs width-0).
- **PERF: `iApply fupd_mask_intro; [set_solver|]` is a hidden 14 s
  (leaf) / 199 s (whole-function) sink — use `apply empty_subseteq`.**
  The batch-2 leaves should be patched (it is most of their compile
  time). Also recorded in optimization.md.
- **Leaf cell-shape gap**: separate rs1/rd cells cannot express
  rd = rs1 (`ld sp,(sp)`); `wwp_ld8_leaf_same` is the worked fix —
  future leaves should take `gpr_file` or ship the same-register
  variant.
- Chain threading: per instruction `hart_ws_agree` pins the view,
  `wpt8_mono` carries owned words, `ws_le` accumulates transitively;
  PC returns as `lookup nextPC s_exec` (`load_sexec_facts` 5th
  conjunct; `jal_sexec_facts` for jumps — nextPC written twice).
- Kernel-text seam: `wkb_covers` (Z-keyed dump → pa-keyed weak image)
  + per-word `vm_compute` byte facts — cheap (~5 s section).

**start()/timerinit() BLOCKED on three named seams** (reported, not
weakened):
1. `csrw mstatus`/`csrw pmpcfg0`/`MRET` leaves sit on
   `InstrBytes.wp_instr_config`, which SURFACES the config cells;
   `wwp_instr` holds them inside `mmode_config` and cannot. Needed
   ONCE: a `wwp_instr_config` funnel variant (~230 lines), then those
   leaves port like the csrr block.
2. timerinit's stack accesses are c.sdsp/c.ldsp under the WRITTEN TOR
   PMP entry — all five weak leaves demand `pmp_all_off`; a TOR-PMP
   variant of the ld8/sd8 leaves is a missing leaf shape.
3. `csrr time` opens `clock_inv` via its SC engine; the weak callback's
   mask admits it but the seam is undesigned. (The
   stimecmp/menvcfg/mcounteren csrw's are NOT blocked.)
Until then the composed `SpecEntry`/`ProofEntry`/`LinkEntry` cone
cannot land; `wwp_entry` is a plain lemma exactly as SC's `wp_entry`
is.

## M4 — the sweep

**Batches and their prices** (from M4-prep's measurements; the ORDER is
[`weak-memory-porting.md`](weak-memory-porting.md) §5).

**REVISED after batch 0 landed** (see the batch-0 block above for where the
numbers come from; the prices below replace M4-prep's).

| # | batch | size | note |
|---|---|---|---|
| 0a | `execR_eff` + kit, the two `run_hart_active` progress mirrors, the step assembly, the certificate join | **DONE — 834 lines / 3.9 s** (`iris/WeakEffSkel.v`) | vs the 400–600 estimate for the whole of batch 0; the interpreter mirror is 3.8× its SC source, the script mirrors 0.65× |
| 0b | the FETCH's `exec_eff` reduction + the `tick_clock` mirror + `wP_eff_of_leaf_base` | **DONE — 2272 lines / 13.1 s** (`WeakPmpEff.v` 358, `WeakTickEff.v` 397, `WeakFetchEff.v` 1112, `WeakFetchRvc.v` 405) **+ the 2-aligned arms: DONE** (`iris/WeakFetch2.v`, 853 code lines / 8.9 s — see the block below) | vs the 250–350 + 25 estimate; the gap is the TRANSITIVE cone (PMP, the interrupt gate, the clock) that the chain merely *names*. All four alignment arms now exist |
| 1 | the memory `execute` mirrors, by SHAPE | **DONE — all five shapes, 3897 lines** (`WeakLeafEff8.v` 557, `WeakLeafEff8s.v` 598, `WeakLeafBase4.v` 1395, `WeakLeafAmo4.v` 1119, + the shared `WeakLeafEffCommon.v` 228) | vs the 30–60-lines-per-shape estimate: a shape is ≈ 800 lines, because the whole `vmem_read`/`vmem_write` cone below the `execute` must be mirrored too (same transitive-cone lesson as 0b). Three of the five needed their SC lemma written as well |
| 2 | the M-mode leaf libraries through `WeakFunnel.wwp_instr` (`WpMmodeLoad`, `WpMmodeStore`, `WpMmodeLeaf*`) | **COMPLETE — all five leaves**: `ld` 472 (`WeakLeafLd8.v`), `sd` 433 (`WeakLeafSd8.v`), `lw`/`lwu` 439 (`WeakLeafLw4.v`, one parametric leaf), `sw` 406 (`WeakLeafSw4.v`), `amoswap.w.aq` ≈685/leaf + ~400 one-time (`WeakLeafAmo4Leaf.v` — the invariant-form lock leaf, slots under `wwp_acquire_loop_real` DEFINITIONALLY). All five green on the FIRST compile. See the per-leaf blocks + "THE FIFTH LEAF" | consolidation hoists DONE (see the fifth-leaf block); batch 3 opens |
| 3 | `WpLock` clients | ≈ 0 — **but the payoff is GATED ON 6c** (2026-08 tier audit): the kernel's real acquire/release are SCONF functions (`wp_amoswap_lockopen_s_sconf` & co.); the M3b/M3c lock library validated the SHAPE at M-mode altitude, not the kernel's lock code. The tier-agnostic halves (`wlock_inv`/`wis_lock`/`wlocked`, `wacquire_core`/`wrelease_core`) transfer now | `iris/WeakWord8.v` covers `cpu`/`name` |
| 4 | the straight-line M-mode function proofs | **THE VERTICAL SLICE IS IN: `wwp_entry`** (`iris/WkEntryNew.v` + `WkEntryEff.v` — the whole 8-instruction `_entry` chain, one Qed, statement = the SC statement under the porting-table swaps, footprint byte-identical to SC `wp_entry`; first consumer of all FOUR fetch-alignment arms). **Price: 2073 lines ≈ 9.8× the SC proof file** — see "THE FIRST FUNCTION PORT" block; the ~150–220-per-register-only-instruction inline cost is the argument for hoisting weak register-leaf lemmas before any bigger sweep. `start`/`timerinit` BLOCKED on three named seams (same block) | the M-mode tier is ONLY the boot path (tier audit); everything else = batch 6c. `sie_cap_gpr`-threading specs do NOT transfer (contain `stack_own` → `↦w₈` respell, `strans_inv` → P4) |
| 5 | `WeakStarted`'s `wstarted_oneshot` invariant conjunct, then `ProofMainSecondary` | small, then a cone | the racy-load rule is landed; the escrow is not |
| 6 | the sconf tier | **DESIGNED (block below); no decision pending** | see "BATCH 6 — THE sconf/WALK DESIGN" |
| 7 | the virtio cone | M5 | |

### BATCH 6 — THE sconf/WALK DESIGN (2026-08; DECIDED: faithful, no kernel patch)

**THE FACTS THAT SHAPE THE DESIGN.** The kernel table is built A/D-CLEAR
(kvmmake's `mappages` writes `perm|V` — 0x0B text / 0x07 data/dev,
`KvmMap.v` header) and this build is Svadu (`menvcfg.ADUE=1`), so the
hardware walker WRITES the found leaf PTE back on an access that needs
bits: the first fetch/load of a page appends an A write-back, the first
store an A|D one — lazily, forever, from ANY hart (kinit's freerange
pre-touches free RAM on hart 0, but text-A, bss-D, per-hart PLIC pages and
kstacks get theirs post-`started`, cross-hart). So PTE leaf words are
genuinely RACY weak memory, and M4-prep's option (b) "prove the walk
write-free" is unavailable. **DECIDED (2026-08, user): we do NOT preset
A/D in kvmmap — the C source stays faithful; the weak tier handles PT
walks over weak-memory writes for real.** (An A/D-preset patch was
evaluated and rejected: `completed/kpt-share.md` had already declined it
for SC, and the point of the weak effort is to verify the kernel as it
is. If a SYNCHRONIZATION bug surfaces — a missing fence, not missing A/D
bits — the kernel gets fixed, per the virtio precedent.)

**THE THREE STRUCTURAL FACTS THAT MAKE THE FAITHFUL DESIGN TRACTABLE.**

1. **Only LEAF words are racy.** `update_PTE_Bits` rewrites exactly the
   level-0 leaf the walk found (A/D/U in a NON-leaf PTE is
   reserved-invalid — the same fact that made `kpt_lb`'s leaf-only
   canonicalisation sound), and nothing else ever stores to PT pages. The
   level-2/1 pointer words are kvminit-written, single-message → PINNED
   through the per-hart receipt (below). Racy surface per translation:
   ONE 8-byte window (the leaf), so 2–3 windows per instruction (fetch
   leaf, data leaf, +1 on a straddling fetch).
2. **The variant lattice is BYTE-STABLE.** Every message to a leaf window
   is `pte_set_ad w0 a d` of the canonical leaf, and A/D are bits 6/7 —
   both in BYTE 0 of the little-endian word. So bytes 1–7 are
   VALUE-IDENTICAL across all messages (a per-byte weak read mixture
   still assembles to a variant), and byte 0 ranges over the reachable
   variant bytes ((a₀,d₀) initial, (1,0), (1,1) — (0,1) is unreachable,
   `update_PTE_Bits` always sets A). Seven of the eight bytes are
   "value-pinned" — every admissible read returns THE value, a pure lemma
   away from behaving SC — and one byte carries a small finite case.
   **The latest variant is NOT monotone — write-backs can supersede each
   other backwards** (found 2026-08, user question): the walker's
   write-back is a PLAIN read at the hart's own view followed by a PLAIN
   store, and stores append at `S (length log)` unconditionally. So hart
   A's store-walk can append (1,1), and hart B — whose view does not
   cover it — can then read the (0,0) original on a load-walk and append
   (1,0) ABOVE it in coherence order: the D bit regresses at the top of
   the log. Note real hardware cannot do this: the privileged spec
   requires the A/D update to be ATOMIC w.r.t. other PTE accesses (an
   atomic check-and-set at the coherence point), so our plain-read+store
   model is strictly WEAKER than the architecture on this axis — the
   sound direction, and BENIGN for the kernel table: no software reads
   A/D, `check_PTE_permission` ignores them, a regressed variant at worst
   triggers another write-back, and every invariant here is stated at
   "∃ variant" with no order on the lattice (do NOT state one). WHERE IT
   STOPS BEING BENIGN — record for the USER cone: once SOFTWARE writes
   PTEs concurrently with walkers (uvmunmap zeroing an entry while
   another hart's stale walker holds an old variant), the model's plain
   write-back can RESURRECT the unmapped PTE — a behavior the
   architecture's atomic re-check ("valid and grants sufficient
   permissions", re-checked at the write) forbids. The user-cone design
   must either model the walker update as the architecture's atomic
   check-and-set (an `ak_latest`-style RMW at the interpreter seam) or
   declare the gap; deciding that is a user-cone prerequisite, NOT a
   batch-6 item.
3. **The SC tier's interfaces are already A/D-CLOSED.** Translation
   results (pa, `check_PTE_permission`) are variant-independent
   (`pte_set_ad_ppn`, checks ignore A/D); the ONLY register the read
   variant reaches is the tlb cell, and `tlb_ok_pt` / `tlb_res_pt`
   already quantify A/D existentially (entries as "SOME variant of the
   tree's leaf"). GPRs, data memory, control flow, devices never see the
   variant. So NO ported S-mode spec statement changes — the
   nondeterminism lives exactly where the SC design already refused to
   pin it.

**THE DESIGN.**

- **`wkpt_inv`** (namespace invariant, all conjuncts objective iProps),
  mirroring `kpt_inv` with `ptree_own` split by role:
  the level-2/1 pointer words as kvminit-timestamped `wlat_pointsto`
  elements; per leaf vpn `∃ ts a d, wlat8 (leaf addr) 1 ts
  (pte_set_ad (canonical leaf) a d)` (EXCLUSIVE — a write-back retargets
  it at the appended message, the lock-release shape; this is why
  `wstep_cert`'s Q carries the message identity); `kmap_auth M` +
  `kpt_lb t` + the spec facts as today; and the **VALUE-CLOSURE conjunct**
  `⌜every log message at a leaf window writes a variant⌝` — a
  whole-log fact, so (the `wstarted_oneshot` lesson) it MUST be an
  invariant conjunct with a per-step preservation lemma, and it is what
  collapses `wadm` at the windows: byte 0 ∈ variant bytes, bytes 1–7 =
  the canonical bytes.
- **The receipt** `⊒ V_kpt` (`View 0` at the kvminit bytes' timestamps) —
  persistent, subjective, per-hart, NEVER in an invariant. Hart 0 from
  its own writes; secondaries through the `started` handoff
  (`release_fence_transfer`; `T_kpt ≤ t_started` by program order). It
  pins the pointer-word reads AND excludes pre-kvminit garbage at leaf
  windows (readable's coherence clause: a view covering kvminit's write
  bars the era-initial value), so every admissible leaf read is a VALID
  variant. **This is the fence-sufficiency statement for the kernel
  table: the existing started handshake is ENOUGH; no kernel change is
  needed for batch 6.** (The analogous question for USER tables —
  fork/exec building tables cross-hart under the proc-lock chains — is
  user-cone work; surface concrete fence obligations there when reached.)
- **The bridge tier: exec-modulo-variants.** Generalize `WeakRacy`'s
  one-window scheme to the walk shape: reads pinned everywhere except
  designated windows Wᵢ with per-byte value collapse (fact 2), plus a
  WRITE confined to the same windows with a variant value (the racy rule
  already tolerates writes after the racy read; the transport across the
  intervening write-back and the multi-window join are the new lemmas).
  The correspondence: every admissible run ≡ SC `exec` at `wflat_st σ`
  PATCHED at the windows with some variant choice, landing ≈_ad-related
  to the canonical successor (≈_ad: equal but for A/D variants at leaf
  windows + tlb entries). Reducibility witnesses at the latest-read
  oracle (reading the latest message is always admissible).
- **The certificate: racy confinement.** Extend `wstep_ok_confined` to
  produce `wstep_ok_racy` (the recorded gap): run the SC interpreter at
  the RESTRICTED memory patched SYMBOLICALLY at the windows (∀ a d — the
  existing `_ad`-generic translate/execute lemmas are exactly the
  symbolic instantiation, so no 4^windows enumeration), reads outside
  windows confined as today, writes confined to the windows by the final
  domain + value-closure of `update_PTE_Bits`.
- **The absorption theorem** mirrors `tlb_res_pt_translateAddr_at` with
  `gen_heap_interp` swapped for `wlat_interp`: open `wkpt_inv`
  (mask-carrying, the `sr_absorb` call form), pointer words via
  `wlat_flat_lookup` + receipt, leaf windows via the closure conjunct's
  `wadm` collapse; on the write-back arm retarget the leaf element at
  the step's appended message (from Q) and re-close — `kpt_lb` survives
  by `ptree_canon_set_leaf` exactly as in SC, and the closure conjunct
  extends by "the write-back wrote a variant".

**STAGING** (P-stages are new base machinery, serial; then the sweep
stages parallelize):
- **P1** (WeakMem/WeakInterp/WeakGhost): value-pinned-byte lemma, the
  variant lattice + byte-0 stability, multi-window `wstep_ok_racy`
  generalization, the value-closure predicate + preservation.
- **P2** (WeakCert): racy confinement — the symbolic-patch confined run
  producing `wstep_ok_racy` (the recorded missing piece).
- **P3** (WeakBridge/WeakRacy): exec-modulo-variants with the confined
  write; transport across the intervening write-back; multi-window join.
- **P4**: `wkpt_inv` + the weak absorption theorem + the Q plumbing for
  the write-back message.
- **6a**: the S-mode fetch chain at the flat state (`tlb_inv_pt_fetch`'s
  pure/wlat restatement over the absorption theorem) + the translate/walk
  `exec_eff` cone. **THE WALK READ-CONE MIRROR IS DONE**
  (`iris/WeakWalkEff.v`, 1186 code lines / 26 s; 45 top-level, all
  `acc`/`p`-parametric; the update/write-back cone deliberately EXCLUDED
  pending the Sail patch): the `wpte_*` eff predicate twins (∀-state SC
  predicates do NOT transport — state the eff walk at empty-trace
  `wpte_*` hypotheses and project back; 6b's `kperm_variant_*` twins
  should be stated at `wpte_*` directly), `exec_eff_read_pte_S` (trace
  `[WEread wak_plain addr 8]` — a PTE read is plain, view-raising),
  `wpt_read_pte_slot` (closed under the global context), the per-level
  ∀-Acc success walk (trace-generic `es2++es1++es0` premises — the
  3-element certificate join is free BY CONVERSION), the fault walks
  split per stop-depth `_l2/_l1/_l0` + the SC-shaped disjunctive
  wrapper (exact traces vs existential — exact-trace consumers use the
  split), `exec_eff_translate_TLB_hit_pt` (O1, literal empty trace —
  the quiet detector was deliberately NOT used: certificates need exact
  traces), and the `translateAddr` heads (O1/O2, `update_PTE_Bits =
  None` premise). **Pricing: 1.15× the SC spans (≈1.03× pure replay) —
  far below the 0b/1 ~800-per-shape figure because the walk's
  transitive cone was already paid for** (WeakLeafEff8's plain-8 read,
  the WeakFetchEff/WeakLeafEffCommon gate twins, WeakEffSkel's kit);
  the only new interpreter-adjacent work was the Supervisor PMP grant +
  PTE-PMA gate (~70 lines). Axioms: one platform axiom
  (`plat_term_write`) on the heads. The two 2-ALIGNED fetch arms are
  also DONE (`iris/WeakFetch2.v` — the 0b-gap block; the straddling jal
  at 0x80000ffe is real S-mode code). REMAINING in 6a: the S-mode
  fetch-chain restatement (needs P4's absorption shape) and, post-Sail-
  patch, the update-cone mirror.
- **6b**: the S-mode leaf `execute` shapes (`_S_walk_pt` towers, widths
  1/2/4/8 + AMO) at exec_eff — batch-1-sized.
- **6c**: the weak S-funnel `wwp_instr_s` (wcfg_regs/device-frame seams
  applied from day one) + leaves at the batch-2 recipe, plus the racy
  continuation (which the absorption theorem hides from specs).
  Pricing datum (2026-08 tier audit): the kinit/kfree cone ALONE uses
  42 distinct sconf leaves (≈15–25k lines at the batch-2 unit prices),
  of which SIX are invariant-form (`wp_amoswap_lockopen`,
  `wp_csd_lkcpu_lockopen`, `wp_holding_lockinv{,_locked}`,
  `wp_sd_zero_lkcpu_lockopen`, `wp_sw_zero_lockfin`) — each pays the
  fifth-leaf ~250-line funnel-replay premium. kfree's `jal memset`
  pulls in `wp_memset_sconf`. The kinit cone is 6c's VALIDATION
  CAPSTONE (see the corrected M3 item).
The sconf/sie_cap/intr_count config tower transfers VERBATIM (M3a
verdict) — batch 6's content is the walk, not the config. OUT of scope:
the satp-switch window / user tables (user cone; note the write-back-
into-previous-table-via-cached-pteAddr hazard recorded in kpt-share
returns there).

**THE MODEL CHANGE (2026-08; DECIDED IN DIRECTION: faithful-only — the
user rejected any NEW over-strengthening, so the earlier
"walker-reads-ak_latest" proposal is DEAD; what follows is the faithful
sketch).** Constraint: change the Sail model only toward the real
RISC-V privileged spec of PT accesses.

*What the spec requires* (verify exact clause wording against the
ratified text at implementation time — flagged below):
(1) implicit PT reads are weakly ordered — ordered by SFENCE.VMA only,
not by FENCE; they may be stale and speculative; (2) Svadu A/D updates
are an ATOMIC read-modify-write that atomically RE-CHECKS the PTE it
reads (valid + sufficient permissions) before setting bits — D-updates
exact, A-updates may be speculative; (3) the update appears in gmo no
later than the explicit access it enables.

*The Sail sketch* — confined to `update_and_write_pte` (sys/vmem.sail;
both call sites, TLB-miss and TLB-hit, funnel through it; `read_pte`
and `_rec_pt_walk` are UNTOUCHED — translation reads stay weak):
```
match update_PTE_Bits(pte_stale, access) with
| None   => Ok(None)                          (* unchanged *)
| Some _ =>                                    (* update indicated *)
  if not Svadu_on => Err(PTW_PTE_Needs_Update) (* Svade arm, unchanged *)
  fresh := pte_rmw_read(pteAddr, w)            (* AV_exclusive read *)
  if not (valid fresh ∧ check_PTE_permission access fresh ∧ leaf ok)
    => Err(recheck_failed)                     (* fault; see TODO *)
  match update_PTE_Bits(fresh, access) with
  | None        => Ok(Some fresh)              (* fresh has the bits *)
  | Some fresh' => pte_rmw_write(pteAddr, w, fresh'); Ok(Some fresh')
```
`pte_rmw_read/_write` build interface requests directly with
`AK_explicit {AV_exclusive, AS_normal}` (the AMO kinds) below the
existing PMP/PMA `supports_pte_{read,write}` gates — no new interface
types, no `read_kind`/`write_kind` enum changes, no LR/SC reservation
contact, NO `Choose` anywhere (preserves the choice-free fragment).
Intra-instruction the read→write pair is atomic (one language step) —
together with AV_exclusive's read-latest semantics this IS the spec's
atomic check-and-set.

*Fidelity ledger*: the RMW is what the spec MANDATES — no new
strengthening. Two PRE-EXISTING strengthenings remain, unchanged, and
must be documented: walk-read staleness bounded by hart views + TLB
(spec allows staler, sfence-only bounds) and no speculation.
**SPEC-TEXT TODO RESOLVED (2026-08, ratified text verified)**: the
update is a COMPARE-AND-SWAP — VATP step 7: "Compare pte to the value
of the PTE at address a + va.vpn[i] × PTESIZE. If the values match,
set pte.a to 1 and, if the original memory access is a store, also set
pte.d to 1. If the comparison fails, return to step 2" — i.e. FAILED
compare = RETRY (redo the PTE read + tablewalk checks), never a
spurious fault; faults come only from the re-checked tablewalk checks
themselves (per the original access type) or PMA/PMP on the PTE store.
Svadu additionally: "must atomically perform all tablewalk checks for
that leaf PTE as part of, and before, conditionally updating the PTE
value" — which makes the loop-free ATOMIC-RECHECK formulation (fresh
exclusive read → redo leaf checks on fresh → write fresh|bits if still
needed) observationally EQUAL to the literal CAS loop, and that is the
implemented shape (terminating, no Choose). Note the conflict arm is
REACHABLE under weak execution even on the kernel table (walked
variant (0,0) vs current (1,1) mismatch) — it must resolve to
use-the-fresh-value, NEVER a fault, or the kernel becomes unprovable.
Also confirmed: "The PTE update must appear in the global memory order
before the memory access that caused the PTE update" — free in the
operational model (same instruction step, program order). QEMU's
target/riscv implements the CAS loop (reference-implementation
precedent). **THE PATCH IS COMMITTED: `ffb7621` on branch
`pte-ad-atomic-update`** in /shared/xv6rocq/sail-riscv (parent
eb31a74 = master; not pushed; sail 0.20.1 at
/root/.opam/default/bin/sail). Validated: baseline regen
byte-identical (properly, via `cmp` on a pristine worktree — NOTE the
regen script's coqc compile-check step can NEVER pass in this
environment, coq-sail-stdpp is not installed; ignore that failure),
typecheck clean (no new warnings), 20/20 upstream ctest incl. both
stale-TLB tests, patched-rv64d diff machine-verified CONFINED to the
vmem cone (398+/318− after renumber normalization; rv64d_types
unchanged). ONE deliberate sequentially-visible difference: the
TLB-HIT A/D update re-checks the in-memory PTE and faults instead of
writing the stale TLB copy back (per the spec's CAS). Landing the
regenerated model into xv6iris is a SEPARATE, still-pending step —
the tree is on the baseline model; when it lands, the SC update-cone
rework (PtTreeAdue/`exec_update_and_write_pte_needs_update`/O3 arms +
the new `check_leaf_pte` factoring) begins.

*Semantic payoff*: every PT write becomes FRESH-derived ⟹ the leaf
word's message sequence is BIT-MONOTONE ⟹ (with the fresh-has-bits
skip arm) whether a write-back occurs is a function of the gmo-latest
value alone — the write-back EVENT is deterministic given the
invariant, and lost updates and resurrection are both impossible. The
stale translation read's residue: which internal path ran (an extra
RMW read event) and the A/D bits cached in the TLB — both already
existential in `tlb_ok_pt`.

*Blast radius*: Sail — one function + two helpers; regen via
`tools/regen_sail_model.sh` (needs sail 0.20.1 + sail-riscv checkout —
not on this machine). SC side — `CommonWalk`'s walk lemmas untouched;
rework confined to the update cone (`exec_update_and_write_pte_needs_update`,
PtTreeAdue's `exec_write_pte_ram` → RMW-pair lemmas,
`exec_translate_TLB_{miss,hit}_pt_upd`, the O3 arms of
`ptree_translateAddr_cases`/absorption) + one new impossible arm
(re-check failure, discharged from the invariant's validity facts).
`RiscvExec.exec` is KIND-BLIND, so SC behavior at one memory is
unchanged (fresh = stale there). Weak side — ZERO WeakInterp change:
AV_exclusive already classifies as `ak_latest`. Litmus — add the
two-hart A/D lost-update regression (must be unobservable) and a
resurrection regression.

*Consequence for this batch*: P1 SHRINKS to the variant/value-closure
core (still needed — stale translation reads are real and faithful);
P2/P3 SHRINK a lot (no patched-memory bridge: the ∀-variant SC
instantiation rides the existing `_ad`-generic lemmas; confinement
gains one maybe-RMW window whose write value is latest-derived); P4's
write-back arm becomes AMO-SHAPED (`wamo_read_latest` — fires off the
invariant-held element with no view hypothesis). The full racy-window
design above remains recorded for reference, but the expectation is
the reduced form.

**GATES**: the Sail patch + regen (environment: sail toolchain +
sail-riscv checkout) precede P1–P4's final statements; 6a/6b are
design-independent and can proceed now. Batch 2's store leaves and
batch 5's escrow are needed only for the boot MINT of `wkpt_inv`.

### THE 2-ALIGNED FETCH ARMS (batch-0b gap, CLOSED 2026-08)

`iris/WeakFetch2.v` (853 code lines / 8.9 s; green on the FIRST compile —
the fetch-mirroring recipe is now deterministic): the width-2 memory
chain (`exec_eff_fetch_bytes_2` generalized over the fetched address, so
ONE lemma serves both chunks), the two arms `exec_eff_fetch_RVC_2` /
`exec_eff_fetch_F_Base_2` (traces `[WEread wak_plain pc 2]` and the
two-chunk `[…pc 2; …(pc+2) 2]`), the `fetch_flat_ok` wrappers, the
recipes `wP_eff_of_leaf_base2`/`_rvc2`, and the certificate instances
(`wcert_{load,store,amo_aq,fence}_base2`, `_rvc2`). Axiom footprints
byte-identical to the 4-aligned originals. Findings worth keeping:
- **The 3-element certificate family cost ~50 lines of one-liners, not
  the priced ≈120**: `WeakEff.wcert_*_gen` at `post := []` concludes
  `pre ++ [e]` on the nose, so the split-fetch certificates are pure
  instances; the only new proof content is `nowrite_fetch2`.
- **misa.C enters BOTH 2-aligned recipes**, not just RVC — the
  misaligned-pc guard probes `Ext_Zca` even for a 32-bit instruction, so
  `wP_eff_of_leaf_base2` has one config premise more than `_base`
  (already inside `wcfg_regs`' misa pin — funnel-fed leaves get it free).
- Trace-join mechanics: two `execR_eff_liftR_cat`s → one `cbn match`
  collapses all nested matches; `rewrite Hconcat` BEFORE the final
  `cbn [app]`; no `app_nil_r` at the fetch altitude.
- `rewrite !fetch_pa_id` (with `!`) in the base2 flat wrapper — two
  distinct instances; the base4 single-rewrite pattern silently leaves
  the second address unrewritten.
- Cost datum: 853 code lines vs the ≈200 estimate, but ~300 is recipe
  STATEMENT transcription; genuinely new proof content ≈400 lines at the
  established ≈1.1× mirroring rate.

### BATCH 1's SHAPES, ENUMERATED FROM THE ACTUAL SC LIBRARY

M4-prep guessed "LOAD/STORE at 1/2/4/8 + AMO = 9 shapes".  Grepping the
tree for what the M-mode side really has (`exec_execute_LOAD_*` /
`_STORE_*` / `_AMO*`, excluding the `_S` / `_U` / `_walk_pt` cones, which
belong to batch 6 and to the user cone) gives **fewer, and the batch-0
assembly says each one's deliverable is now exactly its own `exec_eff`
fact**:

| shape | SC lemma (M-mode) | trace | note |
|---|---|---|---|
| LOAD 8 | `WpMmodeLeafBase.exec_execute_LOAD_8_gpr` (+ `_chk`) | `[WEread akl ea 8]` | **DONE** — `iris/WeakLeafEff8.v`, 691 lines. `ld`; the `wwp_ld8` leaf of `WeakWord8` consumes it. The `_chk` variants were NOT mirrored (nothing needs them yet) |
| STORE 8 | `WpMmodeLeafBase.exec_execute_STORE_8_gpr` (+ `_chk`) | `[WEwrite akw ea 8 v]` | **DONE** — `iris/WeakLeafEff8s.v`, 698 lines. `sd`. `_chk` not mirrored |
| LOAD 4 | reached through `exec_execute_C_LW` / `_C_LDSP` → `ExecuteAs (LOAD … 4)`; the width-4 M-mode `LOAD` lemma did not exist | `[WEread akl ea 4]` | **DONE** — `iris/WeakLeafBase4.v`, 613 SC + 742 mirror = 1456 lines. `lw`/`lwu` (the sign flag is left free), and the spinlock's spin re-read |
| STORE 4 | ditto via `exec_execute_C_SW` / `_C_SDSP` | `[WEwrite akw ea 4 v]` | **DONE** — same file. `sw`, the release and the `started` setter. NOTE the stored value is the TRUNCATION `subrange_vec_dec vrs2 31 0` |
| AMOSWAP 4 | only `WpAmo`'s S-flavoured chain and `WpSmodePtLock.exec_execute_AMOSWAP_4_gpr_S_walk_pt` existed | `[WEread aka ea 4; WEwrite akw ea 4 v]` | **DONE** — `iris/WeakLeafAmo4.v`, 399 SC + 729 mirror = 1237 lines. THE lock instruction; the two effects come out adjacent, as `wcert_amo_aq_gen` assumes. It probes FOUR MMIO gates (both `within_htif_readable` and `_writable`), not three |
| LOAD/STORE 1, 2 | `WpSmodePtMem.exec_execute_STORE_1_…` etc. only | | NOT reachable from M-mode kernel text today — **deferred to batch 6, recorded not built**, as planned |

**BATCH 1 IS COMPLETE: all five shapes.** Total **4082 lines** across five
files, i.e. **≈ 800 per shape**, against the 30–60 estimate — the same
transitive-cone correction as batch 0b (the `vmem_read`/`vmem_write` cone
below an `execute` is not detectable either, so it is mirrored whole). Three
of the five needed their SC lemma written as well (width-4 LOAD, width-4
STORE, M-mode AMOSWAP); the SC halves came to 399–613 lines each and replay
their width-8 template essentially line for line.

Batches 0 and 1 are one agent each and must be serial; 2 and 4 parallelise
freely (each file is independent through the funnel).  Batch 6 must NOT be
scheduled before its design item is resolved.

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
