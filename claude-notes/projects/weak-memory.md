# Project: weak memory (RVWMO) — staged worklist

Design: [`design/weak-memory.md`](../design/weak-memory.md) (PROPOSAL).
Branch: `weak-memory`. Landed: M0 (`iris/WeakMem.v`, `iris/WeakLitmus.v`),
M1a (`iris/WeakInterp.v` + fwd-bank wire-in), M1b (`iris/WeakLang.v`),
M1c (`iris/WeakGhost.v`, `iris/WeakExec.v`, `iris/WeakAdequacy.v`),
M2a (`iris/WeakView.v`, `iris/WeakVProp.v`),
M2b (`iris/WeakBridge.v`, `iris/WeakFence.v`, + `ws_bounded`),
M3a (`iris/WeakInstr.v`), M3b (`iris/WeakStore.v`, `iris/WeakCert.v`,
`iris/WeakLock.v`, `iris/WeakStarted.v`).
Next: M4 — and read
[`weak-memory-porting.md`](weak-memory-porting.md) first.

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

## M3 — vertical slice (the interface test)

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
- [ ] One lock-client cone re-proven unchanged-in-statement (candidate:
      kinit/kfree — small, pure lock+memory).  NOT done: it needs the leaf
      layer's memory arms, i.e. M4's first batch.
- [x] Porting guide written from what the slice taught:
      [`weak-memory-porting.md`](weak-memory-porting.md).

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
