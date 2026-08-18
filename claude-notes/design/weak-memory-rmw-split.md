# The RMW split at the weak tier — mirroring the reservation design (2026-08-18)

**Status: DESIGN (orchestrator), user-confirmed; REVISED after the S0
validation pass against the tree.  Borrow the SHAPE of `main-cycle-port.md`
§3a (the hart-node-port branch) — not the file.  Worklist and per-slice
inventory: the S-track of
[`../projects/weak-memory-certification.md`](../projects/weak-memory-certification.md).**

## 1. The change in one line

The fused `LRmw` label (with `WPRmw`/`PFRmw` and the event language's fused
window `esilent1`/`esilent_run`/`ewr_node`) dies.  An exclusive read and a
conditional write are SEPARATE labels; atomicity is a per-byte window check
at the write's FULFIL, keyed by an AGENT-LOCAL reservation set by the read.
`WPPromise` and front-loading (`wp_swap`/`wp_front_load` are label-generic —
they route through `astep_ok_app`/`astep_ok_prom`/`wp_astep_frame`, none of
which inspect the RMW's structure) are untouched: the reservation never
touches the log, and fulfils read only the agent's own state.

Why: §3a's reachability table — a dangling exclusive read is REACHABLE (the
walker's A/D re-read race, `check_leaf_pte` Err, AMOCAS mismatch); the event
language's fused arm makes those traces STUCK today (`WeakEvLang.v`'s F6
guard) and the tree's escape hatch is the per-image `menvcfg.ADUE = 0`
assumption (`WeakShapeWin.v`) — which this split RETIRES; the kernel WP
corpus is landing on the split shape; and PARM (the D8 port source) is
itself a split machine.

## 2. Labels

- **`LExLoad aq base tvs asrc`** and **`LExStore rl base data asrc vsrc`** —
  new constructors, placed **after `LInstr`** (trailing position keeps every
  bulleted destruct script's arm order intact — the `WeakPromise.v:119`
  convention).  `LExLoad`'s read semantics are `LLoad`'s with `lat := false`
  hardwired (`load_post_run_d` takes no `lat`; the arm is `WPLoad`'s plus
  the reservation write).  `LExStore` is `LStore`'s write semantics plus §4.
- `LRmw` deleted — but only in the CONTRACT slice (§8): the split is
  landed expand/contract, with both shapes coexisting mid-flight.
- **Catch-all matches are a trap**: 22 `match`es on `wlabel` end in
  `| _ =>` and would absorb the new constructors silently (6 of them
  critically: `elab_log`, `edlab_log`, `pcls_ev`, `lbl_class`,
  `lb_writes`, `lb_loads`).  They are exhaustivised FIRST (slice S0.5),
  so the constructor addition really is compiler-flagged.
- **The axiomatic tier (`WeakAxiomatic.lbl`) stays FUSED.**  Its `LRmw`
  carries `rmw_latest` (strictly stronger than `excl_ok`) and `mstate` has
  no per-agent scratch for a two-step reservation.  `proj_lbl` maps
  `LExLoad → LLoad`, `LExStore → LStore` (the move `WeakInterpProj.v`
  already makes and justifies); `unproj_lbl`'s `mstep_rev` produces two
  `wp_pf_step`s.  Confined to one `WeakPromiseBridge.v` section; the
  `own_coh` dovetail and `rmw_latest_excl_ok` become deletions.

## 3. The reservation (agent state)

`wstate` gains `w_res : option wresv` with

```coq
Record wresv := WResv { rv_base : Z; rv_ts : list nat; rv_view : nat }.
```

— per-byte read timestamps positionally from `rv_base` (the vocabulary
`excl_ok` actually consumes: it reads only `tvs.*1`), plus the read half's
banked post-view `rv_view` (= the `ldv_of ws aq (srcs_view ws asrc) base
(tvs.*1)` the fused arm already computes).  Values are NOT carried — the log
at `(b, ts)` has them; consumers (the walker discriminator, WP rules) read
them there.

`w_res` sits with `w_fwd`/`w_regv`/`w_ldv`: IN `wstate`, OUT of `ws_le`
(it is set/cleared/superseded, not monotone), and — required — IN
`ws_bounded`, so `fulfil_vpre` can dominate `rv_view`.

Rules (§3a relabeled, with the S0 corrections):

| §3a (SC) | here (weak) |
|---|---|
| exclusive read sets `gresv cpu := snapshot`, superseding | `LExLoad` sets `w_res := Some R`, superseding |
| EVERY `MemWrite` of the hart clears its reservation | the agent's OWN `LStore`/`LExStore` fulfil clears its OWN `w_res` — and nothing else does: **`LDev` does NOT clear** (Layer 1 treats `LDev` as `LSilent` on `wstate`, by design), **`LRegW`/`LCtrl` do NOT clear** (the AMO's `rd` write fires between its read and its write), other agents' writes (the disk's DMA included) are handled by the window check, not by clearing |
| boundary `Ret` clears it | `LInstr` clears it (instruction start = the same GC point; §3a's up-to-three exclusive reads per cycle live in one `w_res` epoch and supersede correctly) |
| blocked-read drops own / blocked-write keeps | no counterpart in the ABSTRACT machine; see §5 for the one place a retry device IS needed |
| `resv_ok` (snapshot ⊆ memory) | no counterpart: the window check at fulfil is that fact in coherence order |

**The clear-on-own-store rule is load-bearing, not decoration**: a
same-agent store to the byte between the exclusive read and the conditional
write would clear `w_res`, so `w_res = Some R` at the write REFUTES that
case — the L2 window between the pair (`no_store`-style) is a THEOREM from
the state, not a premise in the `no_instr` idiom.

## 4. The write's fulfil (where `excl_ok` moves)

`LExStore` fulfil at timestamp `ts` REQUIRES `w_res = Some R` with
`rv_base R = base ∧ length (rv_ts R) = length data` — **no plain-store
fallback**: a partnerless `LExStore` has NO arm.  (SC needs the fallback for
totality; the promise machine has no totality obligation, the model never
produces the case, and a partnerless exclusive write would force the whole
L2 tower to carry a read-less exclusive event.)  Then:

- **the window, per byte**: `excl_ok_ts log i (rv_base R) (rv_ts R) ts` —
  today's `excl_ok` restated over `list nat` (the value components were
  dead); `excl_ok_app`/`retag_excl_ok` carry over verbatim.
- **EXT**: `fulfil_vpre` additionally includes `rv_view R` — preserving
  deviation D-2's strength (PARM's exbank-view contribution).  This is what
  keeps `WeakCertify.astep_ok_del_vcap`'s arm a one-liner.
- fulfilment clears `w_res`.

Machine arms: ordinary promise + this fulfil (`WPExStore`); the pf form
appends at top (`PFExStore`), where the window is checked against the log
as it stands — a dirty window means the arm has no step, which IS the
walker's `update_PTE_Bits = None` semantics.  `wpstep_rmw_now` becomes
`wpstep_exstore_now`.

Semantic delta, deliberate: `fulfil_ok_d` is now evaluated at the
post-WINDOW state (window steps raise `coh`/`vcap`/`vwNew`; the walker's
`check_leaf_pte` branch raises `w_vcap`), so the promising machine admits
STRICTLY FEWER behaviors than the fused arm — PARM's own shape, the
fidelity-improving direction.  The pf/append-at-top form is unaffected
(`ts = S (length log)` dominates every view via `ws_bounded`).

## 5. Blocking: what crosses and what does not

The ABSTRACT machine (`WeakPromise`) needs nothing: an unfulfillable
conditional write is a doomed run, pruned by `no_promises` — no blocking,
no waiting, no totality obligation.

**But the EVENT LANGUAGE needs a reducibility device, and this is exactly
where §3a's self-loop crosses over.**  `WeakEvAdequacy` runs at `NotStuck`,
and `ewp_ev_rmw`'s reducibility witness today rides on the fused step
(read-latest makes `excl_ok` free, `read_latest_excl_ok`).  After the
split, the `LExLoad` fixes the window's lower bounds at read time; foreign
appends during the window can make the conditional write's `excl_ok_ts`
fail — a stuck node, and `NotStuck` (hence the capstone) falls.  DECISION:
the event-language conditional-write node gets a **retry self-loop arm**
(dirty window ⇒ `LSilent`, monad and state unchanged) — §3a's device,
transplanted to the one tier that demands totality; the WP rule absorbs it
by Löb; the robustness tower sees only extra `LSilent`s.  (`MaybeStuck` was
considered and rejected: it silently weakens a real guarantee.)

Still deliberately NOT crossing: the value snapshot (the log carries
values), the cross-hart blocking of the OTHER harts' arms, the
dangling-deadlock analysis, `resv_ok` as a state invariant.

## 6. The event language and the interpreters

- The producer key is exclusivity, NOT latest-indexing.  `akinfo` gains no
  field (178 positional literals say don't): add derived `av_excl`/
  `ak_excl` with `ak_excl ak = ak_latest ak` (extensionally equal today —
  `classify` sets `ak_latest` exactly at `AV_exclusive`/`AV_atomic_rmw`;
  ifetch/ttw use `ak_coh`).  The ~77 consumer sites that MEAN "exclusive"
  rename to `ak_excl`; the ~10 that mean "latest-indexed" keep `ak_latest`.
- `WeakEvLang`: the fused window machinery (`esilent1`/`esilent_run`/
  `ewr_node`/`ewg_rmw`) deletes; exclusive `MemRead` → `LExLoad`; the
  window's silent nodes are ordinary nodes; conditional `MemWrite` →
  `LExStore` + the §5 retry arm.  The F6 "bare exclusive read is STUCK"
  guard and comment delete: dangling reads become legal traces.
- **`lat` is then entirely unused in the model of record**: the disk's read
  is `lat = false` (`WeakEvInst.pstep_ev_lat_free` proves the instance
  emits no `lat` read); only the archived Sail-LTS machines exercised
  `lat = true`, through `rmw_tight`/`xrmw_tight` — which die with the
  split, as does the `menvcfg.ADUE = 0` escape hatch (`fused_blk`).
- **The walk bridge is ZERO change**: `WeakKpt*`/`WeakWalk*` live at the
  Sail-effect tier where the exclusive read and the A/D write-back were
  always two events, dangling shapes included and already proved.  The
  fusion (and its stuckness) lived only in `WeakEvLang`/`WeakEvInst`.
- `WeakDeps` is a pure decoder: zero change; the AMO's `LRegW rd [DLdRes]`
  keeps working because `w_ldv` is written only by `load_post_run_d` and
  preserved by the window's other post-functions.

## 7. Invariants and known-hard points of the re-land

- `Print Assumptions` on both capstones unchanged at EVERY slice boundary;
  tree green per slice; no `Admitted`/`Axiom`.
- `WeakRobustProv.lstate` mirrors `wstate` field-for-field: `w_res` needs a
  matching `l_res` + `lrel` conjunct + `laev_post` arms + σ-independence
  twins (the `w_relp` idiom).  Budgeted, not optional.
- The three riskiest items: `WeakRobustSim.excl_ok_pf` (the pf-replay
  window straddles two events at different points of `done`); the §5 retry
  arm's WP rule; the `cs_window` signature change (four indices + the
  reservation links) propagating through `cs_windows_ordered`/
  `sf_shape` C4.
- Two places get EASIER: `astep_ok_read_fulfil_same`/`atrace_own_read` (the
  fused label's read∧write coincidence) go vacuous; `rmw_reads_pred`'s new
  same-agent-window case is discharged by the §3 clear-on-own-store rule.
- One place gets harder without being a premise: `atrace_S1_le_f`'s
  `k = k'` case (free when the rmw was one event) becomes the pair case —
  recoverable from `astep_ok_read_coh` at the `LExLoad` + `fulfil_ok_d`'s
  COH conjunct at the `LExStore` (footprint match supplies the byte).

## 8. Slices (expand/contract — every boundary green)

- **S0.5**: exhaustivise the 22 catch-all `wlabel` matches (no semantic
  change; makes S1 compiler-flagged).
- **S1** (additive): the two constructors AFTER `LInstr` + `wresv`/`w_res`
  (+ `ws_bounded`) + full arms/bullets everywhere, `LRmw` STILL PRESENT,
  no producer emitting the new labels.
- **S2**: machine arms (`WPExLoad`/`WPExStore`, `PFExLoad`/`PFExStore`,
  `wpstep_exstore_now`), `WeakPromiseFact` bullets, bridge `proj_lbl`/
  `unproj_lbl`, `WeakRetag`.
- **S3**: event language + `WeakInterp` (`ak_excl`) + `WeakEvLift` WP rules
  (incl. the §5 retry arm) + `WeakEvPf`/capstone plumbing.
- **S4**: the robust tower re-index (Ser/Acyc/Disc/Blocks/Prov/Sim/Cone/
  L2/L2b vocabulary).
- **S5**: `WeakCertify`, the Sail-LTS tier, `WeakCompose*`, capstone
  re-verification.
- **S6** (contract): delete `LRmw`, `WPRmw`/`PFRmw`, `wpstep_rmw_now`,
  the fused event machinery, `fused_blk`/`rmw_tight`/`xrmw_tight`,
  `rmw_latest_excl_ok` + the `own_coh` dovetail.

Size (S0 estimate): ≈3,150 lines written / ≈2,800 net across ~40 files,
≈2,070 semantic.  The per-slice site inventory lives in the S-track of the
certification worklist.
