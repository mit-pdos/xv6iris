# Closing the lift gap (seam 1): WeakLang ↔ wp-machine — the plan

**Status (2026-08-13): L0–L3 LANDED; the residue discharge (stage B) is
DESIGNED and in flight.**  L0 (breaking unifications), L1
(`WeakRobustBlocks.v`), L2 (`WeakSailLTS2.v`) and L3 (`WeakComposeLang.v`,
`xv6_weak_robust_lifted`/`_adequate` on the 5 baseline axioms) are all
committed, plus the Layer-1 hart-restriction fix (`violation_hart`) that
retired the DMA-author refutation.  What remains is the ONE mechanizable
residue L3 named — `xv6_block_cover` — and this file now records the
FINDING that it is refutable as stated, the replacement design (stage B),
and the staged worklist.  The original L0–L4 plan and its three resolved
obstacles are kept at the bottom for reference.

## FINDING (2026-08-13): `xv6_block_cover` is REFUTABLE as stated

`xv6_block_cover g0 u0` says: any `wp_pf_run`-reachable violating
configuration has a block-atomic (`xv6_blocks`) witness of the same
violation.  Counterexample shape (same rank as the L3 DMA-author finding):

  - hart i: plain store `m` to byte `a` (owned, unpublished);
  - hart i: `fence rw,w` — sets `w_relp` (`WeakMem.fence_post`), so i's
    NEXT store will be `WCrel` and will publish `m`;
  - hart i: begins a store instruction whose page walk CASes a PTE
    (the fork's atomic A/D update, emitted as a fused mid-block `LRmw`,
    class `WCexcl`); the pf run switches away — the CAS is in the log,
    the publishing data store is NOT;
  - hart j: reads that dangling CAS (software PTE read), branches on the
    A-bit, and racy-reads `m`.

At event granularity this is pf-reachable and `violates_at` holds (`m`
unpublished).  In ANY instruction-atomic (`WeakLang`) run the author's
instruction is atomic: either the CAS is absent (j's branch goes the
other way) or the `WCrel` data store landed with it (`m` is published).
So no block-atomic witness of the violation exists, and the premise is
false whenever the kernel can branch on a mid-instruction-dangling CAS
while its author is release-pending.  The coarse premise must be replaced
by sharper ones that exclude exactly this shape — which is also what the
static-discipline family (D-M6-8) can actually check.

## The replacement design (stage B): φ-consumption through the exhibit cone

Do NOT prove a standalone run-sorting theorem.  Instead re-derive the one
consumer — `pf_violation_free_hart`, used only by
`WeakRobustMain.no_bad_edge` via `bad_edge_violates` — in BLOCK-ATOMIC
form, inside the minimal-bad-edge exhibit where L1's machinery applies:

1. **Block-ordered cone replay.**  `bad_edge_violates` builds its
   violating config by `cone_Qinv` (topo-sorted ancestor cone of the bad
   read `b2`) + one `Qinv_step` + `Qinv_run`.  `WeakRobustSim.Qinv_step`
   needs NO global acyclicity — only "all `gdep2`-predecessors already
   processed" — so the SAME machinery replays the cone in a
   BLOCK-CONTIGUOUS order provided one exists.  Under (P1) below every
   cross edge's source is its agent's block-LAST event
   (`cut_last_fulfil` + store-last), and then the block-contracted graph
   is acyclic by behavior time (`B.last < C.mid ≤ C.last < B.mid ≤
   B.last` is a time cycle), so ordering blocks by their last event's
   position in any topo order and flattening (program order inside a
   block) satisfies `qorder`'s predecessor condition.  Non-reader agents'
   cuts then end at their last fulfil = a data store, i.e. at a boundary
   modulo the silent epilogue; the reader's cut ends at `b2`.
2. **Sail-level completion** (replaces L1's `blk_fin`, whose abstract
   `msr : P → nat` does not exist for the free monad).  Two lemmas at
   `WeakSailLTS2` altitude, both by STRUCTURAL induction on the inductive
   monad (`iMon` subterm descent is well-founded via a hand-rolled `Acc`
   kit — no nat measure needed; the fused-rmw arm descends through
   `silent_run`/`wr_node`, so the kit provides transitive-subterm
   induction):
   - silent-epilogue completion: a residual that is silent-to-`Ret`
     (supplied by (P2)) runs to `sp_m = None` appending NOTHING — safe
     for every agent including the author;
   - reader-tail completion: an arbitrary shaped residual runs to the
     boundary with FREE read values (`img_total` + `read_latest_*` for
     RAM; `oracle_consistent`'s ∀-paths form serves every device read
     and accepts every device write, which is what discharges
     non-stuckness — this is (P5), the MMIO seam premise the regrouping
     already takes per segment) and CANONICAL classes (the `PFStore` /
     `PFRmw` class binder is free; choose `lbl_class`, so `cls_canon`
     holds and the regrouping applies).  Reader-tail appends are
     j-authored and j ≠ i, so `violates_at_append` keeps the violation
     even if one is `WCrel`.
3. **Run surgery.**  Silent-epilogue completions are inserted right
   after their agent's last block via a commutation lemma
   (`pf_silent_commute`: a solo silent step touches only its agent and
   reads nothing shared, so it commutes left past any other agent's
   step).  The reader's block is the cone's sink, so its prefix + tail
   completion sit at the run's end contiguously with no surgery.
4. **Regrouping + transport.**  The resulting pf run is literally a
   concatenation of solo boundary-to-boundary blocks → map each to a
   WeakLang hart/plic/disk step by `sail_block_wrun` + the
   `WeakComposeLang` plumbing (build the `(g, u)` chain by construction,
   defining each `wgdev g'` from the chosen `wrun`, so no `hart_dev_seam`
   quantifier is owed), then refute with φ via (a direct variant of)
   `xv6_blocks_no_hart_violation`.  The final config equals `wl_cfg g' u'`
   EXACTLY (no embedding generalization needed) because the reader is
   completed pf-side.

### The premise ledger (expected; introduce each only when its stage demands it)

All per-trace (quantified like `main_premises`, joining the D-M6-8 static
family) unless noted:

- **(P1) `cas_edge_free TS`** — no `gdep2` edge (rf or gE) whose source is
  a mid-block A/D-CAS fulfil crosses agents.  This makes every cross-edge
  source block-last (kills the author-dangling corner AND gives
  block-contract acyclicity for free).  xv6 discharge story: kernel PTEs
  are A/D-canonical (kpt-share), so walker CASes happen only on user
  PTEs; software reads of those are the 6c/unmap-pinnedness discipline;
  same-PTE write races are what 6c's pinnedness excludes.
- **(P2) `store_final_shaped (riscv_step b)`** — a NEW sail_shaped-sibling
  Fixpoint on the monad: every RAM non-latest `MemWrite`'s continuation is
  silent-to-`Ret`.  Same epistemic slot as `sail_shaped` (per-instruction,
  decoder-checkable, declared); excludes misaligned page-crossing stores
  (the kernel discipline / checker family covers it).
- **(P3) irq placement** — mid-block `irq_deliver`s in cone blocks: v1
  premise "deliveries in the cone land at boundaries"; upgrade path: a
  generalized `sail_block_wrun` tolerating mid-block deliveries whose
  post-delivery events never `RegRead sig_seip` (per-site checkable —
  xv6's only mid-block sip read is devintr's `w_sip(r_sip() & ~2)`, whose
  SEIP bit is dead in the written value).
- **(P4) disk-cut shape** — the cone's disk restriction ends at a group
  boundary (burst + ALL emits), and the kept groups' `wdisk_step` holds at
  the cut's flat memory (the WeakLang disk arm pins the true flat while
  `pstep_xv6`'s burst arm is existential in it).  Upgrade path: a locality
  lemma for `VirtioModel.wdisk_step` + virtio-discipline coverage of the
  burst-read bytes.
- **(P5) oracle consistency along cone blocks** — `oracle_consistent` at
  each kept block's start (the sharpened MMIO seam; `seg_hart` already
  takes exactly this per segment).  Consumed twice: reader-tail
  non-stuckness at device nodes, and `sail_block_wrun`'s reconstruction.
- **`cls_canonical TS`** — every logged message's class is
  `lbl_class` at its author's pre-state (L2 §C route (B), the hart side;
  the disk side is canonical by construction).  Needed so replayed blocks
  satisfy `pf_solo`'s `cls_canon`.
- **`img_total (wgimg g0)`** — already in the original L4 premise list;
  discharged by the boot image (`wlat_init` covers every RAM byte).
- `rmw_tight` at replayed rmws: TRY to prove from `own_coh`
  (`WeakPromiseBridge`) + the readable window (an own write above the
  read ts contradicts `own_coh`); fall back to a premise only if it
  resists.

## Stage-B worklist

- **B1 — kit + validation** (small, self-contained):
  `iMon` subterm `Acc` well-foundedness kit (transitive descent, enough
  for the fused-rmw completion); spot-check `gE`'s definition
  (`WeakRobustOrd.gE_at`) for the (P1) statement; `wrun`'s Choose/device
  arms; confirm silent trace events carry only `gpo` edges.
- **B2 — `WeakSailComplete.v`**: the two completion lemmas (silent
  epilogue; reader tail with canonical classes), `pf_silent_commute`,
  `store_final_shaped` + its silent-tail consequence, boundary handling
  for parked fences (`sp_fence`).
- **B3 — block-ordered cone** (new file beside `WeakRobustMain`):
  trace-level block vocabulary (block index of an event; block-last);
  under (P1)+(P2): cross-sources are block-last; the block-contiguous
  topological order of the cone satisfies `qorder`; drive `Qinv_step`
  over it; extract the `violates_at` witness as `bad_edge_violates` does
  (π-relocated position).
- **B4 — completion pass**: apply B2 at the B3 config (epilogues for all
  cut agents via commutation; reader tail at the end); `violates_at`
  persistence via `violates_at_append`/`complete_cut_persists` shapes.
- **B5 — regrouping + rewire**: partition the B4 run into `sail_block`s
  (`pf_solo` per step: `cls_canonical` + `rmw_tight`), build the WeakLang
  chain directly (`sail_block_wrun` + `WeakComposeLang` plumbing, disk
  groups under (P4), plic arms under (P3)), refute with φ;
  `no_bad_edge`-variant + rewired `xv6_weak_robust_lifted`/`_adequate`;
  DELETE `xv6_block_cover` (keep the finding in §B of the file header).
- **B6 — L4 capstone**: final premise set = static package (now incl.
  P1–P5, `cls_canonical`, `store_final_shaped`) + `bad_wf` + MMIO + PARM
  note + `sail_shaped` + `img_total` + the 5 baseline axioms;
  `Print Assumptions` audit; update `WeakCompose.v` §6; fold outcomes
  into `design/weak-memory*.md`; move this file to `completed/`.

Keep the tree green at every commit; one stage per commit, findings in
the commit message.

---

## The original plan (L0–L4), for reference — L0–L3 landed

Goal: `pf_violation_free` disappears from `xv6_weak_robust`'s premise
set (discharged by `weak_system_adequacy_phi` through the lift), and
reducibility/observables transport back — the capstone
adequacy-over-RVWMO statement.

The three obstacles the analysis resolved:

1. **Granularity.**  φ is exported at INSTRUCTION boundaries; the
   sim/exhibit stops at EVENT boundaries.  Resolution — the CONE-CUT
   THEOREM (landed as `WeakRobustBlocks.cone_boundary_thm`): cross edges
   emanate from fulfils, so non-reader cuts land at boundaries or at the
   walker A/D CAS; the reader completes its own instruction and the
   violation survives.
2. **Completion admissibility.**  Under `img_total` a read is always
   admissible at the latest write or the image
   (`byte_readable_latest`, `read_latest_*` — landed).
3. **Publication alignment.**  `pub_of` is the log-based
   `WeakMem.wpublished` (landed, L0(c)); `no_violation` and `violation`
   align syntactically.

Stages: **L0** (breaking batch: DMA tid `Some n_disk`, mip-oracle
`irq_deliver`, log-based `pub_of`, PDisk `dev_state` burst/emit) —
landed f7e3ed6d.  **L1** (`WeakRobustBlocks.v`: `blk_shape`, cone-cut,
completion under `img_total`, violation persistence) — landed 335d999d.
**L2** (`WeakSailLTS2.v`: the ⇐ bracket, `sail_block`,
`wprim_hart_block`, `cls_canon`/`rmw_tight` residues) — landed 6b0e6ee6.
**L3** (`WeakComposeLang.v`: the regrouping theorem, φ-consumption
modulo `xv6_block_cover`, `xv6_weak_robust_lifted`/`_adequate`) — landed
117f9014 + b9efdfc8 (hart-restriction fix).  **L4** = stage B6 above.
