# Closing the lift gap (seam 1): WeakLang ↔ wp-machine — the plan

**Status (2026-08-12): PLANNED, design analysis done (coordinator).**
Goal: `pf_violation_free` disappears from `xv6_weak_robust`'s premise
set (discharged by `weak_system_adequacy_phi` through the lift), and
reducibility/observables transport back — the capstone
adequacy-over-RVWMO statement.  Pre-port machinery changes are allowed
and two are load-bearing (L0, L1).

## The three obstacles the analysis resolved

1. **Granularity.**  φ is exported at INSTRUCTION boundaries (the WP
   steps whole instructions); the sim/exhibit stops at EVENT
   boundaries.  Resolution — the CONE-CUT THEOREM: in the bad-edge
   exhibit's ancestor cone, every NON-reader agent's cut lands at an
   instruction boundary automatically, because every cross edge
   (rf, gE source, gE target) emanates from a FULFIL and a block's
   data store is its LAST event ("store-last block shape" — state as
   `blk_shape` on the abstract LTS, satisfied by `sail_step` by
   construction).  Exception: cuts at a mid-block walker A/D CAS
   (WCexcl fulfil, not block-last) — handled by COMPLETION (below).
   The READER itself is mid-block by necessity; complete its own
   instruction: the violation SURVIVES to the reader's next boundary
   (its coh only grows; ¬pub is per-author and the reader ≠ author;
   the author is at a boundary since its bad store is block-last, and
   a block has at most one data store, so no author-WCrel can appear).
2. **Completion admissibility.**  Completing a cut agent's residual
   block events needs readable values in the pf prefix.  Reads are
   always admissible at the LATEST processed write or the image
   (`latest_readable` + `ws_bounded`) PROVIDED the image is total on
   RAM — add **`img_total`** as a stated lift premise, discharged by
   the boot image (wlat_init covers every RAM byte).  Program states
   of completed-with-other-values agents are irrelevant (the violation
   reads only log + wstates, and completion only grows floors —
   growing OTHER agents' coh can only create new violations, never
   destroy ours).
3. **Publication alignment.**  Replace `WeakRobustMain.pub_of` (the
   wstate-w_pub form) with the LOG-BASED `wpublished` (pure, monotone
   under append) — Layer 1 takes pub as a parameter, so this is a
   re-instantiation, and it DELETES the `wpub_covers` wiring debt:
   `no_violation` and `violation` then align syntactically, and the
   exhibit's ¬pub follows directly from bad's no-publish-ancestor
   conjunct (no w_pub fold reasoning).

## The stages

**L0 — small breaking unifications (one batch, do first):**
(a) DMA tid: `WeakLang.wmsgs_of_map` stamps `Some n_disk`
(n_disk = NCPU, matching `pstep_xv6`'s PDisk index); re-key the
tid-None exemptions (`wcds_clean`/`wcds_dirty`, `no_violation`, `bad`)
on `i < NCPU` / an `is_hart` predicate.  (b) mip-oracle: interrupt
bits delivered to a hart become oracle events in `psail` (plic writes
other harts' registers — inexpressible in the log-only wp machine
otherwise); `plic_step` maps to oracle consumption under the MMIO
seam.  (c) `pub_of` → `wpublished` per obstacle 3.  (d) Tighten
`PDisk`: thread `dev_state` + `wdisk_step`-shaped constraints
(replaces the documented superset; the lift's disk arm then maps
1:1).

**L1 — block structure (`WeakRobustBlocks.v`):** `at_boundary : P →
Prop` + `blk_shape` (fetch/reads first, ≤1 data store, store-last;
walker A/D CAS allowed mid-block) on the abstract LTS; `sail_step`
instances; the cone-cut theorem (non-reader cuts are boundaries or
A/D-CAS points); the completion lemma (obstacle 2, under
`img_total`); the reader-completion violation-persistence lemma.
This refines the EXHIBIT only — the full-behavior sim needs no block
machinery (its final config is all-boundaries).

**L2 — the ⇐ bracket (`WeakSailLTS` additions):** a completed
`sail_step` block ↦ one `wrun` execution.  Determinism is NOT needed:
`silent_run` existentially contains the Choose values, so the inverse
walks it and supplies them.  Then hart-arm equivalence: one
`wprim_step` hart step ⇔ one block, with `whart_view`/`whart_write`
framing.

**L3 — `WeakComposeLang.v`:** block-atomic pf runs ↦ WeakLang runs
(hart blocks via L2, disk blocks via L0(d), device/oracle steps
inserted under the MMIO premise; power arm vacuous — gen-0 pinned);
the φ-consumption corollary: `pf_violation_free cls_of wpublished
(pstep_xv6 next) img ps` DERIVED from `weak_system_adequacy_phi` +
the lift + obstacles 1-2's lemmas; the reducibility/observables
transport.

**L4 — the capstone:** the final adequacy-over-RVWMO theorem with the
premise set reduced to: static package (edges_split/ee_ok/bytes_ok) +
`bad_wf` + MMIO + PARM note + `sail_shaped` (until the whole-image
sweep) + the 5 baseline axioms + `img_total`.  Print Assumptions
audit; fold outcomes into the notes; update `WeakCompose.v` §6.

## Order and risk

L0 is mechanical but breaking — quiet point, one agent.  L1 is the
research-residue stage (the cone-cut and completion lemmas; the
A/D-CAS-cut corner is the one place new machinery might still be
needed — if completion at such a cut resists, the fallback is a
sub-block boundary notion for translate+A/D, confined to L1).  L2/L3
are bounded; L4 is assembly.  L1 ∥ L2 after L0; L3 after both.
