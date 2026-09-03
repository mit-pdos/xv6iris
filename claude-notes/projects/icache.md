# Project: the non-coherent instruction cache

**Goal.** Make the Ztso machine (`RiscvLang.mnode_step` over
`TsoMemPa`) honest about RISC-V instruction fetch: fetches are NOT
coherent with the data side, and `fence.i` is what re-establishes order.
The generic any-user-code proof must survive ARBITRARY fetch values with
no synchronisation at all; the specific-binary proofs (`init`/`sync`/
`sh`/`echo`, the `Uk*` engine) will need a freshness receipt, threaded in a
later step.

## Rulings (owner, 2026-09-03)

1. **Two per-hart timestamps.**  A hart gets an INSTRUCTION VIEW `itv`
   beside its data view `tv`; a fetch reads at any view at or above `itv`
   and moves neither; `fence.i` is what raises `itv`.
2. **The U-mode tiers get a STABLE fetch through an invariant, not a
   value-agnostic fetch.**  The generic tier's fetch composers are on the
   `exec`+`goodmb` walker route (`HartMemRun.hmrun` answers a read from its
   own byte map), so a fetch that may return anything would need a second
   interpreter with a fetch oracle.  Instead: every executable user page is
   non-writable, every executable page's writes lie below the hart's
   instruction view, and the context tracks that — which is also what the
   specific-binary proofs (`init`/`sync`/`sh`/`echo`, the `Uk*` engine) need.
3. **Contexts get an INSTRUCTION BOUND `IB` beside their data bound `B`.**
   Invariant: every byte of an executable (X) page the context owns has
   its latest-write timestamp at or below `IB`; X pages are non-writable,
   so nothing moves it under user execution, and `exec`'s text writes raise
   it (the same way a park raises `B` past the dirty set).  The hart-side
   tie `IB <= itv` is what `fence.i` establishes (`userret` STEP 0), and it
   is what a fetch of a context's text pays with.

## The machine

- `gstate.gitv : CPU -> nat`, the icache floor; `mm_ok` adds
  `gitv c <= length glog`; reset/era-birth at 0 beside `gtv`.
- **Fetch arm** (`MemRead` at `AK_ifetch` — the tag the fork's model puts on
  instruction fetches, `RiscvExtras.rk_select`): pick `tvn` with
  `itv <= tvn <= length log`, read every byte latest-visible at `tvn`
  through `TsoMemPa.ifetch_read` = `tso_read` at `ifetch_agent`, an agent
  that never authors a message — so NO store forwarding: a hart's own store
  to code is not fetched until its own `fence.i`.  `tv` and `itv` are both
  UNCHANGED by a fetch: no per-fetch or per-line monotonicity, strictly
  more behaviours than hardware.
- **`Barrier_RISCV_i` arm**: `itv' := max tv (own_pub h log)`
  (`fence_post h log true tv` applied to the instruction view — the drain
  must cover the hart's OWN stores, which its data view never passes);
  `tv` unchanged (`fence.i` orders nothing on the data side;
  `fence_drains` stays false).  `itv <= tv` is NOT an invariant.
- `AK_ttw` walk reads stay on the data arm (TLB non-coherence is the
  sfence layer's business; PTW memory reads are coherent).
- Ghost mirror: `era_iview_name` in `riscvEraGS`, `view_auth` over the
  harts' `itv` in `tso_interp_at`; receipt
  `hart_iview_lb K := view_lb era_iview_name loglen_name (hart_agent cpu_id) K`
  (persistent, monotone: `itv` only grows).
- Litmus (`TsoMem`/`TsoLitmus`, the model of record): a fetch action and
  `fence.i`.  Verdicts: SMC without `fence.i` MAY fetch stale; with it,
  fresh.  MP-code (writer: text store, flag store; reader: load flag,
  `fence.i`, fetch) FORBIDS stale; the same reader without `fence.i` may
  fetch stale even after seeing the flag.

## Node rules and payers

- `HartEvents.wp_hart_ram_read_ifetch` (+ `swp_` twin): the plain rule with
  the obligation indexed by `itv` — `∀ tv', itv <= tv' <= length log →
  ifetch_read_bytes img log tv' pa n w` — and NO view receipt to the
  continuation.  `wp_hart_ram_read_plain` gains `ak_ifetch … = false`.
- Kernel text is era-image (timestamp 0): `TsoCtx.pristine_read_bytes_ok`
  already concludes at every agent and every view, so `HartMFetch`
  (M-mode) and `SmodeCorePt` (S-mode) swap the rule and their payer does not
  move.
- `fence.i` (`WpSmodePtCtl.swp_execute_FENCEI_s`, `UserExecFacts`' U twin,
  `UserretEntryPt` STEP 0) stops being a state identity: it mints
  `hart_iview_lb K` from `hart_view_lb K`.  The silent-node walkers
  (`HartSpan`/`HartLift2`) must let `Barrier_RISCV_i` move the iview
  authority, as the data fence already moves `tv`.

## The U-mode tiers (rulings 2-3)

**The walker never answers a fetch.**  `HartMemRun.hmrun`/`goodmb` refuse an
`AK_ifetch` read (`rk_ram_ok` has no `Read_ifetch`): the walker's value is
its own map's, which a stale fetch need not return, and `goodmb`'s ~4000
occurrences cannot grow a fetch-footprint parameter.  So every fetch node
is stepped by `HartEvents.swp_hart_ram_read_ifetch`, outside the walker,
and the U-mode fetch composers are re-cut at that node:

- `fetch tt` is `catch_early_return` of PC reads, the alignment tests,
  `fetch_bytes` (= `translateAddr` then `mem_read (InstructionFetch)`) and
  the `isRVC` split (`UserFetch.exec_fetch_bytes_ok` is the exec-level
  composition).  The swp composer walks it in the same pieces: register
  and pure nodes by the silent walker, `translateAddr` by
  `swp_hmrun_of_exec` over the existing walk certificate
  (`UserFetchCert.u_walk_fetch_pure`'s `goodmb` half, a data-arm read of
  the PTEs), `checked_mem_read (InstructionFetch)` by a User-privilege twin
  of `SmodeCorePt.swp_checked_mem_read_ifetch4_S`/`_ifetch2_S` (the PMP
  grant is `UserMem.exec_pmpCheck_user_grant`), and the tail by the walker
  again.  Four geometries, as today.
- The fetch node pays with **stamped bytes**: `TsoCtx.ctx_xpointsto ξ IK a
  dq v` is `ctx_pointsto` plus the pure stamp `ts <= IK`; `ctx_xfetch_ok`
  turns it, under `IK <= itv` (from `hart_iview_lb_at cpu_id IK` against the
  rule's `hart_iview_auth`), into `fobl_ifetch` byte by byte.  Data use of
  a text byte (rodata) goes through `ctx_xpointsto_forget`.
- **Where the stamp comes from.**  `ctx_xstamp` mints it from a RUNNING
  context's fact at a `fence.i`: with `own_context` every fact is clean
  (`ts <= B <= K <= tv`) or dirty and mine-on-this-hart (`ts <= own_pub`,
  `TsoMemPa.own_pub_lookup`) or under the bound, and the arm's `itv'` passes
  both `tv` and `own_pub`.  The `fence.i` leaf (a `HartBarrier`-style rule
  at `Barrier_RISCV_i`, minting `hart_iview_lb_at cpu_id itv'`, with a ghost
  step at `⌜gtv <= itv'⌝ ∗ ⌜own_pub <= itv'⌝`) is where `userret` STEP 0
  stamps the process's executable pages.  No `CtxId` field, no
  `own_context` change: the context's "instruction bound" IS the `IK` the
  stamped facts and the receipt carry.
- Why it stays true while the process runs: executable user pages are
  non-writable (the `user_pt_inv` permission map: X ⇒ ¬W), so a stamped
  byte's timestamp does not move under user execution; the kernel writes
  text only in `exec`, before the next `fence.i`.
- The bundle: `uvb`/`ukb` carry `hart_iview_lb_at cpu_id IK` and the text
  pages as `ctx_xpointsto ξ IK`, from the slot entry (`userret`) to both
  tiers' fetch composers (`UserFetchCert`/`UserActiveClass.swp_fetch_of_pure`
  for the safety tier, `UmodeFetch` for the verified one).

## Order of work (gate: full build green + `make audit-only` unchanged)

1. `TsoMemPa` (`ifetch_agent`, `ifetch_read`, its lemmas), `TsoMem` +
   `TsoLitmus` (the verdicts above).
2. `RiscvLang` (field, arms, `mm_ok`, insert instance, write-back,
   reset), `TsoGhost`/`RiscvPtsto` (gname, auth conjunct, receipt),
   `RiscvAdequacy` (the mint at era birth).
3. `HartEvents` rules; `HartSpan`/`HartLift2` fence arm; `HartMemRun`
   refusal; `HartMFetch`/`SmodeCorePt` swap; fence.i leaves mint.
4. `TsoCtx.ctx_xpointsto` + `ctx_xstamp` + `ctx_xfetch_ok` (landed); the
   `fence.i` leaf minting the receipt and running the stamp.
5. The U-mode fetch composers re-cut at the fetch node (the `_U` twins of
   the S-mode `checked_mem_read` fetch lemmas, the four-geometry composer),
   `user_pt_inv`'s X ⇒ ¬W fact, and the bundle threading from `userret`
   STEP 0 to both tiers.
