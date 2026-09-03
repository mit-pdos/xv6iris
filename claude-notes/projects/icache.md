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

- The fetch node inside the walker: `hmrun` keeps answering an `AK_ifetch`
  read from its map; `swp_hmrun` justifies it with a FETCH twin of
  `bytes_own_tso_read_of` — the map's bytes are what `ifetch_read` returns
  at every view `>= itv` — paid by the context's `IB` (each fetched byte has
  `ts <= IB`) and the tie `IB <= IK` with `hart_iview_lb IK`.
- The context's instruction bound: `ctx_at` grows a second monotone
  authority `IB`; a text byte's fact carries "under `IB`" the way a clean
  data fact carries "under `B`".  `exec` writing text moves `IB` past its
  writes before the process runs; `own_context` (while running) carries
  `∃ IK, hart_iview_lb IK ∗ ⌜IB <= IK⌝`, minted at `userret` STEP 0 — where
  `own_context`'s data tie gives `ts <= B <= K <= tv` (clean) or
  `ts <= own_pub` (dirty, mine on this hart) for everything the context
  owns, and the arm sets `itv' >= max tv own_pub` — and dropped by `park`.
- Why it stays true while the process runs: executable user pages are
  non-writable (the `user_pt_inv` permission map: X ⇒ ¬W), so their bytes'
  timestamps do not move under user execution.
- The bundle: `uvb`/`ukb` carry the tie from the slot entry (`userret`)
  down to the fetch composers (`UserFetchCert` for the safety tier,
  `UmodeFetch` for the verified one — both take the same payer).

## Order of work (gate: full build green + `make audit-only` unchanged)

1. `TsoMemPa` (`ifetch_agent`, `ifetch_read`, its lemmas), `TsoMem` +
   `TsoLitmus` (the verdicts above).
2. `RiscvLang` (field, arms, `mm_ok`, insert instance, write-back,
   reset), `TsoGhost`/`RiscvPtsto` (gname, auth conjunct, receipt),
   `RiscvAdequacy` (the mint at era birth).
3. `HartEvents` rules; `HartSpan`/`HartLift2` fence arm; `HartMemRun`
   refusal; `HartMFetch`/`SmodeCorePt` swap; fence.i leaves mint.
4. The context's instruction bound (`TsoCtx`: the authority, the tie in
   `own_context`, `park`/resume, the `fence.i` mint) and the walker's fetch
   payer (`bytes_own` fetch twin, `HartMemRun`); `user_pt_inv`'s X ⇒ ¬W
   fact.
5. The bundle threading from `userret` STEP 0 to both tiers' fetch
   composers.
