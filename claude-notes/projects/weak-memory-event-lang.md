# The event-granular weak language — spike worklist

**Status (2026-08-14): SPIKE IN FLIGHT.**  Design:
[`design/weak-memory-event-granular.md`](../design/weak-memory-event-granular.md).
This spike DECIDES the architecture pivot: it either demonstrates the
port pattern or names the structural blocker, before the M4 port targets
more files at the instruction-atomic interface.  The superseded
instruction-atomic machinery is retained side by side for its failure
record; do not delete any of it during the spike.

## Spike deliverables (timeboxed; each is a named artifact)

- **S1 — the language** (`iris/WeakEvLang.v`): σ = `wgstate` + per-CPU
  `hs`/parked-fence + disk `pend`; token expressions unchanged; the
  event-step relation per the design table (fused RMW one event; store
  classes computed; no oracles — device arms against σ.dev; irq from the
  wire; stuck-is-fine).
- **S2 — the correspondence** (`iris/WeakEvPf.v`): the definitional
  bijection `erased_step ≡ wp_pf_run (pstep_xv6 riscv_step)` (pool/σ ↔
  `wpcfg pxv6` layout repackaging; both directions; the disk agent 1:1).
- **S3 — interp + adequacy skeleton** (`iris/WeakEvAdequacy.v`): the
  state interpretation instantiated per event (reuse the C/D/S ghosts,
  log auth, hart views; add the three new exclusive points-tos:
  `hart_prog`, fence, `disk_pend`); the φ export re-derived —
  SUCCESS CRITERION: `pf_violation_free_hart cls_of pub_of n_disk …`
  derived from the new adequacy with ZERO glue premises.
- **S4 — the instruction-chain lemma + two leaves**: the generic lemma
  turning a per-instruction certification (the existing
  interpreter-walking data) into a chain of event-WPs, stated
  interference-stably (the log may grow between events — floors are
  monotone; this is THE load-bearing unknown, fail criterion 1); port
  ONE plain store leaf and ONE racy-load leaf.
- **S5 — one whole-function proof**: the `started`-flag handshake
  (publish + racy read + fence) re-proven on the event language,
  measuring proof-size delta vs the instruction-atomic original
  (SC-parity check at the new granularity).
- **S6 — the 6c retarget note**: how the translation/walk proofs land at
  event granularity (the walk-bridge dissolution made concrete; what of
  `WeakStale` survives as history).

## Fail criteria (named in advance — hitting one ENDS the spike with a
## record, not a workaround)

1. A leaf that cannot be stated interference-stably at event granularity.
2. An invariant that must span multiple events of one instruction and
   cannot become a ghost protocol.
3. The correspondence (S2) failing to be definitional (needing a
   simulation = the lift again).

If a fail criterion hits: write the finding, keep the spike branch as a
record, and the bounded-glue fallback (finish `rv64d_live_residue`'s 431
enumerated sites; ledger as at premise-elimination C9) becomes the plan,
chosen with eyes open.

## After the spike (not in scope now)

- Retarget the M4 port to the event interface; port the weak leaves via
  the chain lemma; retire the lift tree to `completed/`.
- Phase 2 of [`weak-memory-premises.md`](weak-memory-premises.md)
  (exhibit-level discharge of `main_premises` from per-site WWP tokens)
  proceeds unchanged — it is granularity-independent and is the
  discharge campaign for the one remaining genuine premise family.
