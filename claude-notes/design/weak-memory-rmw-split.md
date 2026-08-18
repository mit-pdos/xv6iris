# The RMW split at the weak tier — mirroring the reservation design (2026-08-18)

**Status: DESIGN (orchestrator), user-confirmed.  Borrow the SHAPE of
`main-cycle-port.md` §3a (the hart-node-port branch, stable) — not the file.
The SC tier's design is SETTLED there ("do not re-fuse"); this file is its
weak-memory version.  Validation against the tree and the precise re-land
inventory: the S-track of
[`../projects/weak-memory-certification.md`](../projects/weak-memory-certification.md).**

## 1. The change in one line

The fused `LRmw` label (and the `WPRmw`/`PFRmw` arms and the event language's
`ak_latest`-triggered fused arm) dies.  An exclusive read and a conditional
write are SEPARATE labels; atomicity is a per-byte window check at the
write's FULFIL, keyed by an AGENT-LOCAL reservation set by the read; the SC
tier's blocking self-loops do not cross over (there is no waiting in a
promise machine — the window at fulfil is the same fact `resv_ok` + blocking
realize at SC).  `WPPromise` and the front-loading factorization
(`wp_behavior_factor`) are untouched: the reservation never touches the log,
and fulfils read only the agent's own state.

Why (recorded in layer2 §13's addendum): §3a's reachability table — a
dangling exclusive read is REACHABLE (the walker's A/D re-read race,
`check_leaf_pte` Err, AMOCAS mismatch) and one cycle carries up to three
exclusive reads, earlier ones superseded.  The event language's fused arm
makes exactly those traces STUCK today; the kernel WP corpus is landing on
the split shape; and PARM (the D8 port source) is itself a split machine.

## 2. Labels

- **`LExLoad aq base tvs asrc`** — new constructor (not a flag on `LLoad`:
  a new constructor makes every match site compiler-flagged).  Read
  semantics IDENTICAL to `LLoad` with `lat = false` (named per-byte
  timestamps; view rules verbatim `LLoad`'s), plus the reservation write
  (§3).  No `lat`: exclusivity and latest-indexing decouple (see §6).
- **`LExStore rl base data asrc vsrc`** — new constructor.  Write semantics
  of `LStore` plus the window check and reservation clear (§4).
- `LRmw` deleted, with its view rules and both machine arms.

## 3. The reservation (agent state)

`wstate` gains `w_res : option resv`, `resv :=` the per-byte pairs
`(addr, ts)` of the exclusive read (gmap or list — whichever `tvs` already
speaks), PLUS the read's post-view contribution (one `nat`, see §4 EXT).
Values are NOT carried: the log at `(b, ts)` has them; any consumer
(the walker discriminator, WP rules) reads them from the log.

Rules — exactly §3a's, relabeled:

| §3a (SC) | here (weak) |
|---|---|
| exclusive read sets `gresv cpu := snapshot`, superseding | `LExLoad` fulfil sets `w_res := Some R`, superseding |
| EVERY `MemWrite` of the hart clears its reservation | every `LStore`/`LExStore` (and device-write) fulfil clears `w_res` |
| boundary `Ret` clears it | `LInstr` clears it |
| blocked-read drops own / blocked-write keeps | no counterpart (no blocking) |
| `resv_ok` (snapshot ⊆ memory) | no counterpart: the window check at the write's fulfil IS that fact, said in coherence order |
| other harts' overlapping writes self-loop | `excl_ok`'s per-byte no-foreign-write window, checked at the `LExStore` fulfil |

`w_res` is NOT monotone (set/cleared/superseded) — it joins `w_regv`/`w_fwd`
outside the `ws_le` fragment, and the L2-M1 window idiom (`no_instr`-style
named windows) is the expected proof currency for carrying it between the
read and the write.

## 4. The write's fulfil (where `excl_ok` moves)

`LExStore` fulfil at timestamp `ts`, agent state `w_res = Some R`:

- **footprint match**: `dom R =` the byte footprint of `(base, |data|)`.
  On mismatch or `w_res = None`, the arm degrades to the PLAIN store
  semantics (§3a: "a standalone conditional write is a plain store"; the
  model never produces one, but totality parity with the SC tier is free).
- **the window, per byte** `b`: no message on `b` in `(R(b), ts)` — today's
  `excl_ok` check verbatim, the lower bound from the reservation instead of
  the fused label's `tvs`.
- **EXT**: `fulfil_vpre` additionally includes the reservation's view (the
  read half's post-view, banked into `w_res` at the `LExLoad`) — preserving
  deviation D-2's strength; this is PARM's exbank-view contribution, and it
  is what keeps `WeakCertify`'s vcap-promise lemma one line at this arm.
- fulfilment then clears `w_res`.

Machine arms: `WPRmw` is replaced by the ordinary promise + this fulfil;
`PFRmw` by the append-at-top form of the same arm (the window check against
the log as it stands — a pf conditional write whose window is dirty simply
has no step, which is the O-FRESH/None path's semantics).  The derived
`wpstep_rmw_now` becomes `wpstep_exstore_now`.

## 5. What deliberately does NOT cross from §3a

Blocking self-loops (an SC totality/Löb device); the value snapshot (the log
carries values); the accepted-dangling-deadlock analysis (liveness, no
counterpart); `resv_ok` as a state invariant.

## 6. The event language and the interpreters

- The producer key is **`ak_excl`** (one predicate keys all three
  `AV_exclusive` sites, per §3a's table) — NOT `ak_latest`.  Exclusive
  `MemRead` → `LExLoad`; the window's silent nodes are ORDINARY nodes;
  conditional `MemWrite` → `LExStore`.  The fused `ewr_node`/`esilent_run`
  window machinery dies.
- `ak_latest` decouples: `av_latest AV_exclusive = true` was the fusion
  trigger; after the split, `lat` reads remain what they were (the disk's
  flat read) and exclusive reads are NOT `lat` — audit every `ak_latest`
  consumer for which of the two meanings it wanted.
- Dangling exclusive reads become LEGAL traces (superseded at the next
  `LExLoad`, cleared at `LInstr`): the walker's O-FRESH and `check_leaf_pte`
  Err paths and the AMOCAS-mismatch path enter the model of record.  The
  walk-bridge shapes (`WeakKpt` shape 3/4) re-state against the two labels.
- `WeakDeps`: `ORamo`'s label sequence becomes read-label … write-label;
  the `rd` write (`LRegW rd [DLdRes]`) is unchanged (the read half still
  banks `w_ldv`).

## 7. Invariants of the re-land

- `Print Assumptions` on both capstones unchanged at EVERY slice boundary;
  tree green per slice; no `Admitted`/`Axiom`.
- The certification file (`WeakCertify.v`) re-lands mechanically: the new
  fulfil arm satisfies the same vcap shape (§4 EXT keeps D-2).
- L2-M1/M2's RMW vocabulary re-indexes from one event to a (read, write)
  pair: `rmw_reads_pred` becomes "the paired write writes immediately above
  what its read read" (same proof content, window now from `w_res`);
  `cs_window`'s acquire becomes `(ka_read, ka_write)` with the `aq` bit on
  the `LExLoad`; C2's "aq entry" likewise.  Arguments survive; statements
  move.

## 8. Slices (implementation order)

- **S1**: labels + `w_res` + `WeakMem` view/state rules.
- **S2**: `WeakPromise` arms + `WeakPromiseFact`/`Bridge` (front-loading
  re-proved over the new arms) + `excl_ok` restatement.
- **S3**: event language + `WeakInterp` + walk bridge (+ `WeakDeps`).
- **S4**: `WeakRobust*` re-index (Ser/Disc/L2/L2b vocabulary).
- **S5**: `WeakCertify`, litmus files, capstone re-verification.

The precise file/lemma inventory per slice is produced by the S-track's
validation pass before S1 starts.
