# Post-campaign ghost-state redundancy review — can the proof be simplified?

STATUS: ASSESSMENT ONLY (2026-08-19, coordinator review; nothing executed).
Verified against `main` @ `874cb5e7` (= the pushed FINAL-GATE tree).  Every
verdict below rests on a consumer enumeration run against the sources; the
two machine-checked verdicts cite the campaign's own probes (recorded in
[`../projects/iclaim-ledger.md`](../projects/iclaim-ledger.md) §5⁗″/§5⁗⁗).
Ranking metric, per the user's refinement: **contract-surface reduction
first** — a candidate that deletes Spec clauses at moderate internal cost
outranks one that only merges invariants.

## 0. Executive summary — the top three by value/cost

1. **SIMP-A: retire the `rg` binder from the runtime iput contracts.**
   `ireg_open` is persistent, so a runtime caller's "lend a copy, get a
   copy back" round-trip (`SpecIput.v:224/:291`, same on `SpecIunlockput`)
   carries no information.  State `wp_iput_sconf`/`wp_iunlockput_sconf` at
   `rg := true` internally (the persistent `ireg_open` premise those specs
   ALREADY carry supplies `ireg_regime true` on the spot); only ireclaim
   keeps the indexed `_gen` form.  Deletes: the `(rg : bool)` binder, the
   `ireg_regime` premise AND its return clause from the contract every
   runtime caller reads — ~10 proof files get one binder and two clauses
   shorter.  Cost: tiny (a specialization lemma + mechanical rethreading).
2. **SIMP-B: fold the provenance unit into the reference.**  Define the
   flavoured reference package (`inode_refb b := inode_ref ∗ runit b`,
   with the existential form at iput).  Deletes: `SpecIget`'s separate
   `runit (is_claim l)` post clause (`SpecIget.v:284`), the `runit_any`
   premise AND the `bfl` binder on `SpecIput`/`SpecIunlockput`
   (`SpecIput.v:240` — the spend destructs the existential internally),
   both `runit` clauses on `SpecIdup`, and reshapes `SpecIalloc`'s receipt
   into one package.  iget goes back to returning ONE resource — at these
   contracts the post-campaign surface becomes *shorter than pre-campaign*.
   Cost: an IIIe-sized rethread (package defs + iget/iput/idup/ilkc arms).
3. **SIMP-C (probe-gated, internal): retire the freeze RECEIPT `frzown`.**
   It predates RULING R-e; post-R-e the two decisions it was minted for are
   covered elsewhere (foreign readers: `frz_slot_kill` off the live share +
   the tail's `frzsel` quarter — that is what ProofIlock's landed kill
   actually uses; the freezer: its own phase fragment).  Its remaining
   consumer graph is a closed self-maintenance loop (`ireg_frzc`'s receipt
   half, `ic_frz_park`/`ic_out_frz`'s frozen arms, the +0x8a "receipt
   home", the deposit threading, boot's `FM` map).  If a satisfiability-
   first probe confirms no decision needs it, the kill deletes one ambient
   gname (`icfg_frzo`), one region clause half, one boot argument, and
   simplifies `ic_frz_park`/`DepFrz`.  No Spec surface — ranked third only
   because of that.

## 1. The spec-clause inventory (what the campaign added, and its fate)

| clause | verdict |
|---|---|
| `SpecIget`: `runit (is_claim l)` post (`:284`) | **DIES** into SIMP-B's package. |
| `SpecIget`: the BufL block-equation premise (`:238`) | **DIES** — move the pure conjunct into `iname`'s BufL arm itself (`IgetLic.v`); ProofIreclaim proves it at licence construction; the `discriminate` at every other call site disappears.  Cheap (SIMP-A′ rider). |
| `SpecIget`: `ireg_inv` + `inodestart` params (`:260/:218`) | **STAYS** — the count/unit mints are region-coupled by the ZZProbeIcnt mask verdict; no merge removes the region handle. |
| `SpecIlock`: the `ilkc` index + three arm premises (`:312`) | **STAYS** — the arms are three genuinely different licences (typed claim / plain unit / generation shot); no common weakening exists (the fd sites provably cannot present units — campaign finding 7b, and shares cannot carry them).  SIMP-B reshapes the ClaimK/PlainK arms to take the package, no clause count change. |
| `SpecIlock`: `ifreeze_off` post (`:391`) + return legs on `SpecIunlock`/`SpecIunlockput`/`create_locked` | **FOLDABLE, mild** — the token can ride inside the named payload bundle the post already hands over (it lives with the payload by A′-custody anyway); deletes one explicit clause + four return legs, at the price of `ireg_link_pin`'s two payers extracting it from the bundle.  Net text ≈ −5 clauses, small rethread. |
| `SpecIput`/`SpecIunlockput`: `(rg : bool)` + `ireg_regime` in/out | **DIES** for runtime callers (SIMP-A); the `_gen` form keeps it for ireclaim alone. |
| `SpecIput`/`SpecIunlockput`: `(bfl : bool)` + `runit_any` premise | **DIES** into SIMP-B (existential flavour inside the package). |
| `SpecIput`: `K_iput 74` / `K_iunlockput 78` | **STAYS** — physical budget (`K_itrunc ≤ K − 6`), not ghost. |
| `SpecIdup`: `!logG` + `ireg_inv` | **STAYS** — verified: `ireg_inv` genuinely mentions `logG` through `ireg_ep`'s `log_epoch_lb` (`InodeRegion.v:1612–1622`), and `ireg_ep` is NOT vestigial (below). |
| `SpecIdup`: the `runit` copy clauses | **DIE** into SIMP-B. |
| `SpecIalloc`: typed `iclaim ty` + `runit_claim` receipt | **RESHAPED** by SIMP-B into one flavoured package; the `ty` itself stays — it IS `create_fresh_ty`'s content. |
| `SpecDirlookup`: the (6′) equation `di_nlink dr = di_nlink dn` | **STAYS** — one pure premise, five callers pay it trivially; folding it into the licence saves nothing. |
| the persistent `ireg_open` premise on ~16 syscall-path specs | **STAYS as content**; optionally a cosmetic alias (`ireg_renv := ireg_inv ∗ ireg_open`) halves the clause pair on the runtime chain.  It cannot merge INTO `ireg_inv` — boot (fsinit/ireclaim) holds `ireg_inv` without `ireg_open`. |

## 2. The hypotheses, verified

**H1a — the freeze mirror `frzm_h` is vestigial: REFUTED.**  Consumed for
real in the final walk (ProofIput `:2260/:3055/:3766/:3872` — the phase
transitions and pool/eviction accounting) and in `frz_park`'s arms read by
ProofIget/ProofIdup.  Nor can it merge with `frzsel`: the mirror is
inum-keyed (its region half sits in `ireg_frzc` beside the f-column), the
selector is slot-keyed (its invariant half sits in `live_slot`, which has
no inum in scope) — the pair is the two sides of the k-vs-inum keying wall
(§3.13), not an accident.

**H1b — the receipt `frzown`: PLAUSIBLE→STRONG, probe-gated** (SIMP-C
above).  The one honest caveat: the probe must include the satisfiability
direction (the §5⁗⁗ lesson) — re-prove the +0x8a close and the deposit
WITHOUT the receipt before touching anything.

**H1c — the freeze pin's count conjunct duplicates R-e's mass: REFUTED.**
`live_frzn`'s whole unit excludes *foreign* shares; it does not hand the
*freezer* `cnt2 = 1` at the +0x82 re-read — that is the icnt agreement's
`icnt_freeze_forces_one`, B1's actual payout.  Both earn their place.

**H2 — icnt vs the r/rc columns: PLAUSIBLE (internal, mid-cost).**  Two
count-shaped ghosts move at every ref-word store: the ½-½ `icnt` agreement
(exact count) and the unit counters (`r + rc ≤ n` pin).  Post-7a′ every
reference carries a unit (all five mint rows mint; idup copies; iput
spends), so `r + rc = n` is plausibly an invariant — in which case `icnt`
(gname `icfg_icnt`, the pool/slot halves, the boot `CM` argument) is a
second copy of a derivable quantity.  Merge = the ledger's unit columns
become THE count; the AU family re-proves; pool bundles and `islot2` drop
their `icnt_half`; the freeze pin reads `r + rc`.  No Spec surface changes
(the region handle stays for the unit mint), so this ranks below SIMP-A/B
despite being the largest pure-ghost deletion.  Risk: the exactness
invariant must survive boot and the conversion — probe first.

**H3 — kill `rc` via a claim-implies-counted clause: REFUTED,
machine-checked.**  `c ≠ None ⟹ 1 ≤ n` is false at the claim mint itself
(`ireg_claim_au` fires before ialloc's iget: `c = Some, n = 0` is the
landed mint state) — this is exactly the counterexample that killed option
C (`probe_C_retire_counterexample`, §5⁗⁗); C′ introduced the rc column
*because* the typed claim alone cannot carry the retire's `1 ≤ n`.

**H4 — the escrow pipe: one PLAUSIBLE trim.**  `escA`'s third gname `gd`
(the deposit ticket, item 7c) exists to let the deposit refute the
FILLED/REDEEMED arms.  But the freer's `ifreeze_post rg` fragment is
already exclusive-per-window and reaches the deposit; keying the
EMPTY→FILLED move on the phase fragment instead would retire `gd`
(escrow 3→2 gnames).  Internal only; small; probe the fill mover's
exclusivity first.  The rest of the pipe is load-bearing: `pool_await`
still needs `escA_inv` (the redeem correlates through it), and the
`reg_full/reg_half` registry is what ties region-pending to pool-pending
across a free cycle.

**H5 — `ireg_ep` is vestigial: REFUTED.**  Its lower-bound face `nlz_obs`
(`InodeRegion.v:1622`) is the §G.13/§G.17 observer token — the walk's
`crz` group-credit upgrade consumes it (the `(if crz then nlz_obs …)`
premise on `ip_free_locked`, threaded from the nlink guard), and
`izrcpt`'s consumers include `SpecIupdate`/`ProofLogWrite`.  It is also
the reason `logG` is in `ireg_inv`'s closure, so no `SpecIdup` slim-down
is available here.  (The in-file note that `ireg_ep_open` is unreachable
refers to one accessor, not the piece.)

**H6 — dead weight found (cheap sweep):**
- `link_mint_freeze` / `link_spend_freeze` (`IcacheRef.v`) — stated by
  increment I for a doc shape that never landed; ZERO consumers.  Delete.
- `frz_park`'s `q` parameter — vestigial (the ghost-state doc itself says
  so).  Delete at the next touch of `IcacheInv.v`.
- `EscrowRegionA.v` — the stage-1a de-risk twin of `EscrowDefs`/
  `EscrowInode`; VERIFIED: in `_CoqProject` (`:970`) but imported by
  nothing — it compiles on every build for zero consumers.  Retire the
  row (keep the file as provenance, or move it beside the probes).
- The three `ZZProbe*` scratch files are untracked and do not travel; the
  `proof_coverage --check` drift rows they cause vanish on any fresh clone.

## 3. A priced simplification campaign (if/when the user wants it)

Gated increments, each ending at the full three-tops/standing-six gate:

1. **SIMP-1 (contract dead-weight, ~1 executor-day):** SIMP-A (the `rg`
   specialization) + the BufL-equation fold + H6's dead-lemma sweep.
   Immediate spec-surface win, near-zero risk.
2. **SIMP-2 (the reference package, IIIe-sized):** SIMP-B across
   SpecIget/SpecIput/SpecIunlockput/SpecIdup/SpecIalloc + the ilkc arms.
   The big contract shortening.
3. **SIMP-3 (gname diet, probe-first):** frzown retirement (H1b) + `gd`
   retirement (H4).  `icfg` shrinks 10 → 8 gnames.  Internal.
4. **SIMP-4 (optional, largest):** the H2 icnt-into-ledger merge —
   worthwhile only if the exactness probe is clean; otherwise skip.

## 4. Leave it alone (accreted, but load-bearing)

The `frzm`/`frzsel` pair (the keying wall); the freeze pin's count
conjunct (B1); the `rc` column and the typed claim (probe-refuted
alternatives); `ireg_ep`/`nlz_obs` (the crz credit chain); the escrow
registry (`reg_full`/`reg_half`); the `ilkc` index's three arms (three
real licences); the regime *indexing itself* (`ireg_regime`/`ireg_fsh` —
ireclaim's round-trip is the one place it cannot be specialized away);
the `ireg_open` threading (boot exists, so it cannot hide inside
`ireg_inv`); the K bumps (physical).
