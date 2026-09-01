# TSO ESCROW ENDGAME: the unified custody design (2026-09-01)

STATUS: AUTHORITATIVE.  This document supersedes the escrow-related parts
of A6.142/A6.147/A6.148/A6.149 as the *current* statement of the design.
The A6-series remains the historical record; when this file and an A6
entry disagree, this file wins.  RULE: corrections to this design are
made by EDITING THIS FILE IN PLACE (with a one-line changelog entry at
the bottom), never by appending a new "correction of the correction"
elsewhere.  Agents inherit one design, not a debate.

## 0. Why this document exists (the diagnosis)

The remaining red cone is one design point: five invariant/cinv bodies
own ξ-indexed cells (itable_inv [DONE, A6.145], buf_escrow [mid-flight],
ic_escrow, inode_pay's cinv, off_hold's cinv).  The work so far produced
the right *mechanisms* — CtxAnchor, pinw/ctx_values, context-λ lock
payloads, the llb-tier acquires, lock_pay_intro_llb — but the effort
spiralled, for five identifiable reasons.  Name them so we stop doing
them:

1. **Freshness was never designed globally.**  "How does a withdrawer
   know its floor covers the box's *current* stamp?" was answered three
   times in three days (A6.147 → correction → A6.149), each time from
   one site's measurement, and the final answer ("both instruments stay;
   the freshness theorem picks per case") leaves the actual per-case
   proof undesigned.  §3 below closes it, once, for every box.

2. **Instrument-first, consumers-later.**  The pinw tier grew ~15
   bespoke AU accessors and the icache reference bundle grew ~22
   spellings (ref/shr × gen/genlo/bare/short/frac0/pin0/…) because
   floors were retrofitted onto existing predicates while trying not to
   touch consumers — and then the consumers were swept anyway, twice
   (the pin0 era, then the cred_floor era).  Compatibility wrappers do
   not avoid the consumer cost; they defer and multiply it.

3. **SC-era protocol shapes were ported arm-for-arm.**  ic_escrow's
   five arms encode SC choreography (mid/held/empty) whose *reasons*
   die under the ratified ownership split (locks own their domains;
   the box owns only transit).  "Transfer the bcache design verbatim"
   must mean transferring the SPLIT ANALYSIS, not the arm count.

4. **Premises were invented inside proofs.**  BioBox's checkout/drop
   withdraw premise `□(∀ n T, astamp γ n T -∗ ⌜T ≤ Kfl⌝)` bounds every
   generation ever minted; no caller-side ghost can produce an upper
   bound on a mutable stamp, so ProofBread:688 would have discovered it
   undischargeable mid-proof and bolted on another instrument.  §3
   replaces the premise shape.  New rule: when a proof needs a premise
   the design doesn't provide, STOP and fix the design doc — never
   improvise an instrument in a proof file.

5. **Append-only notes.**  Three contradictory guard-route rulings
   coexist in tso-machine-flip.md.  Hence the in-place-edit rule above.

## 1. The frozen layer architecture (the allowed-forms law)

Under the TSO model a physical cell has exactly THREE sound assertion
tiers, and every construction in the tree must be one of them:

  T1 HART tier    ctx_phys_pointsto ξ, ξ RUNNING (own_context ξ).
                  Exact value, usable now.  Never inside an inv body.
  T2 BOX tier     cells at a PARKED ξb with stamp T (ctx_parked),
                  packed ∃ξb inside an inv (CtxAnchor).  Exact value,
                  clean at T; withdrawing costs a floor ≥ T.
                  Lock records are the degenerate instance (payload =
                  bundle, AMO win = the withdraw right).
  T3 LEDGER tier  value-set pins above a floor (pinw / ctx_values /
                  pin_ok).  Racy read: any view ≥ floor settles in S.
                  For lock-free reads and immutable-while-armed cells.

Motion: park/deposit (T1→T2, free — the stamp rises past K⊔W);
absorb/withdraw (T2→T1, pay a floor); pin mint/forget (T1↔T3).

THE LAW for invariant and cinv bodies: only (a) ξ-free ghosts, (b) T2
custody with ξb ∃-packed inside, (c) T3 pins.  Lock payloads are
context-λs (CtxMorph).  Credentials appear in exactly one form:
`cred_floor lo tl := ctx_floor cur_ctx tl ∨ ctx_wrote cur_ctx lo _`
(A6.146), and floors are DELIVERED only by:

  R1  the llb-tier acquire posts (SpecAcquire/SpecAcquiresleep,
      LANDED): present `llb Tl` before the acquire, receive
      `∃K, ⌜Tl ≤ K⌝ ∗ ctx_floor cur_ctx K` at the win; and
  R2  lock-payload floor rows folded at release via
      `lock_pay_intro_llb` (LANDED) / the `_in` finisher
      (`lock_finisher_close_in_llb`), received through the payload
      morph at the next win.

No third route.  No new acquire exports.  No lock_finisher
generalization (the `_in` family already absorbs the deposit —
A6.144-closed).  No prophecy variables (the A6.142 analysis stands:
sound but costs operational-semantics surgery for no marginal win once
the box exists).

**The two-spellings rule.**  Every client resource has exactly TWO
forms: the HOLDER form (∃-packed (g,lo,tl) with cred_floor inside —
the live_fracc / inode_*_genlo shape) and the PARKED form (ξ-free:
genlo/ghost only — the only form inside inv bodies).  Conversions:
park = forget (free), unpark = re-mint at a named seam (R1/R2).
Introducing a third spelling of anything in this space is a design
error; stop and come back here.  (The existing _bare/_gen/pin0 strata
are green and LEFT ALONE until the post-endgame cleanup, §6; they may
gain no new dependents.)

## 2. The Transit Box, finalized (3 arms, forever)

One custody shape covers every remaining cross-lock protocol.  A box
instance is declared by:

  - bundle  P : CtxId → iProp   (CtxMorph; the travelling cells+pay)
  - residue Q : iProp           (ξ-FREE, ghost-only checkout residue)
  - guard locks L1, L2          (bcache: bcache.lock / b->sleeplock;
                                 icache: itable.lock / ip->sleeplock)
  - a presence/identity ghost (below)

and its body is, FOREVER, three arms:

  box_body := ∃ n T ξb rb rp,
     anchor γa n ξb T ∗ astamp γa n T ∗ llb T ∗
     pres_core rb ∗ regs rb rp ∗ ⌜tie n T rb rp⌝ ∗
     ( P ξb              (* IN:   bundle parked at ξb            *)
     ∨ Q                 (* OUT:  checked out; ghost residue      *)
     ∨ pres_none )       (* IDLE: refs 0; content in L1's payload *)

Transitions (the four from BioBox, keep the names):
  bump      IDLE→IN   deposit under L1 (refs 0→1)
  checkout  IN→OUT    withdraw under L2 (the sleeplock win)
  park      OUT→IN    deposit under L2 (before releasesleep)
  drop      IN→IDLE   withdraw under L1 (refs 1→0)

HARD RULES:
  - Exactly these three arms and four transitions.  A protocol that
    seems to need a fourth arm or a fifth transition puts the extra
    STATE INSIDE Q (Q is ξ-free ghost — clients may structure it as any
    disjunction they like without touching custody or freshness) or
    dissolves it into a lock payload.  A genuine fourth custody arm is
    a design error — stop.
  - The IN-arm refutation stays the client's full-cell/token clash
    (ctx_word4_excl_x etc.); OUT refutation = Q-exclusivity; IDLE
    refutation = pres validity.  These are the only per-client lemmas.

**Rule of two**: land the bcache concretely first (BioBox is 90%
there); extract the generic `CtxBox.v` (arms + registers + transitions
+ cover lemmas, parameterized by P/Q/locks) WHILE building the icache
instance, so both instantiate one core and cannot drift.  Do not
functorize before the second client exists.

## 3. THE FRESHNESS DESIGN (the deposit-register pattern)

This section is the load-bearing new content: a closed, total answer to
"the withdrawer's floor covers the current stamp", replacing BioBox's
undischargeable `□(∀ n T, astamp …)` premise and A6.149's per-case
hand-wave.

### 3.1 The principle

Freshness cannot be a persistent snapshot (a snapshot can't prove
currency) and cannot be an exclusive ticket (the checkout right is
genuinely shared among ref-holders — any of them may win the
sleeplock first).  The only sound device is: **every deposit publishes
its (generation, stamp, llb) into a register that every one of ITS
legal withdrawers can reach, and the box's pure invariant says which
register is current.**  Withdraw = open box, case-split the tie, agree
with the reachable register, cash its llb/floor by R1 or R2.

### 3.2 The registers (bcache instance; icache is isomorphic)

Ghosts (all tiny, additive; no model or Σ-arm changes):

  - **pres, enriched**: `authR (optionUR (prodUR (agreeR (prodO natO natO))
    positiveR))` replacing `auth (option positive)`.
    ● Some((n_b,T_b), count) — where (n_b,T_b) is the generation and
    stamp of the LAST BUMP — lives **in the box body** across IN/OUT
    (not in L1's payload as A6.148 had it; the withdrawer must reach it
    at the box open).  ● None is the IDLE arm.  Every reference carries
    ◯ Some((n_b,T_b), 1) plus a persistent `llb T_b` (minted from the
    bump's anchor_deposit export; later refs copy it out of the box at
    their refs++, which opens the box for the count edge).
    Validity at any box open gives the fragment (n_b,T_b) = the body's
    — THE CURRENCY ARGUMENT FOR THE BUMP CASE, by ◯/● validity NOW,
    not by history.
  - **reg_park**: `ghost_var γp (1/2) (n,T)` — one half in the box
    body, the other half + `astamp γa n T ∗ llb T` as a ROW IN THE
    SLEEPLOCK'S PAYLOAD R.  Updated at PARK: the parker holds R (it
    holds the sleeplock) AND opens the box — both halves in hand.
    The llb becomes a floor for the next winner via R2 at releasesleep
    (the SleepLock record threading listed as NEXT in r77 — build it
    as this row).
  - **reg_drop**: `ghost_var γd (1/2) (n,T)` — one half in the box,
    the other half + astamp/llb row in L1's (bcache.lock's) payload.
    Synced (rd := rp) at every refs-- decrement: the decrementer holds
    L1's payload and opens the box.  Floor delivered by R2 at the
    decrementer's L1 release.
  - **reg_last** (the self-park receipt): `ghost_var γl (1/2) (n,T)`.
    The box holds one half; PARK hands the other half to the parker as
    its receipt; the parker's later refs-- decrement returns it (same
    step that syncs reg_drop).  Invariant: both halves in the box ⇒
    reg_park = reg_drop.  This is what makes the drop-site case split
    total without naming "the thread that parked last".

The box's pure tie (maintained by inspection at each of the four
transitions, all of which hold the needed halves):

  tie n T rb rp  :=  (n,T) = rb ∨ (n,T) = rp

plus, carried by the γl pairing:  γl-whole-in-box → rp = rd.

### 3.3 The covers, per site (total case splits)

  CHECKOUT (under L2; winner holds: its pres fragment + llb T_b, the
  sleeplock payload R, its win floors):
    case (n,T) = rb:  fragment agrees with pres ● (validity now);
        cash `llb T_b` via R1 — the llb-tier acquiresleep, Tl := T_b,
        which the caller knew BEFORE the acquire from its fragment.
    case (n,T) = rp:  R's reg_park half agrees with the body's half;
        R's row carries the floor (folded by R2 at the last
        releasesleep — no releasesleep, no winner, so no gap).
    Both cases end in `ctx_floor ξ K, T ≤ K` → aguard_intro →
    anchor_withdraw.  No other case exists (the tie).

  DROP (under L1; dropper holds: its fragment + llb T_b, L1's payload,
  its own park receipt γl-half + own llb T_park if it parked, win
  floors from its L1 acquire):
    case (n,T) = rb:            fragment route, as above (R1 at the
                                L1 llb-tier acquire, Tl := T_b).
    case (n,T) = rp, I parked:  γl agree pins rp = my park; cash my
                                own `llb T_park` via R1.
    case (n,T) = rp, not mine:  γl is whole in the box ⇒ rp = rd;
                                L1-payload row's floor via R2.
    Totality: at refs=1 the previous holder's decrement (which synced
    rd and returned its γl half) is L1-ordered before my acquire; the
    pure tie + γl pairing make the split exhaustive in-logic.

  BUMP and PARK are deposits: no cover needed (anchor_deposit is free);
  they UPDATE their registers and export astamp/llb.

The four BioBox transition lemmas keep their shapes but their withdraw
premises become: `astamp γa n T` for the body's n (delivered inside the
lemma by the case split) `∗ ctx_floor ξ Kfl ∗ ⌜T ≤ Kfl⌝` — i.e. exactly
`aguard` at the current generation, produced by TWO reusable cover
lemmas (`box_cover_checkout`, `box_cover_drop`) stated once in the box
file.  Delete the `□(∀ n T, …)` premises.

### 3.4 What this buys

- No per-site freshness improvisation: every future withdraw site is
  one of the two cover lemmas.
- Both landed instruments (R1 llb-tier acquires; R2
  lock_pay_intro_llb) are used, each in a fixed role: R1 cashes an llb
  the withdrawer personally carries (fragment or own park); R2 delivers
  floors that must cross threads (payload rows).  A6.149's "both stay"
  becomes a rule instead of a shrug.
- The registers are ghost_var pairs + one enriched auth — no new
  model arms, no Σ churn beyond small per-box cmras (anchorR
  precedent).

## 4. Instance plans

### 4.1 bcache (finish Phase 5) — rounds R1–R2

R1 (design retrofit, small):
  - Enrich bn_pres's cmra ((n_b,T_b) agree × positive); move ● into
    buf_box_body's IN/OUT arms; IDLE keeps ● None.  (BioInv pres kit:
    ~4 lemmas touched.)
  - Add γp/γd/γl ghost_vars to bio_names; add the reg halves + tie to
    buf_box_body; add the astamp/llb/floor rows to the sleeplock
    payload (the SleepLock record threading — this IS r77's "NEXT"
    item, shaped as a payload row) and to bio_slot_res2's Some-arm.
  - Restate the four transitions' premises per §3.3; prove the two
    cover lemmas.
  Gate: BioBox/BioInv/SleepLock green.
R2 (the cutover): ProofBread/ProofBrelse at the six measured sites
  (A6.147 map): sites 1–4 become bcache_res2 payload cell ops; site 5 =
  checkout (llb-tier acquiresleep with Tl := fragment's T_b); site 6 =
  park + releasesleep row.  brelse's refs-- syncs reg_drop.  bio_ctx's
  `<{ bcache_res bn V }>` takes the λ-flip (bcache_res2).  DELETE:
  buf_escrow, escrow_recyc_*, buf_mid.
  Gate: full -B round green (interface change ⇒ -B is mandatory,
  r76's lesson).

### 4.2 icache escrow (Phase 4.5) — round R3

DO NOT transfer the box "verbatim" onto the five arms.  First redo the
A6.147-style measurement (every iInv icEscN site in
ProofIget/Ilock/Iunlock/Iput + the Spec rows, with lock context), then
apply the SPLIT:
  - empty arm  → itable.lock payload (itable_res2 already exists —
    the refs-0 custody rows), like bcache's IDLE.
  - mid arm    → dissolves into payload ops under itable.lock (the
    recycler runs inside the lock, as buf_mid died).
  - held arm   → dies as an arm: iput's ip->valid read under
    itable.lock becomes a drop-pattern withdraw/deposit pair (the
    refcnt==1 read is IN-state by the same argument as bcache's drop).
  - parked/out → the box's IN/OUT.  Q := ic_tok/ic_id ghost residue.
Expected outcome: ic box = an instantiation of the SAME 3-arm shape;
extract CtxBox.v now (rule of two) and re-express BioBox over it.
Registers: bump under itable.lock (iget), park under ip->sleeplock
(iunlock), drop-sync at iput's refs--.  The withdrawing fragment is the
inode reference's existing genlo bundle — enrich the ic presence ghost
the same way as bn_pres; DO NOT add new inode_* spellings (two-
spellings rule: the holder form already carries cred_floor).
Gate: -B green; ic_escrow's five-arm body and its ~13 open/swap lemmas
deleted.

### 4.3 inode_pay's cinv — round R4a

No box.  The parked share is immutable-while-armed; its ξ-dependence
is (a) the ident CELL fractions (i_dev/i_inum halves) parked for
agreement, (b) the cred_floor inside inode_shr_held_gen.  Fix:
  - (a) replace the parked cell fractions with the GHOST identity
    (ic_id / the existing agree-tier), which is ξ-free; cells stay
    entirely in their lock domains.  Borrower agreement is ghost
    agreement.
  - (b) park the ξ-FREE genlo form (inode_shr_genlo_bare exists);
    the credential stays on the BORROWER side: fileread/filewrite
    already hold the floored holder form post-A6.146, and the cinv
    open re-ties (g,lo) by agree.
The cinv body becomes ghost+pure ⇒ CtxMorph-free ⇒ is_ftable's λ-flip
stops recursing into it.

### 4.4 off_hold's cinv — round R4b (coordinate with main-side)

Same identity fix as 4.3(a) for the permanent f->ip half (ghost agree
keyed by slot).  The off CELL itself is genuinely mutable cross-lock
(any-fraction holder under ip->lock; exclusive holder with no lock).
The likely final shape, to be confirmed against the main-side refactor:
a third, tiny instance of the SAME transit box (bundle = the one off
cell; guards = ftable.lock / ip->sleeplock; the q=1 no-lock reclaim is
the drop pattern — the count authority is the freshness exclusion,
as obligation (b) already argues).  If the main-side agent's refactor
lands first and dissolves off into ip->lock's payload, take that
instead; do NOT invent a bespoke third mechanism.

### 4.5 The endgame tail — rounds R5–R6

R5: re-land the recorded reverts (FileInv.is_ftable λ-flip + the 9
consumer re-spells + park_globals_move — all sitting in comments at
their sites), the bio_ctx λ-flip if not done in R2, and
ProofForkretPark's park_globals/proc_priv bullets (the A6.141 §3
unfold tower; the child twin is born dominating its parker, so the
fork pays nothing).  Gate: ProofForkretPark green.
R6: bucket C, in order: LinkForkretParkPaid → LinkUserinit → LinkMain
→ BootChain/BootShared → FsAdequacyImg → SystemAdequacy — first honest
compile of text written while unbuildable; budget a fallout tail.
Gate: full -B, zero red, zero admits.  THE SYSTEM IS PROVEN UNDER TSO.

## 5. Anti-sprawl process rules (additions to the §4 process law)

1. The §1 allowed-forms law and the §2 three-arm law are LAW.  A need
   that doesn't fit is an owner-ruling item, not a local extension.
2. Two spellings per resource (holder/parked).  Interim wrappers are
   forbidden; if a sweep is needed, sweep once to the final form.
3. Freshness only by §3's registers + R1/R2.  No new floor routes, no
   new acquire exports, no per-site inventions.
4. A premise you can't discharge means the DESIGN is wrong: stop,
   update this file (in place), get the ruling if Σ-level, then build.
5. Site-map-first: before building any box client, write the table of
   every inv-open site (lock context, transition, which register serves
   its withdraw) and check every withdraw row has a cover.  The §3.3
   bcache table is the template.
6. This file is edited in place; the A6 log records history, not
   current design.

## 6. Post-endgame cleanup (do NOT do before SystemAdequacy is green)

- Collapse the IcacheRef flavor zoo to the two-spellings rule
  (retire _bare/_gen intermediates with one final sweep).
- Retire CtxAnchor routes the register design obsoleted at clients
  (aguard_receipt stays — R1 uses it; aguard_boot stays for gen 0).
- Delete ZZFloorProbe/scratch instruments; fold the A6.147–149
  narrative into a short historical note pointing here.

## Changelog

- 2026-09-01: created (supersedes A6.147/148/149's guard-route text;
  replaces BioBox's □∀-cover premises with the §3 register design).
