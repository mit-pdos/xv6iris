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
context-λs (CtxMorph).  TWO floor-shaped objects, each with ONE job
(clarified 2026-09-01, answering R1-pre note (iv)):
  - `ctx_floor ξ K` — the RAW floor.  It is what R1/R2 below deliver at
    the winner's context, and it is what T2 BOX WITHDRAWS consume
    (`aguard_intro` → `anchor_withdraw`; CtxAnchor's guard is
    deliberately on ctx_floor alone — a wrote-arm holder can cash only
    ledger_vis and cannot borrow other harts' cells).  Acquire posts and
    payload floor rows are stated as ctx_floor, NEVER weakened to
    cred_floor.
  - `cred_floor lo tl := ctx_floor cur_ctx tl ∨ ctx_wrote cur_ctx lo _`
    (A6.146) — the HOLDER-side credential for T3 RACY READS only (the
    author rides its own fresh store).  ctx_floor ⊢ cred_floor
    (`cred_floor_of_ctx`); never the other way.
Floors are DELIVERED only by:

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
  - residue Q : iProp           (ξ-FREE, ghost-only checkout residue:
                                 for bcache, bchain ∗ bown ∗ the park
                                 half + its witnesses — §3.3 site notes)
  - guard locks L1, L2          (bcache: bcache.lock / b->sleeplock;
                                 icache: itable.lock / ip->sleeplock)
  - a presence/identity ghost (below)

and its body is, FOREVER, three arms:

  box_body := ∃ n T ξb rb rp,
     anchor γa n ξb T ∗ astamp γa n T ∗ llb T ∗
     pres_core rb ∗ regs rb rp ∗ ⌜tie n T rb rp⌝ ∗
     ( P ξb              (* IN:   bundle parked at ξb            *)
     ∨ Q                 (* OUT:  checked out; ghost residue      *)
     ∨ pres_none ∗ H ξb ) (* IDLE: refs 0; content in L1's payload;
                             H = the park's IDLE credential (below)  *)

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
  - **the TAGGED parked-fragment PILE** (replaces reg_last; refined
    2026-09-01, vetted + tagged the same day).  Every PARK deposits the
    parker's pres fragment into the body, where fragments compose into
    a single `◯ Some(to_agree rb, o)` pile (o ∃-bound, row absent at
    o = 0), AND adds its park generation to a tag multiset
    `S : gmultiset nat` (`authR (gmultisetUR natO)`, ● S in the body),
    handing the parker the CLAIM `◯ {[+ n_P +]}`.  An ex-parker's
    refs-- decrement presents its claim, removes n_P from S, retrieves
    ONE pile fragment and absorbs it into the count.  EVERY decrement
    syncs rd := rp (it holds L1 + the box).  The tags are NOT optional:
    an anonymous pile cannot make the drop site total in-logic (the
    state "the one pile fragment is an un-decremented P ≠ D's, rp = P's
    park ≠ rd" is unrefutable without identity — "the caller knows
    which by program flow" is not a resource).  Three pure rows in the
    body, each maintained by inspection:
      (r1) `size S = o`          — fragment and tag move together, so
                                   `o ≤ c` (hence `size S ≤ c`) is free
                                   by auth validity;
      (r2) `rp ≠ rd → rp.n ∈ S`  — park sets rp and tags; any decrement
                                   syncs (antecedent false).  The
                                   corollary `o = 0 → rp = rd` is what
                                   the non-parker's drop uses;
      (r3) `∀ m ∈ S, rb.n < m`   — a park's gen exceeds the bump's; S is
                                   empty at bump (o = 0 in IDLE).
    Needs one CtxAnchor lemma: `astamp_le : anchor γ n XI T -∗
    astamp γ n' T' -∗ ⌜n' ≤ n⌝` (from the existing dom bound).
  - **reg_cnt** (count sync; added 2026-09-01): `ghost_var γc (1/2) c`
    with one half beside the slot's Some-arm count (= M's count) and
    one in the box beside the pres ●.  This makes the count READABLE
    at any box open: the IDLE refutation at refs ≥ 1 is a γc value
    clash, and the last-drop's fragment accounting is against c = 1.

The box's pure tie (maintained by inspection at each of the four
transitions, all of which hold the needed halves):

  tie n T rb rp  :=  (n,T) = rb ∨ (n,T) = rp

plus the pile rows (r1)–(r3) above.

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

  DROP (under L1; dropper D holds: L1's payload (rd half + floor row,
  M!!k = Some(q,1), γc half ⇒ c = 1 ⇒ o ≤ 1 ⇒ size S ≤ 1), persistent
  copies (n_b,T_b) + llb T_b, and EITHER its pres fragment in hand (it
  never parked — the bunpin dropper) OR its claim ◯{[+ n_mine +]} +
  astamp(n_mine,T_mine) + llb T_mine (it parked — brelse)).  ONE
  acquire: present Tl := max T_b T_mine (llb is downward-monotone, so
  llb (max) follows from the two); the R1 post K ≥ Tl serves both
  routes below.
    D did NOT park (fragment in hand):
      case (n,T) = rb:  fragment agrees with pres ● (currency NOW);
                        R1 floor covers T_b.
      case (n,T) = rp:  if S ≠ ∅ a pile fragment exists beside D's
                        in-hand one, so o + 1 ≤ c = 1 fails by
                        validity; hence S = ∅, (r2) gives rp = rd,
                        L1-payload row's floor via R2.
    D PARKED (claim n_mine):
      case (n,T) = rb:  REFUTED: (r3) rb.n < n_mine, astamp_le gives
                        n_mine ≤ n = rb.n.
      case (n,T) = rp:  n_mine ∈ S and size S ≤ 1 ⇒ S = {n_mine}.
                        If rp ≠ rd: (r2) rp.n = n_mine, astamp_agree
                        gives T = T_mine, own llb via R1.
                        If rp = rd: L1-payload row's floor via R2.
    Totality is in-logic: every branch closes by validity, (r1)–(r3),
    or agreement — no "the other parker must have decremented"
    history argument remains.  THE rb-CASE CURRENCY ARGUMENT REQUIRES
    THE FRAGMENT IN HAND; for a parker (fragment in the pile) the rb
    case is refuted by (r3), never proved by agreement.  Do not try to
    carry rb as a persistent copy — every persistent-witness variant
    fails on currency.

  SITE NOTES: every count edge (bump, refs++, refs--, drop) now opens
  the box (γc, the pile and S live there) — so ProofBpin/ProofBunpin,
  which never touched the escrow, gain one box open each; refs++
  copies (rb, llb T_b) out for the new fragment.  The last drop's OUT
  refutation is the COUNT route, not Q-exclusivity: the dropper holds
  L1's ● M at (q,1) and its own bref_tok, and Q exhibits a second
  bref_tok (bref_tok_two) — bown is in R at that moment, not in hand.
  Boot is IDLE for every buffer (content in the payload; anchor at
  generation 0, stamp 0; S = ∅; rp = rd = (0,0)) — no boot deposit.
  The reference has TWO spellings, BY ROLE (2026-09-01, build agent —
  the holder handle is frozen, see below):
    bref   := bref_tok (share Some q) ∗ (∃ rb, pres_frag rb ∗ llb rb.T)
              ∗ the dev/bno fractions {q}
              — bpin's / the log layer's reference; the fractions pin
              its (dev, bno) to the cells (ProofLogWrite agrees them
              against the handle); passed opaquely.
    bchain := bref_tok0 (share None) ∗ (∃ rb, pres_frag rb ∗ llb rb.T)
              — bread's CHAIN reference, ghost-only: the chain reads
              dev/bno through its handle rows, so it takes NO fraction
              off the slot.  The auth map's share component is
              [option Qp] (bioUR := auth (gmap nat (option frac ×
              positive))); the count component counts BOTH kinds, and
              the slot's tie [Σ fractioned shares + qr = 1/2] is exact
              with no extra register.
  WHY: bio_held/bio_locked (the sleeplock holder's handle) is unfolded
  structurally by ~25 fs-layer files, so NOTHING may be added to it.
  Everything the checkout leaves with the holder must therefore be
  ξ-free ghost and live in the OUT arm's residue Q:
    Q := bchain ∗ bown ∗ (∃ rp, reg_park rp ∗ astamp rp ∗ llb rp.T)
  (the sleeplock payload's γp half moves from R into Q for the length
  of the hold; the box's own half stays in the prefix and agrees).
  box_swap_checkout takes bchain + R's rows and stores them; box_swap_park
  hands bown, bchain (its fragment now in the pile under a fresh tag),
  the claim and the UPDATED park half + witnesses back — which is
  exactly releasesleep's Rdep row plus the refs-- inputs.  The holder
  carries only bio_locked across bread→brelse, as today.
  THE PARK's IDLE CREDENTIAL (2026-09-01, build agent, on the vetted
  simplification): with the fragment in Q the parker holds NOTHING ghost
  that refutes the IDLE arm (pres_frag_none_absurd did that job; the
  bundle only refutes IN, by b_valid exclusivity), and the box cannot
  see L1's None arm.  The parker's only credential is the bundle's
  CELLS, so IDLE holds a cell fraction that clashes with them:
    H ξb := ∃ dsk, b_disk (bpa k) ↦ξb{1/2} dsk
  — b_disk is written only by rw, under the sleeplock, by a holder who
  has the FULL bundle; the recycler never touches it.  L1's None arm
  keeps the content with b_disk at HALF (spelling buf_bundle_h: the
  bundle with the disk cell halved); the bump deposits buf_bundle_h and
  JOINS the halves at ξb into the IN arm's full bundle; checkout/park
  move the full bundle; the last drop withdraws the full bundle, halves
  b_disk, DEPOSITS the half back (a free deposit; IDLE's generation
  advances) and returns buf_bundle_h to L1's None arm.  The park's
  IDLE refutation is ctx_word4_excl_x (full at ξ vs half at ξb).  Boot
  makes ONE deposit per buffer (the b_disk half, generation 0 → 1)
  because the anchor's context is a fresh parked context; rp = rd =
  (0,0) and S = ∅ are unchanged.  bio_locked is untouched (buf_own's
  b_disk row is already in the handle).
  VETTED 2026-09-01 (approved; proceed with ProofBread sites 1–5):
    - This is §2's rule applied literally (state into Q, never into a
      handle or a new arm) and is continuity with v1, whose chain
      reference already rode the escrow's OUT arm (BioInv.v:260).
    - SIMPLIFY box_swap_park: during OUT both γp halves are inside the
      box (prefix + Q), so the park's premises reduce to own_context ∗
      buf_bundle — the bundle is the holder's only (and sufficient)
      credential; drop the caller-supplied pres_frag rb' / reg_park rp'.
      Symmetrically box_swap_checkout gains the R row (bown, the half,
      the witnesses) as a premise and stops returning them.
    - option share: optionUR fracR has None as unit, so (None,1) ⋅
      (Some q,1) = (Some q,2); the count-1 equality case is the same
      gmap/option arm the drop's OUT refutation already uses
      (Some_included, then pos_included) — write the tok kit once
      against that idiom.  Slot tie by match: None ⇒ qr = 1/2 (the
      other half rides the bundle); Some q ⇒ q + qr = 1/2.
    - Fragment accounting: during OUT one UNTAGGED fragment sits in Q
      (the holder who has not parked yet).  Keep it a separate resource
      from the pile: (r1) size S = o counts PILE fragments only; never
      fold Q's fragment into the pile row.  Consistent with (r3): that
      holder tags at its park with a generation above rb.1.  Neither
      cover changes (both withdraw sites have the box IN, where Q does
      not exist); o ≤ c stays free by validity.
    - bref/bchain by ROLE is compatible with the two-spellings rule:
      the difference is a capability (the fraction pins (dev,bno) for
      the log layer; the chain reads them off the withdrawn cells), not
      a compatibility flavor.  Exactly these two.
    - Refutations unchanged: OUT at checkout = bown exclusivity (the
      winner's from R vs Q's); OUT at drop = the count route (any second
      tok, fractioned or None, overflows Some(_,1)).  pres ●, the γc half, the pile, ● S and the
  γp/γd halves sit in the body's COMMON PREFIX outside the three arms;
  IDLE adds only ● None (which forces o = 0 by validity).  The payload's
  None-arm keeps the γd/γc halves (the tie must hold in IDLE).  bunpin
  can drop to 0 (bpin, brelse, bunpin) and is a drop site.

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
- The registers are ghost_var pairs (γp, γd, γc), one enriched auth
  (pres) and one auth gmultiset (the tags) — no new model arms, no Σ
  churn beyond small per-box cmras (anchorR precedent).

## 4. Instance plans

### 4.1 bcache (finish Phase 5) — rounds R1–R2

R1-pre (PREREQUISITE; measured 2026-09-01 by the build agent, design
  settled by the owner the same day): THE SLEEPLOCK PAYLOAD λ-FLIP, AS A
  THIN RELAY OF WpLock's PAYLOAD DISCIPLINE.

  THE MEASUREMENT (verified in code): the inner spinlock's payload is
  the CONST [<{ sl_res_gen γ slk R H }>], and sl_res_gen embeds the lock
  word and the pid field as ambient-XI cells ([slk ↦₄ v],
  [sl_pid slk ↦₄ pid] inside sl_free_hold/sleeplocked_q) — the
  is_ftable class (A6.141 §1), reached from proc_priv through bio_ctx
  and ic_sleeplocks.  A6.146's inventory swept inv bodies only and
  missed const lock payloads (§4.4b closes that class).

  THE DESIGN — nothing sleeplock-specific is invented.  §1's law says
  lock payloads are context-λs; the sleeplock's inner spinlock IS a
  WpLock is_lock, which already takes a context-λ payload and already
  has the two release forms the asymmetry needs.  So:
    - [is_sleeplock_gen γl γ slk s (R : CtxId → iProp) H :=
         sl_name slk s ∗
         is_lock γl (sl_lk slk) "sleep lock"
           (λ ξ, sl_body γ slk H ξ (free-arm: R ξ))]
      with sl_body's own cells at the EXPLICIT ξ (ctx_word4_pointsto ξ
      for the word and the pid) and [CtxMorph R] the client's one
      obligation (ctx_morph_solve for ghost + floor rows).  The held
      arm carries no R, so there is nothing to invent for it.
    - acquiresleep RELAYS the inner acquire's post verbatim: the winner
      receives [R cur_ctx] through the standard payload morph.  The
      landed llb tier (R1) is orthogonal and stays.
    - releasesleep RELAYS BOTH WpLock release forms: PLAIN (premise
      [R cur_ctx] — every ghost-only client can produce it) and _IN
      (premises [llb tl ∗ Rdep cur_ctx] + the one-line entailment
      [∀ ξ, Rdep ξ ∗ ctx_floor ξ tl ⊢ R ξ], the lock record minting the
      floor via lock_finisher_close_in_llb / lock_pay_intro_llb).  The
      _in Parameter lives in RELEASE_IN, so [ReleasesleepProof] gains a
      functor argument [(ReleaseIn : RELEASE_IN)] and LinkReleasesleep.v
      passes the existing [ReleaseIn := ReleaseInOfGen ReleaseGen]
      (LinkRelease.v:12).  THIS is R2 for the sleeplock.
    - Const consumers derive at [R := λ _, R0]: [is_sleeplock γl γ slk s
      R0 := is_sleeplock_gen … (λ _, R0) sl_untracked]; every existing
      consumer is textually unchanged; the plain tiers are the λ tiers
      at that instance (the same way ACQUIRE derives from ACQUIRE_GEN).
      Note: that instance's CtxMorph goal is ctx_morph_const and holds
      even for a cell-bearing R0 — harmless for newlock, but the reason
      the const tier fixes CtxMove ONLY for ξ-free R0 (both current
      clients, bown and ic_tok, are ghost-only).
  WHAT WAS REJECTED, AND WHY: a sleeplock-only bound-indexed payload
  [Rb : nat → iProp] with a built-in floor slot ([λ ξ, ∃ tl,
  ctx_floor ξ tl ∗ sl_body … tl ξ], new genb spec tiers, held-arm
  re-closes at tl := 0).  It bought a trivial CtxMorph goal and no
  release entailment (both one-liners) and forbade ξ-cells in sleeplock
  payloads BY TYPE; in exchange it made the sleeplock's payload algebra
  differ from the spinlock's and added a spec family — a third payload
  spelling of exactly the kind this document forbids.  The "no cells in
  sleeplock payloads" discipline is kept as a CHECKLIST rule (§5 rule
  5's ctx_move_const test on every lock payload), not as a type: the
  bundle travels through the BOX, never through the sleeplock payload.

  bcache INSTANTIATES [R ξ := bown ∗ ∃ np Tp, reg_park (np,Tp) ∗
  astamp np Tp ∗ llb Tp ∗ ctx_floor ξ Tp] — the checkout's rp-case
  cover — and releases through _in with [Rdep := the same row minus the
  floor] and [tl := Tp] (the park's anchor_deposit export).  The boot
  row (rp = (0,0)) needs astamp 0 0: BioInitAt already mints the anchors
  before its sleeplock loop.

  THREADING (file list): SleepLock.v (sl_body at explicit ξ; _at forms
  of sl_free_hold/sleeplocked_q, ambient = cur_ctx instances; the open/
  close kit at cur_ctx; the payload λ + its CtxMorph), SleepLockAt.v /
  new_sleeplock_gen(_at) (CtxMorph side goal by ctx_morph_solve),
  Spec/ProofAcquiresleep (4 payload-open sites: entry, post-sleep,
  nested entry, nb — each now holds R cur_ctx), Spec/ProofReleasesleep
  (plain + _in tiers; the RELEASE_IN functor argument), LinkReleasesleep
  (one line), ProofHoldingsleep (2 opens).  The winner's floor row is
  [ctx_floor cur_ctx Tp] — the raw floor, NOT cred_floor (§1's
  two-object rule; the box withdraw consumes the left arm).
  Gate: SleepLock cone green (the four sleeplock proofs + SleepLockAt +
  IcacheBoot/BioInitAt builders); then a -B round (interface change).

R1 (design retrofit, small):
  - Enrich bn_pres's cmra ((n_b,T_b) agree × positive); move ● into
    buf_box_body's IN/OUT arms; IDLE keeps ● None.  (BioInv pres kit:
    ~4 lemmas touched.)
  - Add γp/γd/γc ghost_vars + the tag-multiset gname to bio_names; add
    the reg halves, the pile, ● S and rows (r1)–(r3) + the tie to
    buf_box_body's common prefix; add the astamp/llb/floor rows to the
    sleeplock payload (the SleepLock record threading — this IS r77's
    "NEXT" item, shaped as a payload row) and the rd/γc halves to
    bio_slot_res2 (both arms).  Add CtxAnchor.astamp_le.
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

### 4.4b The CONST-PAYLOAD class (found 2026-09-01; closes the inventory)

A6.146 closed the ξ-bodied INV-BODY class.  The sleeplock (R1-pre) shows
a second class with the same failure: a constant `<{ R }>` lock payload
whose R embeds ambient-XI cells — is_lock with a ξ-varying payload
argument in disguise, which `is_lock_move` cannot take (A6.141 §1).  Every
`<{ … }>` in a DEFINITION file, measured:

  <{ bcache_res bn V }>   BioInv/BioInitAt   cells   → bcache_res2 λ (R2)
  <{ ftable_res γ }>      FileInv            cells   → recorded revert (R5)
  <{ sl_res_gen … }>      SleepLock          cells   → R1-pre
  <{ log_res … }>         LogInv:1112/1157   CELLS   → NEW: not in any
                          inventory.  log_res owns l_out/l_cmt/l_ncommit
                          as ambient ↦₄; log_ctx is in fs_ready
                          (FsReady.v:300), hence in the fork-crossing
                          cone.  Expected to be a plain λ-flip like
                          is_ftable (everything is under log.lock, no
                          transit), BUT run the A6.141 test first
                          (`apply ctx_move_const` failing = ξ-varying;
                          check for nested ξ-bodied pieces behind Psi /
                          the bref rows).  Lands with R5's reverts.
  <{ tx_res γu }>         UartTxInv          ghost   → fine (ghost_var)
  <{ itable_res }>        IcacheInv:4439     DEAD    → is_itable2 at the
                          real λ is the live one; delete with §6.
  <{ P }> / <{P}>         WpLock generic     n/a

RULE: a const `<{ R }>` payload is legal only for ξ-free R.  Every other
lock payload is a CtxId-λ (WpLock's shape) or, for sleeplocks, the
floor-slotted Rb.  Add the ctx_move_const test to the site-map checklist
(§5 rule 5) for any new lock.

### 4.5 The endgame tail — rounds R5–R6

R5: re-land the recorded reverts (FileInv.is_ftable λ-flip + the 9
consumer re-spells + park_globals_move — all sitting in comments at
their sites), the bio_ctx λ-flip if not done in R2, the log_res λ-flip
(§4.4b), and ProofForkretPark's park_globals/proc_priv bullets (the A6.141 §3
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
   bcache table is the template.  For any lock touched, apply the
   `ctx_move_const` test to its payload (§4.4b): a const payload with
   cells is the is_ftable class and must be λ'd.
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
- 2026-09-01 (build agent): reg_last replaced by the parked-fragment
  PILE (fragments compose in the body; parks deposit, ex-parkers'
  decrements retrieve; every decrement syncs rd := rp; pure row
  ⌜o = 0 → rp = rd⌝); γc count-sync register added.  Reason: a single
  γl half-pair cannot serve overlapping parkers, and its whole-in-box
  case was refutable only globally; the pile + γc make every drop-site
  case local, with no receipt choreography.  Registers: γp, γd, γc.
- 2026-09-01 (build agent, after the vetting): tagged pile ADOPTED as
  written (it subsumes the pair-tag ticket the build side had reached
  independently; astamp_le + (r3) is the cleaner refutation).  Added
  R1-pre: the SleepLock payload λ-flip with the floor slot, measured as
  a 7-file self-contained prerequisite — the const [<{ sl_res_gen }>]
  embeds ambient-XI cells and cannot carry R2's floor, so without it
  the checkout's park-case cover has no floor source.  Site notes:
  bpin/bunpin box opens, the last drop's OUT refutation by count,
  IDLE boot, the single bref spelling.
- 2026-09-01 (design vetting of the pile): pile ACCEPTED (the reg_last
  overlap flaw was real) but TAGGED — an anonymous pile leaves the
  drop's (o = 1, n ≠ n_mine) branch unrefutable in-logic.  Added the
  tag multiset S with parker-held claims, rows (r1)–(r3), astamp_le,
  the max-Tl single-acquire trick, and the site notes (every count edge
  opens the box; rows in the common prefix; bunpin is a drop site).
  Drop cover rewritten as a fully in-logic case split.
- 2026-09-01 (design vetting of R1-pre + site notes): R1-pre and the
  site notes ACCEPTED (sl_res_gen measurement verified in code; both
  sleeplock clients ghost-only, so nat-indexed Rb suffices).  Added the
  sleeplock-payload rule (ξ-free + one floor slot; const tier only for
  ξ-free R) and the BioInitAt anchor-before-sleeplock order.  NEW
  FINDING §4.4b: the const-payload class — log_res (LogInv) embeds
  l_out/l_cmt/l_ncommit at ambient XI under <{ }> and sits in fs_ready;
  not in any inventory; lands as a λ-flip with R5 after the
  ctx_move_const test.  Full <{ }> table recorded; §5 rule 5 extended.
- 2026-09-01 (build agent, R1-pre implementation notes): tier layout
  (genb base, const derived; nested/nb stay const), held-arm re-closes
  at tl := 0, the RELEASE_IN functor argument on ReleasesleepProof, and
  a question on the post's floor spelling vs cred_floor.
- 2026-09-01 (build agent, corroboration of §4.4b): log_res CONFIRMED
  in code (l_out/l_cmt/l_ncommit as ambient ↦₄ under <{ }>, reached
  through log_ctx_at → log_ctx → fs_ready).  A full grep of every
  `<{ … }>` in the tree against the table finds two spellings the table
  omits, both ξ-FREE and hence legal: <{ pr_res γd }> (SpecPrintk,
  ProofMain; pr_res := emp) and <{ tx_res γd }> (the uart family the
  table lists under γu).  The <{ ticks_res }> / <{ pipe_res }> hits are
  comment text at their λ'd sites.  Inventory closed as stated.  The
  anchor-before-sleeplock build order already holds: BioInitAt mints
  the anchors in bio_names_ghost_alloc (the free-tok row), and
  BioInv.bio_init mints them before its sleeplock loop.
- 2026-09-01 (design vetting of the R1-pre implementation notes): (i)–(iii)
  accepted (RELEASE_IN wiring verified at SpecRelease.v:317 /
  LinkRelease.v:12; the close_in_llb fold closes with tl' := tl).  (iv)
  answered: the acquire post and payload rows stay ctx_floor — required
  by the box withdraw (aguard on ctx_floor alone).  §1 reworded from
  "one credential form" to the two-object rule (ctx_floor for T2
  withdraws; cred_floor for T3 racy reads only).  §4.4b corroboration
  accepted; the anchor-before-sleeplock order already holds.
- 2026-09-01 (owner ruling on R1-pre): the bound-indexed Rb / genb tier
  is REJECTED as a third payload spelling.  The sleeplock is a THIN RELAY
  of WpLock's payload discipline: R : CtxId → iProp threaded through
  is_sleeplock_gen, acquiresleep relays the inner post (R cur_ctx),
  releasesleep relays BOTH WpLock release forms (plain / _in), const
  consumers derive at λ _, R0.  Notes (i)/(ii) collapse to "λ base,
  const derived" / "nothing to do for the held arm"; (iii) RELEASE_IN
  functor argument stands; (iv) posts stay ctx_floor.  Sleeplock
  payloads ξ-free-plus-floor remains a checklist rule, not a type.
- 2026-09-01 (build agent, R1-pre landing note): the λ base tier is named
  `is_sleeplock_genl` / `wp_acquiresleep_genl_llb_sconf` /
  `wp_releasesleep_genl_sconf` (plain) + `wp_releasesleep_genin_sconf`
  (_in); `is_sleeplock_gen` and the gen/llb/plain spec names KEEP their
  const `R : iProp` types, since icache/bcache consumers spell them that
  way -- the const tier is the instance at `λ _, R0`, as the doc says,
  just under the old names.  SleepLock's kit stays stated on
  `sl_res_gen` through `sl_body_eq : sl_body … R H cur_ctx =
  sl_res_gen … (R cur_ctx) H` (reflexivity), so no open/close lemma
  changed.
- 2026-09-01 (build agent, R1-pre + R1 LANDED, gate green): §4.1 R1-pre
  and R1 are in the tree (A6.153 lists the pieces).  Two encoding notes,
  no design change: (a) §3.3's two cover lemmas are folded into the
  transition lemmas (box_swap_checkout takes the two floors and the tie
  picks inside; box_swap_drop_hand takes (Kb, Kd); box_swap_drop_pile
  takes (Km ≥ T_mine, Kd) + the claim + the parker's astamp) -- one
  lemma per site, the same total case split; (b) the four new camera
  classes are bundled as Xv6Cameras.bioboxG inside Xv6G.xv6G so that no
  bio_ctx/bio_init consumer gains a binder.  The sleeplock payload is
  bslp := bown ∗ ∃ rp, reg_park rp ∗ astamp rp ∗ llb rp.2 ∗ ctx_floor ξ
  rp.2, exactly §4.1's instantiation; bslp_dep/bslp_fold are the _in
  release's Rdep and entailment.
- 2026-09-01 (build agent, R2 site map finding): the holder handle
  (bio_held/bio_locked) is frozen — ~25 fs-layer files unfold it — so
  the checkout's residue cannot ride the handle.  Refinement, no new
  instrument: the chain's reference is ghost-only (bchain: share None +
  fragment; bioUR's share becomes option Qp; the slot tie stays exact),
  and the OUT arm's Q carries bchain ∗ bown ∗ the park half + witnesses,
  returned by the park.  The (dev,bno)-pinning fractions stay on bpin's
  brefs, which the log layer needs.  §2's Q line and §3.3's site notes
  amended in place.
- 2026-09-01 (design vetting of A6.155): APPROVED — the OUT-residue
  refinement is §2's rule applied and v1 continuity.  Feedback recorded
  in the §3.3 site notes: simplify box_swap_park to own_context ∗
  buf_bundle (both γp halves are in the box during OUT) and move the R
  row into box_swap_checkout's premises; option-share idiom; keep Q's
  untagged fragment out of the pile row; bref/bchain by role is a
  capability difference, not a flavor.  Encoding notes (a)/(b) accepted.
  ProofBread sites 1–5, ProofBrelse, ProofBunpin, the v1 deletion and
  the -B round may proceed.
- 2026-09-01 (build agent, on the vetted park simplification): the park
  needs an IDLE credential once the fragment sits in Q — the IDLE arm
  gains the b_disk half at ξb (H ξb), L1's None arm keeps buf_bundle_h
  (b_disk halved), the bump joins, the last drop re-halves and
  re-deposits, boot deposits the half once per buffer.  §2 IDLE line
  and §3.3 site notes amended in place.  Everything else of the vetting
  is taken as written (park: own_context ∗ buf_bundle; checkout takes
  the R row; option-share tok kit once; Q's fragment outside the pile).
