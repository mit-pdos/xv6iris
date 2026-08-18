# The iclaim/ifreeze ledger — B1/B2 resolution + create_fresh_ty retirement (F1.5c/F1.5d)

STATUS: **DESIGN** (2026-08-17, Fable design session).  Nothing built.  This
is the design of record for TWO converged effort: (PART 1) the two design
debts blocking `IputFreeLockedDev.v` (lane commit `60cc0136b1`, admits at
:1034/:1144 — the A-walk of task 18), and (PART 2) the retirement of the
`create_fresh_ty` axiom by spec/ownership adjustment, per the user's
2026-08-17 direction ("start over ... adjusting specs, ownership, and
permission"; the byte-identity guardrail that killed the nine probes is
LIFTED).  Cross-links: [`iget-licence.md`](iget-licence.md) (this executes
its "WHAT IS LEFT" item 3 and attacks its declared NON-GOAL, the free-side
wall); `design/fs-fragments.md` §7.x (the probe history); task #18 (the A
walk this unblocks).

VERIFIED-AGAINST: lane HEAD `ee1bf28a3d` + `60cc0136b1`.  Every lemma/line
cited below was read on the lane this session.

---

## 0. THE CENTRAL FINDING: B1 and B2 are one debt, and it is PART 2's core

The reorder's free path needs the inum to be **exclusively in-transition**
from the moment the freer commits (the `ref==1 && valid && nlink==0`
decision under the FIRST itable-lock hold, span of `ip_free_entry`) to the
off-lock deposit at +0xba.  Both admits are shadows of the missing
exclusivity token:

* **B1** (`IputFreeLockedDev.v:1034`, the `cnt2 <> 1` arm at +0x8a): the
  `cnt2 >= 2` arm canNOT be "handled" — the off-lock `ifree` write needs a
  region mover, every byte-writing mover needs `dinode_at`, and `dinode_at`
  is single and in the freer's hand.  So the arm must be **refuted**: no
  thread may mint a reference to the dying inum in the 0x66→0x82 window.
  Under the current specs that is unrefutable (`SpanL = ⌜True⌝` alone
  defeats it, before `BufL` is even considered) — exactly the file's
  blocker note.  With the licence hygiene of §2 it is refutable
  **resource-level, inside the iget/idup proofs themselves** (§2.6).
* **B2** (`:1144`, one bundle two consumers): dissolves once the freer can
  park a payload that does NOT contain `dinode_at` — the `pool_await` arm,
  §2.5.  No fourth `islot2` arm is needed (the eviction stays an eviction);
  the earlier (None,Some)-arm idea is WITHDRAWN — see §1.3.

Consequence for sequencing (task 18): **the A walk cannot reach zero admits
before the §2 core lands.**  The user's scope options are in §4.

### 0.1 The revival-trace check (done, negative — no kernel bug)

Because B1 smells like a real race, this session chased the strongest
candidate adversary: a `namex("..")` walk out of an orphaned cwd (the
§20.8 grave-`".."` still names the dying parent), racing the parent's final
iput past +0x94 and re-filling from stale (pre-ifree) bytes — which would
have been a silent double-free on the reordered binary (pre-reorder the
same trace dies at the certified `"ilock: no type"` panic).  It is
**closed by contract, already**: the only licence such a walker could
present is `GreyL`, and (a) `grep GreyL Proof*.v Spec*.v` is EMPTY (the
R14 audit "GreyL: zero sites" holds on the lane), (b) the kernel's own
`fs.c:693` nlink guard is where `ProofNamex` earns its licence
(`ProofNamex.v:3910`) — an nlink==0 home ends the walk.  So the trace is
unreachable in the verified tree and pin 4398009 is not implicated.  Do
not re-derive this; it cost a session-third.

---

## 1. PART 1 — what the A walk needs, site by site

### 1.1 The +0x8a case split stays, but the `cnt2 >= 2` arm is REFUTED

At +0x82 the freer re-acquires itable.lock and re-reads the count.  With
§2 landed it holds `ifreeze (bv_unsigned inum)` (minted in
`ip_free_entry`'s span, §1.4) and the freeze-pin clause (§2.3) gives
`icnt`-agreement = 1, i.e. `cnt2 = 1` outright — the `decide (cnt2 = 1)`
split at `IputFreeLockedDev.v:1027` collapses to its first arm.  The admit
at :1034 is replaced by a pin read, not by new walk code.

### 1.2 The +0x70 park carries `pool_await`, keeping `dinode_at` in hand

Today the +0x70 `sw zero,64(s1)` (that is `ip->valid = 0` — the
instruction-stream comment at `IputFreeLockedDev.v:72` saying "type = 0"
is WRONG, see :769; fix the header when touching the file) is followed by
`ic_swap_park` at `v = false`, whose parked payload `ic_unloaded`
(`IcacheEscrow.v:584`) = `inode_raw ∗ ipool_shape_np` — and `ipool_shape_np`'s
only reachable arm is `ipool_alloc`, which contains `dinode_at`.  That is
B2's root: the record gets buried in the park and comes back
existentially erased.

Fix: widen `ipool_shape_np` with a third arm (and `ipool_shape` stays
`np ∨ pool_pending`):

    pool_await γi z := ∃ ge gr, escA_inv ge gr γi z ∗ redeem_ticketA gr

(both available to the freer at +0x70: `escA_alloc` is mask-only and its
own header comment `EscrowInode.v:40` already says "minted at iput+0x86
(before itable.lock release)" — mint it any time before the park).  The
freer parks `inode_raw ∗ pool_await`, keeps `dinode_at (di_trunc dn)` —
with its identity intact, no existential — plus `ind_res`/`inode_blocks`/
`dir_links` in hand across releasesleep, and hands `OFF.ip_free_offlock`
exactly what its entry demands (`IputOfflockDev.v:144` takes `dinode_at`
bare, plus `escA_inv`; the `redeem_ticketA` in its current precondition
was only there to assemble `pool_pending` at the exit and MOVES into the
park — re-spec the offlock entry/exit accordingly: exit no longer returns
an `ipool_shape`; the ticket is already pool-side).

Note `ic_unloaded` absorbs the new arm for free (it wraps
`ipool_shape_np` opaquely), and `ic_swap_park`/`ic_close_to_empty` are
arm-agnostic on the unloaded polarity (`ic_close_to_empty`'s `v = false`
branch at `IcacheEscrow.v:1484` just re-wraps the parked shape — verified
against its body).

### 1.3 The eviction at +0x8a proceeds UNCHANGED (the (None,Some) arm is withdrawn)

With 1.2, `ic_close_to_empty` pops `inode_raw ∗ pool_await`, the slot goes
`islot_empty`, `ci` deletes `k`, and `ipool_insert` files `pool_await` as
the pool's shape for the inum — the already-proven eviction block at
:1050–1140 survives verbatim; only the `iAssert` under the :1144 admit
changes shape (no `dinode_at` demanded from the bundle — it is in hand).
The earlier idea of a fourth `(None, Some)` `islot2` arm (slot stays in
`ci`, pool does not grow) is WITHDRAWN: it forces every future recycler
that picks the slot as a victim to re-park a shape it cannot have
pre-deposit, i.e. it re-creates B2 one consumer later.  `ic_ci_wf`'s
`dom ci = dom M` stays.

The pool's `await` entries are serviced later on both polarities:
post-deposit, the escA body (`EscrowInode.v:26`) is FILLED and an
`await`-redeem (open `escA_inv`: FILLED → take `imark`, park the ticket,
step to REDEEMED — `escA_redeem`'s body minus the `committedA` input) turns
the arm into `imark`, i.e. classic `ipool_shape_np`; pre-deposit the
would-be consumer (a fill or recycle **of this inum**) is licence-refuted
by §2.6 — package that refutation as the `await` case of
`ipool_shape_to_np` (new premise: the caller's licence), and thread it at
the two call sites, ProofIget:1307 and ProofIlock:1082.

### 1.4 `ip_free_entry` mints the freeze; the deposit retires it

The freeze mint `ireg_freeze_au` fires in `ip_free_entry`'s span (the
nlink==0 → 0x50 arm, still under the FIRST itable-lock hold, where
`Mt !! k = Some (q, 1)` is a live fact and the `icnt` half in the slot arm
says the ledger count is 1).  `IputFreeEntryDev.v`'s scaffold
(`ee1bf28a3d`) must gain: the mint in its Exit-B obligation, and `ifreeze`
threaded through `ip_free_locked`'s entry.  The deposit
(`EscrowDeposit.ireg_free_deposit_au`, extended) retires it: f-slot
Some → None in the same region open that absorbs `dinode_at` and fills the
escrow.  Between mint and retirement the freeze-pin (§2.3) is the walk's
working capital.

### 1.5 Cost table (PART 1 alone, on top of §2 core)

| where | what | size |
|---|---|---|
| `IcacheEscrow.v` | `pool_await` arm in `ipool_shape_np`; `ipool_shape_to_np` await case (+licence premise) | small defs, 2 lemma re-proofs |
| `IputOfflockDev.v` | entry drops `redeem_ticketA`, exit drops the `ipool_shape` hand-back | statement + splice, walk body untouched |
| `IputFreeLockedDev.v` | :1034 admit → pin read; :1144 admit → in-hand assembly; 0x70 park re-shaped | the two admit sites only |
| `IputFreeEntryDev.v` | freeze mint in Exit-B; `ifreeze` in the locked-entry seam | statement-level |
| `ProofIget.v:1307`, `ProofIlock.v:1082` | thread the licence into the await case | mechanical |
| `ProofIput.v` | none until integration (functor splice per task 18) | — |

---

## 2. PART 2 — the ledger scheme (F1.5c/F1.5d executed)

Everything below is per-inum LEDGER state: `link_auth` lives inside
`ireg_slot` (`InodeRegion.v:1266`), i.e. inside the region invariant that
`ireg_claim_au`/`ireg_free_au` already open — the §7.6.4 "horizon" wall
does not apply to ledger-based certificates.  The mechanism inventory is
already in-tree and mostly unwired: `iclaim` (`IcacheRef.v:800`, the
exclusive c-column, "NOTHING MINTS AN iclaim TODAY" per `IgetLic.v:92` —
a sequencing rule, §7.1.5, whose free-side half is exactly the reorder the
A walk is landing), `iref_lic`/r-column with `link_mint_ref`/
`link_spend_ref` (`IcacheRef.v:1294/1309`, designed as "§20.7's (M1)
carrier ... minted at iget from the caller's licence and returned at
iput's ip->ref--", zero consumers today), the boot one-shot
(`ireg_boot = ity_pending icfg_boot`, `ireg_open = ity_shot`,
`ity_shoot`/`ireg_boot_open_excl` at `IcacheRef.v:684/745`, seal "fires
once after fsinit returns" per :731), and the landed boot-shelter clause
`(⌜c = None⌝ ∨ ireg_open)` in `ireg_slot` (`InodeRegion.v:1278`).

### 2.1 New ledger column: the freeze (recommended over overloading c)

Widen `lelem` (`IcacheRef.v:331`) by one component
`f : option (excl unit)`; fragment `ifreeze z`.  RULING: a separate column,
NOT a flavoured c — the landed §7.12 boot clause on c stays byte-identical
and `ireg_claim_au`'s pending-refutation is untouched.  Mechanical blast:
every `lelem` literal gains one `None`/`0` (~30 sites in `IcacheRef.v`,
plus `ireg_slot_intro`-family arities in `InodeRegion.v`).

c keeps its meaning (ialloc's claim); f is iput's transition token.  The
two are the same idea at the two generation boundaries — the user's
"clear separation between the old and new generation of an inode number"
is literally: every boundary crossing holds its exclusive column.

### 2.2 The count coupling (`icnt`)

New per-inum ½-½ agreement ghost `icnt z n` ("in-core reference count of
z"): one half rides in `ireg_slot` (region), the other in the
`(Some (q,n), Some (dev,inum))` arm of `islot2` at value `Pos.to_nat n`,
and in the not-cached arms at 0 (parked wherever the identity halves park;
`islot_empty` gains it at 0).  Every count move (iget hit
`iref_incr_store_au`, iget recycle `iref_alloc_step`, idup, iput's two
close lemmas `iref_close_store_au`/`iref_close_last_store_au`,
IcacheInv.v:1320/:1369) holds the itable lock (slot half) and gains a
region open (auth half) — this is where iget acquires `ireg_inv` in its
contract (persistent, ambient; the "iget takes NO ireg_inv" purity of
`SpecIget.v` is spent here, deliberately).  OPEN(2.2a): whether to ALSO
wire the r-column units (`iref_lic` per holder) now or later; they are
not needed for B1 or for create_fresh_ty (see 2.4) — RECOMMENDATION:
later, as their own increment (they buy per-holder accounting, e.g. a
future iput contract that returns the licence).

### 2.3 The freeze-pin clause (in `ireg_slot`, beside the boot clause)

PROBE CORRECTION (ZZProbeIcnt, 2026-08-17, GO verdict — see §2.9): the
original `icnt = 1` conjunct is FALSE on the reordered free path's own
trace — the +0x8a last close drives icnt 1 → 0 strictly inside the
freeze window (`ireg_strict_pin_is_false` in the probe).  RULING: adopt
the probe's PHASED freeze — one exclusive column, one token, payload
`FrzPre | FrzPost`; +0x8a steps Pre→Post inside the region open it
already takes (fragment-side, no new mask).  This keeps the arithmetic
backstop against a post-eviction foreign re-mint (0 → 1) that a bare
`icnt ≤ 1` would surrender to the licence table alone.

    f = Some FrzPre  ⟹  di_nlink d = 0  ∧  di_type d ≠ 0
                      ∧  icnt-half (region side) = 1
                      ∧  (ireg_open ∨ [this arm holds ireg_boot])
    f = Some FrzPost ⟹  di_nlink d = 0  ∧  di_type d ≠ 0
                      ∧  icnt-half (region side) = 0
                      ∧  (ireg_open ∨ [this arm holds ireg_boot])

The last conjunct is the boot story: a RUNTIME freezer exhibits the
persistent `ireg_open`; ireclaim (the only boot freezer, sequential)
parks its `ireg_boot` in the arm for the freeze's duration and takes it
back at the deposit.  Every reader that needs to refute a foreign boot
freeze does it by exclusivity (`ity_pending` doubles → invalid;
`ireg_boot_open_excl` for the mixed case).  Mint = `ireg_freeze_au`
(reads the slot-side icnt half = 1 under the itable lock, f None→Some);
retire = inside the extended `ireg_free_deposit_au`.

### 2.4 The claim-pin clause and the create_fresh_ty payout

    c = Some ⟹  d = the claimed record (the fresh_shape dn′ that
                 ireg_claim_au wrote)  ∧  di_nlink d = 0

No count conjunct — create_fresh_ty is a RECORD fact, not a count fact.
`ireg_claim_au` (`InodeRegion.v:1887`) gains the c-mint (in-horizon: the
auth is in the arm it already opens) and hands ialloc `iclaim inum`; the
landed boot clause `(c = None ∨ ireg_open)` is established by the
persistent `ireg_open` every runtime claimant carries.  The spend is at
create's ilock-fill: fill of a claimed box withdraws the pinned record —
`ireg_withdraw` needs `di_type ≠ 0`, satisfied by fresh_shape — and the
pin + §2.6 (only the claimant can reach the fill) gives **the record
create reads = dn′**, i.e. `create_fresh_ty` as a lemma; c retires
Some→None there.  `SpanL`'s site becomes `ClaimL` and `SpanL` deletes,
exactly as `IgetLic.v:155` schedules ("IT DELETES ... the site becomes
ClaimL, no signature moves — that is why (d) is kept").

Writes cannot dent the pin: every byte-writing mover consumes
`dinode_at`, whose only flow to a foreign thread is iget→ilock, gated by
§2.6.  Reads (a licenced foreign fill) would not dent it either — but
§2.6 shows none exists at a claimed box anyway.

### 2.5 (moved to §1.2/1.3 — pool_await; listed here because PART 2's
deposit is what redeems it)

### 2.6 The licence table at an in-transition box (f=Some or c=Some)

The refutations are RESOURCE-LEVEL, derivable inside the iget/idup/fill
proofs (this is what answers the blocker note's "a whole-program fact and
not a resource this lemma can hold"):

| licence | refuted by |
|---|---|
| `LinkedL` (`ipaid`, a w-unit) | ledger w-sum = 0: both pins carry nlink=0 and `ireg_link_ok` ties the sum (`IcacheRef.v` §280 block); unit vs auth-0 collides |
| `GreyL` | **DELETE the constructor** (zero sites on the lane, deletion already scheduled by iget-licence.md item 3).  It is NOT refutable at a frozen box (grave-`".."` greys legitimately survive the free, `igrey` "carries no allocatedness ... that is the point") — with the new mint obligation an undeletable GreyL would make iget's own proof unclosable.  Its deletion is now REQUIRED, not housekeeping. |
| `HeldL d` | strengthen `iname`'s HeldL arm with `⌜di_nlink d ≠ 0⌝`; fragment-auth agreement pins d = the arm's record, pins say nlink = 0.  VERIFY(2.6a): audit the HeldL sites — the worked instance is the "." lookup at a caller-locked live dir (`IgetLic.v:88`), which has nlink ≥ 1; check no site presents a torn-down dir. |
| `ClaimL` | c-column Excl doubling (foreign) — the claimant itself is the intended survivor |
| `BufL` | borrow `ireg_boot` into `iname`'s BufL arm (single proof site: `ProofIreclaim.v`).  Runtime: nobody has it post-seal.  Boot: presenter's pending vs the freeze-arm's parked pending doubles → invalid; vs a runtime claim's `ireg_open` → `ireg_boot_open_excl`. |
| `RootL` | pins say nlink = 0; the root clause (`ireg_root_ok`, (L1)) keeps the root's count positive |
| `SpanL` | deleted (2.4) |

idup (the other count-bump, `ProofIdup.v`) is covered the same way its
mint is: OPEN(2.6b) the exact encoding — RECOMMENDATION: the freeze-arm
parks the dying reference's `iref_slot` unit (the REF-1 eviction already
juggles these), so a foreign idup's supply-side collides; the alternative
is a premise on idup's contract.

### 2.7 What PART 2 does NOT do

No state_interp/adequacy change, no PC/trace reasoning, no kernel change
— the two doors of AXIOM VERDICT #7 are both refused; this is the third
door the verdicts could not see because every one of their kills
(§7.6.4 horizon, §7.10.6 frame-law, §7.6.3 affinity wedge, byte-identity)
assumed frozen contracts.  Checked against each: horizon — the
certificate is ledger-state inside the movers' own open; frame-law — the
movers' interfaces change, adversaries must present currency; affinity
wedge — `iclaim` is spent by create's own unconditional ilock, `ifreeze`
by the freer's own deposit, neither is ever needed back by a third party;
byte-identity — lifted by the user.

### 2.8 Blast radius / worklist (sequenced)

Core (prerequisite of A's zero-admit gate), in dependency order:
1. `IcacheRef.v`: lelem widens (f column), `ifreeze`, mint/spend/collision
   lemmas, `icnt` ghost. GreyL/SpanL constructors deleted, HeldL arm
   strengthened, BufL arm boot-gated (`IgetLic.v` — fold-back candidate
   per iget-licence.md item 2).
2. `InodeRegion.v`: `ireg_slot` gains icnt-half + freeze-pin + claim-pin;
   `ireg_freeze_au` new; `ireg_claim_au` mints c; accessor re-threading
   (the A-walk's registry-split session did the identical shape in one
   session — known cost).
3. `IcacheInv.v`/`IcacheEscrow.v`: icnt halves in the slot arms; §1.2/1.3
   pool_await.
4. `SpecIget.v` + the five iget callers (`ProofIalloc`, `ProofDirlookup`,
   `ProofNamex`, `ProofNamexRoot`, `ProofIreclaim`) + `ProofIdup`:
   licence re-threading, `ireg_inv` in iget, mints at the count moves.
5. `EscrowDeposit.v`: deposit extends (freeze retire + fragment absorb).
6. The A-walk splice (§1.5).
Then the payout increment:
7. `ProofIlock` fill at a claimed box → the create_fresh_ty lemma;
   `SpecCreateFreshTy.v` axiom retires; `ProofCreate` consumes the lemma.
   GATE: the task-18 standing set drops `create_fresh_ty` (Print
   Assumptions on the create cone = the standing six alone); both audit
   greps (`SpanL`, `GreyL`) go to zero-and-deleted; `proof_coverage
   --check`; `lemma_diff` intended-only.

OPEN items carried: 2.2a (r-units later), 2.6a (HeldL site audit),
2.6b (idup encoding), and VERIFY-at-build: the `ity_shoot` seal's firing
site after fsinit returns (mechanism landed at `IcacheRef.v:684`; find or
add the fire in main's fsinit-return path).

### 2.9 Honest risks

* ~~The freeze-pin's icnt conjunct makes EVERY count move open the region
  — probe FIRST~~ **PROBED, GO (ZZProbeIcnt.v on the lane, untracked;
  2026-08-17; zero admits, four `Print Assumptions` closed).**  The mask
  risk is refuted STRUCTURALLY: every count move in the tree is a
  ref-word store through `WpAu4.wp_sw_au_s_sconf` (`WpAu4.v:123`), whose
  outer mask is hard-coded `⊤ ∖ ↑minstretN` — `↑iregN` is available at
  every site by the store rule's own signature, and no invariant can be
  held open across one of these instructions (the rule concludes a WP at
  the full mask).  Six sites tabled in the probe; the widened hole
  `⊤∖↑minstretN∖↑icacheN∖↑iregN` discharges all side-conditions by
  `solve_ndisj`.  Cost over the landed proofs: one nested `inv_acc` plus
  ~three lines per count-move lemma.  The §13.1-style lock-held-auth
  indirection is NOT needed (and is strictly worse — see probe §2e).
  The ghost: `gmapUR Z (dfrac_agreeR (leibnizO nat))`, ambient gname, NO
  auth (the `lreg`/`lreg_half` p-column pattern); slot half rides as a
  count-move-lemma ARGUMENT (lock-held), region half behind `iregN`.
  The one real cost stands as booked in §2.2: iget's contract gains
  `ireg_inv` (SpecIget's "no ireg_inv" purity is spent).
* HeldL's nlink≠0 strengthening (2.6a) is the one spec change with
  landed consumers whose tolerance is asserted, not verified.
* `ipool_shape_to_np`'s await case takes a licence premise — its two
  call sites must have one in scope (they do: fill and recycle both run
  under an iget/ilock contract that carries it), but the plumbing is new.

---

## 3. THE IIIb WALLS: RULINGS + AS-BUILT AMENDMENTS (2026-08-18)

Increment IIIb stopped-and-reported four walls (`990f32474a`'s commit
message is the finding record).  This section rules on each, verified
against the lane at `990f32474a`, and ends with the executable IIIc brief.
Where §1/§2 below conflict with this section, THIS SECTION WINS — §3.4
marks the superseded sites.

### 3.1 RULING A — the freeze pin, the token's custody, and the refuter
(one coupled ruling)

**A-pin.  `ireg_frz_ok` gains the record, and BOTH record conjuncts are
phase-dependent:**

    FrzPre  ⟹  di_nlink d = 0  ∧  di_type d ≠ 0  ∧  n = 1
    FrzPost ⟹  di_nlink d = 0  ∧  di_type d ≠ 0  ∧  n = 0
    (signature: ireg_frz_ok (f : frzUR) (n : nat) (d : dinode))

The nlink conjunct is what makes §2.6's licence table implementable (it
is the contradiction surface for LinkedL/HeldL/RootL); the type conjunct
is what refutes a freeze at a claim/free box (claim_au's `di_type = 0`
premise + the pin gives `f = FrzOff` at every claim — which the ClaimL
row needs, see the table below).  Verified mover-by-mover cost (all
checked against the lane's actual premises):

| mover | pin re-establishment | cost |
|---|---|---|
| `ireg_write_au` | FREE — already carries `di_type dn' ≠ 0`, `di_type_stable`, `di_nlink_stable` | none |
| `ireg_write_link_fl` | new pure premise `bv_unsigned (di_nlink dn) ≠ 0` (current record; with the pin's contrapositive this refutes frozen outright) | 1 premise; its one ++ site (mkdir's dp) has nlink ≥ 1 in hand |
| `ireg_write_unlink_fl` | FREE — its premise `nlink dn = nlink dn' + 1` already forces `nlink dn ≠ 0` | none |
| `ireg_free_au` | fires only from the DEPOSIT after this campaign (see below); takes `ifreeze_post` in and retires it in the same move — pin's FrzPost arm dissolves as it fires | folded into increment IV's deposit extension |
| `ireg_claim_au` | FREE — its `di_type (ds!!!islot inum) = 0` premise + the pin's type conjunct give `f = FrzOff` at the claim; it then ESTABLISHES the new `ireg_claim_ok` clause below | none |
| `ireg_withdraw` | FREE — record and count untouched | none |
| `ireg_freeze_au` | gains borrowed `dinode_at γi inum dn` + `⌜bv_unsigned (di_nlink dn) = 0⌝` + `⌜bv_unsigned (di_type dn) ≠ 0⌝` (establishes the pin at the mint via auth agreement; the freezer holds all three at ip_free_entry) | 3 premises, all in the walk's hand |

**`ireg_claim_ok` gains `c = Some ⟹ f = Some (Excl FrzOff)`** —
established at the claim (previous row), preserved by the freeze mint
for free (the mint holds `dinode_at`, so the arm is MARKED, and
`ireg_marked_ok` already says MARKED ⟹ c = None).  This is the ClaimL
row's contradiction surface.

**SpecIupdate narrows: `bv_unsigned (di_type dn') ≠ 0` becomes a
contract premise.**  Post-reorder no verified caller writes a type-0
record through generic iupdate (itrunc, create's fill, size updates all
have type ≠ 0 in hand; the OLD iput free path is retired by this very
campaign); the only type-0 write in the reordered kernel is the off-lock
ifree, which goes through the DEPOSIT.  This deletes ProofIupdate's
`ireg_free_au` branch (:197) and makes `ireg_free_au` the deposit's
private mover, where the freeze token is in hand.  TRIPWIRE t4: grep
SpecIupdate's callers first; if a landed caller genuinely writes type 0,
stop and report.

**A-custody.  The freeze token RIDES THE PAYLOAD; `islot2` is untouched.**
IIIb's "live arm is the coherent home" is OVERRULED — the live arm can
never soundly promise a token the freezer holds, and every attempted
disjunct leaked.  The coherent custody is the payload bundle's, exactly
like `dinode_at`:

  - pool bundle (uncached): `ifreeze_off z` — ALREADY LANDED (IIIa);
  - recycle peel: token moves pool → the entry escrow's PARKED arm with
    the payload;
  - PARKED arm: carries `(ifreeze_off z ∨ ifreeze_pre z)` — ordinary
    parks deposit FrzOff; the freezer's +0x70 mid-free park deposits its
    FrzPre and takes it back at the +0x8a re-extraction;
  - HELD arm (payload out): NO token — it is in the payload holder's
    hand, which is what `ireg_freeze_au`'s caller-token model already
    assumes and what the walk needs at ip_free_entry;
  - eviction (`ic_close_to_empty` / `_await`): payload + token move
    escrow → pool together — IIIa's premises already demand exactly this.

**A-AUs.  The count-move family reworks as:**

  - `iref_incr_store_au` / `iref_dup_store_au` / `iref_upgrade_store_au`
    (up-counts): DROP the `ifreeze_off` in/out (the mover cannot have it
    — the token is with the payload holder, possibly the freezer).  GAIN
    a borrowed `iname γi γfs inum l` and refute `FrzPre` INSIDE the
    region open via the new licence-table lemma (below).
  - `iref_close_store_au` (not-last): unchanged (ge-2 count refutes both
    phases arithmetically, already landed).
  - `iref_close_last_store_au`: II's generic `ifreeze ph → ifreeze
    (frz_close ph)` shape SURVIVES — the custody ruling makes it
    presentable by both callers: the ordinary last closer sources
    `ifreeze_off` from the parked payload it is about to evict; the
    freezer sources `ifreeze_pre` from its hand.
  - NEW `iref_alloc_store_au` (the 0→1 recycle wrapper, region-aware
    sibling; takes the peel's `icnt_half z 0 ∗ ifreeze_off z`).

**A-refuter.  `ipool_await_refuter` is DELETED.**  IIIb proved its shape
unbuildable (a bare wand into False cannot come out of a fupd).  The
peel (`ipool_shape_to_np`) instead takes the borrowed `iname γi γfs inum
l` + `ireg_inv` (+ mask), opens the region inside, and refutes the await
arm's `ifreeze_post` via the table.  Fupd-shaped, licence-taking —
exactly the reshape IIIb's finding demanded.

**The licence-table lemma (`iname_not_frozen`, home: IgetLic.v — it
needs both `iname` and the region internals):** for each runtime licence
at inum z with the slot's arm open (link_auth, `ireg_link_ok`,
`ireg_claim_ok`, `ireg_frz_ok f n d`, the boot disjunct):

| licence | contradiction with `f ∈ {FrzPre, FrzPost}` |
|---|---|
| `LinkedL` | ipaid → w-sum ≥ 1 → `ireg_link_ok` nlink ≥ 1 vs pin nlink = 0 |
| `HeldL d` | dinode_at agreement (auth) pins d = arm record; its `nlink d ≠ 0` vs pin |
| `ClaimL` | iclaim → c = Some (ledger agreement) → new `ireg_claim_ok` clause f = FrzOff |
| `RootL` | `ireg_root_ok` strict (w < nlink) → nlink ≥ 1 vs pin |
| `BufL` | carries `ireg_boot`: kills the f-clause's ireg_boot disjunct by pending-exclusivity and its ireg_open disjunct by `ireg_boot_open_excl` |

Conclusion `⌜f = Some (Excl FrzOff)⌝`, borrowed licence returned.

### 3.2 RULING B — the `ireg_open` producer: seal in forkret-first, ride
`sysc_fs_env`, terminate at the EXISTING forkret IOU

Verified: the seal is a one-liner that already exists (`ity_shoot`,
IcacheRef.v:847; the header at :894 says verbatim "[ireg_boot ==∗
ireg_open] fires once after fsinit returns").  SpecFsinit RETURNS
`ireg_boot` in its post (SpecFsinit:339's comment assigns the seal to
the boot caller, "after fsinit returns and before kexec(/init)" = the
forkret first branch).  forkret's first branch is axiomatized
(`wp_forkret_nf_ax`, LinkForkretNF.v:62) and that axiom is ALREADY in
the accepted adequacy baseline.  Upstream's `sysc_fs_env`
(ProofSyscall.v:511, Persistent) is the ambient fs fabric every syscall
proof receives, and `syscall_env` is a Definition nobody constructs yet
("SATISFIABILITY IS UNCHECKED" — upstream's own header).

**Route (chosen):** `sysc_fs_env` gains one persistent field,
`ireg_open`.  Zero proof cost today (nothing constructs the env); when
the boot wiring lands, the constructor's obligation is discharged by
fsinit's returned `ireg_boot` + `ity_shoot` at exactly the owed site.
Threading: `ireg_open` rides the SAME channel `ireg_inv` already rides —
sysc dispatch → SpecCreate premise (+ the three create-calling syscalls'
proofs pass it) → SpecIalloc premise → ProofIalloc:1476 →
`ireg_claim_au`.  Persistent, so every step is a mechanical
frame-through.

**Termination + honesty clause:** the chain terminates at
`wp_forkret_nf_ax` — an EXISTING, accepted IOU (shared with upstream's
own boot-shelter interest; durable-notes' adequacy baseline records it).
NO new axiom.  Premises do not pull axioms into `Print Assumptions`, so
the create/unlink/iput gate targets are unaffected; the axiom appears
only where forkret is USED (adequacy chain), as it already does.  If the
user wants that IOU retired too, the two honest options are: prove
forkret's first branch (upstream's shared-interest item), or wire the
boot chain to adequacy (the bigger, separately-scoped project).  Neither
blocks this campaign's gates.

### 3.3 RULING D — dirlookup's premise + the contract set

`SpecDirlookup` gains the pure twin of premise (6):
`bv_unsigned (di_nlink dr) ≠ 0` (about the REGION record `dr`, beside
:298's `di_type dr ≠ 0`).  Discharged at the four callers IIIb located:
ProofNamex:3897 (the walk's fs.c:693 nlink guard / inode_held_ty),
ProofCreate:3307 (dp locked and live), ProofDirlink:1794 (caller's live
parent), ProofSysUnlink:2347 (its own nlink guard).  TRIPWIRE t3b: if a
caller's discharge is not in hand, stop and report — do not weaken to a
disjunction.

**Contract-set widening (approved):** `SpecIget`, `SpecIdup`, `SpecIput`
gain `ireg_inv γi γfs inodestart nib` (+ the index params) — forced by
II's count coupling; the `Iput*Dev` walk files already carry `ireg_inv`
(verified: 3/1/3 occurrences), so the walk side is ready.  SpecIget's
"no ireg_inv" header prose is amended: iget still never reads a dinode —
the region open is ghost-only (icnt/freeze columns).

### 3.4 As-built amendments (the doc's earlier §-sites are superseded by)

- §2.3's pin → §3.1's phase-dependent THREE-conjunct form (supersedes
  both the original and increment I's count-only deviation, recorded at
  `de366eb301`).
- §2.6's table → §3.1's `iname_not_frozen` (the table is a LEMMA, its
  rows as above).
- §1.2/§1.3's pool_await/refuter → IIIa's shapes (`65e7403340`) with
  §3.1's refuter deletion; pool_await carries `ifreeze_post` (IIIa
  deviation 3, stands).
- §2.2's half placement → II's islot2 live arm + IIIa's pool bundle
  (`9148a15200`, `65e7403340`); islot_empty carries nothing (II's
  fraction-25 refutation, stands).
- Increment I's five deviations (`de366eb301`): FrzOff three-state,
  arm-coupled claim pin, withdraw spends iclaim, claim_au's ireg_open —
  all stand; only the count-only pin is superseded (above).

### 3.5 THE IIIc BRIEF (dependency-ordered; red trajectory 7 → 3)

Target red set after IIIc: `EscrowDeposit` (increment IV's),
`ProofIput` (the integration's), `ProofIlock` (item 7's — its :1113
iclaim goal is create's contract clause by design; its :749/:1084
mechanical fixes DO land here so item 7 inherits exactly one goal).

1. **InodeRegion.v**: `ireg_frz_ok` → 3-conjunct phase form (+ record
   param; :1354's arm site updates); `ireg_claim_ok` + the `c = Some ⟹
   f = FrzOff` clause (claim_au establishes); `ireg_write_link_fl` +
   nlink≠0 premise; `ireg_freeze_au` + the three premises (§3.1 table);
   re-prove the arm movers' pin re-establishment (the table says which
   are free).
2. **IgetLic.v**: `iname_not_frozen` (five rows; BufL row via the boot
   exclusivities).
3. **IcacheEscrow.v**: PARKED arm gains `(ifreeze_off z ∨ ifreeze_pre
   z)`; peel routes the token pool→parked at the recycle; extraction
   (ilock's payload-out) hands token to holder; `ic_close_to_empty`
   sources its IIIa token premise from the parked payload.  TRIPWIRE t2:
   the ordinary extraction/fill at a FrzPre-parked box must be refuted
   from the extractor's own resources (it holds a reference; pin says
   n = 1 = the freezer's — expected route: count agreement/iref_lookup
   under the itable lock, or valid=0 structural exclusion since the
   mid-free park wrote valid=0 and ordinary extraction requires
   valid=1).  Three failed shapes → stop and report.
4. **IcacheInv.v**: the up-count AU rework (licence premise +
   iname_not_frozen inside the open); NEW `iref_alloc_store_au`;
   close_last generic form retained.
5. **SpecIupdate.v** (+ProofIupdate): the type≠0 narrowing (t4 grep
   first); delete the free_au branch.
6. **Contracts**: SpecIget/SpecIdup/SpecIput widen (ireg_inv + params);
   SpecDirlookup + nlink premise; SpecIalloc + SpecCreate + the three
   create-calling sys_* proofs + `ireg_open` premise; `sysc_fs_env` +
   `ireg_open` field.
7. **Caller cone re-green**: ProofIget (peel-with-licence, alloc AU at
   +0x78, licence-borrowing hit), ProofIdup, ProofDirlookup (+ its four
   callers' new pure discharge), ProofIalloc (ireg_open + ClaimL +
   iclaim into SpecIalloc's post; frame-and-ignore at ProofCreate),
   ProofIlock :749 (`ipool_shape_np` form) + :1084 (peel) + ordinary
   fill — leaving :1113's `iclaim` as item 7's single inherited goal
   (ProofIlock stays red).
8. Whole-tree `make -k`: failures = exactly {EscrowDeposit, ProofIput,
   ProofIlock} + their Link* cones.  Zero admits.  TRIPWIRE t5: any
   growth beyond that set stops the increment.


### 3.9 RULING A′ (IIIc's wall, 2026-08-18): the nlink++ mover pays with the holder's freeze token

IIIc executed steps 1/2/3a/4/5 green (`ccb447c5e4`) and stopped at ruling
A's mispriced `ireg_write_link_fl` row: the `di_nlink dn ≠ 0` premise is
FALSE at 2 of the mover's 3 sites (ProofCreate:4910 fresh child, pre-count
pinned 0 by `fresh_shape`; ProofSysLink:1790 `ip->nlink++`, no guard, no
fact).  Every cheaper route was refuted in the IIIc record commit.

RULING: adopt IIIc's option (A).  The A-custody ruling already places the
freeze token in the payload HOLDER's hand; the missing piece is only the
surfacing route:
- `SpecIlock`'s post hands the holder `ifreeze_off z` alongside the payload
  it already returns (the token travels pool-bundle ↔ PARKED arm ↔ holder,
  so ilock's withdraw has it by construction);
- `wp_iupdate_link`'s premise becomes `⌜di_nlink dn0 ≠ 0⌝ ∨ ifreeze_off z`
  (borrowed-and-returned on the token arm);
- mkdir's dp site (ProofCreate:8715) pays the pure arm unchanged; create's
  fresh child and sys_link pay the token arm from their own ilock;
- `iunlockput`/`ip_free_locked`'s re-park returns the token with the payload
  (the freezer's own path swaps it FrzOff→FrzPre at `ireg_freeze_au`, so the
  free path's park carries the phase the §1.2/§2.3 shapes already state).
Contract set grows by SpecIlock (post clause) — sanctioned.  The pin, the
table, and every other §3 ruling stand unchanged.

INCREMENT IIId (the convergence pass) = A′ + IIIc's unexecuted steps 3-rest/
6/7 + walls B (sysc_fs_env ireg_open threading) and D (SpecDirlookup pure
premise): target red set = {EscrowDeposit, ProofIput, ProofIlock(:1113 only)}.

### 3.10 IIId AS-BUILT (2026-08-18): what landed, the three deviations, and what is left

IIId executed A′ and walls B and D in full and stopped short of IIIc's steps
6/7 (the `SpecIget`/`SpecIdup`/`SpecIput` contract widening and its caller
cone).  Red set 9 → 5.  Every deviation below is a WEAKENING of a ruling's
LETTER that preserves its argument; each is recorded at its site in the
source as well.

**A′ AS BUILT — the token rides `ic_payload`, not the post's text.**
§3.9 says "`SpecIlock`'s post hands the holder `ifreeze_off z`", and IIIc's
record offered the alternative "or the payload bundle carries it".  BOTH
landed, and the second is what made the first cheap:

  - `IcacheEscrow.ic_payload` splits into `ic_payload_np` (the old body) and
    `ic_payload := ic_payload_np ∗ ifreeze_off (bv_unsigned inum)`.  That one
    line puts the token on A-custody's path by construction — `ic_parked`'s
    payload conjunct IS `ic_payload`, so PARKED carries it; `ic_swap_checkout`
    hands it to the holder and `ic_swap_park` takes it back, both with their
    statements otherwise untouched.
  - Why not `ic_loaded`: 45 files name `ic_loaded` and a dozen destructure
    it; EIGHT name `ic_payload`.  And `ic_loaded` would have poisoned
    `ic_close_to_empty_await`, whose payload is the FREEZER's (token at
    `FrzPost`); with the split that lemma keeps its exact signature by
    speaking at `_np`, as do `ic_close_to_empty` and `_core`.
  - DEVIATION 1 (recorded): the PARKED arm carries `ifreeze_off`, not
    A-custody's `(ifreeze_off ∨ ifreeze_pre)`.  The disjunct exists for the
    freezer's +0x70 mid-free park, which is `ProofIput`'s and
    `EscrowDeposit`'s — both red by design here — and every LANDED path
    through the arms is FrzOff-only (pool peel → `ic_unloaded` → fill →
    checkout → park → eviction).  Stating the disjunction now would have
    cost each of those a refutation it cannot yet perform (TRIPWIRE t2's
    obligation) and bought nothing green.  The widening is one line, at the
    same place, when the iput integration lands.
  - Contracts that grew: `SpecIlock`'s post, `SpecIunlock`'s and
    `SpecIunlockput`'s preconditions, `SpecCreate.create_locked`,
    `SpecCreateFreshTy`'s alloc arm (an axiom's body: zero proof cost).
    §3.9 sanctioned only `SpecIlock`; the other four are the SAME clause on
    the return leg, and without them the parked arm cannot be rebuilt.  This
    is the "every ilock caller's continuation pattern" that IIIc's OPTION A
    priced.
  - DEVIATION 2 (recorded): `wp_iupdate_link`'s premise is NOT §3.9's
    disjunction but `InodeRegion.ireg_link_pin pin z d`, a bool-indexed
    predicate (`true` ↦ the token, `false` ↦ `di_nlink d ≠ 0`).  A
    disjunction is the wrong SHAPE for a borrowed-and-returned premise: the
    mover hands back what it was given, but a caller that presented the
    TOKEN could not tell the returned `⌜…⌝ ∨ ifreeze_off` apart from the
    pure arm and would have to drop it — which is exactly the resource
    sys_link needs at its re-park.  With the index, in and out are the same
    proposition at the same `pin`.
  - The three sites, as ruled: ProofCreate's fresh child (`pin = true`,
    paid from `create_fresh_ty`'s relayed token), ProofSysLink's
    `ip->nlink++` (`pin = true`, from its own `ilock(ip)`), ProofCreate's
    mkdir `dp->nlink++` (`pin = false`, `Hp3nlnz`).
    `InodeRegion.ireg_write_link_p` is no longer VACUOUS: IIIc's
    contradictory pair (`di_nlink dn = 0` from `fresh_shape` AND RULING A's
    `≠ 0`) is replaced by the token, so the tagged mint now says something.

**WALL B AS BUILT — exactly §3.2's route.**  `ProofSyscall.sysc_fs_env`
gains `ireg_open` as a final conjunct (zero proof cost: nobody constructs
it), and `FsSyscalls.fs_world` gains it beside `ireg_inv` for the same
reason.  Channel, in order: `sysc_fs_env` / `fs_world` → `SpecSysMkdir`,
`SpecSysMknod`, `SpecSysOpen` → their proofs → `SpecCreate` → `ProofCreate`
→ `SpecCreateFreshTy` (the span) → `SpecIalloc` → `ProofIalloc:1476` →
`InodeRegion.ireg_claim_au`.  ProofIalloc is GREEN.

Two riders came with it, both from the IIIb brief's step 4:
  - `SpecIalloc`'s post now exposes `iclaim (bv_unsigned inum)` — the AU has
    delivered it since increment I and ialloc was dropping it at an
    `iIntros` underscore.  It travels `ia_arms` → `ia_cont` → the contract.
  - **`SpanL` IS DELETED.**  `ProofIalloc`'s tail iget presented it because
    "(d) is foreclosed until F1.5c mints an `iclaim`"; F1.5c has landed, so
    the site is now `ClaimL` and the receipt is borrowed and returned, as
    `IgetLic.v`'s own R14 tombstone promised.  `grep -n "SpanL" iris/*.v`
    now matches only IgetLic.v's tombstone text.

**WALL D AS BUILT — DEVIATION 3 (recorded), and it is forced.**
§3.3 says `SpecDirlookup` gains `bv_unsigned (di_nlink dr) ≠ 0`.  dirlookup
has FIVE callers, not the four §3.3 enumerates, and the fifth —
`FsLookup.wp_dirlookup_tree` — provably cannot pay it: FsLookup's own header
says `node_rep` "says NOTHING about `di_nlink`.  There is no tree-level fact
that implies it", which is why ITS premise (4) is the §7.5.6 disjunction.
Under the ruling's shape the tree layer goes red with no discharge in sight
(t3b territory).

What landed instead is the EQUATION `di_nlink dr = di_nlink dn`.  The proof
site already holds `Hnl0 : di_nlink dn ≠ 0` (that is `dl_lic_live`'s output
on the hit arm, before the self/non-self split), so the only count it is
missing is the region record's, and the equation transports the one it has.
FOUR of the five callers hand the same record in twice and pay `eq_refl`
(FsLookup, ProofCreate, ProofNamex, ProofSysUnlink); the fifth
(ProofDirlink, the one caller with a genuinely stale region index) pays it
out of `di_nlink_stable`'s first conjunct, which its contract already
carries for `SpecIupdate`'s sake.  It is the same "parked-means-flushed"
fact `ic_loaded` states resource-side, at one field.

**THE RED SET AFTER IIId** (whole-tree `make -k`): `EscrowDeposit` (:73,
increment IV's), `ProofIput` (:972, the integration's), `ProofIlock`
(:1084 — the peel; item 7's `iclaim` at :1113 is still behind it),
`ProofIget` (:1306, the recycle's `ipool_shape_to_np` licence) and
`ProofIdup` (:432, `iref_upgrade_store_au`'s licence).  The last two are
IIIc step 7's and were NOT attempted: steps 6/7 (widening
`SpecIget`/`SpecIdup`/`SpecIput` with `ireg_inv` + index params, and the
whole iget/idup/iput caller cone) remain for IIIe.  Zero admits added.

### 3.11 IIIe AS-BUILT (2026-08-18): the iget cone converged; idup hit OPEN(2.6b)

IIIe executed IIIc's deferred steps 6/7 for `SpecIget` and `SpecIput`, greened
`ProofIget` and the whole five-caller iget cone, and reduced `ProofIlock` to the
single `iclaim` goal item 7 owns.  It STOPPED at `SpecIdup`, on tripwire 1.
Red set 5 → 4: `{EscrowDeposit:73, ProofIdup:432, ProofIlock:1123, ProofIput:972}`
(+ a 39-file `Link*` cone).  Zero admits added.

**`SpecIget` WIDENED, and the header's purity clause is spent.**  It gains
`inodestart` and `ireg_inv γi γfs inodestart nib`, placed after `ic_escrows`.
The "NO `ireg_inv`: iget never reads a dinode" paragraph is amended IN PLACE
rather than deleted: iget still reads no dinode, and both new opens are
GHOST-ONLY on the ledger's two columns —

  - the recycle's pool peel (`ipool_shape_to_np`, +0x72), which since §3.1's
    A-refuter refutes the await arm's standing freeze from the borrowed licence
    INSIDE its own fupd, and hands back `icnt_half z 0` and `ifreeze_off z`;
  - the recycle's 0 → 1 (`iref_alloc_store_au`, +0x78), replacing the inline
    region-blind `iref_alloc_step`.  Its token travels on into the parked arm at
    +0x7c (`ic_close_mid_to_parked` already took it) and its half into
    `islot2`'s live arm.

**`SpecIput` NEEDED NOTHING** — §3.3's prediction verified on the lane: it
already carried `ireg_inv`, `inodestart` and the inum bound, and iput's movers
are the two CLOSES, which are licence-free.  So the iput caller cone (fileclose,
kexit, sys_chdir, sys_link, iunlockput, dirlink, ireclaim, namex) did not move at
all.  The whole IIIe ripple is the IGET cone.

**THE LICENCE NOW RIDES THE SCAN, NOT THE TAIL CLOSURE (ProofIget).**  Before
IIIe both of iget's exits reached a shared tail that had captured `Hlic` at
+0x44 and produced it at +0x9c.  Both exits now SPEND it inside their own count
move — the hit's `iref_incr_store_au` borrows it, the recycle's peel borrows it
— so `TAILC` takes it as an argument and the fuel induction carries it.  Also:
`islot2`'s live arm is FOUR conjuncts and the hit arm had been destructing it
into three (the `icnt` half riding along inside the `ic_id` pattern); it is
split explicitly now, and the three MISS exits put it back unmoved.

**ProofIlock: the fill does NO peel.**  `il_load`'s premise at :749 becomes
`ipool_shape_np` (which is what a checked-out UNLOADED payload actually holds —
`ic_unloaded` = `inode_raw ∗ ipool_shape_np`), and the :1084 peel is DELETED.
The conversion happens ONCE, at the recycle that cached the entry, for the whole
lifetime of the cached box; asking the fill to peel again would demand a second
`icnt_half z 0` at an inum whose count is 1.  With that, ProofIlock's first error
is `ireg_withdraw`'s un-supplied `iclaim (bv_unsigned inum)` at :1123, exactly as
§3.5 item 7 predicted — and nothing else stands between :1084 and it.  Also
recorded at the checkout site: `ic_payload` is FOUR pieces since A′, and routing
its `ifreeze_off` through `il_cont` to `SpecIlock`'s post is the SAME un-landed
item as that `iclaim`.

**WALL (tripwire 1): `SpecIdup` CANNOT WIDEN — this is OPEN(2.6b), reached.**
`ip->ref++`'s mover is `iref_upgrade_store_au`, and RULING A gives every UP-count
a borrowed `iname γi γfs inum l`.  The widened contract and a green `ProofIdup`
were BUILT (ireg_inv + inodestart + inum bound + licence, licence returned in the
post) and then REVERTED, because idup's two call sites are both `idup(p->cwd)`
— `ProofKforkB4:365`, `ProofNamex:5660` — and neither can present a licence at
any of the five constructors: `LinkedL` wants a directory payload's `ipaid`,
`HeldL` (and every region-side `iname_*_alloc`) wants a `dinode_at`, `ClaimL`
wants an `iclaim`, `RootL` wants the inum to BE the root, `BufL` is boot-only.
A cwd is not even `nlink ≠ 0` — xv6 permits unlinking a process's cwd.  Both
files went red at exactly that argument on the lane; threading the premise up
would put a licence clause on `SpecKfork` and `SpecNamex` (and `SpecKfork` has no
`ireg_inv` or `logG` at all) with no discharge anywhere above them.

The arithmetic route does not save it either: the licence-free accessor
`ireg_icnt_acc` refutes both phases from the pins (`FrzPost ⇒ n = 0`,
`FrzPre ⇒ n = 1`), so it needs `2 ≤ n`, and a cwd held by one process sits at
`n = 1` — the one value `FrzPre` admits.

RULING NEEDED, and §2.6b already names it: at `FrzPre` the freezer holds the
WHOLE of the slot's outstanding share (`iref_lookup`'s REF-1 exclusivity), so a
foreign share's fraction genuinely collides with it — but the freezer's holdings
are in its hand, not in the region, so the FREEZE ARM must park a witness for the
mover to collide against ("the freeze-arm parks the dying reference's `iref_slot`
unit, so a foreign idup's supply-side collides").  That is a ruling plus an
`InodeRegion` edit on the freeze arm, `ireg_freeze_au` and the deposit — it
belongs with the increment that owns the freeze arm, not with a convergence pass.
The finding is also recorded in `SpecIdup.v`'s own header.

**Premise-plumbing done (all mechanical, ireg_inv + `inodestart` only):**
`SpecDirlookup` (+ its five callers FsLookup / ProofCreate / ProofDirlink /
ProofNamex / ProofSysUnlink), `SpecNamex.wp_namex_root_body` → `ProofNamexRoot`,
`SpecNamei.wp_namei_root_body` → `ProofNameiRoot` (both chains terminate — the
root contracts have no further consumers), and the direct sites in `ProofIalloc`
and `ProofIreclaim`, which already held `ireg_inv`.
