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
