# The file system's abstract/ghost state — a reference inventory

STATUS: verified at the `simp-2` tip — the post-campaign simplification
increment SIMP-2 (**the reference package** and **`fs_ready`**, the boot-free
fs predicate) on top of SIMP-1 (regime specialization, the BufL block-tie
fold, the dead-weight sweep) on top of the pushed FINAL-GATE tree
`bc96776a`.  Whole tree green at fixpoint, staleness 0.  The iclaim-ledger
campaign is COMPLETE: the reordered `iput` (kernel pin 4398009) is proven
end-to-end, and `create_fresh_ty` is a THEOREM
(`iris/ProofCreateFreshTy.v`).  Nothing here is in flight; the three
syscall tops rest on the five Sail platform axioms + funext alone.

WHAT SIMP-2 CHANGED, in one line each — the two halves interact at
`inode_held` and landed together:

* **The reference package** (§6): the reference and its provenance unit stop
  being spelled apart.  `inode_refb`/`inode_refp`/`inode_refp_short`/
  `inode_claimed` (`IcacheRef.v`) are the four shapes, `inode_held` is
  restated over `inode_refp`, and the five fs contracts that used to spell
  the trio now spell one row each.  **The contract surface is now SHORTER
  than it was BEFORE the campaign**: pre-campaign `iget` returned a bare
  reference; post-SIMP-2 it returns one package the rest of the tree
  already wanted.
* **`fs_ready`** (§7): `FsSyscalls.fs_world` is rehomed to its own leaf
  (`FsReady.v`), given the PRODUCER it never had (`fs_ready_establish`, on
  top of the seal `fs_ready_seal : ireg_boot ==∗ ireg_open`), and given a
  projection family.  `fs_world` is now a one-line derived alias.  The
  point is the forkret delta: what `wp_forkret_nf_ax`'s discharge owes the
  file system is **one persistent row**.

Layout: one section per layer, bottom-up.  For each piece: the RA/type, its
HOME (which invariant or lock-held bundle owns the authority), what a
fragment in a client's hand MEANS, who mints/spends it, and why it exists.

---

## 1. Disk and buffer layer

THE LINE THAT ORGANIZES THIS LAYER IS **HOME BLOCK vs LOG-REGION BLOCK**
(`fs_home_set cov logstart` = `cov ∖ log_region_set logstart`).  A home
block belongs to the file system and its owner holds the EXCLUSIVE byte run
`fsblock`; a log-region block is the log's own storage and is not in the
file system's byte view at all, so its owner (`log_state`, and initlog
before it) holds the cache's parked half `fs_chalf`.

| piece | type / home | meaning |
|---|---|---|
| `fsblock (fs_bytes γfs) bno bs` | a run of BSIZE **full** `ghost_map Z (bv 8)` elements (`FsBlocks.v`) | block `bno`'s bytes in the LOGGED VIEW `L`, owned EXCLUSIVELY.  THIS is what every home-block owner above the log holds: `BitmapInv`'s bitmap block and free pool, `InodeRegion.ireg_blk`, `InodeInv.ind_blk`/`blk_res`, the icache escrow's payloads, `FsImgBridge`'s boot bundle.  Sealed with `Typeclasses Opaque` — see the trap below. |
| `fs_chalf γfs bno bs` | ½ of `bno ↪[fs_cache γfs] bs` (`ghost_map`, `FsBlocks.v`) | the PARKED half of block `bno`'s cache entry — what the buffer cache believes.  After durable-disk 1c-flip only TWO kinds of holder are left: the log's own storage (`log_state`'s header + slot rows; `SpecWriteHead`, `ProofEndOp`'s write_log, install_trans's log copies), and a handle's MACHINERY half carried out of a bio payload (`ds_held_L`, `IgetLic`'s `BufL`).  A HOME block's parked half lives inside `fs_bytes_inv` and no mortal ever holds one. |
| `fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home` | `inv logN …` (`FsBlocks.v`) | the tie: the byte auth, the home blocks' parked cache halves, `bytes_tie`, `bytes_dom`.  Three carriers hand it out and every bread client holds one — `LogInv.log_ctx`, `BitmapInv.bitmap_inv`, `InodeRegion.ireg_inv` — plus an explicit premise at the two readers that hold none (`readi`, `bmap`, whose kit is `None` on the read path). |
| `fs_bytes_any γfs` | `∃ home, fs_bytes_inv …` (`FsBlocks.v`) | the home-set-free form of that row.  It is enough for every consumer because **holding the run IS being a home block**: `fsblock_home` derives `b ∈ home` from the byte auth and `bytes_dom`, so neither crossing takes a membership premise. |
| `fs_dirty` | second `ghost_map` in `fs_names` | per-block pinned/dirty flag tying the buffer cache to the log's write set (`LogInv.v:718`). |
| `fs_own` | third `ghost_map` (`Excl`-style per-block token), `blk_own` | the exclusive per-block ownership token.  **REDUNDANT since the flip** wherever it was carried only for disjointness: `fsblock_excl` gives `blk_own_ne`'s conclusion directly, so `InodeInv.blkmap_wf`'s injectivity, `BitmapInv.free_pool_own_used`'s panic refutation and `IcacheEscrow`'s `blk_res` token no longer need it.  Kept until stage 2 replaces the pool with `free_bitmap Γ`. |
| `bio_ctx` / `fs_view` | the buffer-cache invariant | owns the physical buffer array and the `fs_cache`/`fs_dirty` payload halves; `fs_view γfs γd dev cov` is the fs-side lens on it. |

**The two crossings** (`FsBlocks.v`), both fupds at any `E ⊇ ↑logN`:
`fs_bytes_agree`/`fs_bytes_agree_any` — a bread client's `fsblock` against
the handle's payload half gives `bsm = bs`; and `fsblock_update` —
log_write's ghost step, moving both maps.  Every reader that used to close
by an auth-free ½/½ entailment is now one of these, which is why the
readers above gained `↑logN ⊆ E`.

**`fsblock` IS SEALED WITH `Typeclasses Opaque`, AND IT HAS TO BE.**  It is
a 1024-element `big_sepL` under two `Definition`s and `iFrame` resolves its
`Frame` instances up to delta: a bare `iFrame` at a goal holding
`fsblock gL b (bitmap_bytes used)` unfolds through `byte_range` into the
whole run and does not come back — measured as a `BitmapInv.bitmap_res_close`
that ran past ten minutes with no error.  Sealing the two heads leaves
`rewrite /fsblock` and the declared `Timeless` instances working and makes
`iFrame` treat a block run as one atom.

**AND THE ROW CANNOT RIDE WITH THE BLOCK.**  The obvious simplification —
bundle `fs_bytes_any γfs` into the per-block resource so no reader needs a
premise — is not available: `fs_bytes_any` contains an `inv`, which is not
TIMELESS, and `ireg_blk`/`ireg_body`/`bitmap_res`/`blk_res` are all required
to be timeless by the `>`-strips their accessors do.  The row therefore
rides on the three (persistent, non-timeless) invariant carriers instead.

## 1b. The block bitmap (`BitmapInv.v`, invariant `bitmapN`)

| piece | type / home | meaning |
|---|---|---|
| `bitmap_inv γfs bms cov ls size` | `inv bitmapN (∃ used, bitmap_res …)` ∗ the byte view's row | THE OWNER of the free-space state: the pure `bitmap_ok`, the bitmap block's `fsblock` at `bitmap_bytes used`, and the FREE POOL (one `fsblock`+`blk_own` per clear bit) — at an EXISTENTIAL set no contract names.  It also CARRIES `fs_bytes_inv … (fs_home_set cov ls)`, which is what its readers open (`bitmap_inv_bytes`, `bitmap_inv_bytes_at`).  Persistent; a `fs_ready` conjunct (`fs_ready_bitmap`); allocated once in `fs_cfg_alloc`'s era fupd. |
| `bitmap_read` / `bitmap_read_own` | mask-preserving openings, `↑logN ⊆ E` | between `bread` and `brelse`, the handle's machinery half against the invariant's byte run names `∃ used, bs = bitmap_bytes used ∧ bitmap_ok`; the `_own` form adds `b ∈ used` from the caller's `blk_own` — the "freeing free block" panic refutation. |
| `bitmap_alloc_au` / `bitmap_free_au` | `wp_log_write_au` suppliers | the ONLY moments the client half leaves the invariant: balloc's sets a bit and takes `free_blk bi` (+ its cov/log facts) out of the pool; bfree's clears a bit and deposits the caller's `free_blk b`.  Stated at the CALLER's set, `bitmap_bytes_eq_*` bridge to the parked one. |
| `blk_own γfs b` | full `ghost_map` element (`FsBlocks.v`) | unchanged: the exclusive per-block token balloc hands out and bfree consumes; its exclusivity against the pool is the alloc/free handshake. |

Design: [`fs-bitmap.md`](fs-bitmap.md) §"Who owns `bitmap_res` between
calls".  No fs contract mentions the bitmap's set; balloc/bfree (and the
pre-seal ireclaim cone) take the constituent `bitmap_inv` row, everything
post-seal reads it off `fs_ready`.

## 2. The log

| piece | type / home | meaning |
|---|---|---|
| `log_ctx γ bn γfs cov logstart dev` | the log invariant (`LogInv.v:802`) | owns the on-disk log region, the committed/installed views, and the epoch counter; every fs mutation runs inside a `begin_op`/`end_op` bracket against it. |
| `log_opS γ u Sb` | exclusive op token, CLOSED form (`LogInv.v:372`) | "I am inside an op with `u` units of write budget and write-set `Sb`."  `log_opSe` (`:350`) is the OPEN/epoch-indexed form the free path uses; `log_opSw`/`log_opSwe` are the mid-write variants. |
| `log_credit γ cr Sb` | `LogInv.v:595` | the re-credit token — how iput's off-lock tail pays for `ifree`'s `log_write` after re-opening (`iput_units`). |
| `log_epoch_lb γ e` | `mono_nat` lower bound (`LogInv.v:291`) | a persistent floor on the log epoch; lets an off-lock continuation know its op's epoch has not been recycled. |

## 3. The inode region (`InodeRegion.v`, invariant `iregN`, gname `γi`)

The bottom of the inode world: one `ireg_slot γi z d` per inum `z` inside
`ireg_body`, plus the inode-block bytes.  Everything a disk-inode MOVER can
touch lives here; every byte write to a dinode goes through one of the
region's atomic-update movers, which is what makes the clauses below
invariants rather than wishes.

### 3a. Record custody

| piece | type / home | meaning |
|---|---|---|
| `z ↪[γi] d` / `dinode_at γi inum dn` | `ghost_map` fragment (`InodeRegion.v:1068`) | **custody of inum's record**: exclusive, and required by every byte-writing mover.  Parked in the region while the box is idle (the IN arm); checked out through the pool → entry-escrow → `ilock` chain; `dinode_at_excl` makes a second copy absurd. |
| `imark γi z` | marker fragment at `imark_key z` | the MARKED state's stand-in for the record — the box's bytes are type≠0 but its record is checked out to a claimant/freer; the MARKED arm carries `⌜ireg_marked_ok c d⌝` (claims retire on entry to MARKED). |
| `ireg_ep z d` | per-inum `mono_nat` (`icfg_iep z`) | the record's **epoch**: bumps at every flush, giving readers "no older record can reappear". |
| `ireg_claim_no_out` (`InodeRegion.v:3853`) | theorem, not a resource | a claimed inum's record is INSIDE the region — nobody holds its `dinode_at` — so ilock's non-fill routes die and §16.4's box fill is FORCED.  The §20.7 carrier; this is the load-bearing half of the `create_fresh_ty` proof. |

### 3b. The per-inum link ledger — `link_auth z wl wdu wdt g c r p f rc`

One authority per inum (nine columns + the count), inside `ireg_slot` via
`ireg_rcol` (`IcacheRef.v` defines the RA; filed as a `gmap` under the
ambient gname `icfg_link`; the element is `lelemc`, with `lelemf`/`lelem`
the rc-0/f-None defaulted aliases that keep old literals byte-stable).

| col | counts | fragment | minted / spent | why |
|---|---|---|---|---|
| `wl` | paid dirent records (plain) | `ilink z` | dirlink / unlink | pays for a live directory record naming `z`; `ireg_link_ok`: `wl+wdu+wdt ≤ nlink` **and** `nlink ≤ 32767` (L4). |
| `wdu` | paid `".."`-units | `ilinkd z` | mkdir's dot-dot deposit | the d-flavour of the same payment; buys `ireg_dir_ok` (`0 < wd → type = T_DIR`). |
| `wdt` | THE parent-record unit (≤1, `ireg_par_ok`) | `ilinkdp z pv` + `iparent z pv` | mkdir / rmdir | tagged unit carrying half the **parent register** `p` — the `".."`-tie. |
| `g` | grey records — orphaned `".."`s nothing pays for | `igrey z` | unlink's grave-dot-dot | carries NO allocatedness; that is the point (§20.8). |
| `c` | the claim, **TYPED**: `option (excl (bv 16))` (`ctyUR`) | `iclaim z ty` | minted by `ireg_claim_au` at ialloc's type-write, at `ty = di_type dn'`; spent by `ireg_withdraw`'s ClaimK CONVERSION at the claimant's ilock-fill | **exclusive allocation carrying the claimed type** — the claim pin (3c) then pays `di_type d = ty` back at the fill, which is `create_fresh_ty`'s content. |
| `r` | outstanding PLAIN references — **ACTIVE** (item 7a) | `runit_plain z` (the renamed `iref_lic`; `runit_any := runit_plain`) | minted at iget by licence flavour, spent at iput's last close | the reference-provenance unit: every non-allocator reference carries one, and the pin `c ≠ None ⟹ r = 0` is how fifteen ilock sites DERIVE `c = None` at their fill. |
| `rc` | outstanding CLAIM-flavoured references | `runit_claim z` | ialloc's own ClaimL iget mints it; the withdraw's conversion spends it (`rc→rc−1`, `r→r+1`) | keeps the allocator's reference counted without breaking the `r = 0` pin; `runit (b:bool) z` is the flavour-indexed form (`is_claim l`). |
| `p` | parent register (`option (dfrac_agree Z)`) | rides `ilinkdp`/`iparent` | mkdir / rmdir | fractional agreement on who the parent is. |
| `f` | the freeze phase: `frz := FrzOff \| FrzPre (rg:bool) \| FrzPost (rg:bool)` (`option (excl frz)`) | `ifreeze_off z`, `ifreeze_pre rg z`, `ifreeze_post rg z` | boot mints `FrzOff`; `ireg_freeze_au` steps Off→Pre; the +0x8a last close steps Pre→Post; the deposit retires Post→Off | **exclusive free-in-flight, carrying the REGIME INDEX `rg`** — which arm of `ireg_open ∨ ireg_boot` the freezer lent (RULING G′), so the deposit can return exactly it.  `ifreeze_off` rides the payload at rest (pool bundle / escrow tail / ilock holder's hand); the Pre/Post fragment stays in the FREER's hand from mint to deposit — it is what decides the escrow-tail disjunct at +0x70/+0x8a. |

The count coupling `icnt_half z n` and the pin `ireg_ref_ok r rc n c d`
(`r + rc ≤ n`; `type = 0 ⟹ r = rc = 0`; `c ≠ None ⟹ r = 0`) ride in
`ireg_rcol` beside the authority, with `rc` existentially bound so no
destructure site ever names it.

### 3c. The pure/shelter clauses on `ireg_slot` (`InodeRegion.v:2135`)

- `ireg_link_ok` / `ireg_root_ok` / `ireg_dir_ok` / `ireg_dir_wl0` /
  `ireg_par_ok` — the dirent-payment clauses (unchanged; L4 bound included).
- `(⌜c = None⌝ ∨ ireg_open)` — the §7.12 **boot shelter**: a claimed slot
  exhibits the sealed regime; the exclusive `ireg_boot` holder (ireclaim)
  refutes it, proving every slot boot reaches is unclaimed.
- `icnt_half z n` — the region's count half (3d).
- `ireg_claim_ok c f d` — the **claim pin**, typed: `c = Some x ⟹
  fresh_shape d ∧ f = FrzOff ∧ x = Excl (di_type d)`.  Cashed at the
  ClaimK fill: the type you read IS the type you claimed.
- `ireg_frz_ok f n d` — the **freeze pin**, rg-blind: `FrzPre _ ⟹
  nlink = 0 ∧ type ≠ 0 ∧ n = 1`; `FrzPost _ ⟹ same ∧ n = 0`.  B1's
  `cnt2 = 1` payout.
- `ireg_fsh f` — the **regime shelter** (G′): `True` at `FrzOff`,
  `ireg_regime rg` (= `if rg then ireg_open else ireg_boot`) parked at both
  window phases — the mint parks the lent arm, the deposit extracts and
  RETURNS it (agreement with the freer's own phase fragment selects it).
  This is ireclaim's boot round-trip made ghost-complete.
- `ireg_frzc z f` — the **receipt + mirror** conjunct: `(⌜f is FrzPre⌝ ∨
  frzown z)` — the receipt `frzown` is region-parked at every phase except
  `FrzPre`, so "receipt in a thread's hand" ⟺ "this column reads FrzPre"
  by `frzown_excl` alone — plus the inum-keyed mirror half `∃ b, frzm_h z b
  ∗ ⌜ireg_frzm_ok b f⌝` (`frzmUR`, ½-½ bool agreement at `icfg_frzm`),
  whose lock-side half rides `frz_park` (5a).

### 3d. The count coupling (`icnt`)

`icnt_half z n` — ½-½ `dfrac_agree` on a `nat` per inum (`gmap` under the
ambient `icfg_icnt`, NO auth).  Region half in `ireg_slot`; the other half
rides lock-side (`islot2`'s cached arm at the live count, the pool bundle at
0).  Agreement forces **every count move to open `↑iregN`** — structurally
possible at every site because the store rule's mask leaves `iregN` free
(the ZZProbeIcnt verdict).  The count-move AU family (`IcacheInv.v`) is
region-coupled end to end: `iref_dup/incr/upgrade_store_au` (borrowed-iname
licences; `iname_not_frozen` + the fused mint table `iname_mint_ok` supply
the freeze/claim refutations and mint the provenance unit), `iref_close_store_au` (no token), the phase-generic
`iref_close_last_store_au` and its freeze instance
`iref_close_last_freeze_store_au` (the FrzPre→FrzPost step, receipt home,
selector reclaim), and `iref_alloc_store_au` (the recycle's 0→1).

### 3e. The arm structure (option A) and the registry

`ireg_slot`'s arm: **((IN `z ↪[γi] d` ∨ MARKED `⌜ireg_marked_ok c d⌝ ∗
imark`) ∗ reg_full) ∨ PENDING** (`type = 0 ∗ z ↪[γi] d ∗ reg_half ∗
region_pending z`).  `reg_full/reg_half z ge gr` are fractions of the
per-inum **escrow registry** `icfg_reg`; `ireg_claim_au` refutes PENDING by
fraction overflow, and the off-lock deposit splits `reg_full` into the
pending pair.  `ireg_withdraw` is the IN→MARKED mover, indexed by `ilkc`
(6): its ClaimK arm is the CONVERSION (`iclaim z ty ∗ runit_claim z` in,
`runit_plain z` + `⌜di_type = ty⌝` out), its PlainK arm borrows a plain
unit and DERIVES `c = None` by the `ireg_ref_ok` collision
(`ireg_wd_lic/back/ty`, `InodeRegion.v:3639`).

## 4. The option-A escrow (the pending-free pipe)

| piece | type / home | meaning |
|---|---|---|
| `escA_inv ge gr gd γi z rg` | tiny invariant per in-flight free (`EscrowInode.v:71`), **rg-indexed** (G′) | the bridge carrying "the disk free COMMITTED" from the off-lock tail to the next allocator/recycler.  Three gnames now: `ge` (state), `gr` (redeem ticket), `gd` (the **deposit ticket**, item 7c — lets the deposit rule out the FILLED/REDEEMED arms). |
| its arms | `EMPTY ∗ ifreeze_post rg z` → `FILLED ∗ imark ∗ ifreeze_off ∗ ticket gd` → `REDEEMED ∗ ticket gr ∗ ticket gd` | the standing `ifreeze_post` lives HERE between iput+0x8a and the deposit; its agreement with the region's f-column is what tells the deposit which regime arm to hand back. |
| `committedA ge` | persistent `mono_nat_lb` at `ST_FILLED` | "the type-0 write is in the log" — minted by `ireg_free_deposit_au`, read by the redeem. |
| `redeem_ticketA gr` | `Excl ()` | the one-shot right to redeem the escrow back into a normal free-pool entry; parked pool-side (`pool_await`). |
| `region_pending z` / `pool_pending γi z` | the two halves' packagings | region-side and pool-side views of one in-flight free, correlated by the `reg_half` pair. |

Lifecycle: the freezer mints the escrow at +0x86 and parks `pool_await =
∃ ge gr gd rg, escA_inv ∗ ticket gr` at the eviction (keeping `dinode_at`
in hand — B2's fix) → `ireg_free_deposit_au` writes type 0, fills the
escrow, retires the freeze `FrzPost rg → FrzOff`, and **returns
`ireg_regime rg`** (the G round-trip) → the next iget/ilock of that inum
redeems (escrow→`imark`, pool arm→normal, `reg_join`→`reg_full`).

## 5. The icache (lock-held state + per-entry escrows)

### 5a. Under `itable.lock` — `itable_res2` (`IcacheEscrow.v`)

| piece | meaning |
|---|---|
| `itable_half M` | ½ of the authoritative slot map `M : slot k ↦ (q_out, count)` — the other half lives in the itable spinlock's invariant. |
| `ci : k ↦ (dev, inum)` | the pure identity map; `ic_ci_wf` ties `dom ci = dom M`; the pool's domain is its complement. |
| `islot2 cn M ci k` | per-slot arm: EMPTY (`islot_empty`) or LIVE = `islot_rest_at k q dev inum ∗ iref_slots count ∗ ic_id ½ ∗ icnt_half inum count ∗ frz_park k inum`. |
| `frz_park k z` (`IcacheInv.v`) | the lock-side halves of the freeze bookkeeping: OFF = `frzm_h z false ∗ frzsel k ½ false`; ON = `frzm_h z true ∗ frzsel k ¼ true` (the ON quarter is what the +0x82 reclaim brings home).  It carries NO MASS — R-e moved that into `live_slot`'s frozen alternative — so it is indexed by the slot and the inum alone and every count mover re-parks it unchanged. |
| `live_slot M k := live_norm ∨ live_frzn` (`IcacheInv.v:434`, RULING R-e) | the invariant-side live-mass account, per slot, inside `itable_inv`'s `live_pool`: NORM holds the table's complement slice at `frzsel ½ false`; **FRZN holds the WHOLE live unit** (`live_frac k 1`) at `frzsel ½ true` — so ANY reader with a positive `live_frac` share kills the frozen alternative (`frz_slot_kill`) with no lock, no licence, no region open.  This is the index-independent decider ProofIlock and ProofIdup use. |
| `frzsel k q b` (`IcacheRef.v:2466`) | the per-slot freeze SELECTOR — a `dfrac_agree bool` filed at the RESERVED key `NINODE + k` **inside the existing liveness ghost** (`icfg_live`; no new `inG`, no boot premise). |
| `isl_pool M` / `iref_slots_auth` / `iref_slot` | as before: the slots' share authorities (lock-held) and the fungible reference-slot budget a caller brings to iget. |
| `ipool …` | the free pool: one **bundle** per uncached inum = `icnt_half z 0 ∗ ifreeze_off z ∗` shape, shape = `ipool_shape_np` (alloc-arm with `dinode_at`, or `imark`-arm) ∨ `pool_pending` ∨ `pool_await`. |

### 5b. Per-entry escrows — `ic_escrows` (persistent family, `icEscN`)

| piece | meaning |
|---|---|
| `ic_escrow cn γfs γi cov ls k` | slot k's escrow invariant; arms = EMPTY / PARKED / HELD / MID / OUT. |
| `ic_payload_arm = ic_payload_np ∗ ic_frz_park inum` (`:978/:938`) | the parked payload with its **freeze-token slot**: `ic_frz_park z = ifreeze_off z ∨ frzown z` — either the resting token (no free in flight) or the RECEIPT (a freezer is mid-window; the freer's own phase fragment decides which, `ic_payload_arm_decide_frz`).  `ic_payload` (`:884`) is the checked-out form. |
| `ic_out_frz k d dev inum` (`:1324`) | the OUT arm's frozen alternative (the +0x5e window exit): named count fragment + identity fraction + `frzown` — carried by the `DepFrz` constructor of `ic_dep`. |
| the close family | `ic_close_to_empty` (+`_late`: the eviction-before-store wand form; `_frz`: the freezer's REF-1 eviction; `_await`: the eviction into `pool_await`) — `IcacheEscrow.v:2299–2440`. |
| `ic_id cn k q b dev inum` | fractional identity ghost for the slot's `(dev,inum)` cells; the escrow keeps half forever (§13.1e). |
| `live_gen k s g` / `live_frac k s` / `iref_frag k q` | fractions of the slot's live/generation cell and reference mass; `live_whole_share_absurd` and `frz_slot_kill` are the overflow lemmas. |

### 5c. The ambient gname family (`icfg`, `IcacheRef.v:848–863`)

`icfg_iref` (reference mass), `icfg_live` (live/generation cells + the
reserved-key freeze selectors), `icfg_link` (THE link ledger, §3b),
`icfg_iep : Z → gname` (record epochs), `icfg_isl : nat → gname` (per-slot
sleeplock names), `icfg_boot` (the boot one-shot), `icfg_reg` (escrow
registry), `icfg_icnt` (the count coupling), `icfg_frzo` (the freeze
receipt), `icfg_frzm` (the freeze mirror).  One `MkIcfg` record threaded
everywhere as a typeclass.

## 6. Client-side currencies (what proofs hold in their hands)

| piece | meaning |
|---|---|
| `inode_ref k q dev inum` | ONE counted reference to slot k at that identity — the raw currency.  `inode_shr`/`inode_shr_gen` are shares; `inode_ref_short` is a reference with a share carved out of it.  A bare `inode_ref` no longer appears on ANY fs contract: since SIMP-2 every contract speaks a PACKAGE (next four rows). |
| **`inode_refb b k q dev inum`** — the flavoured package (SIMP-2, `IcacheRef.v`) | `inode_ref ∗ runit b (bv_unsigned inum)`.  **`SpecIget`'s whole post**: the reference and the unit iget mints for it, at the flavour the licence chose (`inode_refb (is_claim l)`).  Intro `inode_refb_intro` = `iFrame` — the pack adds no content, which is the satisfiability witness (probe `ZZSimp2` P1). |
| **`inode_refp k q dev inum`** — the plain package | `inode_ref ∗ runit_any (bv_unsigned inum)`, and `inode_refb false` on the nose (`inode_refb_false_refp`, by `reflexivity`).  **`SpecIput`'s whole pre**, and the body of `inode_held`.  There is no spend form for `inode_refb true`: under RULING C′ ilock's ClaimK arm (`ireg_withdraw`) CONVERTS the claim flavour, so the only package that ever reaches an iput is the plain one. |
| **`inode_refp_short k qt qi dev inum`** — the short-parent package | `inode_ref_short ∗ runit_any`.  **Both `wp_iunlockput_*` pres**: what a caller holds across "iunlock; iput" is not a whole reference but the parent of the carve it made for ilock, and the unit rides with the parent (item 7a-wire — a share pays for no count move).  `inode_refp_carve`/`inode_refp_gather` are the package-level ⊣⊢ of `inode_ref_carve`/`inode_ref_gather`; `inode_held_short` is restated over it. |
| **`inode_claimed ty k q dev inum`** — the claim package | `inode_ref ∗ runit_claim ∗ iclaim`.  **`SpecIalloc`'s whole receipt** (3 rows → 1).  Its elim is `InodeRegion.inode_claimed_to_ClaimK`: what sits beside the surviving reference IS `ireg_wd_lic (ClaimK ty)`, i.e. exactly the licence create's fill hands `wp_ilock_sconf` — so the receipt travels bundled and arrives in the shape ilock asks for, in one destruct. |
| `inode_held` / `inode_held_ty` / `inode_held_short` — the POINTER-keyed packages (`IcacheRef.v`) | what `FileInvDefs.inode_pay`'s cinv holds per fd and what `p->cwd` owns (`ProcInv.v:59`).  `inode_held v` is `∃ k q inum, ⌜pure⌝ ∗ inode_refp k q icfg_dev inum` — one unfold shorter since SIMP-2, and unchanged at all ~74 landed positional sites because `inode_refp`'s single delta step is the pair that used to be spelled there.  **`SpecIdup` is now stated over it**: one package in, two out (see the contract-facts row). |
| `runit b z` — the reference-provenance unit (item 7a) | minted by iget FLAVOURED by the licence presented (`is_claim l`: ialloc's ClaimL iget mints `runit_claim` into its own claim box, every other iget mints `runit_plain`), copied by idup, surrendered at the iput that closes the reference.  `runit_any := runit_plain`.  The mint's side conditions are the five-row table `iname_mint_ok` (`IgetLic.v:725`). |
| `iname γi γfs inodestart inum l` — the iget **licence** (`IgetLic.v`) | `l : ilic`, five constructors: `LinkedL fl` (a paid dirent unit), `HeldL d` (caller holds `dinode_at`, type≠0 ∧ nlink≠0), `ClaimL ty` (the typed `iclaim`), `BufL bno ds` (the inode block's `fsblock` half at type≠0 bytes ∗ `⌜bno = IBLOCK inum inodestart⌝` ∗ `ireg_boot` — boot-only), `RootL`.  The BufL **block tie is a conjunct of the arm**, which is why the licence is indexed by the region's start: `SpecIget` states no block equation of its own, so no non-BufL caller pays a `discriminate` for it and the one presenter (`ProofIreclaim`'s boot scan) discharges it where it builds the licence.  `SpecIget` posts the flavoured `runit` beside the reference. |
| `ilkc` — SpecIlock's fill index (`InodeRegion.v:441`) | `ClaimK ty` (create's child fill: spends the typed claim + `runit_claim`, receives `runit_plain` + `⌜filled ∧ di_type = ty⌝` — the `create_fresh_ty` payout) \| `PlainK` (the twelve dirent/kernel sites: borrow `runit_plain`, the pin derives `c = None`) \| `ShotK ty` (the three fd sites: the persistent generation one-shot `ity_shot g ty` they already hold kills the uncached arm — `⌜filled = false⌝`). |
| `ifreeze_off z` | §3b's f-column at rest — surfaces through `SpecIlock`'s post and returns at `iunlock`/`iunlockput`; how create/sys_link prove a fresh box is not mid-free (`ireg_link_pin`). |
| `ireg_regime rg` (= `if rg then ireg_open else ireg_boot`) | the borrowed regime witness, now on **`wp_iput_gen` alone** (G/G′).  ireclaim — the tree's only `rg := false` caller, and the only caller of any iput contract that is not a runtime thread — lends its exclusive `ireg_boot` and gets IT back from the post.  Every RUNTIME contract is specialized: `wp_iput_sconf` and both `wp_iunlockput_*` take the persistent `ireg_open` as an ordinary premise and return nothing, because a persistent lend/return round-trip carries no information.  `ireg_regime` still indexes the LEDGER (the f column's phases, `ireg_fsh`, the escrow) — only the contract surface lost it. |
| contract facts | `SpecIdup` carries `!logG` + `ireg_inv` (the region handle its count move needs — `ireg_inv`'s type really does mention `logG`, via the epoch coupling).  Since SIMP-2 it is stated over `inode_held`: **`inode_held (ientry k)` in, `inode_held ∗ inode_held` out** (6 rows → 3), because both of its callers (`ProofKforkB4`'s parent cwd, `ProofNamex`'s cwd) HOLD `inode_held` already — the shed/gather they used to bracket the call with moved INSIDE the contract, and their sites got shorter.  The `s`/`inum` binders went with it; a pure `dev = icfg_dev` tie rides in their place (the `sysc_fs_env` pattern), because `inode_held` is pointer-keyed at the cache's own device.  `K_iput = 74`, `K_iunlockput = 78`. |

## 7. Boot phase, the seal, and `fs_ready`

`ireg_boot := ity_pending icfg_boot` (exclusive) vs `ireg_open := ∃ ty,
ity_shot icfg_boot ty` (persistent) — a one-shot (`ity_shoot`).
Boot/ireclaim runs holding `ireg_boot`, which refutes every claim it meets
(the c-shelter), backs its `BufL` scan-igets, and — as `ireg_regime false`
— is LENT into each of its boot freezes and returned by the deposit (the
G′ round-trip; `ireg_fsh` parks it, the phase payload remembers it).  That
round-trip is why `wp_iput_gen` keeps the `rg` index at all: ireclaim is its
one consumer, and the runtime contracts, whose regime is the persistent
`ireg_open`, dropped the index.

### 7a. The seal, as a lemma (SIMP-2, `FsReady.v`)

The **seal** converts the exclusive boot token into the persistent regime,
once, after `fsinit` returns.  Since SIMP-2 it is a named, machine-checked
step rather than a sentence:

| piece | statement | why |
|---|---|---|
| `FsReady.fs_ready_seal` | `ireg_boot ==∗ ireg_open` | one `ity_shoot`, no invariant, no mask.  **The boot-freedom witness**: `ireg_boot` is exclusive, so after this step no second seal is possible and nothing boot-shaped survives — `ireg_open` is an existential over the one-shot's value and mentions nothing else. |
| `FsReady.fs_ready_pre` | the TWENTY non-regime conjuncts (two of them pure — `printk_gen_contract`, `fs_geom_ok`), as one persistent assertion | what a seal SITE must hold.  Every one of them is either persistent boot material the chain already carries or a bundle `SpecFsinit`'s post hands back, so the site can be checked constituent by constituent — the checked ledger is fs-cfg-boot.md's stage-(f) charter, table (f-3). |
| `FsReady.fs_ready_establish` | `fs_ready_pre -∗ ireg_boot ==∗ fs_ready` | **the producer `fs_world` never had.**  Booting is over the instant the predicate exists. |

### 7b. `fs_ready` — the runtime file system as ONE persistent assertion

`FsReady.fs_ready` is **PARAMETER-FREE**: 21 conjuncts (the two text/data
certificates, the printk credential pair, the block/log/crash fabric,
`gen_cert`, the disk fabric and its lock as ONE existentially-quantified
conjunct — the three virtio ring pages left `fscfg` in fs-cfg-boot.md's R1,
recovered by `disk_geom_agree` — the icache's four, `ireg_inv` +
`ireg_open`, the kmem lock and `kalloc_avail … None` SPELLED rather than as
`kalloc_env` (SpecFileclose's pipe arm names the pair, and a hidden `∃`
admits no tie), `⌜fs_geom_ok⌝` — the nineteen pure premises every fs
syscall used to state, as one record — and the four discarded superblock
cells `fs_sb_cells`, and the block bitmap's invariant `bitmap_inv` —
§1b) and not one argument.  Every ghost name it used to
take is ambient — the four the inode cache already owned (`icfg_log`,
`icfg_ist`, `icfg_nib`, `icfg_dev`) and the SIXTEEN `FsCfg.fscfg` adds
(nineteen before R1).

**WHY PARAMETER-FREE, and it is not cosmetic.**  `fs_ready` is meant to be
CARRIED — produced by forkret's not-forked arm, held by a running process,
handed to the trap loop, read back by every later syscall.  A
twenty-parameter version can be carried only by existentially quantifying
the twenty, and a bare existential is useless downstream: a consumer handed
`∃ γ…, fs_ready γ…` cannot feed it to `SpecKexec.fs_fabric` or to
`UsertrapRes.ut_res_bare`, whose own resources are keyed to the *caller's*
concrete names, because nothing relates the two.  Ambient names remove the
existential instead of hiding it.  The argument is `IcacheRef.icfg`'s,
verbatim, one layer out: there is exactly one file system per boot.
`FsCfg.fscfg` is per-era for the same reason `icfg` is (the disk image
ghost is re-minted at PowerOn — `design/crash.md`), i.e. a Class ASSUMPTION
each era's boot instantiates, not a global constant.

**`procs_inv` IS NO LONGER A CONJUNCT.**  It is persistent, every consumer
holds it beside the fs environment anyway (`SpecKexec.fs_fabric` lists it
separately), and it was the one conjunct that reached back into the process
layer — which is what made `fs_ready` *look* as though the file system
depended on process abstractions.  A spec that wants it takes `procs_inv γs`
as its own premise; the two friendly bodies in `FsSyscalls.v` do.

`fs_world` is no longer a one-line alias: it is the predicate AT A CALLER'S
OWN NAMES — the tie equations (`bn = fsc_bio`, `glog = icfg_log`, …) beside
the ambient `fs_ready`, with one R1 exception: the three ring-page ties are
now carried as `disk_geom` + the virtio `is_lock` at the caller's own
`pd pav pu` as RESOURCES where the three `⌜⌝` equations used to be
(interderivable with the predicate's existential via `disk_geom_agree`).
`fs_world_all` does the substitution once so that a body which threads its
own names still destructs ONE row and gets the constituents spelled the way
its callee spells them.  This is `SpecKexec`'s existing `g = icfg_log`
idiom at full width.  Three things changed around the assertion:

1. **Its own file**, below the syscall layer, so any file can import the
   predicate without importing the syscall bodies that used to own it —
   and, since the `ic_sleeplocks` move, below the whole Spec layer as well.
   That move is DONE and it is worth reading as a case study; see §7e.
2. **A producer** — §7a.  `fs_world`'s own header called it an assertion "a
   friendly client pays for once, at boot", satisfiability unchecked
   (upstream's `syscall_env` is in the same position); it is a lemma now.
3. **A projection family** — `fs_ready_text`/`_data`/`_printk`/`_panic`/
   `_bio`/`_log`/`_seam`/`_gen`/`_disk`/`_icache`/`_region`/`_kalloc`,
   plus `fs_ready_all`.  Each is one `iDestruct`.  `_panic` is the
   standing weakening `printk_env -∗ panic_env`; `_region` is the pair the
   whole half exists for (`ireg_inv` beside the SEALED `ireg_open`, with no
   arm to case on and no boot token to thread).

**NOT ONE CONJUNCT IS BOOT STATE, and the type enforces it.**  `fsinit` and
`ireclaim` run PRE-seal and hold `ireg_inv` WITHOUT `ireg_open`; the
predicate they cannot form is exactly the predicate whose existence says
they are done.  So they keep their constituent forms, and that is the
design rather than an omission.

**THE SECTION IS LOAD-BEARING** (the class-used-as-INDEX trap,
durable-notes).  `FsSyscalls`'s section names `fileG` but not `icfg`/
`icacheG`, and `fileG` carries both as superclass FIELDS
(`FileInvDefs.file_icfg`, `file_icacheG`) — so every icache-flavoured
conjunct of `fs_world` is elaborated at the BAKED projections, and a foreign
section with its own `ICFG : icfg` cannot frame them.  `FsReady.v` declares
`icacheG` and `icfg` EXPLICITLY and declares them LAST, so resolution
prefers them: `fs_ready` is parametric in the cache's index, every
projection is at that same parameter, and the alias in `FsSyscalls`
instantiates it with `file_icfg`/`file_icacheG`, recovering today's
`fs_world` on the nose.

### 7c. The forkret delta (why any of this)

`LinkForkretNF.v`'s header states the problem: forkret's not-forked arm
calls `fsinit` and `kexec`, and forkret holds the fs environment "only
INSIDE the residue closer … If the arm's proof needs those resources up
front, this contract grows a premise."  Growing it by the CONSTITUENTS is
fifteen-plus rows with the boot/regime story unresolved at that altitude.
Growing it by `fs_ready` is **ONE row, and a persistent one**
(`fs_ready_persistent`); everything the arm's continuation can want comes
back by the projection family, and `fs_ready_all` is that claim as a lemma.
The fs-side obligation of forkret's first branch is therefore: *the boot
chain sealed (`fs_ready` exists), forkret carries it.*

### 7d. The adoption audit (what may take `fs_ready`, and what may not)

SIMP-2's third step was "collapse each fs-internal Spec's ambient pile to
one `fs_ready` premise".  Run against the sources, the audit says: **almost
nothing may**, and each refusal is a design fact rather than an accident.
Recorded here so the question is not re-opened blind.

| Spec | verdict | why |
|---|---|---|
| `SpecIget`, `SpecIlock`, `SpecIunlock` | **MUST NOT** | reachable PRE-SEAL.  `ProofFsinit` calls `ireclaim`; `ProofIreclaim` calls `iget`/`ilock`/`iunlock`.  A boot caller holds `ireg_inv` WITHOUT `ireg_open`, so it cannot form `fs_ready` — which is §7b's boot-freedom, enforced by the type. |
| `SpecIput`, `SpecDirlookup` | **UNBLOCKED**, not yet done | the cycle (`FsReady` → `SpecDirlink` → `SpecIput`/`SpecDirlookup`) is gone with the `ic_sleeplocks` move (§7e).  Whether they SHOULD adopt is now the same weighing as the row below — iput uses ~7 of the eighteen. |
| `SpecIdup`, `SpecIunlockput`, `SpecIalloc`, `SpecNamex`, `SpecCreate` | **SHOULD NOT** | no cycle and no boot caller, but adoption is a contract-content GAIN, not a collapse: `fs_ready` carries `kalloc_env`, `procs_inv`, `gen_cert`, `fs_crash_seam` and `ic_sleeplocks`, and none of these five needs all of them.  Trading 7 rows the callee uses for 19 rows every caller must supply is the "any Spec gaining a row" tripwire in substance. |
| the syscall layer | **ALREADY DONE** | `ProofSyscall.sysc_fs_env` is bundle-fed and mentions `fs_world` by field ties; nothing to collapse. |
| `SpecFsinit`, `SpecIreclaim` | **MUST NOT**, by design | they run pre-seal and keep constituent forms. |

So the second half's deliverable is the PREDICATE, its PRODUCER and its
PROJECTIONS — the things that make the forkret row one row — and not a
sweep.  The one adoption that would pay (`SpecIput`'s ~7 ambient rows) is
gated on the `ic_sleeplocks` move, and even then it must be weighed against
the four constituents iput does not use.

**The seal's SITE is still the tree's one standing IOU — and it is now
CHARTERED.**  `LinkFsinit`'s `Fsinit` module has no consumer — nothing in
the tree applies `wp_fsinit_sconf` — because in xv6 `fsinit()` is called
from forkret's `if (first)` arm, and that arm is
`LinkForkretNF.wp_forkret_nf_ax`.  SIMP-2 made the seal STATABLE and
CHECKED (`fs_ready_establish` is `Qed`); fs-cfg-boot.md's **stage-(f)
charter** ("transport and seal") is the funded plan for the site: the
exclusive pile rides `FirstTok.first_tok`'s widened left disjunct
(`first_boot_persist` / `kalloc_avail fsc_kpages None` / `first_fsinit`),
deposited through userinit's park; the charter's table (f-3) shows every
`fs_ready_pre` conjunct sourced from that payload, fsinit's own post, or
the ambient world — `main_deposit` is NOT the channel (its old C7 (iii)
role is superseded).  What remains at the site is the humans' forkret walk
and the park seam (charter decision points D1/D2, residuals R1–R4).  No
new axiom either way.

### 7e. `ic_sleeplocks`, and how a misplaced definition faked a dependency

Worth reading even if you never touch the icache, because the *symptom* is
general and it was mis-diagnosed once.

`fs_ready`'s dependency cone contained `ProcInv` — the whole process layer —
which reads as "the file system depends on process abstractions".  It does
not.  There were exactly two edges, and only one was real:

* `FsReady.v`'s own `Require Import ProcInv` — **vestigial**.  Checked all
  132 names `ProcInv.v` and `ProcDefs.v` define against the text of
  `FsReady.v`: zero were used.
* `FsReady` → `SpecDirlink` (for `ic_sleeplocks`) → `SpecWritei` → `ProcInv`
  — real, and `SpecWritei → ProcInv` is legitimate: `writei` copies user
  memory, so it takes the process block.

So one five-line definition, sitting in a *function spec*, dragged the
process layer into the file system's cone.  `ic_sleeplocks` now lives in
`IcacheEscrow.v` beside `ic_tok`, which it is built from; nothing in it is
file- or directory-shaped, and every ingredient (`is_sleeplock_gen`,
`ic_tok`, `ientry`, `icfg_isl`) is in scope one layer down from any spec.
Measured: `FsReady`'s cone 161 → 154 files, and `ProcInv` is out of it.

Two things the earlier plan for this move did not know:

* it was defined **twice, byte-identically**, in `SpecDirlink.v` AND
  `SpecFileclose.v`, and its four-line accessor was copied out **seven**
  times (`ProofDirlink`, `LinkCreateFreshTy`, `ProofKexecTail`,
  `ProofCreate`, `ProofSysLink`, `ProofSysUnlink`, `ProofNamex`).
  `IcacheBoot.v` had already flagged the duplication as debt.
* the plan said "leave the two existing names as aliases".  That does not
  work: five sites do `rewrite /SpecDirlink.ic_sleeplocks` and then
  `big_sepL_lookup`, i.e. they need the BODY one unfold away, and a
  transparent alias leaves them one unfold short.  Both copies are retired
  and the ten qualified spellings requalified instead —
  `IcacheEscrow.ic_sleeplocks_lookup` is the one accessor.

**The general rule:** a spec file must not own a definition the invariant
layer needs, and the way you find out that it does is that some predicate's
dependency cone contains a layer it has no business containing.  Read the
cone, not the prose.

## 8. The tree layer (fs-friendly fragments)

| piece | meaning |
|---|---|
| `node_of` / `node_rep n dn data` (`FsTree.v`) | the pure abstraction of one inode: `fsnode` = NDir with its `ents : gmap fname Z` or NFile with its bytes. |
| `fnode γi γfs i n` (`FsRep.v:114`) | node `i` currently IS `n` — holdable only while `i` is locked; the tree-facing view of the payload. |
| `fedges` / `fmap_rep` / `fs_rep t` / `fslice` | the whole-tree representation and its path-slices — the AMBIENT tree a client opens for global facts. |
| `dir_links self dn data` (`DirLinks.v`) | the per-directory link accounting bridging records to the ledger's dirent columns. |
| `FsLookup.wp_dirlookup_tree` | the F2 **logically-atomic** lookup triple: pre/post name the SAME `ents` (the linearization interval is the caller's lock hold), and it claims nothing about any other node. |

## 9. How it composes: the two transition windows

The whole design is two mirrored exclusivity windows over the same ledger.

**ialloc's claim window** (type-write → ilock-fill): `ireg_claim_au` mints
the TYPED `iclaim z ty` under `ireg_open`; the claim pin freezes the
record's identity at the claimed type; the window is unenterable by others
because byte-movers need the parked `dinode_at` (`ireg_claim_no_out` makes
this a theorem: the record IS inside the region), reference-minting needs a
licence — every row refuted at a claim box — and the provenance pin
`c ≠ None ⟹ r = 0` means any plain-unit holder is proof the box is
unclaimed.  The claimant's own iget mints `runit_claim` (the rc column
keeps it countable without denting the pin); its ilock presents `ClaimK ty`
and the withdraw CONVERTS — claim + claim-unit in, plain unit +
`⌜di_type = ty⌝` out.  That equation is `create_fresh_ty`, now the Lemma
at `LinkCreateFreshTy.v:443`.

**iput's freeze window** (ref==1 commit → off-lock deposit):
`ireg_freeze_au` spends the payload's `ifreeze_off` into `FrzPre rg`,
parking the lent regime arm (`ireg_fsh`), the receipt story (`ireg_frzc`)
and the R-e mass: `live_slot` flips to its FRZN alternative holding the
WHOLE live unit, so any foreign reader's positive share is an instant
kill (`frz_slot_kill`) — uniform across ClaimK/PlainK/ShotK, no lock, no
licence.  The freeze pin says the count is exactly 1 and nlink is 0, so
the +0x8a re-read gives `cnt2 = 1` outright (B1); the last close steps
`FrzPre→FrzPost` (receipt home, selector quarter reclaimed), the eviction
parks `pool_await` while the freer keeps `dinode_at` in hand (B2); the
deposit writes type 0, fills the rg-indexed escrow, retires the phase to
`FrzOff`, and hands back `ireg_regime rg` — closing the window and re-arming
the inum for its next life.  That hand-back reaches a CALLER only through
`wp_iput_gen`, where ireclaim's exclusive `ireg_boot` round-trips; on the
runtime contracts it is absorbed inside iput, since a persistent `ireg_open`
the caller never gave up cannot be given back.

The two windows are duals: the claim protects a box being BORN from a
foreign free; the freeze protects a box DYING from a foreign rebirth.  Both
are resource-level facts of the one per-inum ledger — which is why neither
needs a closed-world or trace-level argument, and why the campaign ends
with the three syscall tops on the platform axioms alone.
