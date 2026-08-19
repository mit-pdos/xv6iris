# The file system's abstract/ghost state — a reference inventory

STATUS: verified against `main` @ `bc96776a` (2026-08-19, the pushed tree of
the iclaim-ledger campaign's FINAL GATE).  The campaign is COMPLETE: the
reordered `iput` (kernel pin 4398009) is proven end-to-end, and
`create_fresh_ty` is a THEOREM (`LinkCreateFreshTy.v:443`;
`SpecCreateFreshTy.v` is deleted).  Nothing here is in flight; the three
syscall tops rest on the five Sail platform axioms + funext alone.

Layout: one section per layer, bottom-up.  For each piece: the RA/type, its
HOME (which invariant or lock-held bundle owns the authority), what a
fragment in a client's hand MEANS, who mints/spends it, and why it exists.

---

## 1. Disk and buffer layer

| piece | type / home | meaning |
|---|---|---|
| `fsblock γfs bno bs` | ½ of `bno ↪[fs_L] bs` (`ghost_map`, `FsBlocks.v:70`) | the client half of block `bno`'s **logged content**.  The log invariant holds the other half; holding this half means no `ireg_write_au`/`ireg_claim_au`/`ireg_free_au` at any inum of that block can fire — it is §16.2's serializer as a resource.  Minted at `bread`, returned at `brelse`. |
| `fs_dirty` | second `ghost_map` in `fs_names` | per-block pinned/dirty flag tying the buffer cache to the log's write set (`LogInv.v:718`). |
| `fs_own` | third `ghost_map` (`Excl`-style per-block token) | the exclusive per-block ownership token behind the buffer sleep-lock discipline. |
| `bio_ctx` / `fs_view` | the buffer-cache invariant | owns the physical buffer array and the `fs_L`/`fs_dirty` authorities; `fs_view γfs γd dev cov` is the fs-side lens on it. |

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
| `islot2 cn M ci k` | per-slot arm: EMPTY (`islot_empty`) or LIVE = `islot_rest_at k q dev inum ∗ iref_slots count ∗ ic_id ½ ∗ icnt_half inum count ∗ frz_park k inum q`. |
| `frz_park k z q` (`IcacheInv.v:1807`) | the lock-side halves of the freeze bookkeeping: OFF = `frzm_h z false ∗ frzsel k ½ false`; ON = `frzm_h z true ∗ frzsel k ¼ true` (the ON quarter is what the +0x82 reclaim brings home).  `q` is vestigial. |
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
| `inode_ref k q dev inum` | ONE counted reference to slot k at that identity — what iget returns and iput spends.  `inode_shr`/`inode_shr_gen` are shares; the `inode_held`/`inode_held_ty`/`inode_held_short` PACKAGES (`IcacheRef.v:2950–3022`: reference + its `runit` + the generation shot) are what `FileInvDefs.inode_pay`'s cinv holds per fd and what `p->cwd` owns (`ProcInv.v:59`) — no separate rest-home conjunct was ever needed. |
| `runit b z` — the reference-provenance unit (item 7a) | minted by iget FLAVOURED by the licence presented (`is_claim l`: ialloc's ClaimL iget mints `runit_claim` into its own claim box, every other iget mints `runit_plain`), copied by idup, surrendered at the iput that closes the reference.  `runit_any := runit_plain`.  The mint's side conditions are the five-row table `iname_mint_ok` (`IgetLic.v:725`). |
| `iname γi γfs inum l` — the iget **licence** (`IgetLic.v`) | `l : ilic`, five constructors: `LinkedL fl` (a paid dirent unit), `HeldL d` (caller holds `dinode_at`, type≠0 ∧ nlink≠0), `ClaimL ty` (the typed `iclaim`), `BufL bno ds` (the inode block's `fsblock` half at type≠0 bytes ∗ `ireg_boot` — boot-only), `RootL`.  `SpecIget` additionally takes the pure BufL block-equation (`l = BufL bno ds → bno = IBLOCK inum inodestart`) and posts the flavoured `runit` beside the reference. |
| `ilkc` — SpecIlock's fill index (`InodeRegion.v:441`) | `ClaimK ty` (create's child fill: spends the typed claim + `runit_claim`, receives `runit_plain` + `⌜filled ∧ di_type = ty⌝` — the `create_fresh_ty` payout) \| `PlainK` (the twelve dirent/kernel sites: borrow `runit_plain`, the pin derives `c = None`) \| `ShotK ty` (the three fd sites: the persistent generation one-shot `ity_shot g ty` they already hold kills the uncached arm — `⌜filled = false⌝`). |
| `ifreeze_off z` | §3b's f-column at rest — surfaces through `SpecIlock`'s post and returns at `iunlock`/`iunlockput`; how create/sys_link prove a fresh box is not mid-free (`ireg_link_pin`). |
| `ireg_regime rg` | the borrowed regime witness on `SpecIput`/`SpecIunlockput` (G/G′): runtime callers lend a copy of the persistent `ireg_open` (rg = true); ireclaim lends its exclusive `ireg_boot` (rg = false) and gets IT back from the post. |
| contract facts | `SpecIdup` carries `!logG` + `ireg_inv` (the region handle its count move needs — `ireg_inv`'s type really does mention `logG`, via the epoch coupling) + the `runit` copies; `K_iput = 74`, `K_iunlockput = 78`. |

## 7. Boot phase

`ireg_boot := ity_pending icfg_boot` (exclusive) vs `ireg_open := ∃ ty,
ity_shot icfg_boot ty` (persistent) — a one-shot (`ity_shoot`).
Boot/ireclaim runs holding `ireg_boot`, which refutes every claim it meets
(the c-shelter), backs its `BufL` scan-igets, and — as `ireg_regime false`
— is LENT into each of its boot freezes and returned by the deposit (the
G′ round-trip; `ireg_fsh` parks it, the phase payload remembers it).  The
**seal** fires once after `fsinit` returns, converting to the persistent
`ireg_open` that rides the syscall dispatch env (`sysc_fs_env`/`fs_world`)
down to `ireg_claim_au` and every runtime iput.  The seal's site terminates
at the tree's one standing IOU (`LinkForkretNF.wp_forkret_nf_ax`), shared
with upstream; no new axiom.

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
`FrzOff`, and hands back `ireg_regime rg` — ireclaim's `ireg_boot`
round-trips, a runtime caller's `ireg_open` copy is absorbed — closing
the window and re-arming the inum for its next life.

The two windows are duals: the claim protects a box being BORN from a
foreign free; the freeze protects a box DYING from a foreign rebirth.  Both
are resource-level facts of the one per-inum ledger — which is why neither
needs a closed-world or trace-level argument, and why the campaign ends
with the three syscall tops on the platform axioms alone.
