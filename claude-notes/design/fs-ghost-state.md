# The file system's abstract/ghost state — a reference inventory

STATUS: verified against lane commit `e74eb0f77d` (2026-08-18, post-IVa +
RULING A‴).  Two items still land after this pin: increment IVb adds the
**freeze mirror** (§4a below, marked "landing in IVb") and splices the walk;
item 7 deletes the `create_fresh_ty` axiom (a `Print Assumptions` change,
no ghost-state change).  Everything else here is landed and gated.

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
| `log_opS γ u Sb` | exclusive op token, CLOSED form (`LogInv.v:372`) | "I am inside an op with `u` units of write budget and write-set `Sb`."  `log_opSe` (`:350`) is the OPEN/epoch-indexed form the free path uses (`log_opSe γ (S u) Sb e0`); `log_opSw`/`log_opSwe` are the mid-write variants. |
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
| `z ↪[γi] d` / `dinode_at γi inum dn` | `ghost_map` fragment (`InodeRegion.v:1068`) | **custody of inum's record**: exclusive, and required by every byte-writing mover.  Parked in the region while the box is idle (the IN arm); checked out through the pool → entry-escrow → `ilock` chain; `dinode_at_excl` makes a second copy absurd.  This exclusivity is the create-window's first wall: no reference ⟹ no custody ⟹ no write. |
| `imark γi z` | marker fragment at `imark_key z` (`:1122`) | the MARKED state's stand-in for the record — the box's bytes are type≠0 but its record is checked out to a claimant/freer; `ireg_out`/`ireg_in` classify. |
| `ireg_ep z d` | per-inum `mono_nat` (`icfg_iep z`) | the record's **epoch**: bumps at every flush, giving readers "no older record can reappear". |

### 3b. The per-inum link ledger — `link_auth z wl wdu wdt g c r p f`

One 8-column authority per inum, inside `ireg_slot` (`IcacheRef.v` defines
the RA; filed as a `gmap` under the ambient gname `icfg_link`).  The columns
and their fragment currencies:

| col | counts | fragment | minted / spent | why |
|---|---|---|---|---|
| `wl` | paid dirent records (plain) | `ilink z` | dirlink / unlink | pays for a live directory record naming `z`; `ireg_link_ok`: `wl+wdu+wdt ≤ nlink` **and** `nlink ≤ 32767` (the L4 bound). |
| `wdu` | paid `".."`-units | `ilinkd z` | mkdir's dot-dot deposit | the d-flavour of the same payment; buys `ireg_dir_ok` (`0 < wd → type = T_DIR`). |
| `wdt` | THE parent-record unit (≤1, `ireg_par_ok`) | `ilinkdp z pv` + `iparent z pv` | mkdir / rmdir | tagged unit carrying half the **parent register** `p` (fractional agreement on the parent's inum) — the `".."`-tie. |
| `g` | grey records — orphaned `".."`s nothing pays for | `igrey z` | unlink's grave-dot-dot | carries NO allocatedness; that is the point (§20.8).  (The `GreyL` iget licence over it is DELETED.) |
| `c` | the claim (`option (excl unit)`) | `iclaim z` | minted by `ireg_claim_au` at ialloc's type-write; spent by `ireg_withdraw` at the claimant's ilock-fill | **exclusive allocation**: a second claim of the same inum is a ghost collision; while outstanding, the claim pin (3c) holds. |
| `r` | outstanding icache references (§20.7 M1) | `iref_lic z` | `link_mint_ref` / `link_spend_ref` | designed carrier "minted at iget, returned at iput's ref--"; **still unwired** (OPEN 2.2a) — the icnt coupling (3d) took its load-bearing job. |
| `p` | parent register (`option (dfrac_agree Z)`) | rides `ilinkdp`/`iparent` | mkdir / rmdir | fractional agreement on who the parent is; both halves compose to fraction 1 so the tagged spend's reset is frame-preserving. |
| `f` | the freeze phase (`option (excl frz)`, `frz := FrzOff \| FrzPre \| FrzPost`) | `ifreeze_off/pre/post z` | boot mints `FrzOff`; `ireg_freeze_au` steps Off→Pre; the +0x8a last close steps Pre→Post; the deposit retires Post→Off | **exclusive free-in-flight**: one token per inum, riding the payload (custody: pool bundle ↔ escrow PARKED arm ↔ ilock holder's hand); holding `ifreeze_off` proves no free is in flight and is the right to start one. |

### 3c. The pure clauses on `ireg_slot` (`InodeRegion.v:1472`)

- `ireg_link_ok d (wl+wdu+wdt)` — dirent payments ≤ `nlink`, and `nlink ≤ 32767` (L4).
- `ireg_root_ok z d w` — the root clause, (L1) strict at the root (`w < nlink`).
- `ireg_dir_ok d (wdu+wdt)` / `ireg_dir_wl0 d wl` — d-units force `T_DIR`.
- `ireg_par_ok wdt p` — the tagged unit and the parent register exist together.
- `(⌜c = None⌝ ∨ ireg_open)` — the §7.12 **boot shelter**: a claimed slot exhibits the sealed regime; the exclusive `ireg_boot` holder (ireclaim) refutes it, proving every slot boot reaches is unclaimed.
- `ireg_claim_ok c f d` — the **claim pin**: `c = Some` ⟹ the record is the claimed `fresh_shape` one and `f = FrzOff`.  This is what `create_fresh_ty` cashes at ilock.
- `ireg_frz_ok f n d` — the **freeze pin**: `FrzPre ⟹ nlink = 0 ∧ type ≠ 0 ∧ n = 1`; `FrzPost ⟹ same ∧ n = 0` (n = the icnt value, 3d).  This is B1's `cnt2 = 1` payout.
- `(⌜f = FrzOff⌝ ∨ ireg_open ∨ ireg_boot)` — the freeze's boot-shelter twin (ireclaim parks its `ireg_boot` here for its boot freezes).

### 3d. The count coupling (`icnt`)

`icnt_half z n` — ½-½ `dfrac_agree` on a `nat` per inum (`gmap` under the
ambient `icfg_icnt`, NO auth).  Region half in `ireg_slot`; the other half
rides lock-side (`islot2`'s cached arm at the live count, the pool bundle at
0).  Agreement forces **every count move to open `↑iregN`** — structurally
possible at every site because the store rule's mask leaves `iregN` free
(the ZZProbeIcnt verdict).  This is how the region knows the icache count,
which is what makes the freeze pin a theorem.

### 3e. The arm structure (option A) and the registry

`ireg_slot`'s arm is a 2-way disjunct: **(IN ∨ MARKED) ∗ reg_full** — record
present (`z ↪[γi] d`) or checked out (`imark`) — **∨ PENDING** — a type-0 box
whose free is still in flight: `z ↪[γi] d ∗ reg_half z ge gr ∗
region_pending z`.  `reg_full/reg_half z ge gr` are `ghost_map` fractions of
the per-inum **escrow registry** `icfg_reg : Z → (gname * gname)` (rebindable
across free cycles); `ireg_claim_au` refutes PENDING by fraction overflow
(`reg_full_half_False`), and the off-lock deposit splits `reg_full` into the
pending pair.

## 4. The option-A escrow (the pending-free pipe)

| piece | type / home | meaning |
|---|---|---|
| `escA_inv ge gr γi z` | tiny invariant per in-flight free (`EscrowInode.v:31`), states EMPTY→FILLED→REDEEMED on a `mono_nat` | the bridge that carries "the disk free COMMITTED" from the off-lock tail (which holds no locks) to the next allocator/recycler of that inum. |
| `committedA ge` | persistent `mono_nat_lb` at `ST_FILLED` (`EscrowDefs.v:26`) | "the type-0 write is in the log" — minted by `ireg_free_deposit_au`, read by the redeem. |
| `redeem_ticketA gr` | `Excl ()` (`EscrowDefs.v:33`) | the one-shot right to redeem the escrow back into a normal free-pool entry; parked pool-side (`pool_await`). |
| `region_pending z` / `pool_pending γi z` | the two halves' packagings (`EscrowDefs.v:103` / `EscrowInode.v:100`) | region-side and pool-side views of one in-flight free, correlated by the `reg_half` pair. |

Lifecycle: freezer parks `pool_await = escA_inv ∗ ticket ∗ ifreeze_post` at
the eviction → deposit fills the escrow (region flips to PENDING) → the next
iget/ilock of that inum redeems (escrow→`imark`, pool arm→normal,
`reg_join`→`reg_full`).

## 5. The icache (lock-held state + per-entry escrows)

### 5a. Under `itable.lock` — `itable_res2` (`IcacheEscrow.v:2434`)

| piece | meaning |
|---|---|
| `itable_half M` | ½ of the authoritative slot map `M : slot k ↦ (q_out, count)` — the other half lives in the itable spinlock's invariant; holding the lock composes them. |
| `ci : k ↦ (dev, inum)` | the pure identity map; `ic_ci_wf` ties `dom ci = dom M`; the pool's domain is its complement. |
| `islot2 cn M ci k` | per-slot arm: EMPTY (`islot_empty`) or LIVE = `islot_rest_at k q dev inum ∗ iref_slots count ∗ ic_id ½ ∗ icnt_half inum count`.  **Landing in IVb**: the LIVE arm gains the frozen-park disjunct (`frz_mirror` false, or true ∗ the freezer's two `live_frac` pieces) — RULING A‴. |
| `isl_pool M` | the slots' share authorities, deliberately lock-held (iput holds a slot's authoritative zero across `acquiresleep`). |
| `iref_slots_auth` / `iref_slot` | auth/fragment of the global reference-slot budget (`IrefSlots.v:78`): a caller brings one `iref_slot` to iget, which parks it to account the reference it mints. |
| `ipool … (region_inums ∖ ci_inums ci)` | the free pool: one **bundle** per uncached inum = `icnt_half z 0 ∗ ifreeze_off z ∗` shape, where shape = `ipool_shape_np` (alloc-arm with `dinode_at`, or `imark`-arm) ∨ `pool_pending` ∨ `pool_await` (`:487/:523/:558`). |

### 5b. Per-entry escrows — `ic_escrows` (persistent family, `icEscN`)

| piece | meaning |
|---|---|
| `ic_escrow cn γfs γi cov ls k` | slot k's escrow invariant; arms = EMPTY / PARKED (`ic_parked`: payload parked, entry cached but unlocked) / HELD (`ic_held`: payload checked out to a sleeplock holder) / MID / OUT. |
| `ic_payload = ic_payload_np ∗ ifreeze_off inum` (`:837/:783`) | the parked/checked-out **payload**: `inode_raw` bytes-ownership, `dinode_at`, blockmap, dir-links, epoch — plus (A′) the freeze token, so token custody coincides with payload custody.  IVb owes PARKED the `(off ∨ pre)` disjunct for the freezer's mid-free park. |
| `ic_id cn k q b dev inum` (`:382`) | fractional identity ghost for the slot's `(dev,inum)` cells; the escrow keeps half of both identity cells forever (§13.1e). |
| `live_gen k s g` / `live_frac k s` (`IcacheRef.v:1758/:1766`) | fractions of the slot's live-generation cell: the checkout's ½, the table's share, a reference's share — `live_whole_share_absurd` is the overflow lemma the A‴ frozen-park collides foreign idups against. |
| `iref_frag k q` (`:1895`) | a fraction of one slot's reference mass (`icfg_iref`). |

### 5c. The ambient gname family (`icfg`, `IcacheRef.v:580–663`)

`icfg_iref` (reference mass), `icfg_live` (live/generation cells),
`icfg_link` (THE link ledger, §3b), `icfg_iep : Z → gname` (record epochs),
`icfg_isl : nat → gname` (per-slot sleeplock names), `icfg_reg` (escrow
registry), `icfg_icnt` (the count coupling), `icfg_boot` (the boot one-shot),
+ IVb's mirror gname.  One `MkIcfg` record threaded everywhere as a
typeclass, so no per-inum gname ever needs to be read off a class.

## 6. Client-side currencies (what proofs hold in their hands)

| piece | meaning |
|---|---|
| `inode_ref k q dev inum` (`IcacheRef.v:1977`) | ONE counted reference to slot k at that identity — what iget returns and iput spends.  `inode_shr k s` is a share of one; `inode_ref_gen`/`inode_shr_gen` add the generation pin. |
| `iref_slot` | the fungible budget unit a caller brings to iget (filedup/idup discipline). |
| `iname γi γfs inum l` — the iget **licence** (`IgetLic.v:303`) | the gate on reference-minting; `l : ilic`, five constructors: `LinkedL fl` = a paid dirent unit (`ipaid`); `HeldL d` = the caller already holds `dinode_at d` with type≠0 ∧ nlink≠0; `ClaimL` = `iclaim` (the allocator); `BufL bno ds` = the inode block's `fsblock` half at bytes showing type≠0 **∗ `ireg_boot`** (boot-only — ireclaim); `RootL` = the root inum.  `SpanL` (the old `⌜True⌝` hole) and `GreyL` are deleted tombstones. |
| `ifreeze_off z` | see §3b's f-column — surfaces to clients through `SpecIlock`'s post and returns at iunlock; it is how create/sys_link prove a fresh box is not mid-free (`ireg_link_pin`). |
| `iclaim z` | the allocator's window token: minted at the claim, presented as `ClaimL` at ialloc's iget, spent at the claimant's ilock-fill where the claim pin pays out `create_fresh_ty`. |

## 7. Boot phase

`ireg_boot := ity_pending icfg_boot` (exclusive) vs `ireg_open := ∃ ty,
ity_shot icfg_boot ty` (persistent) — a one-shot (`ity_shoot`,
`IcacheRef.v:847`).  Boot/ireclaim runs holding `ireg_boot`, which refutes
every claim and every runtime freeze it encounters (the two disjunctive
shelter clauses in §3c) and backs its `BufL` scan-igets.  The **seal** fires
once after `fsinit` returns, converting to the persistent `ireg_open` that
rides the syscall dispatch env (`sysc_fs_env`/`fs_world`) down to
`ireg_claim_au`.  The seal's site terminates at the tree's one standing IOU
(`LinkForkretNF.wp_forkret_nf_ax` — forkret's first branch), shared with
upstream; no new axiom.

## 8. The tree layer (fs-friendly fragments)

| piece | meaning |
|---|---|
| `node_of` / `node_rep n dn data` (`FsTree.v:485/:500`) | the pure abstraction of one inode: `fsnode` = NDir with its `ents : gmap fname Z` (via `dir_view`) or NFile with its bytes. |
| `fnode γi γfs i n` (`FsRep.v:114`) | node `i` currently IS `n` — holdable only while `i` is locked (§1.4's theorem); the tree-facing view of the payload. |
| `fedges` / `fmap_rep` / `fs_rep t` / `fslice` (`FsRep.v`) | the whole-tree representation and its path-slices — the AMBIENT tree a client opens for global facts. |
| `dir_links self dn data` (`DirLinks.v:565`) | the per-directory link accounting bridging records to the ledger's dirent columns. |
| `FsLookup.wp_dirlookup_tree` | the F2 **logically-atomic** lookup triple: pre/post name the SAME `ents` (the linearization interval is the caller's lock hold), and it claims nothing about any other node. |

## 9. How it composes: the two transition windows

The whole design is two mirrored exclusivity windows over the same ledger.

**ialloc's claim window** (type-write → ilock-fill): `ireg_claim_au` mints
`iclaim` under `ireg_open`; the claim pin freezes the record's identity; the
window is unenterable by others because byte-movers need the parked
`dinode_at` and reference-minting needs a licence — and every licence row is
refuted at a claim box (no dirent units at nlink 0, custody circular,
`iclaim` exclusive, `BufL` boot-only, root distinct).  The claimant's ilock
spends the claim and reads back its own record: `create_fresh_ty` as a
lemma (item 7 deletes the axiom).

**iput's freeze window** (ref==1 commit → off-lock deposit): `ireg_freeze_au`
spends the payload's `ifreeze_off` into `FrzPre`; the freeze pin says the
count is exactly 1 (the freezer's own) and nlink is 0; up-counts are refuted
by licence or (idup, IVb) by the frozen-park's fraction collision, so the
+0x8a re-read gives `cnt2 = 1` outright (B1); the eviction parks
`pool_await` while the freer keeps `dinode_at` in hand (B2); the deposit
writes type 0, fills the escrow, and retires the token — closing the window
and re-arming the inum for its next life.

The two windows are duals: the claim protects a box being BORN from a
foreign free; the freeze protects a box DYING from a foreign rebirth.  Both
are resource-level facts of the one per-inum ledger, which is why neither
needs a closed-world or trace-level argument.
