# durable-fs-plan — the crash-consistent file system, the whole design in one place

STATUS: DESIGN OF RECORD, ruled by the owner 2026-08-25 after three days
of machine-checked refutations (archived with their lane reports in
[`../completed/durable-disk-2026-08-23-to-25.md`](../completed/durable-disk-2026-08-23-to-25.md);
the refutations themselves are Coq files: `iris/FsDurRefute.v`,
`iris/FsDurDefer.v`, and the walls recorded in `iris/FsDurWire.v`'s and
`iris/FsDurLedger.v`'s headers).  The live worklist is
[`../projects/durable-disk.md`](../projects/durable-disk.md).  This file
supersedes the accreted rulings §4½–§4⁹ of
[`fs-state.md`](fs-state.md); `fs-state.md` §0–§2 (the guiding rule and
the nested predicate) and §7 (as-built notes) remain the reference for
the predicate itself.

Vocabulary used below is xv6's and CSL's only.  "The crash predicate" is
the one Iris predicate the machine layer preserves across a power cycle
(`RiscvPtsto.riscv_crash_pred`, instantiated by `FsCrash.P_fs`).

## 1. Three views of the disk, and who owns what

**The physical disk.**  Owned by the WAL inside the crash predicate: the
physical byte fragments pinning the disk image, and the pure definition
of the **committed view** `D` — the home blocks' contents that recovery
would produce right now (`FsCrash.fs_recovery`, `fr_D`).  The WAL keeps
"`D` = recovery of the physical disk" true at every step; its mirror of
the on-disk log (`log_mirror`, born true at PowerOn — "custody at birth")
is what proves that installing a batch lands the home blocks at the
logged contents (`LogInv.log_mirror_tie_body`, the commit's `D' = L`).

**The logged view `L`.**  A ghost map from home-BYTE address to byte
(`FsBlocks.fs_bytes`, `fsblock`/`byte_range` at dfrac 1), minted fresh at
each boot equal to `D`.  The WAL holds its authority inside the
`FsBlocks.fs_bytes_inv` invariant (namespace `logN`), which is what
freezes `L` during a commit and what lets `bread` clients learn a
buffer's bytes.  File-system code owns `L`'s ELEMENTS, and owning the
elements of a byte range IS the permission to write that range.  `L` is
not durable: it evaporates with the era at a crash — the semantics of
losing uncommitted writes.  The bio layer's own cache map
(`fs_cache`/`fs_chalf`) covers every cached block including the WAL's
own log blocks; only the FS-facing byte view is home-only.

**The durable snapshot.**  Also inside the crash predicate: ONE copy of
the file-system predicate (§2) over its OWN ghost names, describing `D`.
It is NEVER UPDATED.  At each group commit the WAL allocates a fresh copy
over fresh names and drops the old one (affine).  Nothing outside the
crash predicate ever holds a piece of a snapshot.  Its byte points-to
may be persistent (frozen ghosts can be); the link family is not.

## 2. The file-system predicate `fs_state Γ S`

One definition (`iris/FsState*.v`), used twice.  `S : fs_state_rec` is
the abstract state (superblock, inode table `fss_inodes : gmap Z
fs_node`, used set); `Γ` names the ghosts (the byte points-to `fsΦ`, the
link-count family `γlink`, the abstract map `γtop`).  The body is a
separating conjunction over inodes (`fs_inodes`), where inode `i` owns:
its 64-byte on-disk record (`rec_owned`), the bytes of EVERY data block
its record names — regardless of `size`; the file's contents are the
first `size` bytes (`fn_file_bytes`) — its abstract-map fragment
(`top_frag`), its link-count authority (`link_auth`), and, for a
directory, one link token per entry (`ent_toks`: none for `.`, none for
`..` of an orphan, none for an entry naming the directory itself).  Plus
`free_bitmap`, which owns the bitmap block and the bytes of every free
block.  Well-formedness is stated LOCALLY per inode (`inode_local`:
type ∈ {DIR,FILE,DEV}, size bound, block-map coverage, the dots of a
live directory, unique names).  There is NO cross-inode pure clause:
"two inodes never share a block" is the separating conjunction.

- **Era instance** (over `L`'s ghosts, `FsBytesGamma.fs_gamma_L`):
  DISTRIBUTED.  Record bytes sit in the inode-region invariant
  (`InodeRegion.ireg_recs` — the allocator's free-slot scan needs a whole
  inode block's bytes tied to state, ruling (i)), with the lock holder
  carrying an exclusive proxy `dinode_at`.  Each cached inode's remaining
  pieces sit in an escrow keyed by its cache slot
  (`IcacheEscrow.ic_loaded`, holding `FsStateEra.inode_owned_era`),
  whose sleeplock protocol is: unlocked ⇒ bundle inside, locked ⇒ the
  holder has it; `ilock` withdraws, `iunlock` deposits and RE-PROVES
  `inode_local`.  Uncached inodes sit in the pool under the itable
  spinlock (`ipool_alloc`).  Free blocks sit in `BitmapInv.bitmap_inv`
  (= `FsStateBitmap.free_bitmap_at`).  The abstract map's authority sits
  in `InodeRegion.ftop_inv` (namespace `ftopN`).  Link counts:
  `ireg_lnk` in the region (the authority), tokens in the payloads
  (`dlinks` → `ent_toks`).  ALL of this is LANDED (stage 2b).
- **Durable instance** (over fresh names): held whole, immutable.
  `FsDurSnap.fs_snap_alloc` allocates one from a VALUE and pure facts
  (§4); `FsDurSnap.P_dur D` is the snapshot as a function of `D` alone
  (drops into `P_fs` with no arity change).  LANDED (lane 4); NOT YET in
  `P_fs`.

## 3. The WAL's client-facing contracts

- **`bread`/`brelse`** (landed): buffer ownership under the buffer
  sleeplock; `brelse` requires the buffer's bytes to EQUAL the block's
  logged value.  A thread that modified a buffer in place and did not
  `log_write` cannot release it.  This — not inode locks — is what makes
  "the WAL copies the cached buffer at commit time" safe.
- **`begin_op`** (TO BUILD): allocates a transaction id `t` and hands the
  caller the exclusive token `t ↪[γtx] ()` INSIDE the transaction token
  `log_op` (its existential closure stays: `log_op γ u = ∃ …, t ↪ () ∗ …`).
  The authority `γtx` sits in the WAL's lock invariant (`LogInv.log_state`)
  beside the table of open transactions.  **`end_op`** consumes the FULL
  share (fraction 1) and the WAL deletes `t`.  Because the retire step is
  resource-shaped, the ending transaction never has to NAME what it
  touched — `SpecEndOp`'s closed token survives (lane 4c's finding 5 does
  not bite); the only ABI change is that the token is FRACTIONAL while a
  lock is held (§3 `ilock`), so contracts spanning a held lock carry
  that form.
- **`ilock i`** (TO BUILD, ONE spec): withdraws `i`'s bundle and registers
  `i` in the LOCKED REGISTRY — an authority `LOCKED : inum → option
  transaction-id` in the file system's own invariant (`ftopN`, beside
  the abstract map's authority) — as `i ↦ Some t` if the caller passes a
  transaction share (parking HALF of `t ↪ ()` in the registry) or
  `i ↦ None` otherwise (`fileread`, `filestat`, lookups outside a
  transaction); returns the matching receipt.  **`iunlock i`**: deposits
  the bundle CLEAN (`inode_local`, as today), deletes the entry, returns
  the half share.  xv6's `ilock` is one function; the spec's optional
  argument is the transaction share.
- **`log_write b`** (landed shape, TO ADJUST): requires a transaction
  token, the caller's byte elements for the range it changed (the
  byte-range AU, `SpecLogWrite.wp_log_write_au_range`; a whole-block
  writer uses the `off = 0` corollary), and — for an inode record or a
  data block — the `Some t` receipt for the owning inode (so a
  read-locker cannot write: the region's write lemmas
  `ireg_write_*`/the escrow's data-block accessors take the receipt).
  It moves `L` at those bytes and the caller re-establishes the two pure
  facts of §4(a) in the parked payload.
- **Commit** (`end_op` at `outstanding = 0`; WAL-internal, TO BUILD):
  reads the abstract value off the abstract map's authority (`ftop_inv`),
  the bitmap invariant's used set and the superblock; with the two pure
  facts of §4 allocates a fresh durable snapshot at that value
  (`fs_snap_alloc`, a basic update — allocation needs nothing from
  anyone); installs "`D := L`" (as today, `FsCrash.fs_commit_L_*`);
  drops the old snapshot (`FsDurSnap.dsnap_step_of`).  Its receipt: the
  committed view equals the logged view (`D' = L` at home maps) AND the
  new snapshot's state is the quiescent abstract state.  NO caller of
  any WAL function supplies a fupd; the only fupd in the durability story
  is the machine's disk-interface permit, which the WAL discharges.

## 4. The two pure facts the commit needs, and how they are maintained

**(a) The bytes match** — `FsDurSnap.snap_bytes S Dc` (LANDED): "there is
an abstract state `S` whose encoding is exactly the current logged
bytes (records at their slots, data blocks, the bitmap block as
`bm_bytes` of the used set, free blocks present), every inode's blocks
are marked used in the bitmap and are not metadata blocks, and no two
inodes name the same block."  Maintained at each `log_write` by the
writer ALONE (`snap_bytes_frame`): its write changed only its own
object's bytes (its buffer read-modify-write, `FsBlocks.blk_splice`), so
every other inode's encoding is untouched (`snap_untouched_of_own`);
when it adopts a fresh block the bit it read was clear
(`snap_untouched_of_free`), so no inode could have owned that block.
The used-set clause is the ONE whole-map pure statement in the design
(the owner accepted it, 2026-08-25, "if it closes"); its maintenance is
local.  The record-encoder is injective on well-formed records
(`dinode_bytes_inj`, `rec_in_blk_inj`), so `snap_bytes` pins every
inode's node (`snap_bytes_node_inj`).  The parked payload
`LogInv`'s `Ψ D₀ Dc` becomes exactly `⌜∃ S, snap_bytes S Dc ∧ S agrees
with γtop_L's map / the used set / the config's superblock⌝`.

**(b) All inodes clean** — the locked registry (TO BUILD): the
file-system invariant carries "every inode whose registry entry is
`None` or absent is well-formed (`inode_local`) at the current logged
state" (`FsDurSnap.snap_local`, restricted).  Transactional `ilock`
weakens it (free); `iunlock` re-establishes it for the released inode
(already proven today at the escrow deposit); `end_op` cannot run while
any lock is held (a half share is parked in the registry); at commit the
WAL's `γtx` authority is empty, so no share of any id can exist, so no
`Some t` entry can exist, so EVERY inode is clean.  Mid-transaction
states (`create`'s `nlink = 1` written before its dot entries;
`itrunc`'s bits cleared before the pointers are zeroed) never reach a
snapshot — snapshots are taken at quiescence only.

Together, (a) ∧ (b) at `outstanding = 0` is `FsDurSnap.snap_ok S_L (lm_logged L)`,
the exact premise of `fs_snap_alloc`.

## 5. Boot, adequacy, and the theorem

**Boot** (stage 4): the SAME allocator core (`FsDurSnap.fs_state_of_ledger`
— Γ-generic, value-plus-pure-facts in, instance out) clones the current
snapshot onto fresh era ghosts, followed by the era-only extras (the
cache/dirty ghosts, the observation pairs) and the distribution of the
pieces into the region/bitmap/escrow/pool.  This REPLACES the boot-time
decoding of `fs.img` (`FsCfgBoot.img_nodes`, `image_*` premises), which
then survives only at era 0 inside `P_fs_alloc` (`FsDurImg`), and lets
the adequacy theorem delete `Himg`/`fs_boot_image_eras` and assume only
era 0's image — the theorem becomes TRUE (today it is vacuous).

**The theorem** (the spike, `mknod_durable`): for the batch containing a
`mknod`'s transaction, after its commit the CURRENT snapshot's inode
table at `inum` is `create_made ty major minor` and the parent's
directory entries contain `(name ↦ inum)` — read off the snapshot via
`P_dur_node_of_slot`/`snap_dir_entry_of_first` (LANDED readings) from
`D' = L` plus `mknod`'s own facts about `L` at its objects.  The
bytes-level statement is a corollary.  Later theorems read any effect
the same way.

## 6. What it costs, and what is deleted

Costs: the transaction token is fractional while locks are held
(contracts spanning a held lock carry that form — wide, shallow); nine
`log_write` call sites each prove the "only my object changed" step
(`ProofBfree`, `ProofBmap`, `ProofBalloc` ×2, `ProofIupdate`, `ProofIalloc`,
`ProofIput`, `ProofWritei` ×2 — today each is one `log_psi_write_rebase`
line); the one whole-map pure clause of §4(a).

Deleted once consumers are re-pointed: `FsDurWire`'s `P_wf_dec`/`Psi_dec`/
`kinds_of_state`/`dwire_geom`/`psi_*` (the rejected pure-kinds tie),
`LogInv.log_psi_*`, `LogDefs.fs_dstep`/`fs_dstep_rebase`/`fs_dview`-as-`P_wf`,
`RiscvPtsto.fdn_bmap/ist/nin` and `riscv_dview_name` (geometry equations
become by-construction), `FsDurLedger`'s fold family (its entry
constructors are era-side content — keep if consumed).
`FsDurRefute.v`/`FsDurDefer.v` stay as the documented refutations.

## 7. The vacuity discipline (why the tie cannot silently go empty)

The WAL cannot police the CONTENT of the file system's invariant — a
weaker invariant makes every writer's obligation EASIER, never harder
(3b's degenerate-state witness compiled).  The strength of the durable
snapshot is cashed only by its READERS: the boot mint (§5) that must
re-found an era from it, and the theorems stated on it.  Therefore:
every hedged or quantified conjunct gets a non-vacuity witness AT THE
REAL INSTANCE (xv6's own superblock layout — 3b'/`dwire_geom` were
caught by witnesses at made-up layouts), and the definition of done for
any strengthening is "stage 4's boot mint consumes it", not "the tree
compiles".

## 8. Why the earlier mechanisms died (so nobody re-derives them)

- Deposited client fupds moving durable resources: refuted — a fupd over
  fragments alone is not frame-preserving against the authority that
  necessarily sits in the crash predicate (`FsDurRefute`); a fupd over
  the whole body ∀-quantified over states is undischargeable at
  mid-batch two-owner states (the `itrunc` window) and kills modularity;
  a ∀-auth-quantified one is the library lemma (informationally empty).
- Per-transaction deferred WRITE SETS in the WAL's ledger: refuted by
  concurrency — the ledger is order-blind while a shared block's final
  bytes are order-dependent (`FsDurDefer`); forcing agreement evicts one
  transaction's obligation onto another.
- Pure decode ties over bytes with a KIND MAP: rejected by the owner
  (re-imports pure role/disjointness reasoning) and twice found
  unsatisfiable/degenerate at xv6's layout.
- The pure delta LEDGER with a fold over an updated durable body: closed
  (`FsDurLedger.dled_fold_body`) but needed cross-write "hands" and the
  geometry equations; superseded by snapshots, where nothing is updated.
