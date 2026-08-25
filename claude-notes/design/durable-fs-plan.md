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
crash predicate ever holds a piece of a snapshot.  Its byte points-to is
EXCLUSIVE — the same full ghost-map element the era's view uses — because
that is what makes the `∗` between two inodes of a durable `fs_state`
mean something, and because the ONE allocator core has to serve the boot
mint too (§5) and the era's `fsΦ` cannot be `□`-ed.

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
- **`ilock i`** (ONE spec; the lock-side half TO BUILD in lane B′):
  withdraws `i`'s bundle from its escrow.  With a transaction share it
  withdraws everything and the escrow's "out for writing" arm PARKS a
  share of the transaction's token `t ↪[γtx] ()` (so `end_op`, which
  needs the whole token, cannot run while any inode of the transaction
  is write-locked); without one (`fileread`, `filestat`, lookups outside
  a transaction) it withdraws a ¼ fraction of the byte elements and the
  "out for reading" arm keeps ¾ plus the rest of the bundle (§4 says why
  ¼).  **`iunlock i`**: deposits the bundle CLEAN (`inode_local`, as
  today) and returns the parked share.  The escrow — not `ftop_inv` —
  is what knows the lock state, which is why the token parks there.
- **The armed set** (LANDED, lanes A and B″-arm): the abstract map's one
  mover (`InodeRegion.ireg_top_retag`) requires `inode_local` of the new
  node unless the transaction has ARMED the inum in `ftop_inv`'s registry
  (`icfg_lk : arm-id → (txid, share, gset inum)`; an entry parks ANY
  positive share of the arming transaction's token, keyed by a fresh arm
  id so no freshness of the transaction is needed — a walk that has
  parked shares in escrows can still arm).  Only `create`'s mkdir child (`nlink = 1`
  flushed before its dot entries) needs it in this kernel.  `ftop_inv`'s
  row "every unarmed inum's node is `inode_local`" plus an empty `γtx`
  authority yields `snap_local` of the abstract state
  (`IregClean.ireg_snap_local_acc`/`_of_ops`).  A read-locker cannot move
  a record because `ireg_write_au` takes the exclusive proxy `dinode_at`
  that only a lock holder has.
- **`log_write b`** (landed): requires a transaction token, the caller's
  byte elements for the range it changed (the byte-range AU,
  `SpecLogWrite.wp_log_write_au_range`; a whole-block writer uses the
  `off = 0` corollary), and — for an inode record or a data block — the
  `Some t` receipt for the owning inode (so a read-locker cannot write:
  the region's write lemmas `ireg_write_*`/the escrow's data-block
  accessors take the receipt).  It moves `L` at those bytes.  IT PROVES
  NOTHING ABOUT THE FILE SYSTEM: no pure fact is re-established at a
  write, and the WAL's lock invariant carries no file-system payload
  (the parked `Ψ D₀ Dc` and the `log_psi_*` laws are deleted — §4, §8).
- **Commit** (`end_op` at `outstanding = 0`; WAL-internal, TO BUILD):
  installs "`D := L`" (as today, `FsCrash.fs_commit_L_*`) and, at the same
  ghost step, RECONSTRUCTS the file-system predicate over `L` and clones
  it onto fresh names as the new snapshot (§4), dropping the old one
  (`FsDurSnap.dsnap_step_of`).  The reconstruction is a persistent,
  file-system-supplied law parked in `log_ctx` (the WAL stays
  file-system-agnostic): given the byte authority at `L` and "no
  transaction is open", it yields `∃ S, snap_ok S L` and hands the
  authority back — it moves NO durable resource (§8's refutation is about
  fupds that do).  Its receipt: the committed view equals the logged view
  (`D' = L` at home maps) AND the new snapshot's state is the quiescent
  abstract state.  NO caller of any WAL function supplies anything at the
  call site; the only fupd in the durability story is the machine's
  disk-interface permit, which the WAL discharges.

## 4. Where the commit's proof comes from: collection at quiescence

The allocator (`FsDurSnap.fs_snap_alloc`, over the Γ-generic core
`fs_state_of_ledger`) takes the value `L` and `snap_ok S L` — "the bytes
are the encoding of `S`, every inode of `S` is well-formed, no two share
a block".  NOTHING MAINTAINS THAT FACT INCREMENTALLY.  It is false in the
middle of an operation on the byte side exactly as on the local side
(`itrunc` frees blocks one `log_write` at a time and rewrites the record
once, at its tail `iupdate`; `FsDurTrunc.v` is the machine-checked
refutation of a per-write accumulation, §8), and every such state
belongs to an inode that is LOCKED.  So the commit RECONSTRUCTS it from
the file system's own invariants at the one moment they are all clean:

- **No inode is write-locked and no inode is armed** — at commit the
  WAL's `γtx` authority is empty, so no share of any transaction id
  exists: no escrow "out for writing" arm (it parks a share,
  `IcacheEscrow.ic_out_no_write_arm`) and no armed entry (it parks a
  share, `IregClean.ireg_snap_local_acc`).  Every inode is either unlocked or
  read-locked, and every node of the abstract map is `inode_local`
  (`IregClean`).
- **Every inode's validity predicate is inside the invariants.**  An
  unlocked inode's bundle (`inode_owned`: its record proxy, its data and
  indirect blocks' byte elements of `L` at FULL fraction, its abstract
  fragment, its link authority and entry tokens, and `inode_local`) sits
  in its cache-slot escrow (`ic_loaded`; one invariant PER SLOT at
  `icEscN .@ k`, so the commit can open all fifty at once — lane B′; a
  single shared namespace opens only once, `FsDurQuiesce.ns_not_reopenable`)
  or, uncached, in the pool (`IcacheEscrow.ipool` — its own invariant at
  per-inum namespaces, lane B′; it must NOT sit in the itable spinlock's
  resource `itable_res2`, which only a lock holder reaches and the commit
  never does; `IcacheInv.live_pool` inside `inv icacheN` is the
  refcount pool and holds no bundle); the records themselves sit region-side at full
  fraction always (`ireg_recs`, `inv iregN`); the free blocks and the
  bitmap sit in `bitmap_inv`; the abstract map's authority in `ftop_inv`.
  A READ-LOCKED inode (`ilock` with no transaction — `fileread`, `stat`,
  lookups) has withdrawn only a ¼ FRACTION of its byte elements; the
  escrow keeps ¾ and the rest of the bundle.  A transactional `ilock`
  withdraws everything.
- **Collected, they ARE `fs_state` over `L`.**  Opening those invariants
  at the commit's ghost step and ∗-ing the bundles gives, against the
  byte authority in `fs_bytes_inv`: the bytes at every record slot and
  data block by AGREEMENT (any fraction suffices), the used set and the
  free blocks' bytes off `bitmap_inv`, `inode_local` of every inode off
  its bundle, and cross-inode block DISJOINTNESS from separation logic —
  two full elements at one address are inconsistent, and so are two ¾
  elements (¾ + ¾ > 1), which is why the reader's share is ¼ and not ½.
  That is `snap_ok S L` for the abstract `S` the `ftop_inv` authority
  holds; the allocator clones it.  The same collection lemma is what
  §5's boot mint runs in the other direction.

There is NO cross-inode pure clause anywhere and no obligation on any
writer beyond owning the bytes it writes.  `FsDurSnap.snap_bytes` keeps
its used-set coupling clauses (`sk_own_used`, `sk_disj`) because the
allocator needs them to SPLIT a linear ledger; at the commit they are
read off the ∗, at boot off the snapshot.

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
(contracts spanning a held lock carry that form — wide, shallow); the
inode bundle's byte elements are fraction-indexed so a read-locker can
take ¼ (`inode_owned_era`/`blk_owned` at `fs_gamma_L` are dfrac-1 today:
the footprint is every consumer of the bundle's data-block accessors);
the commit's collection lemma opens five invariant families at one ghost
step.  Nothing is owed at a `log_write` beyond the bytes it writes.

Deleted once consumers are re-pointed: `FsDurWire`'s `P_wf_dec`/`Psi_dec`/
`kinds_of_state`/`dwire_geom`/`psi_*` (the rejected pure-kinds tie),
`LogInv.log_psi_*` and the parked `Ψ D₀ Dc` (with the nine suppliers' `log_psi_write_rebase` lines), `LogDefs.fs_dstep`/`fs_dstep_rebase`/`fs_dview`-as-`P_wf`,
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
- A per-`log_write` accumulation of the bytes-match fact (`snap_bytes` as
  the WAL's parked payload, re-proven by every writer): refuted
  (`FsDurTrunc.v`) — `itrunc`'s window holds a record naming blocks whose
  bits are clear, so no abstract state fits the logged bytes; every
  mid-operation state is a LOCKED inode's, which is why the fact is
  collected at quiescence (§4) and never carried.
