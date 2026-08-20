# fs-cfg-boot — allocating the file system's ghost state and giving `fscfg` a value

Design of record: [`design/fs-ghost-state.md`](../design/fs-ghost-state.md) §7
(`fs_ready`, the seal, the adoption audit),
[`design/fs-icache.md`](../design/fs-icache.md) (the cache),
[`design/fs-log.md`](../design/fs-log.md) (the block layer). This file is what
is LEFT: the boot-side allocation that gives `IcacheRef.icfg` and
`FsCfg.fscfg` values, stocks the inode pool, and gets `FsReady.fs_ready`
produced.

It subsumes [`fs-icache.md`](fs-icache.md)'s C7 owed items (b), (c), (iii) and
(iv), and it is the gate [`main-boot.md`](main-boot.md) §G3's table names.

## The state of the two config records

`FsReady.fs_ready` is a parameter-free persistent assertion over `icfg`'s 14
fields and `FsCfg.fscfg`'s 18, and its producer `fs_ready_establish` is `Qed`.
`FirstTok.first_tok` is the carrier that decides forkret's `if (first)` branch.
**Nothing in the tree ever produced an `icfg` or an `fscfg`.**
`SystemAdequacy.adequacy_icfg` / `adequacy_fscfg` are hardcoded records of
`1%positive` that nobody allocated, and `adequacy_icfg` pins `icfg_nib = 0`, at
which an `IcacheRef.inode_held` cannot exist — so the boot cone's one assumed
contract is VACUOUS at the instance the `xv6Σ` corollaries are taken at. That
is the reason to do this: it is a defect in the top-level statement, not a
missing convenience.

## The obstruction, in two halves — they are not the same problem

**(c-instance).** `icfg`/`fscfg` reach every proof as superclass fields of
`FileInvDefs.fileG`, an ambient `Context` of `xv6_boot_era` and both adequacy
theorems, so they are fixed before any fupd runs.

**(c-timing).** Most fs ghost names are minted by constructors that run at WP
time and return existentials: `newlock` (six sites in `ProofMain`), `bio_init`
→ `∃ bn`, `icache_boot` → `∃ γl cn`, `initlog` → `∃ γ : log_names, log_ctx …`.
An ambient field cannot be an existential.

(b) — the pool stocking — is a consequence of (c-timing) plus
`FsBoot.fs_boot_bundle` having no consumer.

## THE PRINCIPLE: mint every name once, in the era fupd

Every downstream constructor becomes an `_at` form that FILLS a name it is
given rather than returning a fresh one. The tree already commits to this and
says why:

- `icfg_isl` is allocated "BEFORE any lock is built … the ordinary constructor
  allocates the gname itself, which is too late for anything that has to
  mention it" (`IcacheRef.v`), consumed by `SleepLock.sl_fresh_new_gen_at`.
- `IcacheBoot.icache_boot` takes `own icfg_iref (● ∅)`, the `live_frac`s and
  the `icfg_isl` ghosts as PREMISES, annotated "this lemma cannot mint it and
  then claim to have built THE itable".
- `IcacheBoot.ireg_alloc` takes EVERY ledger family (`link_auth`, `icnt_half`,
  `frzown`, `frzm_h`, `mono_nat_auth_own (icfg_iep z)`, the registry auth,
  `ireg_boot`) the same way, each annotated "the gname is the ambient class's,
  so only the `own_alloc` that minted it can hand them over".
- `BootShared.boot_shared_alloc` ALREADY allocates `fdslotG`/`irefslotG`/`pavG`
  inside the boot fupd and returns them existentially, with only the `…GpreS`
  classes ambient. `fileG` is that move again.

So the work is finishing a pattern, not introducing one. The `_at` precedents
that already exist: `WpLock.newlock_delayed`, `SleepLock.sl_fresh_new_gen_at`,
`IcacheEscrow.ic_names_alloc` (a standalone `bupd`), `FsBoot.fs_boot_ghosts`
(the ghost-only half of `fs_boot_bundle`, needing only the disk mint).

## Settled rulings

**R1 — `fsc_desc`/`fsc_avail`/`fsc_used` LEAVE `fscfg`.** They are the three
virtio ring pages, `kalloc`'d inside `virtio_disk_init` at WP time — the one
family that cannot be known at boot. `FsCfg.v`'s own note concedes they were
included only because "one door for the whole fs configuration is simpler than
two, and it costs nothing"; this is the bill. Existentially quantify them
inside `fs_ready`'s disk conjuncts, recovered by agreement against
`disk_geom`'s persistent cells (`d_desc_ptr ↦₈□ pd`, …).
`SpecMainSecondary.main_deposit` already quantifies `pd pav pu` exactly so.
An existential is recoverable HERE and not for a gname, which is the whole
distinction `FsCfg.v`'s header is drawing.

**R2 — the geometry fields stay plain `Z`s; only their VALUES come from the
image.** `FsCfg.v`'s record does not change. `fs_cfg_alloc` instantiates
`fsc_logst`/`fsc_bmapstart`/`fsc_size`/`fsc_ninodes`/`icfg_ist`/`icfg_nib` at
`FsImg.fs_parse_sb dk`'s projections, which the era fupd can compute because it
holds `dk`.

**R3 — the generic `xv6_fs_adequacy` gains image hypotheses**, discharged at
the literal image by `FsImgCheck`'s projections. The HEADLINE corollary's
hypothesis list does not grow: this is `fsimg_recovery`'s existing shape at
full width.

**R4 — `cov` is INSTANTIATED in the corollary, not left universally
quantified.** `cov : gset Z` is the coverage set: the set of block numbers the
proof maintains logical content for. It is the domain of `fs_L0 dk cov` /
`fs_D0` / `blk_own`, and it is `bv_cov` of the buffer cache's `bio_view`, hence
exactly the set `bread` accepts (`bread`'s precondition is `⌜covered bno⌝`).
`design/fs-log.md` states the intent — `fs_covered bno := 1 <= bno < FSSIZE`,
block 0 excluded because binit leaves all thirty buffers claiming blockno 0 —
and it is a parametric `gset` so the block layer names no FS constant
(`FsBoot.v`: "nothing has to know the FS's disk size").

Stocking the pool forces every block an image inode names into `cov`
(`blkmap_wf`, inside `inode_ok`), on top of the log region
(`log_geom_ok`), the bitmap block (`bitmap_geom_ok`) and the inode blocks
(`ireg_blocks_ok`). **`cov` is free today only because the file system is not
wired into boot at all** — at `cov = ∅` the corollary says nothing about a file
system. Constraining it costs nothing in strength: the conclusion is
`reducible e2 g2` and never mentions `cov`, so `∀ cov` quantifies over
something the statement does not talk about. Keep the parameter on the generic
theorem; in `xv6_fs_adequacy_xv6Σ` drop it and instantiate at the image's own
range (`1 ≤ b < 2000`; `fsimg_sb = MkFsSb 0x10203040 2000 1953 200 31 2 33 46`,
so logstart 2, inodestart 33, `nib = 13`, bmapstart 46, data from 47).

**R5 — CUSTODY TRANSFERS AT `iget`, NOT AT `ilock`, and the pool must be
image-accurate before `userinit`.** `iget` inside `namei("/")` in `userinit`
returns an entry with `valid = 0`, which does NOT mean the ghost state is
silent about its contents:

```
ic_payload_np … v := if v then ∃ dn bm, ic_loaded … ∗ ity_shot g (di_type dn)
                          else ic_unloaded … ∗ ity_pending g
ic_unloaded … k inum := inode_raw (ientry k) ∗ ipool_shape_np … inum
ipool_shape_np … := ipool_alloc … ∨ imark γi (uint inum)
ipool_alloc …    := ∃ dn0 bm0 data0, ⌜inode_ok …⌝ ∗ ⌜dir_ok …⌝ ∗ ⌜dir_dots_ix …⌝
                    ∗ ⌜dir_orphan_clean …⌝ ∗ ⌜dir_uniq …⌝ ∗ dir_links …
                    ∗ dinode_at γi inum dn0 ∗ ind_res γfs bm0
                    ∗ inode_blocks γfs bm0 data0
```

`iget`'s recycle moves that whole bundle out of the pool into the entry
(`+0x72`: pool bundle in, old payload out via `ipool_insert`). The only thing
the `valid` split buys is the `ity_pending` / `ity_shot (di_type dn)` one-shot.

It is forced by the C: **`ilock` does not take `itable.lock`** — it takes
`ip->lock` and `bread`s, so at fill time there is no path back to the pool, and
whatever the fill must produce (`ic_loaded`) has to already be in the entry.
`iget` is the only step that holds `itable.lock` and knows the inum. `valid`
tracks whether the BYTES were read; the bundle tracks CUSTODY, and custody must
transfer earlier than content.

Consequence: `ipool_alloc`'s ALLOCATED arm must be discharged in the era fupd.
`ipool_alloc_all_free` (the type-0-only shortcut) will not do — the root inode
is allocated in the image. This is C7 (iv), and it is on the critical path
before `main`, not a follow-on.

**R6 — the boot kit splits in two, and the boundary is "does `userinit` need
it".**
- `fs_kit_icache` — spent inside main before +0x9e: the stocked pool,
  `iref_slots_auth`, `own icfg_iref (● ∅)`, the `live_frac`s, the fifty
  sleeplock ghosts. Consumed by `icache_boot_at` in `ProofMain.mn_grp_fs`.
- `fs_kit_fsinit` — must survive to forkret's first arm: block 1's `fsblock`,
  the 32 raw `.bss` superblock bytes, the log's raw cells + `log_mirror_full` +
  the log gnames' `own`s, `bitmap_res`, `ireg_boot`, the 35 `bslots`, one
  `iref_slot`.
- the persistent rows (`bio_ctx`, `ireg_inv`, `is_itable2`, `itable_inv`,
  `ic_escrows`, `ic_sleeplocks`, the three locks) go into `main_deposit`.

Each kit is ONE opaque `Definition` at the ambient names, not twenty rows —
`fs_ready`'s own argument applied to the boot side.

## `FsCfgBoot.fs_cfg_alloc` — contents and order

One new leaf, one lemma, run inside (or immediately after) `boot_shared_alloc`
and before `started_inv` is formed:

```
fs_cfg_alloc : ⌜fs_cov_in cov ndisk⌝ → ⌜image obligations about dk⌝ →
  disk_bytes γv 0 (disk_read dk 0 ndisk) ={E}=∗
    ∃ (ICFG : icfg) (FSC : fscfg), ⌜ties⌝ ∗ fs_kit_icache ∗ fs_kit_fsinit
```

The order is forced:

1. `γd`/`γv` are already minted by `boot_shared_alloc` — REUSE them as
   `fsc_uart`/`fsc_disk`; do not re-mint.
2. four `own_alloc`s for `log_names`; read `ist`, `nib` off the parsed
   superblock; `IcacheRef.icfg_alloc dv nib LM CM FM BM γlog ist` → `ICFG`.
3. `FsBoot.fs_boot_ghosts` (needs ONLY the disk mint) → `γfs`, the `fs_L` /
   `fs_dirty` authorities at `fs_L0 dk cov`, the dirty halves, every home
   block's `fsblock`, `blk_own`.
4. gname-only mints: bio's three gnames and three families; a new
   `lock_ghost_alloc` for the four lock gnames; the `kpages` pair;
   `IcacheEscrow.ic_names_alloc`. → `FSC`.
5. `IcacheBoot.ireg_alloc_at fsc_ireg` — it needs the inode blocks' `fsblock`
   halves, which step 3 produced, so the WHOLE inode region is built here:
   `ireg_inv` plus one `dinode_at` per inum.
6. `IcacheBoot.ipool_alloc` — the allocated arm from `fsimg_wf`'s projections
   (W3 `fs_inodes_wf` + W5 `fs_bitmap_wf` → `inode_ok`; W6 `fs_dirs_wf` + W7
   `fs_root_wf` → the `dir_*` conjuncts; `dinode_at` from step 5;
   `ind_res`/`inode_blocks` from step 3's home-block halves).

What must NOT move here: the escrows, the fifty inode sleeplocks and the itable
spinlock. They need `sl_fresh` and zeroed lock cells, which exist only after
`iinit` runs.

## Where each resource is built

| when | what |
|---|---|
| era fupd (`boot_shared_alloc`) | `ICFG`, `FSC`, `ireg_inv`, the stocked pool, all `dinode_at`s, the fs block ghosts, every gname |
| `ProofMain.mn_grp_fs` (main+0x8e→0xa2) | `bio_init_at fsc_bio` on binit's post; `icache_boot_at` on iinit's post (one ghost step between +0x92 and +0x9e); `newlock_at` for kmem/virtio/itable/pr |
| main+0x9e, `userinit` | `namei("/")`'s root corner, holding the four icache rows — so `LinkNameiRootBoot.v`'s `Axiom` is discharged by a functor application over `LinkNameiRoot.NameiRoot`, not by a proof |
| forkret's first arm | `fsinit` → `initlog_at icfg_log`, `ireclaim`, then `fs_ready_establish` |

`userinit` runs INSIDE main, so the four icache rows need no transport at all.
That is the earliest payoff and it is what retires the boot-cone axiom.

## Transport to forkret's first arm

`SpecFsinit`'s precondition is a large EXCLUSIVE pile and it runs on a
scheduler thread, arbitrarily far from main. Two channels, both already
designed:

- **persistent half** → `SpecMainSecondary.main_deposit`, the `started_inv`
  payload. It already carries `printk_env`, the virtio lock and `disk_geom`
  with `γpr`/`γk` existential; those become `fsc_printk`/`fsc_dlock` and the fs
  invariants join them. This is C7 owed (iii).
- **exclusive half** → **widen `FirstTok.first_tok`'s left disjunct** from
  `first_addr ↦₄ 1` to `first_addr ↦₄ 1 ∗ fs_kit_fsinit`. Mutual exclusion is
  untouched: it rests on the dfrac at `first_addr` alone
  (`first_tok_boot_excl`), the right arm stays persistent, and the left arm
  already IS "the right to run the boot arm: fsinit, the store of 0,
  kexec". Main deposits it through `SpecUserinit` into the first process's
  block.

## Restating the top (C7 (c) proper)

`fileG` is down to ONE capacity field (`file_inG : inG Σ fileUR`) since
`pipeG`/`icacheG`/`cinvG` moved to `Xv6G.xv6G`, so:

- replace `!fileG Σ` with `!inG Σ fileUR` (or a one-field `fileGpreS`) in
  `xv6_boot_era`, `xv6_power_adequacy`, `xv6_fs_adequacy`;
- build `FileG _ ICFG FSC` inside the fupd and apply `boot_hart_primary` /
  `Main.wp_main_boot_sconf` at it EXPLICITLY — the `Module Type` parameters are
  `∀`-quantified over the classes (`SpecMain.v`'s `MAIN`), so this is an
  application, not an elaboration, which is what keeps FileInv.v's "two
  instance paths print identically and do not unify" trap shut;
- **delete `adequacy_icfg` and `adequacy_fscfg`.** The 400 GB nontermination
  hazard documented at `adequacy_fscfg` goes with them, because there is no
  longer a `fileG xv6Σ` to resolve.

No conclusion mentions the configuration, so this weakens nothing.

## Verified, so it is not re-derived

- **`RootL` is PURE** — `⌜bv_unsigned inum = ireg_root⌝` (`IgetLic.v`). The
  root's `iget` needs no `ireg_boot`, no `fsblock`, no log.
- **`namei("/")` never `ilock`s.** With `nameiparent = 0` the
  `while(skipelem…)` body never runs, so no `bread` — no block layer at +0x9e.
- **`ireclaim` tolerates a cached root.** Its scan reads each inode block
  through `InodeRegion.ireg_read_blk`, which takes only `ireg_inv` + the
  block's `fs_L` half and NO per-inum custody (unlike `ireg_read`), and it only
  `iget`s inodes with `type ≠ 0 ∧ nlink == 0`. The root has `nlink > 0`, so it
  is skipped and its checked-out record never matters. `SpecIreclaim` takes the
  four icache rows as PERSISTENT premises; nothing in it requires an empty
  table (its header's "at the ALL-EMPTY table" describes where they come from).
- **`ireg_boot` is untouched between the era fupd and fsinit**, since
  `userinit` uses `RootL`. Main only carries it.
- This ordering is upstream xv6's own: `userinit` sets `p->cwd = namei("/")`
  before `forkret` ever calls `fsinit`, so the root is cached before the orphan
  sweep in the C too. `RootL` and `ireg_read_blk` exist for exactly that.

## Staging

1. **The `_at` refactors** — `newlock_at` (a ten-line split of
   `newlock_delayed`, whose ghost step is one `own_alloc` of an `excl_auth`),
   `bio_init_at`, `icache_boot_at`, `ireg_alloc_at`, `SpecInitlog` at
   `icfg_log`, expose `fs_boot_ghosts`. Additive, no contract changes meaning,
   independent of every ruling above, parallelizable.
2. **Shrink `fscfg`** (R1) — **DONE, whole lane green.** `fscfg` is **16**
   fields. `fs_ready`/`fs_ready_pre` carry the disk fabric as ONE conjunct,
   `∃ pd pav pu, disk_geom fsc_disk pd pav pu ∗ is_lock fsc_dlock d_lock
   "virtio_disk" (disk_res fsc_disk pd pav pu)` (20 / 19 conjuncts). New
   recovery lemma `FsReady.disk_geom_agree`. The three ties reached
   `FsSyscalls.fs_world` and `ProofSyscall.sysc_ties` (`sct_pd`/`sct_pav`/
   `sct_pu`) — NOT a design stop: each bundle keeps its `pd pav pu`
   parameters and now carries `disk_geom` + the virtio `is_lock` at the
   caller's own three as RESOURCES where the three ⌜⌝ equations used to be.
   `fs_world_all`/`sysc_fs_env_all`'s statements are byte-identical, so all
   eleven syscall arms and both friendly wrappers are untouched; a producer
   discharges the new rows by unpacking `fs_ready`'s existential and building
   its own `fn`/parameters at the witness, and `disk_geom_agree` goes the
   other way, so the two spellings are interderivable. `fs_world_ready`'s
   `⊣⊢` split into `fs_world_ready` (⊢, `pd pav pu` universal) and
   `fs_ready_world` (⊢ ∃). One tactic casualty: `sct_dlock` had to leave
   `sysc_fs_env_all`'s blanket rewrite chain — `fsc_dlock` no longer occurs
   anywhere in that goal. `adequacy_fscfg` lost three `mword_of_int 0` args.
   Instantiate the geometry fields (R2) — still open.
3. **`FsCfgBoot.fs_cfg_alloc`**, wired into `boot_shared_alloc`.
4. **Restate adequacy**, delete the two `Local Instance`s. Do this WITH 3, not
   later — it is what makes the boot cone's assumption non-vacuous.
5. **5a** `icache_boot_at` at main+0x92 → discharges `LinkNameiRootBoot`'s
   `Axiom`. **5b** `bio_init_at`, the `newlock_at`s, deposit `fs_kit_fsinit`
   through `SpecUserinit`.
6. **Transport + seal**: widen `first_tok`, publish the persistent half in
   `main_deposit`, `fs_ready_establish` at fsinit's return in forkret's first
   arm — the IOU `design/fs-ghost-state.md` §7d records.

## Acceptance criterion

`make audit-only` goes from EIGHT entries to SEVEN. The baseline is the five
Sail platform axioms (`valid_reservation`, `plat_term_write`,
`match_reservation`, `load_reservation`, `cancel_reservation`),
`functional_extensionality_dep`,
`LinkNameiRootBoot.NameiRootBoot.wp_namei_root_boot` (LEAVES) and
`LinkForkretPark.ForkretPark.forkret_park` (STAYS).

## Scout verdicts (2026-08-20) — the three opens, sized

- **`fs_cfg_alloc` goes INSIDE `boot_shared_alloc` (R6a).** Audited twice
  (source chase + coqtop `About` on the compiled sections): NOTHING in
  `BootShared.v` uses `fileG` — all three binders are dead (`boot_bss_carve`
  captures only `riscvGS/fdslotG/irefslotG`; `boot_shared_alloc` captures no
  `fileG`). So the new instance lands in the existing existential row, exactly
  like `fdslotG`/`irefslotG`/`pavG` (`iExists Hfd, Hir, Hpav, …` at `:1183`,
  destructed at `SystemAdequacy.v:142` before the chain arms — which ARE the
  genuine `fileG` consumers). One missing piece: **no `fileGpreS` exists**;
  the class's only constructors are `subG_fileΣ` (which requires ambient
  `icfg`/`fscfg` — the divergence engine) or a binder. So stage 3 adds a
  camera-only `fileGpreS Σ := { file_preG : inG Σ fileUR }` beside the class,
  `subG` instance included, and `fs_cfg_alloc` builds `FileG _ ICFG FSC` from
  it. Comment drift to cut when there: `BootShared.v:732-733` ("capacity
  only") and `:794-798` = `SystemAdequacy.v:126-131` ("fileG carries icacheG"
  — stale since `icacheG` moved to `xv6G`).
- **`ireg_alloc`/`ipool_alloc` need NO `_at` forms.** They run inside the era
  fupd BEFORE the `FSC` record is assembled, so `γi`/`dss` are ordinary
  in-fupd existentials and `fsc_ireg := γi`; apply them explicitly at the
  freshly-minted `ICFG` instance. The `_at` discipline is only for the
  WP-time constructors: `bio_init` (binit's post), `icache_boot` (after
  iinit), `newlock` (kmem/virtio/itable/pr), `initlog` (forkret). Stage 1
  shrinks accordingly.
- **The `fsc_ic` ordering wrinkle dissolves.** `ic_names_alloc`'s `dvs`
  (per-slot dev/inum words, readable only at `icache_boot` time) looked like
  it blocked minting `fsc_ic` at the era: it does not. `ic_id` is a plain
  `ghost_var` (`IcacheEscrow.v:382`) and `ic_id_flip` (`:404`) updates both
  halves to ANY value. The era fupd mints `fsc_ic` at dummy dev/inum;
  `icache_boot_at` takes the families at whatever recorded values and flips
  `ic_id` to what it reads. No image premise.
- **`mn_grp_fs` is better-conditioned than feared**: it already contains a
  mid-walk ghost interlude at exactly the needed spot (`disk_res_boot` +
  `iMod newlock` at mask ⊤, `ProofMain.v:1346-1351`, between +0x9a's return
  and +0x9e); the new steps copy that idiom after `+0x92`'s return. 257
  lines, 26 wand premises; the group applies the weak `SpecUserinit.USERINIT`
  and already carries the counted regimes to the call site.
- **`first_tok` is wired to NOTHING today** — no producer, no consumer
  (`grep`: only FirstTok.v itself + one comment; forkret's proven arm takes
  the raw `first_addr ↦₄□ 0` cell instead, `SpecForkret.v:230`). Widening the
  left disjunct therefore ripples into zero existing proofs.
- **`initlog`'s existential exits through a WP continuation**, so its `_at`
  conversion lands on SpecInitlog's post (`∃ γ, log_ctx γ …` becomes
  `log_ctx icfg_log …` + free-state `own` premises for the four gnames) and
  on ProofInitlog's internal mint — and `SpecFsinit`'s post must then speak
  `icfg_log` too, or the seal site cannot form `fs_ready`. `wp_fsinit_sconf`
  has no consumer yet, so the reshape is cheap now.
- Stale counts, corrected here so nobody re-trusts them: `fscfg` was **19**
  fields (not 18) and is **16** since R1 landed; `fs_ready` was **21**
  conjuncts and is **20** since R1 merged the two disk rows into one
  existential (fs_geom_ok + fs_sb_cells landed with the dispatcher
  increment). `design/fs-ghost-state.md` §7b still says 18 — refresh it at
  the seal increment.

## Still open

- **A timing probe on ONE `ipool_alloc` bundle before writing the stocking
  lemma.** `ipool_insert`'s own comment measured 106 s for a single bare
  `iFrame` over one `ipool_shape` (`inode_blocks` is a 268-element big-op per
  inode), and `fsimg_wf_ok` is ~43 s of `vm_compute`. Stocking `region_inums
  13` = 208 inums (~25 allocated, the rest type-0 and cheap) in one era fupd is
  the biggest proof-performance risk here, and it lands on the serial build
  tail. Never `iFrame` an `ipool_shape` — split and `iExact`; keep the per-inum
  discharge behind a named lemma so the big-op is built by induction and never
  unfolded at the fupd's altitude.

## Do not

- Thread the configuration as pure premises — tried and REVERTED
  ([`main-boot.md`](main-boot.md) §G3): nothing at the far end can discharge
  `icfg_dev = ROOTDEV`, because `icfg` arrives behind `subG_fileΣ`'s `Qed`.
  `reflexivity` fails; `vm_compute` does not fail, it grinds for fifteen
  minutes.
- Split `icache_boot` INTERNALLY to publish `ic_escrows` + the sleeplocks early
  at an existential `cn` while deferring the itable `newlock` — `itable_res2`
  contains the pool and `is_itable2` is `newlock` over it, so the early half
  hands a client a `cn` with nothing to use it on. (Running the whole fupd
  EARLIER, at main+0x92, is a different thing and is what this plan does.)
- Keep late names existential behind a "config agreement" ghost. You can
  allocate a `to_agree` of the eventual record early, but you still cannot
  WRITE `is_lock fsc_dlock …` before the value exists, so `fs_ready` stays
  unstatable. Eager minting is the only route.
