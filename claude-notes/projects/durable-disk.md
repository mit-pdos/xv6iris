# durable-disk — HANDOFF WORKLIST (written 2026-08-25 for a fresh session)

Design of record: [`../design/durable-fs-plan.md`](../design/durable-fs-plan.md)
— read it FIRST, in full; everything below cites its sections.  The
predicate itself: [`../design/fs-state.md`](../design/fs-state.md) §0–§2
and §7.  History (three days of rulings, refutations and lane reports —
do NOT re-derive them): [`../completed/durable-disk-2026-08-23-to-25.md`](../completed/durable-disk-2026-08-23-to-25.md).
Tree at handoff: `main` at the commit that lands this file; VM-green;
`make audit-only` at the three-entry baseline (`xv6iris_extras.resv_matches`,
`resv_is_valid`, `functional_extensionality_dep`); ZERO placeholder
lemmas tree-wide.

**Goal (owner):** xv6 correctness across crashes INCLUDING file-system
consistency.  `SystemAdequacy.xv6_power_adequacy` is vacuous today (its
`Himg` premise is refutable); it becomes true when the durable snapshot
carries the file system across eras and `Himg` is deleted (lane E).

## Working rules (keep; they proved out)

- Design pinned here before a lane launches; execution on Opus agents
  in ISOLATED WORKTREES (`remote-build-gcp.md`'s worktree recipe; never
  `pkill -f` on the shared VM; the stale-`.vo` loop: VM worktree build
  once, then `run-on-gcp --pull-vo` + local single-file `coqc`).
- Linearize lane commits onto `main` (cherry-pick, no merge commits);
  build the MERGED tree on the VM (`QUIET=1 ./gcp-rocq/run-on-gcp make -k
  -j 192`) + `make audit-only` BEFORE every push; grep the build log for
  plain `Error` (the `File …`/`Error:` pair spans two lines); check the
  push succeeded before assuming green is upstream.  Push EVERY green
  checkpoint and every notes change immediately (owner rule).
- Upstream moves under you (nightly dead-import sweeps, conformance
  fixes, `XV6_REV` bumps): rebase, and if the incoming commit touches
  `iris/`, rebuild before pushing; a sweep that removed an import a
  cherry-picked lane needs is fixed by restoring the import.
- No gate lemmas, no `True` bodies with placeholder lemmas, no premises
  nobody can discharge.  A lane that cannot reach green STOPS at its
  last green commit and reports the wall with a minimal Coq witness —
  that is a result.  Every hedged/quantified conjunct gets a non-vacuity
  witness AT THE REAL INSTANCE (plan §7).
- LOCAL REASONING (fs-state.md §0): no lemma above one inode states a
  pure fact about more than one inode, except the ONE sanctioned
  used-set clause of `snap_bytes` (plan §4a).  "Geometry gunk" is
  tolerated only where the plan names it.
- The traps in `durable-notes.md` (Typeclasses Opaque for big_sepL
  behind definitions; capacity classes must be `Require Import`ed;
  inline `ltac:(solve_ndisj)` breaks when a fupd's post grows; the
  `orb`-both-arms vm_compute rule; `injection` on `Some (bm_bytes …)`
  hangs — `apply (inj Some)`; spell `@bool_decide_eq_true_2 P _ H`).

## What is LANDED (do not rebuild)

- **The log's contract (stage 1).** Custody at birth (`FsCrash.P_fs_swap`,
  `LogDefs.log_mirror_born`); row (b) proven and consumed
  (`LogInv.log_mirror_tie_body`, `_deposit`); the commit permit
  `FsCrash.fs_commit_L_sector0_rec`/`_seq_permit` concluding at the
  logged view; byte-keyed exclusive `fs_L`
  (`FsBlocks.fsblock`/`byte_range`, `fs_bytes_inv` at `logN`,
  `byte_range_log_update`); `SpecLogWrite.wp_log_write_au_range` with the
  block-local tie; the parked payload `Ψ D₀ Dc` in `log_state` and the
  laws `log_psi_commit`/`log_psi_step`/`log_psi_write` (TO BE REPLACED,
  lane B); `end_op` has NO FS-facing premise.
- **The predicate (stage 2a):** `iris/FsState{Defs,Link,Inode,Bitmap,Era}.v`,
  `FsState.v`, `FsBytesGamma.v`, the movers, `fs_boot_alloc_at`/
  `fs_links_full_alloc`, the dirent-insert equation (`FsTree.dir_view_insert`).
- **The era instance (stage 2b), all four legs:** bitmap = `free_bitmap_at`
  (`blk_own` gone); region records byte-granular (`ireg_recs`; ruling
  (i): records park region-side, `dinode_at` is the holder's proxy);
  payload = `inode_owned_era` in `ic_loaded`/`ipool_alloc` (boot mints the
  image's node map, `ftop_inv` at `ftopN`); links = the counting RA in
  the region (`ireg_lnk`) with tokens in the payload (`dlinks` →
  `ent_toks`), boot validity free, root's self-record exemption.
- **The durable side (lanes 4, 4b):** `iris/FsDurSnap.v` — `fs_snap_alloc`
  (the allocator-transport, Γ-generic core `fs_state_of_ledger`),
  `P_dur D`, `dsnap_step_of`, `snap_ok = snap_bytes ∧ snap_local` with
  the used-set coupling and the local frame (`snap_bytes_frame`,
  `snap_untouched_of_free/_of_own`), encoder injectivity
  (`dinode_bytes_inj`, `rec_in_blk_inj`, `snap_bytes_node_inj`), the spike
  readings (`P_dur_node_of_slot`, `snap_dir_entry_of_first`).
  `iris/FsDurBytes.v` (the byte-map flattening), `iris/FsDurImg.v` (the
  image instance; adapt to `snap_ok`), `iris/FsDurLedger.v` (entry
  constructors — era-side content; its fold is superseded).
- **Refutations kept as documentation:** `iris/FsDurRefute.v`,
  `iris/FsDurDefer.v`; `FsDurWire.v` is the rejected kinds tie (delete
  in lane C).
- Image checks (14) `fs_region_bare` and (15) `fs_root_no_self` in
  `FsImg`/`FsImgCheck` (not yet wired into `fs_boot_image_wf`; taken as
  premises by `FsDurImg`).
- The demolition of the old link ledger: slice 6a only (the root clause).

## STILL PRESENT BUT SUPERSEDED (delete when their consumers move)

`FsDurWire.v`'s `P_wf_dec`/`Psi_dec`/`kinds_of_state`/`dwire_geom`/`psi_*`;
`LogInv.log_psi_commit`/`_step`/`_write`/`_write_rebase`/`_spend`;
`LogDefs.fs_dstep`/`fs_dstep_rebase`/`fs_dview` as `P_fs`'s durable slot
(`FsCrash.P_fs` still holds `ghost_map_auth γv 1 (fs_dbytes (fr_D r)) ∗
fs_dview γv …`); `RiscvPtsto.fs_dur_names`' `fdn_bmap/ist/nin` and
`riscv_dview_name`; the nine suppliers' `log_psi_write_rebase` lines
(`ProofBfree:651`, `ProofBmap:1961`, `ProofBalloc:1910/:2353`,
`ProofIupdate:1999`, `ProofIalloc:1471`, `ProofIput:1787`,
`ProofWritei:3130/:3664` — line numbers at handoff);
`ProofInitlog`'s `Ψ := fs_dstep …` witness (`:2587`, `:2711`).
Preserved patches in the session scratchpad are NOT needed; everything
reusable is on `main`.

## The lanes, in order (each is one green checkpoint; specs cite the plan)

- [ ] **Lane A — transactions and the locked registry (plan §3, §4b).**
  1. `γtx`: an authority of open transaction ids in `LogInv.log_state`
     (beside `op_entry`); `begin_op` allocates `t` and puts `t ↪[γtx] ()`
     INSIDE `log_op`'s existential closure (`log_op γ u = ∃ … t, t ↪ () ∗
     …`); `end_op` consumes the FULL share and deletes `t`
     (`ProofEndOp`/`SpecEndOp`; the token stays closed — no naming).
     While a lock is held the token carries `t ↪{½} ()`: define the
     fractional form and thread it through contracts that span a held
     lock (`create` → `sys_open`/`sys_mkdir`/`sys_mknod`, `dirlink`,
     `iunlockput` callers …) — measure the footprint first (grep
     `log_op`, `log_opS`, `log_opSe`).
  2. The LOCKED REGISTRY in `InodeRegion.ftop_inv` (`ftopN`): authority
     `LOCKED : gmap Z (option gname-or-id)`; for each `Some t` entry the
     registry holds `t ↪{½} ()`; the pure row "∀ i, LOCKED !! i ∈ {None,
     absent} → the node at i (off the `γtop_L` authority) satisfies
     `inode_local`" — i.e. `FsDurSnap.snap_local` restricted.
  3. ONE `ilock` spec (`SpecIlock*`/the fill in `ProofIlock*`): optional
     transaction share in; registers `Some t` (parks the half) or `None`;
     returns the receipt `i ↦ …`.  `iunlock`: deposits clean (already
     proven), deletes the entry, returns the half.
  4. The write lemmas require the `Some t` receipt: `InodeRegion.ireg_write_*`,
     `ireg_claim_au` (ialloc — the claim is under the region's own
     serialization; decide what it registers), `EscrowDeposit.ireg_free_deposit_au`,
     the data-block accessors used by `writei`/`bmap`/`itrunc`.
  5. The commit-side consequence as a lemma: `γtx` empty ⊢ `dom LOCKED`
     has no `Some` entries ⊢ `snap_local` of the current state.
  6. Green; note the fractional-token footprint as landed.
- [ ] **Lane B — the payload becomes the bytes-match fact (plan §4a).**
  `Ψ D₀ Dc := ⌜∃ S, snap_bytes S Dc ∧ ⟨S's inodes = γtop_L's map; used set
  = the bitmap invariant's; sb = the config's⟩⌝`; `SpecLogWrite`'s
  payload premise becomes this pure step, discharged by each of the nine
  suppliers from its splice fact (`snap_bytes_frame` + `snap_untouched_of_own`;
  adoption via `snap_untouched_of_free` off the bitmap AU); the
  `log_psi_*` laws die; `ProofInitlog` parks the boot payload off `P_dur`'s
  own `snap_ok`.  Per-supplier: `bm` writes (balloc ×2, bfree), data
  writes (bzero, bmap-indirect, writei ×2), record writes (ialloc,
  iupdate, iput).
- [ ] **Lane C — `P_fs`'s durable slot and the commit (plan §3 commit).**
  `P_fs`'s durable conjunct → `P_dur (fr_D r)` (arity-free); both commit
  permits: fr_D advance + `dsnap_step_of` at `snap_ok S_L (lm_logged L)`
  = lane B's payload ∧ lane A's item 5, with the allocator inside the
  permit (a bupd); receipt gains the snapshot's state; `P_fs_alloc` via
  `FsDurImg` at `snap_ok` for the image (coupling from W3/W4/W5,
  `sk_links` from `img_link_valid`; the (14)/(15) premises through
  `SystemAdequacy` off `FsImgCheck`); timelessness; DELETE the superseded
  families (previous section) incl. `fdn_*`/`riscv_dview_name`.
- [ ] **Lane D — the spike theorem (plan §5).**  `ProofSysMknod` keeps
  `create`'s `made` clause (today discarded at its `iDestruct`, ~`:1690`);
  prove `mknod_durable` off the snapshot; quote it here.  Then the
  other arms are the same pattern (unlink/rmdir/link/write) — schedule
  by value.
- [ ] **Lane E — boot and the theorem (plan §5).**  Stage 4: the era's
  instance minted from the current snapshot by `fs_state_of_ledger` +
  the era-only extras, distributed into region/bitmap/escrow/pool
  (`fs_cfg_alloc`, `FsBoot`, `BootShared` lose every image premise;
  `image_dinode_fs_dinode` disappears); wire (14)/(15) into
  `fs_boot_image_wf` or retire that predicate to era 0; the `Pdur`
  parameter on `riscv_power_adequacy` (3b''s finding: any boot-time fact
  about the durable bundle needs it); then Stage I: delete `Himg`/
  `fs_boot_image_eras`/`fsimg_at_every_era`; adequacy assumes era 0's
  image only.  Definition of done: the boot mint CONSUMES the snapshot.
- [ ] **Lane F — strengthening and receipts.**  Persistent snapshot
  copies as sync-style receipts (`sys_sync`'s spec — see the fs-syscall
  notes another session landed); the `P_log`/`P_fs` split as two
  ordinary invariants if wanted (the crash predicate slims to the WAL's
  half; `P_fs` an `inv` over immortal gnames); any further local clauses.
- [ ] **Lane G — cleanups (independent, run in the gaps).**  The
  demolition slices 6b–6f of the old link ledger (`DirLinks.v` 2009
  lines, `IcacheRef`'s five columns, `IregLinkNz.v`, the `fl` index,
  `FsRep.fedges`; 6c's rmdir question "`2 ≤ nlink dp` has no token-side
  reading a walk can reach" needs a design answer first); the
  `eo_minst`/`lm_install` unification; the lemma relocations 2c-img
  listed; `fs_boot_bundle` (no callers); `SpecBfree`'s two dead premises
  are already gone.

## Sizing notes for whoever runs the lanes

- Big cones: `ProofEndOp` (commit path), `ProofInitlog` (2748 lines —
  size its boot pack FIRST in lane C), `ProofSysUnlink`/`ProofSysLink`
  (carry the payload FLAT — price at their flat lists), `InodeRegion`
  (5100 lines).  Per-file < 5 min; split rather than push through.
- `log_ctx` is named in ~75 files, `log_op` in 62, `wp_end_op` at 53 call
  sites, `fs_crash_seam` in 90: anything that changes their ARITY is a
  tree-wide sweep; prefer existential closure / ambient fixed-layer
  names (`riscvGS` sections) / persistent conjuncts, as every landed
  lane did.
- `git worktree list` should show only the main checkout between lanes;
  remove finished lanes' worktrees and branches after cherry-picking.
