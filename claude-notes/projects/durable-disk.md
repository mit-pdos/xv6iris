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
  used-set clauses of `snap_bytes` (plan §4: read off the ∗ at commit, off the snapshot at boot).  "Geometry gunk" is
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
  block-local tie; `end_op` has NO FS-facing premise, and neither
  `log_state` nor `log_ctx` carries a file-system payload at all (lane C).
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
  Lane 4c as landed: the durable byte points-to is EXCLUSIVE
  (`snap_gamma_excl` is `phi_excl`, so `free_pool_used`/`blk_owned_ne`
  read on the durable side too), and the core takes a LINEAR ledger —
  `blk_ledger_cut` names the footprint slot by slot (`fp_slot`/`fp_list`)
  and `ledger_carve` spends it, the disjointness coming from the used-set
  coupling plus three per-object clauses at the END of `snap_bytes`
  (`sk_sbok`, `sk_reg`, `sk_slot` = `FsImg.fs_slot_inj`), all three
  discharged by `FsDurImg.img_snap_ok` and so witnessed at the literal
  image by `FsAdequacyImg.fsimg_snap_ok`; `fs_state_of_ledger_era` is the
  check that the same core applies at `FsBytesGamma.fs_gamma_L`, which is
  what lane E calls.
- **Refutations kept as documentation:** `iris/FsDurRefute.v`,
  `iris/FsDurDefer.v`, `iris/FsDurTrunc.v` (the per-write accumulation of
  `snap_bytes`' used-set coupling — lane B's finding, plan §4, §8);
  `iris/FsDurQuiesce.v` (lane C's finding: where the era parks its bundles
  is what blocks the collection at quiescence).
- Image checks (14) `fs_region_bare` and (15) `fs_root_no_self` in
  `FsImg`/`FsImgCheck`, and (lane C-img) they are now the LAST two
  conjuncts of `FsCfgBoot.fs_boot_image_wf`, discharged in
  `FsAdequacyImg.fsimg_image_wf` off those two citations.
- **The image's snapshot tie (lane C-img):** `FsDurImg.img_snap_ok`
  (`fs_boot_image_wf` ⊢ `snap_ok (img_state …) (fs_restrict … home)`),
  `img_P_dur_alloc`, `img_boot_P_fs_dur` (the boot point, `P_fs_alloc_clean`
  plus `P_dur` at the same `D0`), witnessed at the literal image by
  `FsAdequacyImg.fsimg_snap_ok`.
- The demolition of the old link ledger: slice 6a only (the root clause).

## STILL PRESENT BUT SUPERSEDED (delete when their consumers move)

`LogDefs.fs_dview` as `P_fs`'s durable slot (`FsCrash.P_fs` still holds
`ghost_map_auth γv 1 (fs_dbytes (fr_D r)) ∗ fs_dview γv …`, and the commit
permits still re-base it themselves); `RiscvPtsto.fs_dur_names`'
`fdn_bmap/ist/nin` and `riscv_dview_name`, with `RiscvAdequacy`/
`SystemAdequacy`'s `Pc` arguments and `FsDurLedger`'s geometry equations
as their remaining consumers.

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

  **AS LANDED.**  Item 1 is `LogInv.log_tx γ = ∃ t, t ↪[ln_tx γ] ()` inside
  `log_op γ u = log_opb γ u ∗ log_tx γ`; `begin_op` mints, `end_op` consumes
  the whole element, and the tie to the ledger is CARDINALITY (`log_res`
  carries `size T = size om`; `log_tx_empty_of_ops` reads it at zero) — a
  retiring transaction never names its id, and nothing needs it to.  The bill
  was the ~85 `log_op`↔`log_opS` conversions (59 `log_opS_op`, 24
  `log_op_openS`) and the eleven walk-stage lemmas spanning
  `begin_op..end_op`; `SpecLogWrite`/`SpecBfree`/`SpecItrunc`/`SpecWritei` and
  the loop shapes are byte-stable on `log_opb`.  THE TOKEN IS NEVER
  FRACTIONAL — item 2's shape removed the need.

  THE REGISTRY IS KEYED BY TRANSACTION, not by inum: `icfg_lk : gmap nat
  (gset Z)` as the LAST conjuncts of `InodeRegion.ftop_body`, beside the
  parked `ln_tx` elements of the armed transactions and the pure row
  `ftop_clean I A` ("every inum the map names and no armed transaction names
  is `inode_local`").  The `inum → option txid` shape does not close: an arm
  keyed by inum must prove its key free, which is the inode LOCK's property
  and invisible at `ftopN`, and one transaction holding two inodes needs two
  halves of one token that then cannot come back whole.  Keyed by transaction
  both vanish — the entry parks the arming transaction's WHOLE token, so a
  walk still holding it is provably unregistered (`ghost_map_elem_ne` on two
  whole elements), and the receipt `ireg_armed t S` names a SET
  (`ireg_arm`, `ireg_arm_more`, `ireg_disarm`, `ireg_release`).

  ITEM 3'S ONE `ilock` SPEC DID NOT LAND AND IS NOT WANTED: registration is
  not at the lock.  The row's whole cost is one premise on
  `ireg_top_retag` — the ONE mover of the abstract map, 17 sites in 10
  files — namely `inode_local i n'`, free at sixteen of them
  (`FsStateEra.inode_local_of_ok_rec` off the four facts the site's
  `ic_loaded`/`inode_owned_era` re-pack already names).  The seventeenth is
  create's mkdir child, the ONE mid-transaction ill-formed state this kernel
  produces (a directory with a link count and no dots): create ARMS at the
  `ip->nlink = 1` flush, rides the window on `cr_dirty` / `cr_dirty_retag`
  (`ireg_top_retag_armed`), and CLEARS at each of its four exits
  (`cr_dirty_clear` = retag + `ireg_disarm` + `ireg_release`) — the FILE arm
  at once, the mkdir success at the dots, the two mkdir failures at the
  `nlink = 0` flush that orphans the child.  `SpecCreate.wp_create_sconf_body`
  gains `log_tx γ` in and out; its three callers (`sys_open`, `sys_mkdir`,
  `sys_mknod`) cost one line each.  `log_ctx`, `fs_crash_seam` and
  `wp_end_op` are untouched.

  ITEM 4 IS REFUTED AS STATED AND IS NOT NEEDED.  A `Some t` receipt on
  `ireg_write_*` (8 files), `ireg_claim_au` (18) or `ireg_free_deposit_au` (9)
  would demand of every writer a resource only an ARMING walk holds, and
  arming means "my inode is briefly ill-formed", not "I hold the write lock".
  What it was for is already enforced: `ireg_write_au` takes `dinode_at`, the
  EXCLUSIVE per-inum record proxy `ilock` withdraws and `iunlock` deposits, so
  a read-locker cannot move a record; and a data block needs its byte elements
  at full fraction, which lane B′ makes literal by handing a read-locker ¼.

  Item 5 is `IregClean.ireg_snap_local_acc` (and `_of_ops`, the same off the
  ledger through `log_tx_empty_of_ops`) in its OWN file, because `snap_local`
  is `FsDurSnap`'s and the registry is `InodeRegion`'s and neither is on the
  other's cone.  It borrows the `ln_tx` authority and hands the map's
  authority straight back, so it moves NO resource — which is what lets the
  commit take it at its own ghost step.  Checked with coqdep at the real
  import: `ProofEndOp` and `IregClean` are on neither's cone, so lane C's
  `Require Import IregClean` is acyclic (+13 files to `ProofEndOp`'s cone).

  BOOT: `ftop_alloc` takes the row and the empty registry authority;
  `FsCfgBoot.img_nodes_local` proves it off conjunct (14) `fs_region_bare`
  (a garbage type-0 record would break `inl_size`/`inl_covers`), so
  `fs_cfg_alloc` gained that ONE premise and `BootShared` passes the name it
  already destructures.  `FsDurImg`'s section 2 (`img_node_rec`/`_ent`/`_blk`,
  `img_node_bare`, `img_inode_local_free`/`_ok_at`/`_local_live`/`_local`)
  MOVED to `FsCfgBoot`, which sits below it and is where the row is
  established; `FsDurImg` consumes them through its import as before.

  FOR LANE B′ (measured here): the fraction cannot stop at
  `FsStateEra.inode_owned_era`.  Its byte legs are `FsStateDefs.blk_owned` and
  `FsStateInode.ind_owned` over `FsStateDefs.byte_range`/`fsΦ` — the SAME
  definitions the DURABLE side uses at dfrac 1 — so `fsΦ` takes a dfrac and
  `byte_range`/`blk_owned`/`ind_owned`/`inode_owned_era` become
  fraction-indexed with 1 as today's reading.  The real cost is
  `FsStateDefs.phi_excl`, the class lane 4c's `blk_owned_excl`/`blk_owned_ne`/
  `free_pool_used` and the commit's cross-inode disjointness all read: it
  becomes a fraction-aware law, and that is what forces the reader's share to
  ¼ (¾ + ¾ > 1).  Era-side consumers to sweep: `FsStateEra` 11,
  `IcacheEscrow` 11, `FsStateInode` 10, `FsStateDefs` 7, `FsState` 4,
  `ProofIlock` 4, `IcacheBoot` 3, `InodeRegion` 3; the durable side
  (`FsDurBytes`/`FsDurImg`/`FsDurObj`/`FsDurSnap`/`FsDurLedger`/
  `FsStateBitmap`, ~75 uses) stays at 1 and does not move if the index
  defaults.  `ilock` today still withdraws the whole bundle and registers
  nothing; B′ is where `ic_out` splits into "out for reading at ¼" and "out
  for writing".
- [x] **Lane B — CLOSED BY REFUTATION** (`iris/FsDurTrunc.v`): the
  per-write accumulation of `snap_bytes` as the WAL's payload has no
  witness at `bfree`'s `log_write` (`itrunc`'s window) and `sk_disj` dies
  at the record writers; plan §4 and §8 record the ruling that replaced
  it (collection at quiescence).  Nothing else of the original item is
  wanted; `LogInv.log_psi_*` and the nine `log_psi_write_rebase` lines are
  deleted by lane C.
- [ ] **Lane B′ — fraction-indexed inode bundles (plan §4, §6).**  The
  bundle's byte elements (`FsStateEra.inode_owned_era` → `blk_owned` at
  `fs_gamma_L`, today dfrac 1) become fraction-indexed; `ilock` without a
  transaction withdraws ¼ and the escrow keeps ¾ plus the rest of the
  bundle (`ic_out` becomes "out for reading at ¼" vs "out for writing");
  a transactional `ilock` withdraws everything; `iunlock` returns the
  matching share.  Readers (`readi`, `stati`, `dirlookup`) are proven at
  ¼: measure the data-block accessor footprint first.  Green + audit.

  **AS LANDED — THE PREDICATE HALF ONLY.**  `FsStateDefs.fsΦ` takes a
  leading `dfrac`, and the block shapes gained `_q` forms
  (`byte_range_q`, `blk_owned_q`, `FsStateInode.ind_owned_q`,
  `FsStateEra.inode_owned_era_q` and its byte-legs-only `inode_bytes_era`).
  THE UNSUFFIXED NAMES DID NOT MOVE: `byte_range`/`blk_owned`/`ind_owned`/
  `inode_owned_era` are still written exactly as they were, as the
  `DfracOwn 1` READINGS, which is what keeps the durable side
  (`FsDurBytes`/`FsDurImg`/`FsDurObj`/`FsDurSnap`/`FsDurLedger`/
  `FsStateBitmap`, ~75 uses) and `fs_state_of_ledger` textually unchanged —
  the only durable-side edits are the ten places naming the FIELD `fsΦ`
  and the three `MkFsView` constructions.  Measured before choosing: the
  alternative (a dfrac argument on the unsuffixed names) is ~75 durable
  edits plus ~40 era-side; a `q`-indexed `Γ` needs `fsΦ` to take the dfrac
  anyway and adds a redundant second mechanism.

  `phi_excl` is now `fsΦ dq1 a v ∗ fsΦ dq2 a w ⊢ ⌜✓ (dq1 ⋅ dq2)⌝`, with
  `byte_range_excl`/`blk_owned_excl`/`blk_owned_ne`/`free_pool_used`
  unchanged in statement (their `1 ⋅ 1` readings) and the two
  specialisations the plan names: `blk_owned_ne_full` (1 against ANY share
  — the resource reading of "a read-locker cannot write", since
  `SpecLogWrite.wp_log_write_au_range` needs fraction 1) and
  `blk_owned_ne_34` (¾ against ¾, off `dfrac_34_nvalid`), which is what
  lane C's collection reads between two read-locked inodes.
  `FsStateBitmap.free_pool_used_q` is the pool refutation at any share.
  The splitting law is the new parameter `phi_frac` (the `Fractional` law,
  witnessed at the era instance by `FsBytesGamma.fs_gamma_L_frac`; the
  durable instances never split).  The escrow's arithmetic is
  `FsStateEra.inode_owned_era_shed`: the bundle at 1 IS the bundle at ¾
  beside the reader's quarter of the byte legs, both ways.  Era-side
  readings at a share: `inode_owned_era_q_slot_inj` (hence
  `inode_owned_era_34_slot_inj`), `inode_owned_era_q_local`, and the
  read-only borrows `inode_owned_era_q_blk_read` /
  `inode_bytes_era_blk_read`.

  **THE ESCROW ARMS AND THE ONE `ilock` SPEC DID NOT LAND, AND THE WRITE
  ARM IS REFUTED AS SPECIFIED** (`iris/IcacheTxRefute.v`, compiled).
  Parking a FRACTION of `LogInv.log_tx` in the checked-out entry cannot be
  undone at `iunlock`: `log_tx γ = ∃ t, t ↪[ln_tx γ] ()` closes the id
  existentially (lane A did that on purpose — the ledger tie is
  cardinality), so an arm holding a share binds its own `t`, the holder
  holds its residue at ITS `t`, and two ghost-map elements at different
  keys are consistent — `tx_two_halves_no_whole` exhibits the reachable
  two-transaction state that satisfies the arm's predicate twice and
  contains no whole token at any id.  Lane A met the same trap at the
  registry and keyed it by TRANSACTION; the escrow cannot copy that,
  because it is keyed by cache SLOT and `create` holds two slots inside
  one transaction.  THE CHEAPEST FIX, and the recommendation: widen
  `Xv6Cameras.ic_dep` with a write-checkout constructor
  `DepTx (s : Qp) (dev inum) (g : gname) (t : nat) (q : Qp)` — the
  `ic_deposit` ghost_var already pins the checkout's fraction, device and
  inum between arm and holder, so it pins `(t, q)` for free; it is
  ADDITIVE (the ~66 `DepShr` sites in 23 files do not move) and costs the
  ten `match d with` sites plus the writers' checkout/park.

  WHAT THE NEXT INCREMENT MUST DO FIRST, and it is structural: the bridge
  `FsBytesGamma.gamma_blk_owned` ties `blk_owned` to `FsBlocks.fsblock`
  AT FRACTION 1 ONLY, and `FsStateEra.inode_owned_era_of`/`_to` (the
  conversion `ic_loaded` and `ipool_alloc` are stated through) go through
  it.  So NOTHING at ¾ or ¼ can cross into the `InodeInv` vocabulary today:
  the escrow's read arm and `readi` at ¼ both need `FsBlocks.fsblock_q`
  and the `InodeInv` shapes over it before either can be written.  The
  same `_q`-twin-plus-fraction-1-reading shape this lane used keeps every
  existing site textually unchanged (`k ↪[γ] v` IS `k ↪[γ]{DfracOwn 1} v`,
  so each `X = X_q … 1` equation is `reflexivity`), which is what makes
  the ~106 `rewrite /byte_range`-style unfold sites cost nothing.

  **THE TWO PLACEMENT FACTS LANE C ASKED FOR.**  (1) LANDED: the fifty
  entry escrows are at `icEscN .@ k`, one namespace each, so the commit can
  hold them all open at one ghost step (`ic_escrow_ns_disjoint`,
  `ic_escrow_ns_sub`); no contract's arity moved and `↑icEscN` still covers
  the family, so only the twenty-one masks written INSIDE an escrow opening
  changed, each to the slot it already names.  (2) NOT LANDED, and the
  obstruction is checked in the tree
  (`IcacheEscrow.ipool_no_timeless_check`): `ipool` cannot simply move into
  an Iris invariant, because `inv N P` hands its opener `▷ P`, both
  consumers (iget's miss at the `+0x72` store, iput's two evictions) spend
  the bundle inside an ATOMIC UPDATE with no step to absorb a later, and
  this tree has no later credits (`RiscvPtsto.num_laters_per_step _ := 0`)
  — while `ipool_shape` is NOT timeless: its pending and await
  alternatives hold `EscrowInode.escA_inv`, an `inv`.  That placement is
  the escrow's own recorded trade ("`esc_inv` (not Timeless) rides the POOL
  side, so this stays Timeless", `IcacheEscrow.v` at `pool_await`), and it
  is what `ic_escrow_body_timeless` — hence every `iInv "Hesc" as ">"` in
  the tree — is built on.

  THE SPLIT THAT DOES WORK, with its enabling fact already proven
  (`IcacheEscrow.ipool_shape_ord_timeless`): the ORDINARY alternative
  (`ipool_shape_np` beside the count half, the freeze-mirror half and
  `ifreeze_off`) IS timeless, and it is the only alternative carrying an
  `inode_owned_era` at all — i.e. the only one the collection wants.  So
  split the pool BY ARM: the ordinary inums into an invariant (timeless
  body, `iInv .. as ">"` keeps working at both consumers), the
  pending/await inums under the itable lock as today, with the lock holding
  the residency key for the invariant's index set as ONE conjunct in
  `ipool`'s old position (so `itable_res2`'s arity and iget's scan-loop
  hypothesis list do not move).  A consumer landing on a pending/await inum
  refutes it exactly where it does today — the licence, `ipool_shape_to_np`'s
  `ifreeze_off` premise and `IcacheRef.ifreeze_excl` — but now in the MAIN
  FLOW, off the lock-held side, with no invariant open and no later in the
  way.  Sites: `IcacheEscrow` (the definitions and `itable_res2`),
  `IcacheBoot` (boot builds the invariant with `Pext = ∅`), `FsCfgBoot`
  (thread the persistent invariant — bundling it into `is_itable2` keeps
  that predicate's arity and leaves its 55 files untouched), `ProofIget`
  (one withdraw plus the case split), `ProofIput` (two deposits),
  `ProofIdup`/`ProofMain` (pass-through).

  FOOTPRINTS MEASURED FOR THE NEXT INCREMENT.  The reader's ¼ needs the
  BLOCK layer fraction-indexed too, not just the predicate:
  `FsBlocks.fsblock` (34 files), `InodeInv.inode_blocks` (35, and
  `Typeclasses Opaque`, so a fraction-1 wrapper does NOT frame through —
  each caller needs one explicit `rewrite`), `blk_res` (6), `inode_map`
  (31); `SpecReadi` takes `inode_blocks` and `inode_map` directly and its
  buffer/bytes tie (`ProofReadiParts.rd_held_content` →
  `fs_bytes_agree_any`) is an AGREEMENT, so it survives any share.  The
  escrow side: `ic_out` is only 4 files / 16 mentions, `ic_loaded` is
  named in 57 files but `rewrite /ic_loaded` in 11, `inode_owned_era` in
  6.  `wp_ilock_sconf` has callers in 20 files, but the TRUE read-lockers
  — the ones with no `log_op` in hand — are exactly two, `ProofFileread`
  and `ProofFilestat`; every other `ilock` caller (`namex`, `create`,
  `sys_open`/`link`/`unlink`/`chdir`, `kexec`, `filewrite`) already holds
  a transaction and keeps the full bundle.

  **AS LANDED — B″-esc: THE POOL SPLIT.  THE WRITE ARM IS A SECOND WALL.**

  THE POOL SPLIT IS DONE, and it is the second of the two escrow-side
  obstructions lane C named.  `IcacheEscrow.ipool_shape` splits BY ARM into
  `ipool_ord` (the count half, the mirror half, the Timeless two-arm
  `ipool_shape_np` and `ifreeze_off` — the only alternative carrying an
  `inode_owned_era`, hence the only one the collection wants) and
  `ipool_ext` (pending / await, not Timeless), tied back to the full shape
  by `ipool_ord_shape` / `ipool_ext_shape` / `ipool_shape_arms`.  The
  ordinary rows live in ONE invariant — `ipool_inv γfs γi cov logstart =
  inv ipoolN (ipool_body …)` at `ipoolN = nroot .@ "ipool"`, body
  `∃ O, ipool_key O ∗ ipool_rows … O`, TIMELESS — so the commit opens it
  once and holds every ordinary bundle beside all fifty slot escrows.  The
  itable lock keeps, in `ipool`'s OWN position and at its own arity, the
  residency key `ipool_key O = ghost_var icfg_pool (1/2) O` plus `⌜O ⊆ P⌝`
  and the in-transition rows over `P ∖ O`; `icfg_pool` is a new ambient
  gname (`IcacheRef.icfg_pool`, `Xv6Cameras.icache_poolG`), allocated WHOLE
  at `∅` by `icfg_alloc`.  So `itable_res2`'s arity, iget's scan-loop
  hypothesis list, and `is_itable2`'s ~55 threading files did not move.

  THE MOVERS HAND OUT AND TAKE BACK THE FULL `ipool_shape`
  (`ipool_take` / `ipool_put`, fupds at any `E ⊇ ↑ipoolN`), which is what
  kept the split invisible below them: `ProofIget`'s recycle still runs
  `ipool_shape_to_np` on what comes out, `ProofIput`'s eviction still
  deposits the ordinary row and its free path still parks the await arm
  (`ipool_put` reads the side off the shape itself).  Each of the three
  sites cost one `iApply fupd_wp` / `iMod` / `iModIntro` wrapper and nothing
  else.  GONE: `ipool_acc`, `ipool_insert`, `ipool_acc_back`.  RENAMED:
  `IcacheBoot.ipool_split` → `ipool_rows_split`.  RE-TYPED (same arity,
  conclusion `ipool_rows`): `IcacheBoot.ipool_shape_free`/`_alloc`/
  `ipool_alloc`/`ipool_alloc_all_free`, `FsCfgBoot.ipool_alloc_of_image` —
  boot stocks ORDINARY rows only.  `IcacheBoot.icache_boot_at` gained the
  whole key beside the rows and is what ALLOCATES the invariant
  (`IcacheEscrow.ipool_alloc_inv`); `FsCfgBoot.fs_kit_icache` /
  `fs_kit_icache_rest` carry the pair.

  THE INVARIANT REACHES ITS CONSUMERS THROUGH `is_itable2`, which now
  BUNDLES `ipool_inv` beside the lock (`is_itable2_lock`, `is_itable2_pool`)
  — arity fixed, threading files untouched; the four files that use it AS a
  lock project.  In `ProofIput` the four internal lemmas' `is_lock gtl
  itable_lock …` premise became `is_itable2 gtl cn …` in the same position,
  so their callers are byte-stable.

  THE COMMIT'S DOOR IS `IcacheEscrow.ipool_inv_acc`: `ipool_inv … ={E,
  E∖↑ipoolN}=∗ ∃ O, ipool_rows … O ∗ (rows ={…}=∗ True)` — read-only, no
  lock, one ghost step.  WHAT LANE C STILL OWES ITSELF: `O` is the
  invariant's own index, and "`O` ∪ the cached inums = the region's inums"
  is `ic_ci_wf` plus `ipool`'s domain, both LOCK-HELD — so the collection
  can now reach every ordinary pooled bundle but cannot yet PROVE it has
  them all.  The cheapest shape for that accounting is a per-inum "checked
  out of the pool" token riding the escrow payload (one conjunct at the END
  of `ic_loaded`/`ic_unloaded`, ~40 payload sites at one edit each by
  durable-notes' last-conjunct rule); `IcacheRef.icnt` nearly does it
  already — the region's half is inside `iregN`, which the commit opens —
  but the uncached halves live on the very rows whose presence is the
  question.

  **THE WRITE ARM IS A SECOND WALL** (`iris/IcacheTxArm.v`, compiled:
  `arm_needs_whole`, `arm_state_reachable`).  B′'s recommended `DepTx` fix
  DOES close the re-identification — the descriptor pins `(t, q)` between
  arm and holder, so `iunlock` recovers exactly what `ilock` parked — but a
  transaction that has PARKED a share of `LogInv.log_tx` can never supply a
  WHOLE element again, and lane A's `InodeRegion.ireg_arm` demands exactly
  that (`A !! t = None` has no other proof than "a parked entry would hold
  this very element").  `create` is xv6's one arming walk and it arms at the
  `ip->nlink = 1` flush with BOTH its parent and its fresh child
  write-locked, so the escrow's write arm and lane A's armed registry are
  mutually exclusive as they stand.  Closing it needs ONE of: (a) lane A's
  registry re-keyed so the arm needs no freshness — a parked SHARE still
  refutes a non-empty registry at an empty `ln_tx` authority, which is all
  `IregClean.ireg_snap_local_acc` reads off it (`InodeRegion` +
  `ProofCreate`); or (b) a second per-transaction ghost minted by `begin_op`
  and consumed by `end_op` (`LogInv` + `ProofBeginOp`/`ProofEndOp`).  Neither
  is this lane's file.  `Xv6Cameras.DepTx` was therefore NOT added: an arm
  nobody can park in is a weakening every escrow opener would have to refute
  for nothing.

  MEASURED WHILE LOOKING, so the next attempt does not re-measure: the
  held-lock ABI the write arm costs is much SMALLER than plan §6 feared.
  The interior contracts already take the tx-free forms — `SpecWritei`,
  `SpecIupdate`, `SpecItrunc`, `SpecDirlink`, `SpecBmap`, `SpecBalloc`,
  `SpecBfree`, `SpecIunlockput` all have `log_opS`/`log_opSe` GEN contracts,
  and `ProofCreate` calls the GEN forms throughout, framing `log_tx` itself
  — so what moves is (i) the `_sconf` corollaries' callers that hold a lock
  and (ii) the five files that name `log_tx` (`SpecCreate`, `ProofCreate`,
  `ProofSysOpen`, `ProofSysUnlink`, `ProofSysLinkTails`).

  ONE `ilock` SPEC: unchanged.  Its read arm is still blocked on the block
  layer's fraction indexing (B′'s structural note) and its write arm on the
  wall above, so `ilock` still withdraws the whole bundle and parks nothing.
  **AS LANDED — THE BLOCK HALF (lane B″-blk).**  The block layer now
  carries a share, in the same shape lane B′ used one level up: `_q` twins
  beside unsuffixed names that DID NOT MOVE and are their `DfracOwn 1`
  readings (`k ↪[γ] v` IS `k ↪[γ]{DfracOwn 1} v`, so every `X_1` equation
  is `reflexivity` and the ~30 files spelling `fsblock` / ~34 spelling
  `inode_blocks` are textually untouched).  `FsBlocks`:
  `byte_range_q`/`fsblock_q`, the fraction-aware exclusivity readings
  (`byte_range_q_valid`, `fsblock_q_excl`/`_q_ne`, plus the two the plan
  names, `fsblock_ne_full` and `fsblock_ne_34`), the splitting laws
  (`byte_range_q_split`, `fsblock_q_split`, `fsblock_split_34`) and the
  SHARE-SIDE AGREEMENTS, which are what a read-locker actually runs:
  `byte_range_q_lookup` (its own three-line proof — iris 4.4.0's
  `ghost_map_lookup_big` is stated at fraction 1 only, though
  `ghost_map_lookup` takes a dfrac), `byte_range_q_home`, `fsblock_q_home`,
  `fsblock_q_home_open`, `fs_bytes_agree_q`, `fs_bytes_agree_any_q`.
  `InodeInv`: `ind_blk_q`/`ind_res_q`/`inode_map_q`/`blk_res_q`/
  `inode_blocks_q` with their `_1` equations, splitting laws, accessors
  (`inode_map_q_dir_acc`/`_ind_acc`, `inode_blocks_q_frame`/`_acc`/
  `_insert`, `ind_blk_q_run`) and `inode_fresh_q(_at)` — which needs NO
  fraction premise, because balloc's fresh run is FULL and a full owner
  excludes any other share.

  THE STRUCTURAL UNBLOCK IS `FsBytesGamma.gamma_blk_owned_q` (and
  `gamma_byte_range_q`): the fraction-1-only bridge was what kept anything
  at ¾ or ¼ out of the `InodeInv` vocabulary.  Over it, `FsStateEra` gains
  `inode_blocks_era_q`, `ind_res_era_q`, `inode_owned_era_of_q`/`_to_q`,
  and — the join point for the escrow lane — `inode_bytes_era_to`/`_of`,
  which turn the reader's `inode_bytes_era γfs (DfracOwn (1/4)) n` into
  exactly `ind_res_q … ¼ (bm_of n) ∗ inode_blocks_q … ¼ (bm_of n)
  (fn_data n)` under `inode_local`.

  A `Typeclasses Opaque` SEAL IS NOT CROSSED BY A `reflexivity` EQUATION,
  and that is the whole cost of the shape.  `inode_blocks`/`fsblock` are
  sealed (they must be — a 1024/268-element `big_sepL` behind a
  `Definition` is an `iFrame` hang), so neither `iFrame` nor `IntoWand`
  will unify `X` with `X_q … (DfracOwn 1)` even though they are
  convertible, and `iEval (rewrite …) in "H"` does not reliably fold them
  either.  The crossing that DOES work is a wand taking the fraction as a
  premise — `FsBlocks.fsblock_q_1_of`/`_to`,
  `InodeInv.inode_blocks_q_1_of`/`_to`, `ind_blk_q_1_of`/`_to`,
  `inode_map_q_1_of`/`_to` — one `iDestruct` per crossing.

  `readi` IS PROVEN AT A SHARE, AND `stati` NEEDED NOTHING.
  `SpecReadi.wp_readi_sconf_body` and `SpecBmap.wp_bmap_noalloc_sconf_body`
  take `inode_map_q γfs dq` / `inode_blocks_q γfs dq`, and NO ARITY MOVED:
  `dq` was already a vestigial binder in both (and in `bm_gen_stmt`), so it
  is now the block fraction.  readi modifies nothing — its only use of a
  data block is the agreement `ProofReadiParts.rd_held_content` (now
  fraction-generic, over `fs_bytes_agree_any_q`), and bmap-with-no-alloc
  reads the indirect block through the same agreement
  (`ProofBmapParts.bm_held_content`, likewise generic; its other consumer,
  `ProofItrunc`, crosses at 1 in two lines).  `stati`/`filestat` touch NO
  byte-layer resource at all (`inode_meta` is in-memory cells, which the
  design keeps at fraction 1), so they are already callable by a
  read-locker with nothing to prove.

  ONLY THE ALLOCATING ARMS ARE FRACTION-1 ARMS.  `ProofBmap`'s shared core
  gained one premise, `ak <> None -> dq = DfracOwn 1`, discharged
  vacuously by the no-alloc seal and by `reflexivity` at the two
  allocating seals (which now pass `DfracOwn 1` and cross with the wands
  above).  Inside, exactly three steps need it: the two
  `inode_blocks_insert` deposits of balloc's fresh block and the
  `log_write` of the indirect block; everything else — the indirect-block
  agreement, `inode_fresh`, the map/blocks framing — is share-blind.
  readi's seven callers pass `DfracOwn 1` and cross with two `iDestruct`s
  on each side of the call (`ProofFileread`, `ProofDirlookup`,
  `ProofDirlink`, `ProofKexecA`/`B2`/`B3`, `ProofSysUnlink`; three of them
  were passing `DfracOwn (1/4)` into the vestigial slot and now pass 1).

  WHAT THE JOIN WITH THE ESCROW LANE NEEDS.  `ProofFileread` and
  `ProofFilestat` still call `wp_ilock` at the FULL bundle and are
  unchanged in that respect.  When B″-esc's read arm lands, `ilock`
  without a transaction hands the holder `inode_meta`, `inode_addrs`, the
  pure facts and `inode_bytes_era γfs (DfracOwn (1/4)) n` (the escrow
  keeping `inode_owned_era_q γfs (DfracOwn (3/4))`, i.e. `dinode_at` — so
  a read-locker still cannot move a record — plus the ¾ residue).
  `fileread` then applies `FsStateEra.inode_bytes_era_to`, pairs the
  result with `inode_addrs` to make `inode_map_q γfs ¼ ip bm`, and calls
  `readi` at `dq := DfracOwn (1/4)`: one argument change and the two
  crossing `iDestruct`s deleted.  `filestat` needs no change at all.
  LEFTOVER: the ALLOCATING bmap contracts (`wp_bmap_sconf_body`,
  `wp_bmap_gen_body`) still carry `dq` as a vestigial binder while the
  no-alloc one uses it as the fraction; `ProofReadi.rd_q` now feeds only
  bread/brelse's own vestigial slots.
  layer's fraction indexing (B′'s structural note); its write arm is
  B″-arm's, below.

  **AS LANDED — B″-arm: THE TWO WALLS ARE GONE, AND THE WRITE ARM IS ARMED.**

  THE ARMED REGISTRY IS KEYED BY AN ARM ID AND PARKS A SHARE.  This
  SUPERSEDES lane A's "keyed by TRANSACTION" paragraph above and plan §3/§4's
  "the entry parking the arming transaction's WHOLE token" — both now
  misdescribe the mechanism and the plan needs the one-line correction.  Lane
  A keyed by transaction because `ghost_map_insert` needs `A !! t = None` and
  the only proof of that was "a parked entry would hold this very element";
  keyed by an ARM ID freshness costs nothing at all — the ghost step SEES the
  registry's map, so `fresh (dom A)` is a key nobody holds and the arm may
  park ANY share.  `Xv6Cameras.ireg_arm_ent = (nat * Qp * gset Z)` is the
  entry (transaction, share parked, inums suspended); the share is a FIELD
  for `ic_dep`'s reason — an arm must hand back exactly what it took.  What
  the parked share still buys is the ONLY thing the commit reads off the
  registry (`InodeRegion.ireg_clean_acc`, hence
  `IregClean.ireg_snap_local_acc`): every entry holds a POSITIVE share, so an
  empty `ln_tx` authority refutes it.  Names: `ireg_armed k t q S`,
  `ireg_parked e`, `ireg_arm` (a bare `t ↪[ln_tx icfg_log]{#q} tt` in, no
  freshness), `ireg_arm_more` / `ireg_disarm` / `ireg_top_retag_armed` (gain
  `k`, `q`), `ireg_release` (hands back the share), and the whole-token
  readings `ireg_arm_tx` / `ireg_release_tx`.  `create` got SIMPLER: `cr_dirty
  i = ∃ k t, ireg_armed k t 1 {[i]}` and the family gained `cr_dirty_arm`
  (arm + first retag), so all four exits speak only
  `cr_dirty_arm`/`_retag`/`_clear` — the two raw registry dances in the FILE
  and orphan arms are gone.  `wp_create_sconf_body` and its three callers are
  byte-stable.

  THE WRITE ARM IS `Xv6Cameras.DepTx (s : Qp) (dev inum) (g : gname) (t :
  nat) (q : Qp)`, LAST so the ~66 `DepShr` sites in 23 files and every
  `destruct d as [| .. | .. | ..]` keep their shape.  `IcacheEscrow`'s OUT
  arm at that descriptor holds `DepShr`'s content PLUS the parked share
  `t ↪[ln_tx icfg_log]{#q} tt`.  IT IS ITS OWN GHOST STEP, NOT PART OF
  `ilock`, and that was a measurement, not a preference: bolting the share
  onto `SpecIlock.wp_ilock_sconf_body` moves that contract's arity (20 caller
  files) and `SpecIunlock`'s with it, and it additionally costs the ~56
  `ic_deposit cn k (DepShr …)` conjuncts in the walk-stage statements of 15
  files — for a mechanism whose value is only cashed once every transactional
  caller actually arms.  As two ghost steps on a deposit the walk already
  holds, `IcacheEscrow.ic_arm_tx` / `ic_disarm_tx` (at `icEscN .@ k`, the
  full valid cell selecting the OUT arm exactly as `ic_open_out` does) cost
  the contracts NOTHING and each walk converts independently; a walk that
  `ilock`s inside a transaction only to READ (namex's lookups) need not arm,
  which the coupled form could not express.  `LogInv.log_tx_halve` /
  `log_tx_join` take the id out of `log_tx`'s existential for the arm to name
  it and put it straight back, so nothing above those two lines sees an id.

  THE TWO LEMMAS THE COLLECTION CALLS: `IcacheEscrow.ic_out_no_write_arm`
  (an OUT arm beside a write-armed deposit is refuted at an empty `ln_tx`
  authority; its core is `ic_dep_own_tx_no_ops`) and
  `IregClean.ireg_snap_local_acc` (nothing is armed, hence `snap_local`).
  Together they are plan §4's "no inode is write-locked and no inum is
  armed".

  THE NON-VACUITY WITNESS IS `sys_chdir`, converted: it already split its
  `log_op` into `log_opS` + `log_tx` at begin_op and framed `log_tx` across
  the whole `ilock` .. `iunlock`/`iunlockput` window, and calls nothing that
  wants the token in between — so the conversion is three ghost steps and no
  contract change.  Both release paths recover exactly the half parked.  It
  is the ONLY cheap one: every other transactional `ilock` caller threads
  `ic_deposit` through its walk-stage statements, and converting one is that
  file's share of the ~56-conjunct ABI bill.

  COVERAGE (B″-esc's open item): the commit can already name EVERY CACHED
  INUM with no lock — all five arms of `ic_escrow_body` carry the escrow's
  own half of the identification ghost as their LAST conjunct, so
  `IcacheEscrow.ic_escrow_body_ident` reads (live, dev, inum) off an open
  body.  The per-inum token on ~40 payload sites B″-esc costed is therefore
  NOT the cheapest shape and should not be built.  WHAT IS ACTUALLY MISSING
  is the PARTITION — that `ipool_inv`'s index `O` plus those fifty identities
  exhausts `region_inums nib`.  That is `ic_ci_wf`'s `dom ci = dom M` plus
  `ipool`'s domain, both under the itable lock, and NO resource ties the pool
  invariant to the escrows: the lock is the only place the two meet (the pool
  shares `ipool_key` with it, the escrows share `ic_id`).  It needs exactly
  one new tie, and the cheapest is a QUARTER of `ic_id` parked in
  `ipool_body` for every slot beside the pure row `region_inums nib = O ∪
  {inum_k | live_k}`: every mover of a slot's identity (iget's recycle,
  iput's two evictions) already opens the pool invariant, and that is exactly
  where the partition changes.  It reaches into `ProofIget`'s and
  `ProofIput`'s windows and `ipool_inv`/`ipool_body`/`ipool` gain `cn`, so it
  is its own increment.

  REMAINS: that partition tie; the ABI sweep that arms the other
  transactional walks (`create` first — it is the arming walk, and its arm
  and its write lock now coexist); and the read arm, still on lane B″-blk's
  block-layer fraction indexing.
- [ ] **Lane C — the commit reconstructs the snapshot (plan §3 commit, §4).**
  1. The COLLECTION lemma: with `γtx` empty (lane A item 5 ⇒ no `Some`
     entry in LOCKED), opening `ftopN`/`iregN`/`icacheN`/`icEscN`/`bitmapN`
     at a ghost step and ∗-ing every inode's bundle against the byte
     authority of `fs_bytes_inv` yields `∃ S, snap_ok S L` with `S` the
     `ftop_inv` authority's map; the three CUT clauses `sk_sbok`/`sk_reg`/
     `sk_slot` off the config's superblock, the region's numbering and one
     inode's own ∗; disjointness from the ∗ (full elements
     for unlocked inodes; ¾ for read-locked ones once lane B′ lands —
     until then every bundle is full or absent, and a read-locked inode
     at commit is the ONE case the lemma cannot close: state it as the
     premise "no inode is out for reading" and let B′ discharge it).
  2. The law parked in `log_ctx` (persistent; pure-fact-producing; hands
     the authority back), discharged once by the FS from item 1;
     `end_op`'s commit path calls it at `outstanding = 0`; the parked
     `Ψ`/`log_psi_*` and the nine `log_psi_write_rebase` lines are
     deleted; `SpecLogWrite` loses its payload premise.
  3. `P_fs`'s durable conjunct → `P_dur (fr_D r)` (arity-free; boot via
     `FsDurImg.img_boot_P_fs_dur`); both commit permits: fr_D advance +
     `dsnap_step_of` at the collected `snap_ok`, allocator inside the
     permit (a bupd); receipt gains the snapshot's state; timelessness;
     DELETE the superseded families incl. `fdn_*`/`riscv_dview_name`.

  **AS LANDED — THE IMAGE HALF ONLY (lane C-img).**  The image's tie is
  `FsDurImg.img_snap_ok`: `FsCfgBoot.fs_boot_image_wf dk ndisk sb nib cov`
  ALONE yields `snap_ok (img_state (fs_blocks dk) sb nib) (fs_restrict
  (fs_blocks dk) (fs_home_set cov (sb_logstart sb)))` — the state is the
  decoder already in the tree (`img_state`/`img_nodes`; no second one
  exists) and the map is exactly `FsCrash.P_fs_alloc_clean`'s `fr_D`.
  Conjuncts (14) `fs_region_bare` and (15) `fs_root_no_self` are WIRED INTO
  `fs_boot_image_wf`, last so no destructuring pattern moves; the sweep was
  four sites (`BootShared`, `ProofMain`, `FsDurImg`'s two lemmas — which
  therefore LOST their two extra premises — and the discharge in
  `FsAdequacyImg.fsimg_image_wf`, two `FsImgCheck` citations, no new
  computation).  The used-set coupling is W3/W4/W5 through three pure
  readings: `img_node_owns_slot` (a node's own block IS a `FsImg.fs_slot` of
  its record), `img_owned_block` (hence in `fs_inode_blocks`, hence in W3's
  `[fs_data_start, size)`) and `img_used_of_blocks` (hence bit-set, W5); a
  FREE inum owns nothing, which is conjunct (14)'s second use; `sk_disj` is
  W4's `NoDup` via `fs_inode_blocks_disjoint`.  The record tie is
  `diblk_bytes_split` + `img_rec_in_blk` (the pure half of
  `FsStateInode.rec_owned_at_diblk`; `diblk_bytes_split` belongs in
  `DinodeEnc.v`), `sk_links` is `img_link_valid`, `snap_local` is
  `img_inode_local`.  Boot: `FsDurImg.img_P_dur_alloc` (`⊢ |==> P_dur D0`
  off the bundle alone — the snapshot needs NO resource from anyone, which
  is what makes this lane's `P_fs` change arity-free) and
  `img_boot_P_fs_dur`, which is `P_fs_alloc_clean` with `P_dur (fr_D r)`
  beside it at the same `D0`; W2 discharges its clean-log premise, so no
  caller gains one.  `FsCrash.v` is UNTOUCHED.  Non-vacuity at the literal
  image: `FsAdequacyImg.fsimg_snap_ok`.  RETIRED (nothing consumed them):
  `FsDurImg`'s 3b' kind assignment `img_kinds*`/`img_region_*`/
  `img_dur_seed` and its `FsDurObj`/`FsDurWire` imports.
  STILL PRESENT AND SUPERSEDED: `fs_dur_of_image`/
  `fs_dur_view_of_image` (the resource-MOVING image conversion; lane E says
  whether the boot mint still wants it).

  **AS LANDED — THE WAL SIDE: THE PARKED PAYLOAD IS GONE.**  The log's lock
  resource carries no client proposition and its context carries no client
  law: `log_state`/`log_res` lose their `Psi` parameter and `log_state`'s
  last conjunct, `log_ctx_at` and its `_at_` projections are DELETED (the
  existential closure had nothing left to close, so `log_ctx` IS the bundle
  and keeps its arity — the ~75 files that thread it are untouched), and
  `log_psi_commit`/`_step`/`_write`/`_write_rebase`/`_spend`,
  `LogDefs.fs_dstep`/`_rebase`/`_id`/`_trans` and `FsDurWire.v` go with
  them.  `SpecLogWrite`'s three atomic-update forms lose the payload-step
  premise and their closing wand ends at `|={Efs,⊤}=> Φfsb`; `lw_au_rec`
  loses its `bs` binder with it.  `FsCrash.fs_commit_L_sector0_rec`/
  `_seq_permit` lose the client's prepared step and run `fs_dview_rebase`
  themselves, which is what they did before the payload existed.  The nine
  suppliers' `log_psi_write_rebase` lines and the two `iDestruct "Hlctx" as
  (Psi)` openings per file go; `ProofIupdate`'s `iu_region_au`/`iu_region_step`
  lose the quantifier; `eo_commit`/`eo_loop` lose `D0`/`Dc` and their two
  pure ties; `ProofInitlog` parks nothing.  `log_op`, `wp_end_op`,
  `fs_crash_seam` and `P_fs` are byte-stable.

  **THE REST OF LANE C IS BLOCKED, AND NOT AT THE PROOF LEVEL**
  (`iris/FsDurQuiesce.v` is the finding, with its two machine-checked
  namespace facts).  `P_fs`'s conjunct, the commit permits and the receipt
  all hang off `dsnap_step_of`, which needs `snap_ok S L`, which only the
  collection at quiescence produces — and the collection is unstatable
  against the escrow AS IT IS, for two reasons that are both about WHERE the
  era parks its bundles:

  1. **The fifty cache escrows share ONE namespace.**
     `IcacheEscrow.ic_escrow … k` is `inv icEscN (ic_escrow_body … k)` for
     every slot, so at most one is open at a time
     (`FsDurQuiesce.ns_not_reopenable`).  `snap_bytes`' `sk_disj` and
     `sk_own_used` are read off the ∗ between TWO inodes, so the commit must
     hold every bundle at once.  Fix: allocate at `icEscN .@ k`
     (`esc_ns_disjoint`/`esc_ns_still_open` are the induction step that then
     works).
  2. **The uncached inodes' bundles are behind the itable SPINLOCK.**
     Plan §4's "the pool (`live_pool` inside `inv icacheN`)" conflates two
     objects: `IcacheInv.live_pool` is the reference-count fraction pool and
     holds no bundle, while `IcacheEscrow.ipool` — which holds the uncached
     inums' `inode_owned_era` — is a conjunct of `itable_res2`, the itable
     spinlock's resource.  The commit's ghost step runs inside a disk-write
     permit, where no code runs and no lock can be taken, and `end_op` never
     takes `itable.lock` anyway.  Fix: move `ipool` into its own invariant
     at per-inum namespaces; `itable_res2`'s own comment forbids the move
     only for `isl_pool`, not for `ipool`.

  Both fixes are in `IcacheEscrow.v` — lane B′'s file — so they belong with
  B′ (or with a ruling that hands them to it).  REMAINS for lane C after
  that: the collection lemma, `P_fs`'s conjunct → `P_dur (fr_D r)` (boot via
  `FsDurImg.img_boot_P_fs_dur`, which already produces exactly that pair),
  the two commit permits at `dsnap_step_of`, the receipt's snapshot state,
  timelessness, and the `fdn_bmap/ist/nin`/`riscv_dview_name` deletions
  (which are an adequacy sweep: `RiscvAdequacy`'s `Pc` takes the
  `fs_dur_names` bundle and the dview gname as arguments, and `FsDurLedger`
  still reads `fdn_bmap/ist/nin`).
- [ ] **Lane D — the spike theorem (plan §5).**  `ProofSysMknod` keeps
  `create`'s `made` clause (today discarded at its `iDestruct`, ~`:1690`);
  prove `mknod_durable` off the snapshot; quote it here.  Then the
  other arms are the same pattern (unlink/rmdir/link/write) — schedule
  by value.
- [ ] **Lane E — boot and the theorem (plan §5).**  Stage 4: the era's
  instance minted from the current snapshot by `fs_state_of_ledger` +
  the era-only extras, distributed into region/bitmap/escrow/pool
  (`fs_cfg_alloc`, `FsBoot`, `BootShared` lose every image premise;
  `image_dinode_fs_dinode` disappears); [(14)/(15) are already conjuncts
  of `fs_boot_image_wf` — lane C-img did that]; the `Pdur`
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
