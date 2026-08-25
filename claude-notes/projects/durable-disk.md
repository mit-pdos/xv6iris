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

  ONE `ilock` SPEC: unchanged, and it stays that way — both arms landed as
  GHOST STEPS on the deposit a holder already carries (B″-arm's `ic_arm_tx`,
  B″-join's `ic_shed_rd`), which is what keeps `SpecIlock` and `SpecIunlock`
  byte-stable across twenty caller files.
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

  LEFTOVER: the ALLOCATING bmap contracts (`wp_bmap_sconf_body`,
  `wp_bmap_gen_body`) still carry `dq` as a vestigial binder while the
  no-alloc one uses it as the fraction; `ProofReadi.rd_q` now feeds only
  bread/brelse's own vestigial slots.

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

  REMAINS: that partition tie, and the ABI sweep that arms the other
  transactional walks (`create` first — it is the arming walk, and its arm
  and its write lock now coexist).

  **AS LANDED — B″-join: THE READ ARM, AND THE COVERAGE LEMMA OVER THE
  FIFTY SLOTS.**

  THE READ ARM IS `Xv6Cameras.DepRd` (LAST, after `DepTx`, so the ~66
  `DepShr` sites in 23 files and every `destruct d` keep their shape), and
  what distinguishes it is not the credential — `ic_dep_own` at `DepRd` is
  `DepShr`'s verbatim — but what the escrow KEEPS beside it.
  `IcacheEscrow.ic_rd_arm` is that residue: the five pure clauses, `dlinks`,
  `inode_owned_era_q γfs (DfracOwn (3/4)) γi inum n` and the two contents
  holds, at an existential `(dn, bm, data)`.  `ic_rd_held` is what a
  read-locker carries in its place: `inode_ok`, `inode_local`, the metadata
  and addrs CELLS (fraction 1 — the design keeps in-memory cells there) and
  `FsStateEra.inode_rd_era γfs (DfracOwn (1/4)) inum n`.  `ic_loaded_shed`
  and `ic_rd_join` are the two directions; `ic_out` gained `γfs γi cov
  logstart` and one LAST conjunct `ic_out_rd` (`ic_rd_arm` at `DepRd`, `emp`
  everywhere else, `ic_out_rd_none` the equation), and NOTHING OUTSIDE
  `IcacheEscrow.v` names `ic_out`, so that arity move cost one file.
  `ic_swap_checkout` and `ic_close_out` keep their ABSTRACT descriptor and
  gained the pure side condition `IcacheRef.ic_dep_rd d = false` (a checkout
  hands the holder the WHOLE payload; `ProofIlock` pays `eq_refl`).

  IT IS TWO GHOST STEPS, NOT A CONTRACT CHANGE — `IcacheEscrow.ic_shed_rd` /
  `ic_unshed_rd` at `icEscN .@ k`, the full valid cell selecting OUT exactly
  as `ic_open_out` does — for B″-arm's measured reason: bolting the arm onto
  `SpecIlock.wp_ilock_sconf_body` moves that contract's arity (20 caller
  files) and `SpecIunlock`'s with it.  Both contracts are BYTE-STABLE and
  each read-locker converts on its own.

  THE RE-IDENTIFICATION IS A QUARTER OF `top_frag`, AND THAT IS THE WHOLE
  DIFFERENCE BETWEEN THE TWO ARMS.  A transaction's id is determined by
  nothing the escrow holds (`IcacheTxRefute.tx_two_halves_no_whole`), so the
  write arm had to write `(t, q)` into the descriptor; an inode's NODE is
  determined — so `FsStateEra.inode_owned_era_q` takes the share on the
  abstract fragment too (`FsState.top_frag_q`, with `top_frag` its `DfracOwn
  1` reading, so no site that spells `top_frag` moved), the reader carries
  `inode_rd_era` = byte legs ∗ fragment at ¼, and
  `FsStateEra.inode_rd_era_agree` pins the arm's existential node to the
  holder's.  `FsStateEra.era_node_pair_inj` turns that into the PAIR equal:
  two `inode_ok` pairs with the same node ARE the same pair, `data` playing
  no part (it is not determined, which is exactly why the join re-forms
  `ic_loaded` at the ARM's `data`).  Two of the design's sentences become
  resource facts: `dinode_at` never leaves the escrow, so a read-locker
  cannot move a record; the fragment is short of a whole element, so it
  cannot retag.  `inode_owned_era_shed` is restated over `inode_rd_era`, and
  `inode_owned_era_shed_to` / `_of` are its two WAND readings.

  THE TWO TRUE READ-LOCKERS ARE CONVERTED, and they are the arm's
  non-vacuity witness.  `ProofFilestat`'s `ic_loaded_open` / `ic_mk_loaded`
  pair is gone outright — `stati` reads only the metadata cells.
  `ProofFileread` sheds around the offset borrow, turns the quarter into
  `readi`'s `inode_map_q` / `inode_blocks_q` pair with the new
  `FsStateEra.inode_rd_era_era_node_to` / `_of`, and calls
  `SpecReadi.wp_readi_sconf` at `dq := DfracOwn (1/4)` — exactly B″-blk's
  prediction: one argument change and the four crossing `iDestruct`s
  deleted.  No contract moved.

  THE COVERAGE LEMMA IS `IcacheEscrow.ic_escrow_body_cover` (and
  `_cover_all`, the same under a `big_sepS` over a `gset nat` of slots).  At
  an EMPTY `ln_tx` authority it classifies slot `k` EXHAUSTIVELY into
  `ic_slot_cover`'s four alternatives — (a) the slot is not live; (b) live
  but unloaded, and what the escrow holds IS an `ipool_shape_np` row, the
  same shape `ipool_inv` hands out; (c) live and loaded, the bundle inside
  at a share whose double is INVALID (1 unlocked, ¾ read-locked — the
  premise `blk_owned_ne_full` / `blk_owned_ne_34` want, and the reason the
  reader's share is a quarter and not a half); (d) the RESIDUE.  It moves no
  resource — the authority comes straight back and each alternative carries
  its own closing wand (`ic_lend`, whose frame is existential) — so the
  commit can hold all fifty open at one ghost step.  The WRITE arm is not
  among the four: a `DepTx` arm holds a positive share of an open
  transaction's element and is refuted outright (`ic_dep_own_tx_no_ops`).
  `ic_out_no_write_arm` gained `ic_out`'s four new arguments.

  (Alternative (d) — what the caller sweep still owed at this point — is
  gone: B″-tx4 retired the bundleless lock descriptor and B″-tx5 gave iput's
  three windows their share.  `ic_slot_cover` is three alternatives.)

  TWO PERFORMANCE FACTS, both instances of durable-notes rules and both
  worth the scale they set.  (i) `inode_owned_era_q` / `inode_bytes_era` /
  `inode_rd_era` are `Global Typeclasses Opaque`: each is a `∗` over a
  `big_sepM` of block runs beside an `ind_owned_q` whose body is a `decide`
  no resolution can reduce, and UNSEALED, one `apply _` for `ic_rd_arm`'s
  `Timeless` instance ran **nineteen minutes** with no error and no output —
  it reads as a hung build, and `rocq compile -time` streamed to a file is
  what names the sentence.  The read arm's own `ic_rd_arm` / `ic_rd_held` /
  `ic_out_rd` are sealed inside the section too, with `tl_struct` moved
  above them.  (ii) `inode_owned_era_shed` is an `⊣⊢`, and `rewrite`ing it
  inside a proof that carries the payload rewrites the whole proofmode goal,
  environments included; use the wand readings.  The same proofs spell every
  re-pack of `ic_escrow_body` as `iSplitL`-by-name plus `iExact`, never a
  bare `iFrame` — the body is the goal's last conjunct and a framing search
  walks it first.

  REMAINS.  (1) THE ABI SWEEP that arms the other transactional walks: ~56
  `ic_deposit … (DepShr …)` conjuncts in the walk-stage statements of 15
  files become `DepTx … t q` (two extra binders per stage lemma), and the
  `log_tx γ` those stages carry across the locked window becomes the residue
  half `t ↪[ln_tx icfg_log]{#(1/2)} tt` (5 files name `log_tx`).
  `sys_chdir` is the worked instance and costs three ghost steps wherever
  `ilock` and `iunlock` sit in one proof block; `create` is next.
  (2) THE PARTITION TIE (`region_inums nib = O ∪ {inum_k | slot k live}`, a
  quarter of `ic_id` in `ipool_body`, `ipool_inv`/`ipool_body`/`ipool`
  gaining `cn`) — untouched here; it reaches into `ProofIget`'s recycle and
  `ProofIput`'s two evictions and is its own increment.
  **AS LANDED — B″-tx: THE TRANSACTIONAL `ilock`, AND SIX OF THE NINE WALKS.**

  THE ARM IS INSIDE THE CONTRACT NOW, and the ABI bill B″-arm measured was
  paid by ONE PREDICATE rather than by two binders per stage lemma.
  `IcacheEscrow.ic_tx_dep cn k s dev inum g` bundles the `DepTx` descriptor
  with the holder's residue at a FIXED half —
  `∃ t, ic_deposit cn k (DepTx s dev inum g t (1/2)) ∗ t ↪[ln_tx icfg_log]{#(1/2)} tt`
  — so it stands exactly where `ic_deposit cn k (DepShr s dev inum g)` stood,
  at the same arguments, and the walk-stage conjuncts convert by
  substitution: no stage lemma gained a binder, no `with`-list position
  moved.  The transaction id is DETERMINED by the residue the holder keeps,
  which is what lets the id be closed existentially at BOTH ends;
  `ic_arm_tx_half` / `ic_disarm_tx_half` are the two steps at that packaging
  and `SpecIlock.ic_arm_tx_log` / `SpecIunlock.ic_disarm_tx_log` their
  `LogInv.log_tx` readings (the id leaves and re-enters the existential
  there, `log_tx_halve`/`log_tx_join`).

  FOUR NEW CONTRACTS, EACH A DERIVATION, so not a line of any function's own
  proof is re-run: the arm is a fupd on the deposit the plain post already
  hands out, the disarm a fupd before the call.
  `SpecIlock.wp_ilock_tx_sconf` (`log_tx icfg_log` in, `ic_tx_dep` out),
  `SpecIunlock.wp_iunlock_tx_sconf`, `SpecIunlockput.wp_iunlockput_tx_sconf`
  (`log_opb` in, `log_op` out — the caller's token is half-parked, so it
  cannot present `log_op`) and `wp_iunlockput_tx_gen` (`log_opSe` in,
  `log_opS` ∗ `log_tx` out).  `ILOCK`/`IUNLOCK`/`IUNLOCKPUT` gain one, one
  and two `Parameter`s, discharged in `ProofIlock`/`ProofIunlock`/
  `ProofIunlockput` by `wp_ilock_tx_of_sconf` / `wp_iunlock_tx_of_sconf` /
  `wp_iunlockput_tx_of_sconf` / `_of_gen`.  EVERY PLAIN CONTRACT IS
  BYTE-STABLE — the read-lockers and the unconverted walks did not move.

  THE SAME BUNDLING TRICK ONE LEVEL UP, and it is what made `namex`
  affordable: `LogInv.log_opSt γ u Sb = log_opS γ u Sb ∗ log_tx γ`
  (`log_opSt_split`/`_intro`, `log_op_openSt`, `log_opSt_op`).  namex has to
  be HOLDING the token at each per-level `ilock`, and as a second conjunct
  that would have moved every walk-stage statement of namex, namei,
  nameiparent and their six callers; in `log_opS`'s own position it moved
  none.  It is split exactly once per locked window.

  WHAT A WALK CARRIES ACROSS A HELD LOCK, in four shapes, and which one is
  a file's answer is decided by what its interior calls want: `log_opb`
  (the budget half — `sys_link`'s `sl_tail_c`/`_d`, kexec's `kxc_open`
  bundles, `sys_open`'s and `sys_unlink`'s stages when they land),
  `log_opS` (the set form, when the interior writes — `filewrite`, which
  therefore calls `Writei.wp_writei_gen` instead of `wp_writei_sconf`,
  exactly B″-arm's prediction: one `Sb` argument, one `Sb'` binder and the
  four extra pure conjuncts the set form reports), `log_opSt` (namex), and
  NOTHING AT ALL where the stage's own `log_tx` conjunct DIES because the
  token is inside the descriptor (`sys_link`'s `sl_tail_f`/`_e2`).

  THE AMBIENT LOG HAS TO BE NAMED, and that is the one genuinely new premise
  this lane adds: the escrow parks a share of `icfg_log`'s element and
  carries no `log_names` parameter, so a walk that arms must know its own
  `g` IS the ambient log.  Three ways were used and the third is the one to
  copy.  (i) `sys_chdir`/`namex`/`sys_link`'s tails already had the
  equation.  (ii) `SpecIreclaim`, `SpecFilewrite` (as `fwn_log fn =
  icfg_log`, beside `fwn_j`/`fwn_procs`), `SpecSysWrite` and `sl_tail_c`/`_d`
  gained it as a pure premise — cheap because their callers (`ProofFsinit`
  at the literal `icfg_log`, `ProofSyscall` off `sysc_ties`' `sct_log`,
  `ProofSysLink`) already prove it.  (iii) FOR A CONE, PUT IT IN THE
  PERSISTENT BUNDLE: `SpecKexec.fs_fabric` gained `⌜g = icfg_log⌝` as its
  LAST conjunct, which hands it to all dozen lemmas of the kexec cone for
  free and cost only the seven fabric openings (`& %Hclogf`),
  `fs_fabric_mk`'s new LEADING wand and its ten call sites (one `[%]` slot
  each), and the two places that build a fabric from scratch
  (`ProofSyscall.sysc_fs_fabric`, `ProofForkret`'s inline assembly).

  CONVERTED, SIX OF THE NINE TRANSACTIONAL WALKS, each its own green commit:
  `sys_chdir` (B″-arm's three voluntary ghost steps deleted — the arm is in
  the contracts and `log_tx_halve`/`log_tx_join` and the bound id leave the
  file), `ireclaim` (`log_op_split` at `begin_op`, `log_opb_op` at the
  `iunlock`), `filewrite` (+ `writei` at its GEN form), `namex` (both
  walks — `ProofNamex` and `ProofNamexTr` — with all five exits per walk:
  four `wp_iunlockput_tx_gen` and namei's one `wp_iunlock_tx_sconf`; the
  counted seals of namex/namei/nameiparent open with `log_op_openSt` and
  close with `log_opSt_op` instead of framing `log_tx` past the walk;
  `SpecNamei`/`SpecNameiparent`/`SpecNameiTr`/`SpecNamexTr`/`DirViewPin`/
  `NameiInitPinned` are pass-throughs), `sys_link` (all three windows), and
  `kexec` (both releases, and the pinned walk's stage).

  THE WALL, AND IT IS A SPEC-SHAPE FACT, NOT A PROOF DIFFICULTY:
  **`ic_tx_dep` CANNOT BE USED TWICE AT ONE TRANSACTION.**  Its invariant is
  "the arm holds `q` and the holder holds `q` beside it", which forces
  `q = 1/2` for the two to rejoin into a whole element — so two of them at
  the same `t` claim 2, and the pair is UNSATISFIABLE (a premise nobody can
  discharge, durable-notes' worst defect).  `create` (parent + fresh child,
  the arming walk) and `sys_unlink` (`dp` + `ip`) each hold TWO write locks
  at once and each spells both deposits in one stage statement
  (`ProofCreate` at its three joint statements, `ProofSysUnlink` at
  `kd`/`ks`), so neither can convert as the other six did.  THE SHAPE THAT
  DOES WORK, and it is one predicate over both slots so the arity argument
  still holds:
  `ic_tx_dep2 cn k1 s1 d1 i1 g1 k2 s2 d2 i2 g2 = ∃ t, ic_deposit cn k1 (DepTx … t (1/4)) ∗ ic_deposit cn k2 (DepTx … t (1/4)) ∗ t ↪[ln_tx icfg_log]{#(1/2)} tt`,
  built from `ic_tx_dep k1` plus a second `DepShr` by SHRINKING k1's arm
  from ½ to ¼ and arming k2 at ¼, and torn down in either order by GROWING
  the survivor's arm back to ½.  That needs two new body lemmas beside
  `ic_arm_tx_body` (`ic_shrink_tx_body` / `ic_grow_tx_body`, the same
  `ghost_var_update_2` on the descriptor with the share moving between the
  arm and the holder) and three fupds; the caller cost is that two
  conjuncts of a joint statement become one.  `create` ALSO needs
  `IregClean`/`InodeRegion`'s arming to run off a SHARE — `ireg_arm` already
  takes a bare `t ↪[ln_tx icfg_log]{#q} tt` (B″-arm), but `cr_dirty_arm` is
  built on the whole-token reading `ireg_arm_tx`, which a walk with two
  parked halves cannot supply.  `sys_open` is blocked behind `create` and
  not by anything of its own: its four `so_*` stage statements and its five
  tails carry ONE deposit, but that deposit reaches them from BOTH its own
  `ilock` and `SpecCreate.create_locked`, so the two must convert together
  (`create_locked` / `create_locked_mk` are the only two sites to edit on
  create's published side).

  NOT ATTEMPTED, AND WHY.  (1) iput's windows and `ic_held` (the lane's item
  3): they are under a transaction in the C, but the CONTRACT iput is called
  at does not carry one — `SpecIunlockput`'s GEN form hands iput `log_opSe`
  and the tx forms this lane added disarm BEFORE the call and frame the
  token AROUND it, so `DepRef`/`DepFrz`/the mid-free park/`ic_held` cannot
  park a share until `SpecIput` itself takes one.  That is `SpecIput` +
  `ProofIput` (5246 lines) + every iput caller, and it is its own increment;
  nothing here invented a premise for it.  (2) Retiring `DepShr` and
  restating `ic_escrow_body_cover` with three alternatives: `DepShr` is
  still the descriptor `ilock` publishes (the read arm reaches `DepRd`
  through `ic_shed_rd`, and three walks still check out at it), so the
  fourth alternative of `ic_slot_cover` is still inhabited and the lemma
  keeps its four arms.  The end state is unchanged from B″-join's: once
  `create`/`sys_open`/`sys_unlink` and iput's windows are converted,
  `wp_ilock_sconf` becomes the READ form (folding `ic_shed_rd` in, two
  caller files), `DepShr` goes, and `ic_escrow_body_cover` loses arm (d).

  **AS LANDED — B″-tx2: THE LAST THREE WALKS, AT A QUARTER EACH.**

  TWO ARMS OF ONE TRANSACTION LIVE AT A QUARTER, AND THE ID IS NAMED.
  `ic_tx_dep`'s invariant ("the arm holds `q`, the holder holds `q` beside
  it") forces `q = 1/2`, so two of them at one transaction claim 2 — B″-tx's
  wall.  `IcacheEscrow.ic_tx_dep_at cn k s dev inum g t q` is the same bundle
  with the id and the share NAMED, and two arms of ¼ plus a residue of ½
  rejoin to 1 exactly as one arm of ½ and a residue of ½ do.  The moves are
  `ic_shrink_tx_body` / `ic_grow_tx_body` (`ic_arm_tx_body`'s
  `ghost_var_update_2` with the share moving between the arm and the holder;
  the total is an EQUATION PREMISE `q = q1 + q2`, so no caller ever rewrites
  a `Qp` sum inside the proofmode) and their fupds `ic_shrink_tx` /
  `ic_grow_tx`.  `ic_tx_dep2` is the two-slot form at a CLOSED id, with
  `ic_arm_tx2` (shrink the first arm, arm the second) and `ic_disarm_tx2_fst`
  / `_snd` (release either, the survivor GROWS back to a half); it is the
  two-slot twin of `SpecCreate.create_locked`'s `ic_tx_dep` and NOTHING IN
  THIS KERNEL CONSUMES IT YET — every walk uses the `_at` form directly,
  because that is what keeps the sweep position-stable.  `LogInv` gained the
  general share arithmetic beside `log_tx_halve`/`_join`: `log_tx_split` /
  `log_tx_add` (equation premise) and `log_tx_full` / `log_tx_open`.

  THE SWEEP MOVED NO CONJUNCT, and that was the point of naming the id.  A
  stage's `ic_deposit cn k (DepShr s dev inum g)` becomes
  `ic_deposit cn k (DepTx s dev inum g t (1/4))` IN PLACE; its `log_tx g`
  becomes `t ↪[ln_tx g]{#(1/2)} tt` IN PLACE; a stage that carried the whole
  `log_op g u` instead carries `log_opb g u` and bundles the residue into
  `ic_tx_dep` (one lock) or into two `ic_tx_dep_at`s (two locks).  Exactly
  ONE binder is added per stage statement, always LAST, and the walks' ~33
  deposit conjuncts converted by substitution.  The one genuinely new premise
  is `g = icfg_log`, added to nine lemmas that lacked it (`so_tail_pub`,
  `so_stores`, `so_alloc`, `so_join`; `so_tail_c`/`_d`/`_e`/`_f`/`_s`;
  `su_w2`, `su_w2_bad`, `su_w3`, `su_tail_bad`/`_d`/`_e`) — every caller
  already proves it.

  CONVERTED: `create` (+ `sys_mkdir`, `sys_mknod`), `sys_open`, `sys_unlink`.
  `create` is the arming walk and its three shares now add up explicitly:
  ¼ in the parent's escrow, ¼ in the child's, ½ in the registry.  `cr_dirty`
  is therefore KEYED BY THE TRANSACTION ID (`cr_dirty t i = ∃ k,
  ireg_armed k t (1/2) {[i]}`) and `cr_dirty_arm` runs off `InodeRegion`'s
  SHARE form `ireg_arm` rather than the whole-token `ireg_arm_tx` —
  `ireg_arm` already took a bare `t ↪[ln_tx icfg_log]{#q} tt` (B″-arm), so
  `InodeRegion` did not move.  `SpecCreate.create_locked` carries
  `ic_tx_dep` in the deposit's own position, and `wp_create_sconf_body`'s
  post hands `log_tx` back only on the FAILURE arm (on the success arms it
  is inside the bundle) — three caller files pay one `iDestruct` each.

  TWO CONTRACTS HAD TO MOVE TO THEIR GEN FORMS, for one reason: a walk whose
  token is half-parked cannot present a counted `log_op`.  `sys_open`'s
  `so_stores` calls `SpecItrunc.wp_itrunc_gen` (`log_opSe` in, `log_opS` out,
  `log_credit … false` by `log_credit_own`), and `sys_unlink`'s `su_tail_e` —
  the one arm holding two locked inodes — calls
  `SpecIunlockput.wp_iunlockput_gen`.  This is B″-arm's prediction at the
  `_sconf` corollaries, and it is the whole held-lock ABI bill: two call
  sites, both with the GEN contract already in the tree.

  `DepShr` HAS NO NON-LOCK USE LEFT (checked): every remaining mention is
  inside `SpecIlock`/`SpecIunlock`/`SpecIunlockput` and their proofs, plus
  `ProofCreateFreshTy`, which relays `ilock`'s post to a caller that arms it
  immediately.  `ic_slot_cover` therefore still has FOUR alternatives, and
  its comment now names exactly what inhabits the residue: (i) iput's
  `DepRef`/`DepFrz`/mid-free park/`ic_held`, and (ii) the `DepShr` the PLAIN
  `ilock` publishes in the gap between its checkout and whichever later fupd
  arms or sheds it.  (ii) is not closed by converting more callers: it dies
  only when `ic_swap_checkout` ITSELF publishes `DepRd` or `DepTx`, i.e. when
  the arm moves into the checkout's own ghost step rather than a fupd after
  the contract's post.  That is one more increment in `ProofIlock` +
  `SpecIlock` and it is what "retire `DepShr`" now means.

  IPUT'S SHARE, MEASURED HERE AND BUILT BY B″-tx5.  Every
  `iput` in this kernel runs inside a transaction (its `nlink = 0` path calls
  `itrunc` + `iupdate`), so no window of it is exempt and nothing here needed
  a premise nobody can discharge.  What blocks it is the CONTRACT: the
  counted `SpecIput.wp_iput_sconf` carries the WHOLE `log_op g n`, while the
  GEN `wp_iput_gen` carries `log_opSe` and no token at all — and it is the
  GEN form that `SpecIunlockput` hands its interior iput.  Giving iput a
  share means a third family (`log_opSe` beside `t ↪[ln_tx icfg_log]{#q} tt`,
  in and out) across `SpecIput` (523 lines) + `ProofIput` (5246, sixteen
  mentions of the four window predicates) + `SpecIunlockput` (902) +
  `ProofIunlockput`, and the nine files that name an iput contract
  (`LinkIput`, `ProofDirlink`, `ProofFileclose`, `ProofIreclaim` ×2,
  `ProofIunlockput`, `ProofKexit`, `ProofNamex`, `ProofSysChdir`,
  `ProofSysLink`).  Each of those callers already holds a share at the call —
  the walks above put one in their hands — so the sweep is threading, not
  design.

  REMAINS at that point: iput's share and the checkout-side arm that retires
  `DepShr` (B″-tx4 and B″-tx5 close both).

  **AS LANDED — B″-tx3: THE ARM MOVES INTO THE CHECKOUT, AND THE READ ARM
  WITH IT.**

  THE DEAD DESCRIPTOR WENT FIRST.  `Xv6Cameras.ic_dep`'s `DepRef` — "iput's
  authority-side window exit, which deposits its WHOLE reference" — had NO
  PRODUCER anywhere in this kernel: iput's window exits through
  `IcacheEscrow.ic_held` and its freeze window through `DepFrz`.  It cost
  `ic_escrow_body_cover` an alternative nothing could ever populate and every
  arm-generic lemma a branch.  Retired; every positional
  `destruct d as [| … ]` in `IcacheEscrow.v` loses a slot.

  A `DepShr` OUT-STATE USED TO STAND AT EVERY LOCK, AND IT IS A REAL STATE.
  Under B″-tx/-tx2 the arm was a fupd on the deposit `ilock`'s post handed out
  (`ic_arm_tx_log`, `ic_shed_rd`), and `ilock` RETURNS between the two: the
  escrow is closed at a bundleless descriptor across a program step, which is
  exactly what another thread's commit can open.  The same held at the far end
  (`ic_disarm_tx` then `iunlock`) and, worse, ACROSS THE WHOLE FILL — the
  uncached arm holds its deposit through `bread`.  Two lemmas move it:

  * `IcacheEscrow.ic_swap_checkout_gen` states the checkout in WAND form — the
    body comes back as `ic_out_rd d inum -∗ ic_escrow_body`, so the caller
    picks the descriptor BEFORE the ghost step and owes exactly what that
    descriptor's arm keeps.  `ic_swap_checkout` is that plus `ic_out_rd_none`
    and is byte-stable.
  * `IcacheEscrow.ic_swap_park_dep` is the mirror at the park: the two
    conversions (`ic_disarm_tx_body`, `ic_unshed_rd_body`) run under the
    caller's OWN opening of the escrow and then `ic_swap_park`, so the
    descriptor is retired in the step that parks the payload.  A `DepShr` that
    exists only between two bupds inside one opening is not a state.

  ONE CONTRACT, THREE ARMS, AND FOUR BYTE-STABLE READINGS.
  `SpecIlock.wp_ilock_dep_sconf_body` and `SpecIunlock.wp_iunlock_dep_sconf_body`
  take the descriptor; `wp_ilock_sconf` / `wp_ilock_tx_sconf` and
  `wp_iunlock_sconf` / `wp_iunlock_tx_sconf` are their `DepShr` and `DepTx`
  readings (`wp_ilock_sconf_of_dep` / `wp_ilock_tx_of_dep`,
  `wp_iunlock_sconf_of_dep` / `wp_iunlock_tx_of_dep`) and not one of the four
  statements moved.  What the three arms SHARE is `IcacheEscrow.ic_dep_shr` —
  the caller's generation-named slice, identical at `DepShr`, `DepTx` and
  `DepRd`; what DIFFERS is two projections, `ic_dep_side` (the parked
  transaction share at `DepTx`, `emp` elsewhere) and `ic_dep_held` (the whole
  bundle, or the reader's `ic_rd_held`), with `ic_dep_gname_of_shr` /
  `ic_dep_rd_shr` / `ic_dep_own_of_shr` / `ic_dep_held_loaded` the four
  readings.  Inside `ProofIlock` the three stage predicates (`il_cont`,
  `il_epilogue`, `il_load`) take the descriptor and `il_payload` is the
  checkout's outcome at either arm; its UNLOADED alternative carries
  `⌜ic_dep_rd d = false⌝`, which is what says the read arm never meets the
  fill.  `wp_ilock_tx_of_sconf`, `ic_shed_rd`, `ic_shed_rd_body` and
  `ic_unshed_rd` retire.

  THE READ ARM'S PREMISE IS THE ONE ITS TWO CALLERS ALREADY PAY, and it is
  what makes a checkout-side shed possible at all.  `DepRd`'s arm keeps three
  quarters of a BUNDLE, so the checkout can only be taken where one exists —
  and at `valid = 0` there is none, which is why B″-join could only shed
  afterwards.  `InodeRegion.ShotK` closes it: `fileread`'s and `filestat`'s
  licence index IS this generation's type one-shot, so
  `ic_swap_checkout_rd` kills the `valid = 0` outcome INSIDE its own ghost
  step (`ity_pending_shot_excl` against the unloaded payload's `ity_pending`)
  and `ic_loaded_shed` runs before the escrow closes.  The generic contract
  states it as the pure premise `ic_dep_rd d = true -> ∃ ty, o = ShotK ty`,
  which pays for a second thing too: the CACHED arm's `ClaimK` refutation
  reads `dinode_at` off the holder's bundle, and a read-locker's stays in the
  arm.  Both read-lockers are converted, their five `ic_shed_rd` /
  `ic_unshed_rd` fupds are gone, and `ilock`'s post hands out `ic_rd_held`
  directly.

  ALL SIX WITHDRAWAL SITES CONVERTED — `sys_unlink`'s two, `sys_open`'s,
  `create`'s parent and re-locked child, and create's FRESH child behind
  `ProofCreateFreshTy`'s span.  At a quarter site the `ic_shrink_tx` simply
  moves ABOVE the call; the arithmetic is unchanged.  The span was the only
  one with a shape problem — its slot and generation are chosen INSIDE it, so
  the descriptor cannot be fixed by the caller — and the fix is that the
  descriptor need not be: `create_fresh_ty_body` takes `(t, qt)` and the share
  itself, publishes `DepTx (q/2) dev inum g t qt` at the checkout its own
  `ilock` hypothesis performs, and hands the share back BARE on the A-FAIL arm
  (where no lock was taken and create grows the parent's arm back with
  `ic_grow_tx`).  So no `ilock` in this kernel leaves a bundleless arm behind
  any more, and `ic_arm_tx` / `ic_arm_tx_log` / `ic_arm_tx2` have no walk-side
  caller left.

  WHY `ic_held` NEEDED A PIN AND THE OTHER TWO DID NOT (B″-tx5 built it):
  its window spans iput's `acquiresleep` (+0x3c..+0x5e), where the slot's
  descriptor variable is inside the ENTRY'S SLEEPLOCK (`ic_tok cn k`), not in
  iput's hand and not in the escrow, and `ic_held` holds only cells, `ic_mid`
  and half of `ic_id` — none of which can carry a transaction id, so a share
  parked there would come back from `ic_open_held` at an EXISTENTIAL `(t, q)`
  that iput could not rejoin with the residue its caller must get back.  Two
  escapes were checked and both fail: parking a WHOLE `LogInv.log_tx` element
  requires iput to hold the whole token, which `sys_unlink`'s `su_tail_e` —
  the arm that calls `iunlockput` with a second inode still write-locked at a
  quarter — cannot supply; and parking the arm in `InodeRegion`'s registry
  instead moves the share out of the slot, where the per-slot cover lemma
  cannot see it.


  **AS LANDED — B″-tx4: THE RETIREMENT SIDE, AND `DepShr` GOES.**

  ONE GENERIC FORM PER LOCK FUNCTION, AND EVERY PUBLISHED CONTRACT IS AN
  INSTANCE OF IT.  `SpecIunlockput` gained
  `wp_iunlockput_dep_sconf_body` / `wp_iunlockput_dep_gen_body` — the park's
  descriptor chosen by the caller under the pure premise
  `ic_dep_shr d = Some (s, dev, inum, gy)`, taking `IcacheEscrow.ic_dep_held`
  in place of `ic_loaded` and handing `ic_dep_side d` back in the post — and
  the four readings became `wp_iunlockput_sconf_of_dep` /
  `_gen_of_dep` / `_tx_of_dep_sconf` / `_tx_of_dep_gen`.  `ProofIunlockput`
  proves the two generic forms (`wp_iunlockput_dep_gen` walks the code, its
  single `IU.wp_iunlock_dep_sconf` call takes `d`; `wp_iunlockput_dep_sconf`
  is the counted seal over it) and derives the rest.  THE SCONF FORM CARRIES
  THE BUDGET HALF ONLY (`log_opb` in, `log_opb` out): at `DepTx` the caller's
  token is part-parked and it cannot present `log_op`, and the parked share
  comes home as `ic_dep_side d`, so the `_tx_` reading rejoins it there and
  the `DepShr` reading framed a whole `log_tx` across the call instead.

  ALL ~22 RETIREMENT SITES DROPPED THEIR `ic_disarm_tx` FUPD: `ProofCreate`
  ×11 (not ×9), `ProofSysUnlink` ×4, `ProofSysOpenTails` ×4 (three
  iunlockput, one iunlock), `ProofSysUnlinkTails` ×2, `ProofSysMknod`,
  `ProofSysMkdir`.  A half-share site simply takes the `_tx_` contract
  outright — its `with`-list and its `iIntros` do not move, it gains the
  `g = icfg_log` premise and loses six lines; a quarter-share site takes the
  `_dep_` one at the descriptor it already names and receives the quarter in
  the post instead of before the call, which moves the token-rejoin block
  (`log_tx_add`/`log_tx_full`) three lines down.

  `DepShr` IS GONE, and with it every bundleless lock state.  Nothing
  published one: `ilock` publishes its final arm at the checkout (B″-tx3) and
  the park now retires it in the ghost step that parks the payload — for the
  READ arm too, which is the one real proof change:
  `IcacheEscrow.ic_swap_park_arm` takes its payload as a WAND from what the
  arm keeps (`ic_out_rd d inum -∗ ic_payload …`), so `ic_rd_join` runs INSIDE
  the park's own step and `ic_swap_park_dep` deposits no intermediate
  descriptor at all.  `ic_swap_park` survives as its `ic_dep_rd d = false`
  reading.  Retired with their last consumer: `ic_arm_tx_body`,
  `ic_disarm_tx_body`, `ic_arm_tx`, `ic_disarm_tx`, `ic_arm_tx_half`,
  `ic_disarm_tx_half`, `ic_unshed_rd_body`, the never-consumed two-slot family
  (`ic_tx_dep2`, `ic_tx_dep2_intro`, `ic_tx_dep2_open`, `ic_arm_tx2`,
  `ic_disarm_tx2_fst`, `ic_disarm_tx2_snd`), `SpecIlock.ic_arm_tx_log` and
  `SpecIunlock.ic_disarm_tx_log`, and the three `DepShr` contract readings
  (`wp_ilock_sconf` / `wp_iunlock_sconf` / `wp_iunlockput_sconf` /
  `wp_iunlockput_gen` with their bodies, their `_of_dep` derivations,
  `wp_iunlock_tx_of_sconf`, and their `Parameter`s in `ILOCK` / `IUNLOCK` /
  `IUNLOCKPUT`).  `ic_shrink_tx` / `ic_grow_tx` and `ic_tx_dep_at` stay: they
  are what a two-lock walk moves between.

  WHAT B″-tx4 LEFT FOR B″-tx5, and the design it wrote out for it: iput's
  share, the three-alternative cover and the pool-side twin.  The two
  corrections to the ruling that the code forced are below, and both landed
  as written.

  CORRECTION 1: THE PIN GHOST MUST BE AN `icfg` FIELD, NOT A FIELD OF
  `ic_names`, AND THE REASON IS ONE PREDICATE.  The mid-free park is
  `IcacheEscrow.ic_payload_arm`'s frozen alternative, and `ic_payload_arm`
  takes NO `cn` (37 sites in `IcacheEscrow.v` alone, plus `ProofIput`); a
  per-slot ghost named through `ic_names` would give it one.  An `icfg` field
  is ambient and costs no arity anywhere, which is the rule §5c already
  states.  The cheapest shape is `icfg_frzm`'s verbatim, at the slot key and
  the pair value: `hpnUR := gmapUR nat (dfrac_agreeR (leibnizO (option (nat *
  Qp))))`, one `inG`, one gname, `hpn_at k q o` / `hpn_h` / `hpn_full` with
  `frzm_agree`/`_update`/`_split`/`_join` cloned, and a `hpn_boot_map` over
  `seq 0 NINODE` that `icfg_alloc` mints and `IcacheBoot`'s escrow loop hands
  out one whole element per slot (`gset_to_gmap_singletons` needs
  generalizing from `Z` keys to any `Countable`).  `icache_boot_at` /
  `icache_boot` / `FsCfgBoot.fs_kit_icache` and its three siblings gain the
  premise, exactly as they did for `icfg_pext` in C-3b.

  CORRECTION 2: THE PIN CANNOT SIT BESIDE THE ARMS, IT HAS TO SIT INSIDE
  THEM.  A body-level `(hpn_full k None ∨ ∃ t q, hpn_h k (Some (t,q)) ∗ t ↪{#q})`
  beside the five-way disjunction is refutable at an empty `ln_tx` authority
  but says nothing about WHICH arm is standing, so it does not refute
  `ic_held`.  The placement that does is per-arm, LAST conjunct each:

  * `hpn_full k None` in `ic_out`, `ic_mid_arm`, `ic_empty_arm` and
    `ic_payload_arm`'s LEFT alternative;
  * `∃ t q, hpn_h k (Some (t, q)) ∗ t ↪[ln_tx icfg_log]{#q} tt` in `ic_held`
    and in `ic_payload_arm`'s FROZEN alternative.

  The transitions all have the whole variable in the right hand at the right
  step: iput enters `ic_held` off `ic_open_auth_ref`'s opening of PARKED (it
  takes the payload, hence the LEFT alternative's whole pin), sets it to
  `Some (t, q)`, parks half plus the share and keeps half; `ic_open_held`
  agrees the two halves, so it returns the share AT THE NAMED `(t, q)` —
  which is the whole point — and iput rejoins, sets `None` and puts the whole
  pin into `ic_out` at `ic_close_out_frz`.  `ic_swap_park_frz` (+0x70) does
  the reverse: it opens `ic_out`, takes the whole pin, sets `Some (t, q)`,
  parks half plus the share in the frozen payload alternative, hands iput the
  other half; the +0x8a eviction agrees and takes the share back.  `DepFrz`
  needs no pin at all — the DESCRIPTOR is in iput's hand across that window,
  so `(t, qt)` go in as two more fields of the constructor and the share
  rides in `ic_out_frz`, exactly as `DepTx`'s does in `ic_dep_own`.

  THE CONTRACT SIDE, MEASURED.  `SpecIput.wp_iput_gen_body` takes
  `t ↪[ln_tx icfg_log]{#q} tt` beside its `log_opSe` and hands it back beside
  `log_opS` (bundle it as `LogInv.log_opSet g u Sb e t q` the way `log_opSt`
  bundles the closed form, so the ~10 threading sites move by substitution);
  `wp_iput_sconf` is BYTE-STABLE, derived by `log_op_split` + framing the
  residue, exactly as `wp_iunlockput_sconf` was derived here.  `ProofIput`
  threads the pin half and the two binders `(t, q)` through `ip_free_entry`,
  `ip_free_locked`, `ip_free_offlock`, `ip_tail`, `ip_tail_exit` and
  `ip_epilogue` — six ~50-hypothesis statements and their call boundaries —
  and the share itself only outside the windows.  `SpecIunlockput`'s two
  generic bodies relay it (their interior `IP.wp_iput_gen` call is the one
  site).  Callers: `LinkIput`, `ProofDirlink`, `ProofFileclose`,
  `ProofIreclaim` ×2, `ProofIunlockput`, `ProofKexit`, `ProofNamex`,
  `ProofSysChdir`, `ProofSysLink` — every RUNTIME one already holds a share.
  `ProofIreclaim` IS INSIDE A TRANSACTION (checked: it calls `begin_op` at
  +0x1e and `end_op` after the iput, and it is already a
  `wp_ilock_tx_sconf` caller, i.e. it holds `log_tx`), so it needs no
  exemption and the `rg := false` GEN contract keeps only its regime
  round-trip, not a token-free form.

  FINDING, AND IT IS THE POOL-SIDE TWIN'S: **`X = ∅` AT AN EMPTY `ln_tx`
  AUTHORITY IS FALSE AS STATED.**  `ipool_body` holds `ipool_xkey X` and
  `ipool` holds the other half at `(P ∖ O) ∪ T`, so `X` is the pending/await
  rows TOGETHER WITH the transit set.  An `ipool_ext` row deposited by iput's
  free path stands until a later `iget` of that inum redeems it — arbitrarily
  many transactions later — so no share of the depositing transaction can be
  parked for it, and `X` is not empty at a commit.  What IS refutable is the
  `T` half (a walk between an eviction's identity flip and its deposit holds
  the itable lock, hence is inside a transaction), and for the `P ∖ O` half
  the collection has to read the inum's bundle REGION-side, which is what
  C-3c's `FsCollect.col_free_slot_acc` and `ireg_slot`'s PENDING arm exist
  for.  Whoever writes the twin must therefore SPLIT `ipool_body`'s `X` into
  the two parts (or carry `T` as its own key) before it can state anything at
  all; taking `X = ∅` as a premise would be a premise nobody can discharge.

  REMAINS: the pool-side twin at the shape the finding forces (see B''-tx5).


  **AS LANDED — B''-tx5: THE PIN, IPUT'S SHARE, AND THE COVER AT THREE.**

  THE LOCK-WINDOW PIN IS AN `icfg` FIELD AND IT SITS INSIDE THE ARMS, exactly
  as B''-tx4's two corrections said.  `Xv6Cameras.hpnUR := gmapUR nat
  (dfrac_agreeR (leibnizO (option (nat * Qp))))` (one `inG`,
  `IcacheRef.icfg_hpn`, vocabulary `hpn_at`/`hpn_h`/`hpn_full` with
  `hpn_agree`/`_update`/`_split`/`_join`/`_full_update` cloned off `frzm`'s);
  `hpn_boot_map` is minted BY `icfg_alloc` rather than passed to it -- one
  whole element per SLOT at `None` is a fact that file knows in full -- and
  `hpn_boot_split` fans it out for `IcacheBoot`'s escrow loop, which puts one
  into each `ic_empty_arm` it builds.  `icache_boot_at`/`icache_boot` and
  `FsCfgBoot.fs_kit_icache`/`_rest` (with their two `_open`s) gained the
  premise LAST, so no destructuring pattern above it moved.

  PER ARM, LAST CONJUNCT EACH: `IcacheEscrow.ic_pin_rest k` (`hpn_full k
  None`) in `ic_out`, `ic_mid_arm`, `ic_empty_arm` and `ic_payload_arm`'s LEFT
  alternative; `ic_pin_tx k` (`∃ t q, hpn_h k (Some (t, q)) ∗ t ↪[ln_tx
  icfg_log]{#q} tt`) in `ic_held` and in `ic_payload_arm`'s FROZEN
  alternative.  `ic_pin_tx_no_ops` is the refutation the commit reads;
  `ic_pin_enter`/`ic_pin_exit` are the two movers and `ic_close_held_tx` is
  the +0x3c entry.  `DepFrz` gained `(t, qt)` as FIELDS and parks its share in
  `ic_out_frz` (`ic_out_frz_no_ops`).  The ~40 sites this moved are all inside
  `IcacheEscrow.v` bar four: `ProofIget`'s recycle (three destructuring
  patterns), `ProofMain`'s boot call, and `ProofIput`.

  `ic_slot_cover` HAS THREE ALTERNATIVES -- not live, pool row, bundle inside
  at a share whose double is invalid -- and `ic_escrow_body_cover` /
  `ic_escrow_body_cover_all` are the per-slot and fifty-slot readings.  **That
  is the lemma lane C calls**, and there is nothing per-slot left in it: the
  old alternative (d) was iput's three windows and all three are now refuted
  at an empty `ln_tx` authority.

  IPUT'S SHARE, AND WHO PAYS FOR IT.  `SpecIput.wp_iput_gen_body` takes
  `LogInv.log_opSet g u Sb e t q` (the new bundle: `log_opSe` beside `t
  ↪[ln_tx g]{#q} tt`, in `log_opSe`'s own position) and hands `log_opS` plus
  the share back on every arm, under the pure premise `g = icfg_log`;
  `wp_iput_sconf` gains ONLY that equation, because its `log_op` carries the
  whole element and the derivation halves it.  `ProofIput` threads the pin
  half and `(t, q)` through `ip_free_entry` (premise, and both exits: the
  share on Exit A, the pin half on Exit B) and `ip_free_locked` (the pin half
  in, the share out), and the share alone through `ip_tail`/`ip_tail_exit`;
  `ip_free_offlock` and `ip_epilogue` did not move -- the share is framed
  across them in the continuation's closure.

  **NO CALLER OF ANY `iunlockput` FORM FINDS A SHARE, AND THAT IS THE FINDING
  THAT SHRANK THE SWEEP FROM SIXTEEN RESOURCE SITES TO SIXTEEN `eq_refl`s.**
  iunlockput is `iunlock` then `iput`, and the share the WRITE ARM parked
  comes home at the FIRST of the two -- so `SpecIunlockput`'s two generic
  bodies relay `IcacheEscrow.ic_dep_side d` straight on, under the pure
  premise `SpecIunlockput.ic_dep_side_tx d = Some (t, q)` ("the park is a
  write arm's", which every iunlockput in this kernel is; `ic_dep_side_of_tx`
  is the reading) plus `g = icfg_log`.  The two `_tx_` readings are
  BYTE-STABLE.  The sixteen direct `wp_iunlockput_dep_gen` sites (`ProofCreate`
  x11, `ProofSysUnlink` x4, `ProofSysUnlinkTails`) each gained two positional
  arguments and nothing else.

  THE FIVE `wp_dirlink_gen` SITES DO LEND ONE, because dirlink holds no token
  of its own -- a write-locked walk's is part-parked in the escrow -- and its
  "already exists" arm iputs what `dirlookup` found.  `SpecDirlink`'s gen form
  takes the share in and out (`ProofDirlink` threads it through `dl_after_body`
  and `dl_scan_body`); the counted form gains only `γ = icfg_log` and halves
  its `log_op`.  create's FILE arm lends its free residue; its two dot links
  and its parent link shrink an escrow arm by an EIGHTH across the call and
  grow it back (`ic_shrink_tx`/`ic_grow_tx`); sys_link splits a quarter out of
  its write-arm bundle's residue.  The other direct iput callers pay less:
  `ProofIreclaim` and `ProofNamex` halve a token they are holding,
  `ProofFileclose`/`ProofKexit`/`ProofSysChdir`/`ProofSysLink` add one
  `eq_refl`-or-`Hclog` for the equation (`ProofKexit.kx_rest` gained it as a
  premise).

  CONTRACTS WHOSE STATEMENT CHANGED: `SpecIput.wp_iput_gen_body` (+`g =
  icfg_log`, `log_opSet`, the share in the post) and `wp_iput_sconf_body`
  (+the equation); `SpecIunlockput.wp_iunlockput_dep_sconf_body`/`_dep_gen_body`
  (+the equation and `ic_dep_side_tx`); `SpecDirlink.wp_dirlink_gen_body`
  (+the equation and the share) and `wp_dirlink_sconf_body` (+the equation);
  `IcacheBoot.icache_boot_at`/`icache_boot` and `FsCfgBoot.fs_kit_icache` /
  `_rest` / their `_open`s (+the pin row); `IcacheRef.icfg`/`icfg_alloc`;
  `Xv6Cameras.ic_dep`'s `DepFrz`; and inside `IcacheEscrow` the arm-touching
  movers (`ic_payload_to_arm`, `ic_payload_arm_frz`, `ic_payload_arm_decide_frz`,
  `ic_mk_parked`, `ic_mk_mid_arm`, `ic_swap_park_frz`, `ic_open_empty_free`,
  `ic_close_to_empty`+`_core`/`_late`/`_frz`/`_await`, `ic_close_frozen`,
  `ic_open_frozen`, `ic_close_mid_to_parked`, `ic_close_out`, `ic_close_out_frz`,
  `ic_open_held`).  New beside them: `ic_close_held_tx`, `ic_pin_*`,
  `ic_out_frz_no_ops`, `LogInv.log_opSet`+`_split`/`_intro`.

  REMAINS -- THE POOL-SIDE TWIN, AND THE SHAPE IS NOW FORCED.  B''-tx4's
  finding stands: `ipool_body`'s `X` is the pending/await rows TOGETHER WITH
  the transit set, and `X = ∅` at an empty `ln_tx` authority is false as
  stated.  What tx5 adds is that the TRANSIT half is now payable: the set is
  grown only by `ipool_evict_lend`, which iput calls holding a share of its
  caller's transaction, so a transit row can park one and the commit refutes
  it exactly as it refutes iput's three windows.  The share must sit in
  `ipool_body` and not under the itable lock for the commit to see it, which
  is what "carry the transit set under its own key" means: a new ambient
  gname beside `icfg_pext`, the invariant holding `⌜region_inums nib = O ∪ X
  ∪ T ∪ ic_live_inums ids⌝` with `[∗ set] z ∈ T, ∃ t q, t ↪[ln_tx
  icfg_log]{#q} tt` beside it, and `ipool_evict_lend`/`ipool_put` moving the
  share in and out.  The PENDING/AWAIT half is not a residue at all: its
  region slot is on `ireg_slot`'s PENDING arm carrying C-3c's
  `ireg_top_park`, so the collection reads the bundle region-side through
  `FsCollect.col_free_slot_acc`.  [BUILT by C-4 — and its LAST sentence is
  WRONG: the pending/await row is parked BEFORE iput's off-lock deposit, so
  the region slot is still MARKED for the length of that window.  See C-4's
  residue (F).]
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

  **AS LANDED — C-2: THE COLLECTION'S ARITHMETIC CLOSES, AND FOUR SUPPLIERS
  DO NOT EXIST.**

  `iris/FsCollect.v` is the collection at quiescence with its sources named
  as ONE predicate, `col_hand γfs γi ist nib sb sbb used I m Lb C home`, and
  the whole of `snap_ok` read off it: `col_snap_bytes`, `col_snap_ok`,
  `col_snap_ok_ex` (the `∃ S` form the parked law is stated at).  It is a
  LEAF over the predicate layer on purpose — the commit's cone must not
  acquire the boot chain — and every conclusion is PURE, so nothing is
  consumed and a caller hands all fifty escrows back untouched.  The block
  map is `col_view C home = fs_restrict (dv_of_D C) home`, which is
  `FsCrash.fs_commit_L_sector0_rec`'s `D'` on the nose, `C` being the very
  cache map `LogInv.log_state` carries.

  WHERE EACH CLAUSE COMES FROM.  `sk_sb`/`sk_bmap`/`sk_rec`/`sk_blk`/`sk_ind`
  are AGREEMENTS against the byte authority and need no share (`col_blk`,
  over `FsBlocks.fsblock_q_home` + `map_seqZ_inj`); `sk_pool` and `sk_bsz`
  off the free pool and the log invariant's own row (b); `sk_meta_used` and
  `sk_own_used` by the pool refutation (`free_pool_used_q`) plus the three
  FULL-fraction metadata owners (block 1, the bitmap block, the region's
  record blocks); `sk_disj` and `sk_slot` off the `∗`; `sk_links` off
  `FsState.fs_links_valid`; the geometry off `col_geom`, whose every clause
  is `FsCfgBoot.fs_boot_image_wf`'s — witnessed at the real instance by
  `FsCollectImg.img_col_geom` (plan §7), in its own file so `FsCollect`
  stays a leaf.

  THE SHARE LAW THE DESIGN'S ¾ RESTS ON IS `FsCollect.dfrac_nvalid_pair`:
  two shares whose DOUBLES are invalid have an invalid PRODUCT.  That is
  what makes cross-inode disjointness work between an unlocked inode at 1
  and a read-locked one at ¾ — `blk_owned_ne_full` and `blk_owned_ne_34` are
  its two instances, and the general form is what the cover lemma's
  existentially-bound `dq` actually needs.

  FOUR SUPPLIERS OF `col_hand` DID NOT EXIST IN THE TREE, and none was a proof
  difficulty (the full list is in `FsCollect.v`'s header).  Three are now
  supplied — (A) by C-3b, (C) by C-3a, (D) by C-3c; (B) is what remains:

  (A) THE PARTITION (B″-join's open item), unchanged in shape.  MEASURED
  here and it is what makes the increment delicate: the row is FALSE between
  `ipool_take` and the escrow deposit, and at iget's recycle those are two
  ghost steps — `ipool_take` under `fupd_wp` just before the `+0x72` store,
  the deposit inside that store's atomic update.  Nothing is unsound today
  (the leading fupd fuses with the step's own mask change, so no other
  hart's ghost step interleaves), but the take must move INSIDE the atomic
  update, beside the identity flip; `ipoolN` is outside that update's mask
  already.

  (B) ALTERNATIVE (d) of `ic_escrow_body_cover` — CLOSED by B″-tx5.
  `ic_slot_cover` has THREE alternatives and there is nothing per-slot the
  collection cannot close; what remains of supplier (A) is the pool-side
  twin's transit half (B″-tx5's REMAINS).

  (C) NOBODY OWNED BLOCK 1 — closed by C-3a below.  `col_hand` wants
  `FsState.sb_owned`: the superblock's block at FULL fraction plus its
  parse.  It must be fraction 1 and NOT discarded — `sk_own_used` refutes a
  node owning block 1 through `blk_owned_ne_full`, and a discarded share
  does not refute ¾ — and it has to reach the commit through `log_ctx`,
  which is the only persistent bundle `wp_end_op` carries.

  (D) A FREE INUM'S ABSTRACT NODE WAS UNTIED TO ITS RECORD — closed by C-3c
  below.  The pool's marker arm held the era's `top_frag` UNTIED while the
  region held the record, so at a free inum the commit could prove neither
  `sk_rec` nor `sk_links`.

  NOT LANDED, and blocked on the rest of them: the law parked in `log_ctx`,
  `end_op`'s call at `outstanding = 0`, the two commit permits at
  `dsnap_step_of`, the receipt's snapshot state, `P_fs`'s conjunct →
  `P_dur (fr_D r)`, and the `fdn_*`/`riscv_dview_name` adequacy sweep.  The
  shape of the law is fixed by this increment: `col_snap_ok_ex` is what it
  concludes, and `col_hand` is what it must assemble.

  **AS LANDED — C-3a: SUPPLIER (C), BLOCK 1 IS OWNED, AND ITS HOME IS
  `log_ctx`.**

  `iris/SbPark.v` is the park: `sb_park γfs sb` is
  `inv sbN (∃ bs, ⌜fs_parse_sb (fun _ => bs) = Some sb⌝ ∗ fsblock
  (fs_bytes γfs) SB_BNO bs)`, with `sb_park_alloc` and `sb_park_acc` — open,
  read, close, the run handed back verbatim, because every conclusion the
  collection draws from block 1 is pure.  `LogInv.log_ctx` gains
  `sb_parked γfs` (`= ∃ sb, ⌜fs_sb_ok sb⌝ ∗ sb_park γfs sb`) as its LAST
  conjunct: no arity change, and the only patterns that moved are the four
  `rewrite /log_ctx` sites inside `LogInv.v` itself (`log_ctx_sb` is the new
  projection).  `FsCollectImg` restates the accessor in the vocabulary
  `col_hand`'s superblock leg actually asks for — `sb_park_owned_acc` and
  `log_ctx_sb_owned_acc`, both concluding `FsState.sb_owned` through
  `FsBytesGamma.gamma_blk_owned`.  The non-vacuity witness is
  `FsCollectImg.log_ctx_sb_not_owned`, and it is `sk_meta_used`'s block-1
  leg end to end: off `log_ctx` alone, no bundle's block is `SB_BNO`, by
  `blk_owned_ne_full` against the park's FULL share.  A `DfracDiscarded`
  park does not close that goal, which is the whole reason the run is at
  fraction 1.

  NOT `bitmap_body` NOR `ireg_body`, AND THE REASON IS TIMING, NOT
  FOOTPRINT.  Both invariants are allocated in the era fupd
  (`FsCfgBoot.fs_cfg_alloc`, via `bitmap_inv_alloc` and the icache boot) and
  handed to fsinit as PERSISTENT credentials, while block 1's run is out of
  every invariant from that same fupd until fsinit is past its `readsb`:
  fsinit pins what bread returned by an agreement against the run it holds
  (`ProofFsinit`, the `fs_bytes_agree_any` just after the bread at +0x12).  An invariant cannot be
  allocated without its body, so there is no later deposit into either one.
  `initlog` is the first point at which the run is free AND a bundle the
  commit will hold is being built — and `SpecEndOp.wp_end_op` carries NO fs
  invariant at all (only `log_ctx`, `fs_crash_seam`, `gen_cert`, `bio_ctx`),
  so `log_ctx` is the only door in any case, exactly as C-2's finding (C)
  said.  Measured: `log_ctx` is destructured in ONE file (`LogInv.v`, four
  sites) and built at ONE site (`ProofInitlog.v`), so the conjunct costs the
  ~75 files that thread it nothing.

  CONTRACTS WHOSE STATEMENT CHANGED.  `SpecInitlog.wp_initlog_sconf_body`
  gains two binders (`bs_sb`, `sbrec`), two pure premises (`fs_sb_ok sbrec`,
  `fs_parse_sb (fun _ => bs_sb) = Some sbrec`) and the run itself as its
  last resource premise; initlog allocates the park in the same ghost step
  as the "log" lock's seal.  `SpecFsinit.wp_fsinit_sconf_body` gains the
  binder `sbrec` and the same two premises (as (a'), beside the image
  premise (a)), and its POST LOSES `fsblock (fs_bytes γfs) 1 bs_sb` — the
  run `ProofForkret` used to drop is spent inside.
  `FirstTok.first_fsinit_pures` gains the two facts as its last two
  conjuncts, which is how forkret supplies them;
  `first_fsinit_pures_of_image` already took both (the parse is its
  `Hparse` premise, discharged at the literal image by
  `FsImgCheck.fsimg_parse_sb`; `fs_sb_ok` is its `fsimg_wf_sb`), so nothing
  is recomputed on the adequacy cone.

  WHAT THE LAW STILL OWES ON THIS LEG.  `log_ctx`'s conjunct closes over
  `sb`, so a holder of `log_ctx` ALONE learns `fs_sb_ok sb` and the parse
  but not that `sb` is the boot configuration's record — `log_ctx` has no
  room for `fsc_bmapstart`/`fsc_size` and gaining a parameter would sweep
  ~75 files.  That identification is the LAW's business and it is free
  there: the law is assembled at fsinit/initlog, which hold the CONCRETE
  `sb_park γfs sb` at the config's record beside `bitmap_inv`, `ireg_inv`
  and `ic_escrows`, so the closure fixes all of them together.  Should the
  collection instead take its own `sb` from the park, `col_geom` follows
  from `fs_sb_ok sb` plus `sb_bmapstart sb = fsc_bmapstart` and
  `sb_size sb = fsc_size`: `fs_sb_ok` pins `logstart`, `nlog`, `inodestart`
  and `magic` outright, and `cg_nin` comes for free because
  `sb_ninodes sb / 16 = sb_bmapstart sb - sb_inodestart sb - 1`.  Those two
  field ties are the whole of what a `log_ctx`-only holder lacks.

  **AS LANDED — C-3b: SUPPLIER (A), AND THE PARTITION HAS THREE PARTS.**

  The pool's own invariant now CARRIES the partition.  `IcacheEscrow`'s
  `ipool_body` gains `cn` and `nib` and holds
  `⌜region_inums nib = O ∪ X ∪ ic_live_inums ids⌝` beside a QUARTER of every
  slot's `ic_id` (`ic_ids cn ids`, `length ids = NINODE`); `islot2`'s and
  `islot_empty`'s share drops from a half to a quarter to pay for it, and the
  escrow arm's half is untouched, so the five arms and `ic_escrow_body_ident`
  are byte-stable.  `ipool_inv` gains `cn`/`nib` (`is_itable2` already carried
  both, so its arity does not move); `ipool` gains a TRANSIT set `T`, `∅` in
  `itable_res2`.

  IT IS A THREE-WAY PARTITION AND NOT B″-join's TWO-WAY ONE, and that is the
  finding.  "`O` together with the live slots' identities exhausts
  `region_inums nib`" is FALSE in this kernel, for one reason with two faces
  — an inum a WALK is carrying.  (i) iput's free path deposits an AWAIT row
  (`ipool_ext`), which cannot live in an invariant at all (`escA_inv` is an
  `inv`; that is B″-esc's own reason for splitting the pool), so it sits under
  the itable lock in `ipool`'s `P ∖ O` for as long as it stands — and it holds
  NO `inode_owned_era`, so no partition could have handed the commit a bundle
  for it anyway.  (ii) an eviction's identity flip and its deposit are two
  ghost steps: the deposited bundle's three ledger columns (`icnt_half` at 0,
  the mirror, `ifreeze_off`) do not exist until the refcount store has fired,
  so the evicted inum is in neither part in between.  Both go into one third
  part `X`, PINNED and not free: a new ambient gname `icfg_pext` whose other
  half is a conjunct of `ipool` at `(P ∖ O) ∪ T`, so only a lock holder can
  grow `X` and the row cannot go vacuous by taking `X` to be the region.  At
  boot `X = ∅` and the partition IS the two-way one (`ipool_alloc_inv`).  What
  it leaves the collection is ONE residue, the pool-side twin: an inum in `X`
  has no bundle anywhere.  B″-tx4's finding split it in two and B″-tx5's
  REMAINS states the shape that closes each half.

  THE MOVERS ARE ACCESSORS, NOT PLAIN FUPDS, and that is what forced C-3b's
  first commit: the pool's quarter has to be in the caller's hand at the same
  ghost step as the escrow arm's half, because the flip needs the whole cell
  and the partition moves with it.  Each lends a HALF (its quarter joined to
  the table's), so `ic_open_empty_free` and the `ic_close_to_empty` family are
  called UNCHANGED.  `ipool_take_lend` — iget's recycle: hands the row out,
  takes the inum out of `O` or out of `X`, lends the quarter, and its wand
  records the new identity.  `ipool_evict_lend` — iput's two evictions: flips
  live → dead and puts the inum into `X`.  `ipool_id_lend` — iget's `+0x6e`
  dev re-tag, where the slot is dead on both sides so only the recorded words
  move.  `ipool_put` — out of `X` into `O`, or left in `X` when the row is a
  pending/await arm; it needs no identity at all.  The `+0x6e` PEEK re-tagged
  nothing even before, so it now runs at the table's quarter alone
  (`ic_open_empty_dev_peek`), and `ic_open_held` takes the table's share at a
  fraction parameter `qid` (it only READS it).

  THE TWO ACCESSOR LEMMAS THE COLLECTION CALLS.  `ipool_inv_acc` (restated:
  hands out `O`, `X`, `ids`, the row and the fifty quarters, read-only), with
  its pure reading `ipool_cover_inum`; and `ic_ids_pin` — the identity the
  partition records for slot `k` IS the escrow arm's, one cell and two shares.
  Exercised at the real shape by `ipool_partition_cached`: an inum that is
  neither an ordinary row nor in transit is CACHED, and this names the slot,
  reads the escrow's own identity half off the open body and pins it to that
  inum — which is exactly what `ic_escrow_body_cover`'s four alternatives are
  stated at.  Two set moves `set_solver` will not do (they need the decidable
  split on `y = z`) are `gset_move_out`/`gset_move_mid`.

  CONTRACTS WHOSE STATEMENT CHANGED.  `IcacheRef.icfg` gains `icfg_pext` and
  `icfg_alloc` a conjunct; `IcacheBoot.icache_boot_at`/`icache_boot` gain the
  premise `ghost_var icfg_pext 1 ∅` and allocate the pool invariant AFTER the
  escrow loop (the quarters do not exist until that loop re-tags the fifty
  identities at the values the entry cells hold);
  `FsCfgBoot.fs_kit_icache`/`_open`/`_rest`/`_rest_open` gain the same
  conjunct.  `IcacheEscrow.ipool_alloc_inv`, `ipool_inv_acc`, `ipool_put`,
  `ic_open_held` and `is_itable2_pool` changed shape; `ipool_take` is gone,
  replaced by `ipool_take_lend`.  UNTOUCHED: the escrow's five arms,
  `ic_escrow_body_cover`/`ic_slot_cover`, `is_itable2`'s and `itable_res2`'s
  arity, and every consumer of `ipool` outside `ProofIget`, `ProofIput` and
  `ProofIdup` (which only passes it through).

  **AS LANDED — C-3c: SUPPLIER (D), AND THE FRAGMENT PARKS WITH THE
  RECORD.**

  `InodeRegion.ireg_top_park γfs z d` is the park: `∃ n, ⌜di_type d = 0 →
  ireg_bare d ∧ n = free_node d⌝ ∗ top_frag …`, a conjunct of `ireg_slot`'s
  IN sub-arm and of its PENDING arm — exactly the two arms that hold
  `z ↪[γi] d`.  THE TIE IS GUARDED BY THE TYPE, and that is what makes it
  free at every mover: at a type-0 record the node is `free_node d`
  outright (`fn_bare` pins the entry array and the block map, so
  `free_node_of_bare` leaves no choice), and at a claim box the fragment
  rides UNTIED exactly as it did in the pool.  So `ireg_claim_au` carries it
  0 → `fresh_shape` with NO resource move and no `↑ftopN` premise, and
  `ireg_withdraw` hands it to the fill in the shape the marker arm used to —
  `ProofIlock`'s `ireg_top_retag` is unchanged.  Neither of the two shapes
  C-3b measured is what landed: the whole fragment goes region-side (b's
  half) but the tie is guarded (a's), which is strictly cheaper than either.

  THE ROAD BACK TO THE REGION IS THE ESCROW, and that was the whole
  difficulty.  A free record is created by ONE mover — iput's off-lock
  deposit — and the fragment it must park is the one the freed payload
  carried, which the walk gives up at +0x94 when it parks the pool entry.
  The deposit cannot reach the pool (the itable lock went at +0x94) and the
  park cannot reach the deposit; the one thing both open is the per-inum
  escrow.  So the fragment travels the road the standing freeze already
  travels: in at `EscrowInode.escA_alloc`, parked in `escA_body`'s EMPTY
  arm, out at `escA_deposit_acc`.  `ProofIput` moves one hypothesis between
  two adjacent lines; no contract spanning iput's sleeplock window changes.

  A PENDING SLOT IS NOT A RESIDUE.  The deposit re-parks into `ireg_slot`'s
  PENDING arm, which stands until a later claim, so it had to carry the park
  too — and it does, which is why the collection owes nothing extra at a
  freed-but-unrecycled inum beyond (A)'s `X` row.

  THE ACCESSOR IS `FsCollect.col_free_slot_acc`: the pool's ordinary row is
  on its marker arm, which carries `imark`, so the region's own marked arm is
  refuted (`imark_excl`) and the slot is on the IN or the PENDING arm — both
  hold the fragment and the park.  It LENDS a whole
  `FsStateEra.inode_owned_era` at `free_node d` and takes it back (every
  conclusion the collection draws is pure); `col_bundle_free` and
  `col_bundle_of_owned` are the same reading at `col_bundle`'s shape.  It
  lives in a nested section so only those lemmas take the `icfg` parameter,
  and `FsCollect` stays a leaf.  Non-vacuity at the real instance:
  `FsCollectImg.img_col_bundle_free` — at the mkfs image the bundle comes out
  at `FsCfgBoot.img_node`, the very value `ftop_inv`'s map holds at boot, off
  conjunct (14) `fs_region_bare` and nothing else.

  CONTRACTS WHOSE STATEMENT CHANGED.  `EscrowInode.escA_body`/`escA_inv`/
  `escA_alloc`/`escA_deposit_acc`/`escA_redeem`/`escA_await_peel` and
  `pool_pending` gain `γfs`; `escA_alloc` takes the fragment and
  `escA_deposit_acc` hands it out.  `EscrowDeposit.ireg_free_deposit_au`
  gains `↑ftopN ⊆ E ∖ ↑iregN ∖ ↑escAN z` and `InodeRegion.ireg_bare dn'`
  (free at iput: itrunc has zeroed size and addresses) and does the retag
  itself.  `InodeRegion.ireg_slot`/`ireg_slot_intro` gain the park in two
  sub-arms — only the three sites that BUILD those arms moved (the claim,
  the free deposit, boot); the other 30 `ireg_slot_intro` calls re-park the
  arm verbatim and are byte-stable.  `ireg_withdraw` gains the fragment as
  its last output.  `IcacheEscrow.ipool_shape_np`'s marker arm and
  `ipool_shape`/`ipool_ext`'s two in-transition arms LOSE theirs, and with
  them `ipool_shape_await`, `ic_close_to_empty_await`, `ipool_shape_free`,
  `ipool_alloc` and `ipool_alloc_all_free` lose an argument.
  `IcacheBoot.ireg_alloc` gains a record function `D : Z → dinode`, two
  ∀-over-decodings conjuncts (`image_bare`, `image_rec_at`, LAST) and the
  free inums' fragments (`ireg_top_boot`); `FsCfgBoot.ipool_alloc_of_image`
  takes only the LIVE inums'; `image_ireg_premises` gains
  `fs_region_bare … = true`.  `SpecIput`'s off-lock lemma
  `ProofIput.ip_free_offlock` gains `InodeRegion.ireg_bare dn`.
  UNTOUCHED: `log_op`, `wp_end_op`, `fs_crash_seam`, `P_fs`, `log_ctx`,
  `ireg_inv`'s arity, `ic_escrow_body`'s five arms.

  WHAT (D) LEAVES.  Nothing of its own.  `col_hand`'s remaining supplier is
  (A)'s `X` row alone — see B″-tx5's REMAINS; alternative (d) of
  `ic_escrow_body_cover` is gone.

  **AS LANDED — C-4: THE POOL-SIDE TWIN, AND TWO WINDOWS NOBODY HAD NAMED.**

  B''-tx5's REMAINS, at the shape its finding forced.  The transit part of
  C-3b's third component now has its OWN key and its own parked share:
  `IcacheRef.icfg_ptrn` (a new ambient gname beside `icfg_pext`, one
  `ghost_varG Σ (gmap Z (nat * Qp))` in `Xv6Cameras.icacheG`) carries the
  ledger `T`, `IcacheEscrow.ipool_tkey` is its two halves (one in
  `ipool_body`, one in `ipool`) and `ipool_transit T` the shares, one per
  inum in transit.  `(t, q)` are FIELDS for `Xv6Cameras.ic_dep`'s reason
  verbatim (`IcacheTxRefute.tx_two_halves_no_whole`): `ipool_put` has to
  hand the walk back EXACTLY the element it parked, and an existentially
  keyed share cannot be re-identified.  The row is
  `region_inums nib = O ∪ X ∪ dom T ∪ ic_live_inums ids` and the body stays
  TIMELESS.  `ipool_transit_no_ops` is the refutation and
  **`ipool_quiesce_acc`** the commit's door: `ipool_inv_acc` plus that
  refutation, handing out B''-join's own three-part row at an empty `ln_tx`
  authority.

  THE SHARE IS PAID AT `ipool_evict_lend`'s CLOSING STEP, NOT ITS OPENING,
  and that position is forced: the free path's evicting walk has its share
  parked in the escrow's FROZEN arm at the opening and gets it back
  (`ic_pin_exit`) inside the very window the accessor holds `ipoolN` open
  for.  The ledger's VALUE moves at the opening, where both halves are in
  hand; only the resource waits for the close.  iput hands the WHOLE
  `tid ↪[ln_tx icfg_log]{#qtx} ()` over at both eviction sites and takes it
  back at `ipool_put` — nothing between the two uses it, so no split.

  CONTRACTS WHOSE STATEMENT CHANGED: `IcacheEscrow.ipool` (its `T` is a
  `gmap Z (nat * Qp)` and `ipool_xkey` no longer carries it), `ipool_body`,
  `ipool_alloc_inv`, `ipool_evict_lend` (+`(t, q)`, the share at the closing
  wand), `ipool_put` (+`(t, q)`, the share in the post), `ipool_inv_acc`
  (+`T` and the shares); `IcacheRef.icfg`/`icfg_alloc`;
  `IcacheBoot.icache_boot_at`/`icache_boot` and `FsCfgBoot.fs_kit_icache` /
  `_rest` / their two `_open`s (+the ledger, LAST).  The consumer sweep is
  three files: `ProofIput` (the two evict/put pairs), `ProofMain` (one
  destructuring pattern, one `with`-list) and `FsCfgBoot`'s own kit plumbing.
  UNTOUCHED: `log_ctx`, `log_op`, `wp_end_op`, `fs_crash_seam`, `P_fs`,
  `is_itable2`/`itable_res2`'s arity, `ic_escrow_body`'s five arms and
  `ic_escrow_body_cover`.

  **THE ASSEMBLY (items 2–5) IS BLOCKED ON TWO WINDOWS THAT ARE NOT (A)–(D),
  AND FINDING THEM IS THIS LANE'S OTHER RESULT.**  Both are inside ONE
  transaction and therefore unreachable at a commit; neither is PROVED so,
  because neither parks a share of its transaction's `ln_tx` element the way
  `IcacheEscrow.ic_pin_tx` and `ipool_transit` do.  They are recorded as
  residues (E) and (F) in `FsCollect.v`'s header.

  (E) THE CLAIM BOX.  ialloc's `InodeRegion.ireg_claim_au` retags a FREE
  record to a `fresh_shape` one — a NONZERO type by definition
  (`InodeRegion.v:419`) — and the pool row for that inum stays on its MARKER
  arm until the `iget` inside ialloc takes it.  In that window the region
  slot is on `ireg_slot`'s IN arm (`ireg_in d = di_type d = 0 ∨ fresh_shape
  d`), so `FsCollect.col_free_slot_acc`'s `di_type d = 0` premise fails and
  `InodeRegion.ireg_top_park` is on its VACUOUS side: the fragment it carries
  is at an ARBITRARY node.  `FsCollect.col_claim_box_untied` is that
  statement, machine-checked.  So neither `sk_rec` nor `sk_links` can be read
  at the inum — this is (D)'s residue at a record type (D) does not reach,
  and it is NOT (A)'s: the inum is an ORDINARY pool row, in `O`.
  THE FIX IS CHEAP IN SHAPE AND WIDE IN SWEEP, and it is `ireg_top_park`'s
  own: a nonzero-type park occurs ONLY at a claim box (the two arms that hold
  the park are IN, where `ireg_in`, and PENDING, where the type is zero), so
  giving `ireg_top_park` a parked share on its nonzero-type side refutes the
  window outright and lets `col_free_slot_acc` DROP its type premise at a
  commit.  The sweep is `ireg_top_park_nz`/`_retype`, `ireg_claim_au`,
  `ireg_withdraw` and then ialloc's spec and its callers — B''-tx5-sized.

  (F) THE CORPSE BEFORE ITS DEPOSIT, and it CORRECTS B''-tx5's REMAINS.
  "Every `X` inum's region slot is on `ireg_slot`'s PENDING arm carrying
  `ireg_top_park`" is true only AFTER iput's off-lock deposit
  (`EscrowDeposit.ireg_free_deposit_au`, which opens the arm on its MARKED
  alternative).  The pool's pending row is parked at +0x94 and the await row
  at the free path's eviction, BOTH BEFORE that deposit, and until it fires
  the region slot is still MARKED — `InodeRegion.imark` and NO record
  fragment (`ireg_marked_ok` forces a nonzero type there,
  `InodeRegion.v:790`), the fragment being in the walk's own hand.  So such
  an inum has no bundle anywhere, exactly as C-3b's `X` residue said, and
  C-3c's accessor does not reach it.  THE HOOK FOR THE FIX IS THE FREEZE
  COLUMN: `ireg_free_deposit_au`'s own proof reads `f = FrzPost` across that
  window (its regime leg refutes `⌜f = FrzOff⌝` there), so the corpse window
  is exactly "the MARKED arm at a non-`FrzOff` column" and a share parked in
  `ireg_slot`'s freeze clause closes it.

  **AS LANDED — C-5: THE CLAIM BOX IS REFUTED, AND THE COLLECTION READS THE
  TYPE OFF THE REGION.**

  Residue (E) is CLOSED by (B)'s device at the c column, and the whole of it
  is that the c column's VALUE now carries the claiming transaction:
  `Xv6Cameras.ctyval = bv 16 * (nat * Qp)`, `IcacheRef.iclaim z ty t q`.
  `InodeRegion.ireg_cpin c` parks `t ↪[ln_tx icfg_log]{#q} tt` for as long
  as the claim stands and `ireg_in c d` (= `type = 0 ∨ (fresh_shape d ∧
  c ≠ None)`) records that a nonzero-typed IN arm IS a standing claim — so
  at a commit `ireg_cpin_no_ops` reads `c = None` off the empty `ln_tx`
  authority and `ireg_in_quiesce` collapses the arm to `di_type d = 0`.
  `FsCollect.col_region_slot_acc` is the door the assembly calls at EVERY
  region inum whose record the region itself holds: it CONCLUDES the type
  rather than assuming it, hands out `inode_owned_era` at `free_node d` on
  the IN and PENDING arms and `imark` on the MARKED one, and lends
  everything back (every conclusion is pure).  `col_free_slot_acc` is its
  `imark`-fed corollary and has LOST its `di_type d = 0` premise.

  TWO BUNDLINGS ARE WHAT KEEP THE SWEEP SMALL (durable-notes, "REPLACING ONE
  CONJUNCT OF A BIG PAYLOAD BY ANOTHER").  `ireg_cpin` rides in `ireg_fsh`'s
  position as `ireg_shp c f`, so the thirty-odd sites that thread the slot's
  f-shelter through a re-park are byte-stable and only the claim, the
  withdrawal, the freeze mint, the phase step and the free deposit split it;
  and the returned share rides INSIDE `ireg_wd_back`'s ClaimK arm, so
  `SpecIlock`'s fifteen `PlainK`/`ShotK` callers do not move at all — the
  first cut, a separate `ireg_wd_side o` conjunct in the post, broke eleven
  files with "iApply: cannot apply wp_next".

  THE SHARE'S ROUND TRIP, and it is entirely inside create's own span.
  `ProofCreate` splits a second QUARTER off the residue it already names
  (`log_tx_split`, and the new general `LogInv.log_tx_join_q` puts it back)
  and lends it to `ProofCreateFreshTy`'s `create_fresh_ty` at a new binder
  `qc`; ialloc parks it at `ireg_claim_au`; the span's own `ilock` gets it
  back at the fill and hands it out on BOTH arms.  It cannot be the quarter
  the child's checkout parks — the fill parks that at the same instant the
  claim returns this one — which is why it is a second share and not a
  split of `qt`.

  CONTRACTS WHOSE STATEMENT CHANGED.  `IcacheRef.iclaim` /
  `link_claim_agree` / `link_mint_claim` / `link_spend_claim` /
  `iclaim_excl` / `inode_claimed` (+`t`, `qt`, LAST);
  `IgetLic.ilic`'s `ClaimL` and `InodeRegion.ilkc`'s `ClaimK` (+`t`, `q`);
  `InodeRegion.ireg_claim_ok` (its third conjunct is now `v.1 = di_type d`,
  with `Some ExclBot` refuted), `ireg_in`, `ireg_slot`/`ireg_slot_intro`
  (`ireg_shp c f` in `ireg_fsh f`'s position, `ireg_in c d` in the arm),
  `ireg_claim_au` (+the share, +`t q`), `ireg_withdraw` (`ireg_wd_back`'s
  claim arm is a pair), `ireg_claim_ok_ty`, `ireg_rcol_claim_agree`,
  `ireg_claim_no_out`, `IregLinkNz.ireg_boot_no_claim`,
  `IgetLic.iname_not_frozen` (takes `ireg_shp c f`);
  `SpecIalloc.wp_ialloc_gen_body`/`wp_ialloc_sconf_body` (+`t`, `qt` LAST,
  +the share premise, +the share on the no-inodes arm);
  `ProofCreateFreshTy.create_fresh_ty_body` (+`qc`, +its premise, +the share
  on both arms).  `LogInv` gains `log_tx_join_q` and nothing else.
  UNTOUCHED: `log_ctx`, `log_op`, `wp_end_op`, `fs_crash_seam`, `P_fs`,
  `ireg_inv`/`ireg_body`'s arity, `SpecIlock`'s posts, `ic_escrow_body`'s
  five arms, `ipool`'s shape.

  NON-VACUITY (plan §7).  `FsCollect.col_claim_box_no_ops` is the residue
  closed end to end — a slot the pool's marker arm reaches cannot carry a
  nonzero-typed record while no transaction is open — and
  `FsCollectImg.img_col_region_slot` runs the premise-free accessor at the
  mkfs image, getting the bundle out at `FsCfgBoot.img_node`.  THE IMAGE HAS
  NO CLAIM BOXES: `IcacheBoot.ireg_alloc` mints every ledger column at
  `None` (`ireg_claim_ok_none` at both of its arms) and every free record
  bare (conjunct (14) `fs_region_bare`), so the IN arm's nonzero side is
  uninhabited at boot and the first commit meets the free reading at nearly
  every inum of the region.

  **(F) IS NOT LANDED, AND `FsCollect.v` SECTION 5c IS THE WALL,
  MACHINE-CHECKED.**  `col_corpse_not_refuted`: `ireg_fsh` at either window
  phase is the REGIME alone — a persistent `ireg_open` at the runtime index
  — so the clause and an empty `ln_tx` authority coexist.  The fix is (E)'s
  device at the f column: the freeze index `rg` carries the freezing
  transaction and its share, `ireg_fsh`'s two window arms park it beside the
  regime, `ireg_freeze_au` takes it and `EscrowDeposit.ireg_free_deposit_au`
  returns it; the pair must be in the INDEX (not existential) for
  `IcacheTxRefute.tx_two_halves_no_whole`'s reason, and the index is exactly
  where the freezer's own `ifreeze_pre`/`ifreeze_post` fragment already
  re-identifies it.  MEASURED: widening `Xv6Cameras.frz`'s `rg` from `bool`
  to `bool * (nat * Qp)` leaves every `FrzPre rg`/`FrzPost rg` site
  byte-stable (there is not one literal in the tree) and moves ~20
  `rg : bool` binders in eight files plus the four `ireg_regime_true`/
  `_false` readings; the WORK is iput's fraction accounting, because the
  freeze window SPANS the eviction that hands `ipool_evict_lend` the whole
  share, and it lands in the two slowest files in the tree (`ProofIput`,
  `IcacheEscrow`).  AND IT DOES NOT FINISH `X` ON ITS OWN: a MARKED slot at
  `FrzOff` is every cached or pooled inode, so refuting the window yields
  only "an `X` inum's slot is MARKED implies its column is `FrzOff`".
  Ruling that combination out needs a POOL-SIDE witness for `X`'s rows — a
  `reg_half` per pending/await inum inside `ipool_body`, colliding with the
  MARKED arm's `reg_full` — which is `IcacheEscrow.v` and lane B′/C-3b's
  business, not the region's.

  NOT LANDED: the assembly itself — see C-7's closing paragraph for the
  current list.

  **AS LANDED — C-6: THE CORPSE WINDOW PARKS ITS TRANSACTION, AND THE
  POOL-SIDE WITNESS IS A WALL.**

  RESIDUE (F) IS CLOSED, by (E)'s device at the f column and at exactly the
  measured shape.  `Xv6Cameras.frzidx = bool * (nat * Qp)` is the freeze
  phase's index: `rg.1` is RULING G′'s regime arm as before, `rg.2` the
  freezing transaction and its share.  `InodeRegion.ireg_fpin rg` is that
  share (`rg.2.1 ↪[ln_tx icfg_log]{#(rg.2.2)} tt`) and `ireg_fsh` parks it
  BESIDE the regime at both window phases; `ireg_freeze_au` takes it at the
  mint, `IcacheInv.iref_close_last_freeze_store_au` rides it through the
  `FrzPre → FrzPost` step (`ireg_fsh_step` moves the phase, never the
  index), and `EscrowDeposit.ireg_free_deposit_au` returns it with the
  regime.  `InodeRegion.ireg_fsh_no_ops` is the reading the commit takes:
  at an empty `ln_tx` authority every region slot's f column is `FrzOff`,
  `ireg_frz_ok` ruling out the absent column and `ExclBot` exactly as
  `ireg_claim_ok` does for the c column.  The widening was byte-stable
  wherever C-5 measured it: not one `FrzPre`/`FrzPost` literal in the tree,
  and the binder sweep was ~10 `(rg : bool)` → `(rg : frzidx)` in six files
  (`EscrowInode`, `EscrowDeposit`, `IcacheRef`, `IcacheInv`,
  `IcacheEscrow`, `ProofIput`).  `ireg_regime` stays at `bool` and
  `ireg_fsh_step`, `ireg_fsh_boot_off`, `ireg_frzm_ok_*`, `frz_close`,
  `frz_reg` need no statement change beyond the index's type.

  IPUT'S FRACTION PLAN, which was the work.  The freeze window SPANS the
  eviction that hands `ipool_evict_lend` its share, so one share cannot
  serve both.  `ProofIput.ip_free_entry` splits the caller's `qtx` in half
  at the one point before either park — immediately before the +0x3a
  checkout window — with `LogInv.log_tx_split` at `eq_sym (Qp.div_2 qtx)`:
  one half enters the window (`ic_pin_enter`, then the +0x5e exit, the
  mid-free park, the +0x8a eviction and `ipool_put`), the other is the
  freeze index's `(tid, qtx/2)`.  BOTH Exit-A arms rejoin inside
  `ip_free_entry` (`log_tx_join_q`), so the caller never sees the split;
  on Exit B `wp_iput_gen` instantiates `ip_free_locked` at `qtx/2` and at
  `rg := (rg, (tid, qtx/2))` and joins its two outputs.  Consequence:
  `wp_iput_gen`, `wp_iput_sconf` and `SpecIput` keep their `(rg : bool)`
  and their `tid ↪{#qtx}`, so ireclaim and the sixteen iput call sites are
  untouched.

  CONTRACTS WHOSE STATEMENT CHANGED.  `Xv6Cameras.frz` (both payloads);
  `IcacheRef.ifreeze_pre`/`ifreeze_post`/`frz_reg` (+the index type);
  `InodeRegion.ireg_fsh` (the share beside the regime), `ireg_fsh_pre`/
  `_post` (two arguments), `ireg_fsh_post_acc` (a pair out),
  `ireg_frzm_ok_true`, `ireg_freeze_au` (+`ireg_fpin rg`, and its regime
  premise is now `ireg_regime rg.1`); `EscrowInode.escA_body`/`escA_inv`/
  `pool_await`; `EscrowDeposit.ireg_free_deposit_au` (its second fupd
  yields `committedA ge ∗ ireg_regime rg.1 ∗ ireg_fpin rg`);
  `IcacheInv.icnt_freeze_forces_one`/`frz_park_pre_reclaim`/
  `iref_close_last_freeze_store_au`; `IcacheEscrow.ic_payload_arm_decide_frz`/
  `ipool_shape_await`/`ic_close_to_empty_await`/`ic_open_frozen`;
  `ProofIput.ip_free_locked` and `ip_free_offlock` (+`ireg_fpin rg` in the
  post, after the regime).  NEW: `InodeRegion.ireg_fpin`,
  `ireg_fsh_no_ops`.  UNTOUCHED: `log_ctx`, `log_op`, `wp_end_op`,
  `fs_crash_seam`, `P_fs`, `ireg_slot`/`ireg_slot_intro`'s arity,
  `ireg_shp`, `ic_escrow_body`'s five arms, `ipool`'s shape, `LogInv`.

  THE COLLECTION'S SIDE.  `FsCollect` section 5c is no longer a wall:
  `col_corpse_no_ops` refutes a slot whose freeze token is in ANY thread's
  hand at either phase against an empty `ln_tx` authority, and
  `col_slot_unfrozen` is the accessor form (pure, the slot comes straight
  back) that a pool-side consumer would feed with the `ifreeze_post rg`
  standing in `escA_body`'s EMPTY arm.  `col_region_slot_acc` and
  `col_free_slot_acc` did not have to move.

  **(G), THE POOL-SIDE WITNESS FOR `X`, IS WHAT C-6 LEFT — closed by C-7.**
  The measured fix ("a `EscrowDefs.reg_half` per pending/await inum inside
  `ipool_body`, colliding with the MARKED arm's `reg_full`") CANNOT BE
  MINTED, and the obstruction is accounting, not proof.  The registry
  element at one inum is entirely REGION-side on every arm: IN and MARKED
  hold `reg_full`, and the PENDING arm holds `reg_half` beside
  `EscrowDefs.region_pending`'s — which is the other half, also in
  `ireg_slot`.  `FsCollect.reg_full_no_pool_half` states exactly that (a
  `reg_half` at an inum is refuted by that inum's slot on EVERY arm, not
  just the two the witness is meant to rule out), and its one producer, the
  deposit's `reg_split`, runs OFF-LOCK: iput gives the itable lock up at
  +0x94, twenty instructions before `ireg_free_deposit_au`, so the deposit
  can open `ipoolN` but cannot find the row for its own inum (`z ∈ X` needs
  both halves of `icfg_pext`, one of which is the lock's).  The same wall
  kills every cheaper variant: `ipool_ext`'s rows are lock-side, so the
  commit sees NOTHING at an `X` inum, and `escA_inv` is an `inv` and
  therefore cannot move into the Timeless `ipool_body`.  C-7's answer is a
  per-inum ghost map whose ELEMENT the walk carries — see its own paragraph
  below.


  **AS LANDED — C-7: THE CORPSE LEDGER, AND THE MARKER MOVES OUT OF THE
  ESCROW.**

  RESIDUE (G) IS CLOSED, and with it the whole of `col_hand`'s supplier
  list: nothing in `FsCollect.v`'s header is outstanding.  The pool's
  in-transition part `X` now has one CORPSE LEDGER row per inum inside
  `IcacheEscrow.ipool_body` — `Xv6Cameras.icorpse` (`CrpPre t q` /
  `CrpDep`), a `ghost_map Z icorpse` at the new ambient gname
  `IcacheRef.icfg_pcrp`, with `ipool_ckey` the authority (whole, in the
  body), `crp_row` the per-row payload, `ipool_corpse` the big-op and
  `EscrowDefs.crp_elem` the element.  `⌜dom K = X⌝` is the body's new pure
  row.  `CrpPre t q` parks the freeing transaction's share, so
  `ipool_corpse_no_ops` reads "every corpse has been deposited" off an empty
  `ln_tx` authority exactly as `ipool_transit_no_ops` does; `CrpDep` parks
  `InodeRegion.imark`, so `ipool_quiesce_acc` hands the commit
  `[∗ set] z ∈ X, imark γi z` and `FsCollect.col_free_slot_acc` turns each
  into that inum's free bundle.

  A `ghost_map` AND NOT `ipool_tkey`'s PAIRED `ghost_var`, and that is what
  C-6's wall forced: the deposit runs twenty instructions after iput gave the
  itable lock up, so it holds neither half of `icfg_pext` and cannot tell
  that its inum is in `X`.  The ELEMENT locates the row — created at
  `ipool_put_corpse` (the +0x94 park), carried off-lock, spent at
  `ipool_deposit_corpse` inside `EscrowDeposit.ireg_free_deposit_au`.

  THE MARKER IS THE WITNESS, NOT A `reg_half`, and C-6's measured shape is
  refuted rather than built: `FsCollect.reg_full_no_pool_half` survives as
  the reason (the registry element at one inum is entirely region-side on
  every arm), and moving one half out is not available either —
  `InodeRegion.ireg_claim_au`'s PENDING branch RECOMBINES the two
  region-side halves at ialloc, long before any recycle could hand a
  pool-side half over.

  THE TIE BETWEEN THE TWO ONE-SHOTS IS WHAT MADE THE RE-PLUMBING NECESSARY.
  `escA_body`'s FILLED arm loses `imark` and keeps the ledger's ELEMENT at
  `CrpDep` in its place.  Without that swap the escrow's state machine and
  the ledger's are untied, and a recycler that peels the escrow cannot
  conclude that its row is `CrpDep` — so it cannot produce the marker at
  all.  With it, `ghost_map_lookup` against the open body decides it in one
  line.  Consequence: `ipool_take_lend` ABSORBS `ipool_shape_to_np` (which
  is deleted).  The merge is forced, not tidy — the row's deletion needs the
  element, the element comes from the peel, and `dom K = X` means the peel
  and the index move must be the same ghost step.  What take_lend returns is
  an ORDINARY row's four pieces on BOTH branches, plus the borrowed licence;
  ProofIget's recycle drops one call and gains none.

  THE FRACTION PLAN: NO NEW SHARE.  The corpse row parks the share
  `ipool_evict_lend` already took — the half iput split off at the +0x3a
  window (C-6's plan) — instead of `ipool_put` handing it straight back, and
  the deposit returns it beside `ireg_fpin`.  So `ip_free_locked`'s post
  carries the ELEMENT where it used to carry that share,
  `ip_free_offlock`'s post carries the share, and `wp_iput_gen`'s join at
  Exit B is unchanged.  `SpecIput`, ireclaim and the sixteen iput call sites
  are untouched.

  CONTRACTS WHOSE STATEMENT CHANGED.  `Xv6Cameras.icacheG` (+`icache_pcrpG`)
  and `icacheΣ`; `IcacheRef.icfg` (+`icfg_pcrp`) and `icfg_alloc` (+the
  ledger's auth, LAST).  `EscrowInode.escA_body`/`escA_inv`/`escA_alloc`/
  `escA_deposit_acc`/`escA_redeem`/`escA_await_peel` and `pool_pending`/
  `IcacheEscrow.pool_await` all DROP `γi` (the marker was its only use), and
  the three peels yield `crp_elem z CrpDep` where they yielded `imark`.
  `IcacheEscrow.ipool_body` (+`K`, +`⌜dom K = X⌝`, +the ledger),
  `ipool_alloc_inv` (+the empty auth), `ipool_inv_acc` (+`K` and the rows),
  `ipool_quiesce_acc` (+the `X` markers), `ipool_take_lend` (the peel's
  premises and the licence in, an ordinary row out; `ipool_shape_to_np` is
  gone), `ipool_put` SPLIT into `ipool_put_ord` (`ipool_ord` in, the share
  out) and `ipool_put_corpse` (`ipool_ext` in, the element out);
  `ic_close_to_empty`/`_late` now yield `ipool_ord` and
  `ipool_shape_await`/`ic_close_to_empty_await` `ipool_ext` (the
  `ipool_ord`/`ipool_ext` definitions moved above them; `ipool_shape` and its
  three equations stay, and `ipool_no_timeless_check` with them).
  `EscrowDeposit.ireg_free_deposit_au` (+`icn`/`cov`/`logstart`/`(t, q)`,
  +`ipool_inv`, +the element, +`↑ipoolN`, and its second fupd yields the
  share LAST).  `ProofIput.ip_free_offlock` (+`cn`, +`(t, q)`, +`ipool_inv`,
  +the element; its continuation gains the share).  NEW:
  `IcacheEscrow.ipool_ckey`/`crp_row`/`ipool_corpse`/`ipool_corpse_no_ops`/
  `ipool_corpse_marks`/`ipool_deposit_corpse`/`ipl_moi_inum`,
  `EscrowDefs.crp_elem`/`crp_elem_excl`.  BOOT: `IcacheBoot.icache_boot_at`/
  `icache_boot` and `FsCfgBoot.fs_kit_icache`/`_rest`/their two `_open`s gain
  the empty ledger authority, LAST; `ProofMain` moves one destructuring
  pattern and one `with`-list.  UNTOUCHED: `log_ctx`, `log_op`, `wp_end_op`,
  `fs_crash_seam`, `P_fs`, `is_itable2`/`itable_res2`'s arity,
  `ic_escrow_body`'s five arms and `ic_escrow_body_cover`,
  `ireg_slot`/`ireg_slot_intro`, `SpecIget`/`SpecIlock`/`SpecIput`'s posts,
  `LogInv`.

  THE ASSEMBLY'S DOOR is `FsCollect.col_region_quiesce_acc`, and it is
  statable now only because (G) is closed: `col_side` is the two things the
  pool and the escrows hand the commit at one region inum — the MARKER (the
  pool's ordinary row for an `O` inum, the corpse ledger for an `X` one) or
  a whole bundle at a share whose double is invalid (a slot escrow's cover,
  or the pool row's ALLOC arm) — and the accessor turns either into
  `inode_owned_era_q` at a NAMED share, which `col_bundle_of_side` packs
  into `col_hand`'s own currency.  The share is named and not
  existentialised so that the closing wand can give back exactly what it
  lent.  NON-VACUITY (plan §7): `FsCollectImg.img_col_quiesce_marker` runs
  the marker side at the mkfs image and gets the payload out at
  `FsCfgBoot.img_node`, the value `ftop_inv`'s map holds at boot, with the
  marker and the slot handed back.

  WHAT REMAINS FOR THE ASSEMBLY (items 2–5), now with no residue under it:
  `fs_collect_snap_ok`, the law parked in `log_ctx`, `eo_commit`'s call at
  `outstanding = 0`, the two commit permits at `dsnap_step_of`,
  `fs_commit_receipt`, `P_fs`'s conjunct → `P_dur (fr_D r)`, and the
  `fs_dview`-as-slot / `fdn_*` / `riscv_dview_name` deletions.
  `col_snap_ok_ex` is still what the law concludes and `col_hand` still what
  it must assemble.

- [ ] **Lane D — the durability theorem, and its worked instance (plan §5).**
  The GENERAL statement is the commit's receipt itself: after a commit, the
  current snapshot's abstract state IS the era's abstract state (the
  `ftop_inv` map the transactions produced) — state it once as a theorem
  over `P_dur_tie`/`P_dur_node_of_slot`, since every syscall spec already
  states its effect on that map (`top_frag`/`ireg_top_retag`).  Then ONE
  worked instance, `mknod_durable`: `ProofSysMknod` keeps `create`'s
  `made` clause (today discarded at its `iDestruct`, ~`:1690`) and the
  snapshot's inode at `inum` is `create_made ty major minor` with the
  parent's entries containing `(name ↦ inum)`.  This lane is the vacuity
  check of plan §7, not a step in lane E; other syscalls' durable
  corollaries are the same two lines and are written only on request.
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
