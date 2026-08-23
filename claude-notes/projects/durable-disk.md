# durable-disk — the worklist under ruling 3 (rewritten from the tree, 2026-08-23)

Design of record: [`../design/fs-state.md`](../design/fs-state.md) (read it
first), on the crash-side mechanics of [`../design/crash.md`](../design/crash.md).
The previous worklist, with its history, is archived in
[`../completed/durable-disk-byteview.md`](../completed/durable-disk-byteview.md)
— its §1½ "remaining path" is VOID.  Every file:line below is at `129eefab`
unless marked.

**Goal (owner):** xv6 correctness across crashes, INCLUDING file-system
consistency.  The adequacy theorem `SystemAdequacy.xv6_power_adequacy` is
vacuous today (its `Himg` premise is refutable); it becomes true when
`P_fs` carries the durable file system across eras and the `Himg` premise
is deleted (stage I).

**Where the tree is:** stages A, B, D, H0 of the old list stand (fixed-gname
durable disk, `hdr_wf`, general `initlog`/`install_trans`, the adequacy
pure-projection hook).  EVERYTHING the FS layer states about durability
today is a placeholder: `FsWf.v:42` `fs_durable_wf := True`;
`end_op_pres_placeholder` ×30, `end_op_fin_placeholder` ×30,
`log_row_a_pending` ×6, `log_mirror_tie_pending` ×4.  Row (b)'s deposit
half is proven and unused (`LogInv.log_mirror_tie_deposit`, `:889-905`).

## Working rules (keep)

- Design pinned here before a lane launches; lanes run on Opus agents in
  isolated worktrees (`remote-build-gcp.md`'s worktree recipe — the
  current text is the truth); commits linearized onto `main`
  (reset/cherry-pick, no merge commits); the MERGED tree built on the VM
  (`QUIET=1 ./gcp-rocq/run-on-gcp make -k -j 192`) + `make audit-only` at
  the three-entry baseline (`xv6iris_extras.resv_matches`,
  `resv_is_valid`, `functional_extensionality_dep`) before every push;
  grep build logs for plain `Error`.
- **Push every green checkpoint to `main`** (owner, 2026-08-23); push
  notes as soon as written.  A long non-green stretch is expected on the
  big lanes; that is accepted, not a reason to land placeholders.
- No gate lemmas masquerading as progress.  A Ψ-parametric interface
  proven against an arbitrary Ψ is real (the log's contract); a `True`
  body with a placeholder lemma is not.  Local reasoning is the rule
  (`fs-state.md` §0): a lane that finds itself stating a fact about the
  whole file system stops and reports.

## Stage 0 — housekeeping

- [x] Twelve stale agent worktrees pruned (all their commits were on `main`).
- [x] Design of record written (`fs-state.md`), ruling 3 in `crash.md`,
      old worklist archived.
- [x] **0a. Dead crash-side code deleted** — `FsCrash.v` 4674 → 3523 lines
      (1151 removed): the nine consumer-free block-level `_rec` permits
      (`fs_swap_permit_rec`, `fs_{logfill,commit,install,clear}_permit_rec`,
      `fs_{logfill,install}_permit_v_rec`, `fs_commit_permit_named_rec`,
      `fs_clear_permit_keep_rec`) and the flip-B leftovers
      (`fs_{logfill,install,commit,clear}_seq_permit`, `fs_at_sector_rec`,
      `fs_hdr_sector1_any_rec`, `fs_commit_sector0_rec`), with the
      comment-only references in `RiscvPtsto.v`, `SpecBwrite.v`,
      `SpecEndOp.v`, `ProofEndOp.v`, `SpecSysSync.v`, `SpecWriteHead.v`,
      `LogInv.v` and `ProofInitlog.v` re-pointed at the live sequential
      permits.  `fs_hdr_sector1_rec` and `fs_clear_sector0_rec` stay —
      they are live and die with 1a.

## Stage 1 — the log's contract (owner: "prove the log upholds its contract first")

The log's interface after this stage is `fs-state.md` §5 and nothing else.
Four lanes; 1a and 1b share `FsCrash.v`/`ProofEndOp.v` and run in
sequence; 1c is independent of both; 1d lands last.

- [ ] **1a. H2 + H2a together: custody at birth, recovery a ghost no-op.**
      The old H2a was right and under-costed; its "no write ever re-bases"
      presupposes H2's recovering install, so they land as ONE lane.
      - `RiscvAdequacy.v`: the per-era mirror is allocated at a DUMMY
        (`:1087-1090`, `MkLogMirror (fun _ => [])`) and handed out whole by
        `power_boot_res` (`:915-919`).  Allocate it at
        `mirror_of (fs_blocks (v_disk (dvirtio (gdev g'))))`; add a second
        client hook `Hswap` placed AFTER `iMod "Hback"` at `:1108` (mask
        back to ⊤, era record and `γmir` exist, `Hsauth` at `ggen+1`) — NOT
        at `Hproj`'s site (`:1018-1022`, before the era exists):
        `∀ HE gen dk, era_registered gen HE -∗ gen_started gen -∗ start_auth (gen+1)
        -∗ disk_fixed_auth dk -∗ ghost_var (era_mirror_name HE) 1 (mirror_of (fs_blocks dk))
        -∗ ▷ riscv_crash_pred ={⊤}=∗ start_auth (gen+1) ∗ disk_fixed_auth dk
        ∗ ▷ riscv_crash_pred ∗ ghost_var … (1/2) (mirror_of (fs_blocks dk)) ∗ swap_lb (S gen)`
        (needs the auth for the same reason `Hproj` does: `P_fs_named`
        closes `dk` existentially, `FsCrash.v:1766-1772`).  `power_boot_res`
        hands out the NAMED half + `swap_lb`.  The single-generation twin at
        `:583` needs a trivial instance.
      - `FsCrash.v`: supply `Hswap` from `fs_arm_swap` (`:1644-1668`) +
        `mirror_of_ok` (`:556`).  DELETE `fs_era_custody` (`:2890-2931`),
        `log_mirror_any` (`:2462-2488`), `fs_recover_permit(_rec)`
        (`:2932-3054`), `fs_recover_seq_permit` (`:3797-3874`),
        `fs_swap_sector0_rec` (`:3398-3467`), `fs_boot_head_sector0_rec`
        (`:3468-3491`), `fs_boot_head_seq_permit` (`:3743-3796`),
        `fs_hdr_sector1_rec` (`:3125-3194`), `fs_clear_sector0_rec`
        (`:3329-3397`) — 557 lines.  After this, every boot-path disk
        write carries the mirror half (audit that precondition; it is
        sound, nothing re-bases).
      - The boot chain: `SystemAdequacy.v:255-260` weakens to
        `log_mirror_full` — dies; `Hboot` binds `g'` (`RiscvAdequacy.v:1236`)
        so `xv6_boot_era` names `dk_boot`.  Six interfaces change from
        `log_mirror_full` to the value-carrying row: `FirstTok.v:318/330`
        → `SpecMain.v:576` → `ProofMain.v:1374` → `BootChain.v:699` →
        `SpecFsinit.v:345` → `SpecInitlog.v:258`.  `BootShared.v:1097-1129`
        and `:1277-1283`, `:1551` carry the named value.
      - `ProofInitlog.v`: `:1939-1940` (`fs_era_custody_boot`) deleted; the
        recovering install (`:1989`, `:1997-2009`, today the CONSTANT
        family `fun _ => fs_era_custody`) re-pointed at
        `fs_install_v_seq_permit` with a cursor-indexed `lm_upd`-chained
        family — an `eo_minst`-analogue (`ProofEndOp.v:584-660`) whose
        `Lw i` are the slot contents `bread` learns in the recovering loop,
        threaded through the loop invariant (`SpecInstallTrans`'s `R` is
        already cursor-indexed); the final head-write (`:2150-2171`)
        re-pointed at `fs_clear_keep_seq_permit` (`FsCrash.v:4573-`); the
        `log_state` pack (`:2388-2427`) at a NAMED `M`, row (b) by
        computation — `log_mirror_tie_pending`'s boot site dies.
      - `fr_D` no longer re-bases anywhere (ruling 2.3/2.4 made literal);
        `SpecFsinit.v:318` / `FirstTok.v:275` drop `hdr_n = 0` (old H3).
      - Silver lining to USE: with custody at birth the era knows `fr_D`
        BY VALUE (`fs_install (lm_view M_born) ls (lm_hdr M_born ls).2 (…)`);
        export it from the hook as a pure fact — it is what 1d's payload
        index `D₀` is.
- [ ] **1b. Row (b) through `ProofEndOp`; the commit concludes `D' = L|home`.**
      - `eo_open_of_batch` (`ProofEndOp.v:776-811`) DROPS `LB`, `pend`,
        `%Hmtie`, `%Hrowa` (`:797-798`); `eo_open` (`:756-775`) has no slot.
        Re-export `⌜log_mirror_tie_body M₀ L cov ls LB⌝` and
        `LB = list_to_set (map uint W)`; carry through `eo_loop`
        (`:2452-2515`) beside `HLw`/`HMcslot` to `eo_commit` (`:1815-1873`).
        The fills write log SLOTS, so the row transports from `M₀` to `Mc`
        for free (`fs_home_set = cov ∖ log_region_set`).
      - The permit's sole application site is `:1936-1944` (`V := lm_view Mc`,
        `Ws := map uint W`); at `∅` the only spatial hypothesis is
        `log_mirror_half Mc`.  The four PURE facts that conclude
        `D' = L|home`: row (b) at `Mc`; `HMcslot` (`:1841`); `HLw` (`:1834`);
        and `dom L ⊇ fs_home_set cov ls` — stated NOWHERE reachable today
        (the only `dom` fact is `FsBoot.v:202` at the boot mint): add
        `⌜dom L = cov⌝` to `log_state`.  `log_mirror_tie_deposit` is, up to
        one rewrite, the same arithmetic (`fs_install V ls Ws (…)` IS
        `fs_restrict (lm_view M_postinstall) home` along `eo_minst`'s chain).
      - New commit permit in `FsCrash.v` beside `fs_commit_v_sector0_rec`
        (`:4011-4120`, spent at `:4111`): takes `⌜D' = L|home⌝`'s
        ingredients, lends the `γD` auth (1d) to a client basic update,
        and NO client pure premise.  `fs_commit_pres` (`:496-514`),
        `end_op_pres` (`:516-527`), the `Hcli` threading (`FsCrash.v:4021,
        4111, 4466, 4521, 4562`; `ProofEndOp.v:1844, 1943, 2470, 3723, 3988,
        4929`), `SpecEndOp.v:130-142`, and the 30 `end_op_pres_placeholder`
        call sites across 16 files (two idioms: `ltac:(apply …)` positional
        in `ProofSys*`, `all: try exact (…)` in `Proof*`) — DELETED.
      - `eo_open_to_batch` (`:827-867`, gate at `:856`) calls
        `log_mirror_tie_deposit`; `ProofLogWrite.v:2488`/`:2605` (the two
        free maintenance sites) prove the row; the gate `log_mirror_tie` /
        `log_mirror_tie_pending` (`LogInv.v:803-888`) dies, `_body` and
        `_deposit` survive.
- [ ] **1c. Byte-keyed `fs_L` with FULL-element clients; bio's share moves to `γcache`.**
      - `FsBlocks.v:62-70`: `fs_L : ghost_map Z (bv 8)` keyed by byte
        address; `fsblock b bs := [∗ list] k ↦ v ∈ bs, (b·BSIZE+k) ↪[fs_L] v`
        at dfrac 1 (the derived whole-block form keeps every current
        consumer's interface); `blk_own` stays for now (it is deleted when
        `free_bitmap Γ` replaces the pool in stage 2).
      - The bio payloads `Ψc`/`Ψd` (`fs-log.md` §"The ghost state") stop
        holding an `fs_L` half: bio holds halves of a bio-side
        `γcache : ghost_map Z (list (bv 8))` (block-keyed is fine there);
        a log-layer INVARIANT `inv logN (∃ L C, auth L ∗ auth C ∗
        ⌜∀ b cached, C b = bytes of L at b⌝)` — the `fs_L` auth moves from
        the spinlock resource `log_state` (`LogInv.v:1077`) into this
        invariant, with `log_state` keeping what it needs to freeze `L`
        during commit (a ½ of the auth, or a token) — `log_write` opens it
        under `log.lock`; `bread`'s client opens it to turn `bytes = C(b)`
        into `bytes = L(b)`.  Timelessness of every payload is kept.
      - `log_write`'s ghost update becomes: learn the checked-out buffer's
        bytes equal `L(b)` on every byte (`γcache` half vs its auth), the
        writer's stores touched only its range (the buffer's memory
        points-tos), update the `fs_L` elements of the bytes that differ
        (auth + the writer's full elements).  `ProofLogWrite`'s absorb and
        append arms, `ProofBread`/`ProofBrelse`/`ProofBwrite` and the bio
        escrow proofs are the footprint.
      - `dom L = cov` (at byte granularity: the covered blocks' byte range)
        as a `logN` conjunct — 1b's missing fact.
- [ ] **1d. The parked payload and the two AUs; `γD`.**
      - `γD : ghost_map Z (bv 8)` (byte-keyed), fixed-layer gname beside
        `riscv_disk_name`; its auth is `fr_D` inside `P_disk`
        (`FsCrash.v:1262-1290`, `fs_rec`); `P_fs` gains
        `P_wf : iProp` as an OPAQUE, timeless parameter of the crash layer
        (`P_fs_named_timeless` `:1906` and `P_fs_rec_agree` `:1801` take
        it as a side condition).  The FS instantiates it in stage 2.
      - `LogInv.log_state` parks `Ψ D₀ L` (Ψ a parameter of `log_ctx`, as
        `bio_view` is of bio); `D₀` is the value 1a exports.
      - `SpecLogWrite`'s four forms (`_au`, `_gene`, `_gen`, `_sconf`) take
        the §5 AU instead of the `Ob : gset fsobj` declaration; the eleven
        suppliers (balloc ×2, ialloc, iput, iupdate, bfree, writei ×2,
        bmap, the two `ProofBmap` contract suppliers) instantiate it at
        their current content (moving their `fsblock` + whatever their
        invariant holds — stage 2 re-states those invariants over
        `inode_owned Γ_L`; here the AU's SHAPE lands).
      - `SpecEndOp` loses `end_op_fin` (`LogInv.v:990-1029`,
        `SpecEndOp.v:143-163`, 30 call sites); the commit path runs the
        payload's debt through the 1b permit with the lent `γD` auth.
      - DELETE: `FsObj.v`, `FsObjEff.v`, `FsObjType.v`; the object set in
        `Xv6Cameras.op_entry` (back to `(nat * gset Z * nat)`, the three
        projections lose one `.1`); `op_pending` over objects;
        `log_row_a`/`_body`/`_pending`/`_body_mono` (`LogInv.v:908-971`);
        `log_state_fin`'s bundle; `FsWfImg.v`.  `FsWf.v` and the
        `FsEff*`/`FsOp*` files stay until stage 2 decides what survives
        (`fs-state.md` §6).

## Stage 2 — the file system predicates

- [ ] **2a. `FsState.v`**: `Γ`, `byte_range`, `blk_owned`, `rec_owned`,
      `inode_owned`, `dir_owned`, `free_bitmap`, `fs_inodes`, `fs_state`,
      `fs_view`, the link RA (`link_auth`/`link_tok`, an auth-nat with
      `#tokens ≤ auth`), exactly `fs-state.md` §2, Γ-parametric, with the
      per-kind encode lemmas beside each predicate (from `DinodeEnc`,
      `BitmapEnc`, `FsTree.dir_written_at`/`dir_view`, `BlockWords`) and
      `fs_state_mint` (§1).  Pure, iris-generic, no dependency on any
      `Proof*`.  Verify functoriality: the mint lemma is proven here.
- [ ] **2b. Re-state the in-memory owners over `Γ_L`**: `InodeRegion`'s
      `ireg_blk`/`ireg_slot` coupling (`InodeRegion.v:2252-2258`,
      `:1448-1452`) becomes `rec_owned Γ_L`; `ic_loaded`'s payload
      (`IcacheEscrow.v:811-832`: `dinode_at`, `inode_blocks`, `ind_res`,
      `dir_links`, `dv_ride`) becomes `inode_owned Γ_L i n` + the top
      fragment; `BitmapInv.bitmap_res` (`BitmapInv.v:235-239`) becomes
      `free_bitmap Γ_L`; `dir_links`'s `dlc_bound`/`dlc_lower` and the
      link ledger's L1 become the link RA.  The `ipool` (uncached inodes)
      holds `inode_owned Γ_L` pieces under the itable spin lock — fine,
      since only the holder of a locked inode ever updates one.
- [ ] **2c. `P_wf := fs_view Γ_D`**, the debt's shape in the payload, and
      the commit AU's discharge from the debt; `FsAdequacyImg` builds
      `fs_view Γ_D` from `fs.img` once (the only place the image is
      decoded).

## Stage 3 — the vertical spike: `sys_mknod`

- [ ] One arm end to end with NO placeholder: `ialloc` (slot write),
      `iupdate` (slot), `dirlink`→`writei` (a dir record; the growing-append
      sub-arm allocates), the link token minted from `ip` into `dp`'s
      entry, `iunlockput ×2` returning both `inode_owned Γ_L` pieces, the
      debt composed at each AU, `end_op` with no premise.  Thread the
      `made` clause that `ProofSysMknod.v:1690` discards.  Whatever this
      spike cannot do is the next ruling — report, do not gate.

## Stage 4 — boot and the theorem

- [ ] **H1** = `fs_state_mint` applied in the era fupd off `P_wf`
      (`fs_cfg_alloc`, `FsBoot.fs_boot_ghosts`, `BootShared.boot_shared_alloc`
      lose every image premise; `image_dinode_fs_dinode` disappears).
- [ ] **H4/H5** (old): boot-time reads that must learn durable facts at
      the completion instant; audit that no `disk_img_bytes` at the fixed
      name exists outside `P_fs`.
- [ ] **Stage I**: delete `fs_boot_image_eras` (`SystemAdequacy.v:147`),
      the `Himg` premises, `FsAdequacyImg.fsimg_at_every_era`;
      `xv6_power_adequacy_fsimg` assumes `v_disk g = fsimg_dk` at era 0
      ONLY; audit baseline unchanged.

## Stage 5 — the remaining arms; delete the superseded layer

- [ ] The other 25 exit arms over the `Γ_L` predicates (create's `fail:`
      tail; `iput`'s free path as a token/ownership move, no discriminant
      needed; the unlink arms; `filewrite` incl. the 12-block crossing;
      `ireclaim`).
- [ ] Delete what `fs-state.md` §6 says is superseded once its last
      consumer is gone; update `fs-ghost-state.md`, `fs-log.md`,
      `fs-bitmap.md`, `fs-inode.md` to the `Γ` vocabulary.
