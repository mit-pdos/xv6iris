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
pure-projection hook).  What the FS layer still states about durability
with a placeholder: `FsWf.v:42` `fs_durable_wf := True`;
`end_op_fin_placeholder` ×30, `log_row_a_pending` ×6.  Row (b) is REAL
(1b): `LogInv.log_state` carries `log_mirror_tie_body`, both
establishment sites prove it, and the commit permit turns it into
`D' = L|home`.

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
sequence; 1c's byte layer is independent, but its CONSUMER FLIP wants 1a
landed first (1c's step 5: the recovering install still moves the cache
map at home blocks); 1d lands last.

- [x] **1a. H2 + H2a: custody at birth, recovery a ghost no-op.** LANDED.
      - `RiscvAdequacy`: `power_boot_res` takes the client's picture
        function `Mof : (Z -> bv 8) -> log_mirror` and hands out the era's
        mirror HALF at `Mof (v_disk g')` plus `swap_lb (S gen)`.  PowerOn
        allocates the variable there and runs a SECOND client hook after
        `iMod "Hback"` (mask ⊤; the era record and `γmir` exist), which
        opens `crashN` and installs the custody arm:
        `∀ HE gen dk, era_registered gen HE -∗ gen_started gen -∗
        start_auth (gen+1) -∗ disk_fixed_auth dk -∗
        ghost_var (era_mirror_name HE) 1 (Mof dk) -∗ ▷ riscv_crash_pred ==∗
        ◇ (start_auth (gen+1) ∗ disk_fixed_auth dk ∗ ▷ riscv_crash_pred ∗
        ghost_var … (1/2) (Mof dk) ∗ swap_lb (S gen))`.
        **A basic update under `◇`, not a `={⊤}=∗`** — forced twice: the arm
        runs the hook with `crashN` OPEN, so a ⊤-indexed fupd cannot be
        eliminated there, and the raw-gname form at `riscv_power_adequacy`
        is stated in a context carrying `invGpreS` and no `invGS`, so no
        fupd exists to write it with at all.  The `◇` is what lets the
        client strip the crash predicate's later.  `Mof` is a parameter
        because no FS constant may appear below `SystemAdequacy`.
      - `FsCrash`: `P_fs_swap` discharges the hook — `P_fs_project`'s
        pattern (lend the durable auth, re-index the record at the
        machine's `dk`, `fs_arm_swap` at `mirror_of (fs_blocks dk)` with
        `mirror_of_ok`, re-index back).  DELETED, 547 lines (3523 → 2976):
        `fs_era_custody`/`_boot`, `log_mirror_any`/`_intro`,
        `fs_recover_permit`/`_rec`, `fs_recover_seq_permit`,
        `fs_swap_sector0_rec`, `fs_boot_head_sector0_rec`,
        `fs_boot_head_seq_permit`, `fs_hdr_sector1_rec`,
        `fs_clear_sector0_rec`, `hdr_wf_hdr_sector1`.  The silver lining is
        `fs_recovery_of_mirror`: the era knows `fr_D` BY VALUE, as
        `fs_install (lm_view M) ls (lm_hdr M ls).2 (fs_restrict (lm_view M)
        (fs_home_set cov ls))` — that term is 1d's `D₀`.
      - The boot row is `LogDefs.log_mirror_born M := log_mirror_half M ∗
        swap_lb (S gen_id)`; `log_mirror_full` is DELETED with the boot swap
        it existed for.  It rides `SystemAdequacy` → `BootShared` →
        `SpecMain`/`ProofMain` → `BootChain` → `FirstTok.first_fsinit` →
        `SpecFsinit` → `SpecInitlog`, at `mirror_of (fs_blocks dk)` for the
        bundle's own `dk`.  ONE new pure premise travels beside it — the
        era's two readings of one image, `∀ b ∈ cov, L !! b = Some (lm_view
        M b)` — produced inside `FsCfgBoot.fs_kit_fsinit_ghost` from
        `FsBoot.fs_L0_lookup`.
      - `ProofInitlog`: the recovering install is the STEADY-STATE permit
        `fs_install_v_seq_permit` over the cursor-indexed family
        `R i := log_mirror_half (lm_install M Ws Lw i)`
        (`LogDefs.lm_install`/`_miss`/`_hdr`/`_hit`, `Ws = (hdr_dec
        bs_hdr).2`, `Lw i = ys !!! i` the slot contents the loop's `bread`s
        learn); the closing head write is `fs_clear_keep_seq_permit`, whose
        caught-up premise is `lm_install_hit`/`_miss` plus the slot
        equation; the `log_state` pack is at the NAMED `lm_upd (lm_install
        …) (log_hdr_bno ls) bs'` and its row (b) is PROVEN, off the new
        `SpecInstallTrans.it_rec_L_hit`/`_miss`.
        Row (a) stays gated — it is 1d's.
      - `LogDefs.lm_install` is `ProofEndOp.eo_minst` generalised
        (block-keyed, over the header's own `list Z` write set, and its
        duplicate-freedom premise is the INJECTIVITY it is used through
        rather than a `NoDup` — the bare name resolves to two different
        inductives in this tree).  `eo_minst` is still a duplicate of it;
        see 1b's last bullet for what re-pointing costs.
      - `fr_D` no longer re-bases anywhere on the boot path.  AUDIT: the
        boot path's only disk writes are the recovering install's home
        blocks and the closing header, and both now carry the mirror half.
      - NOT DONE, and it is a lane of its own: `hdr_n bs_hdr = 0` stays on
        `SpecFsinit`/`FirstTok` (old H3).  `SpecInitlog` does not want it;
        what still does is fsinit's own supply of the ENTRIES' home client
        halves, which at a dirty log has to be routed out of the coverage
        remainder by the decoded write set, plus `hdr_wf`-shaped premises at
        fsinit's level.
- [x] **1b. Row (b) through `ProofEndOp`; the commit concludes
      `D' = L|home`.** LANDED.
      - Row (b) is UNGATED: `LogInv.log_state` carries
        `⌜log_mirror_tie_body M L cov logstart LB⌝` outright.
        `log_mirror_tie`, `log_mirror_tie_pending` and
        `log_mirror_tie_of_body` are DELETED; `_body` and `_deposit`
        survive.  Maintenance is free everywhere it was predicted to be:
        `ProofLogWrite`'s absorb arm (the scan found `bno` in `LB`, so the
        one key `L` moves at is off the row's domain) and its append arm
        (`LB` grows by exactly that key); `ProofBeginOp.bo_batch_lhn`
        re-exports the row verbatim.  `ProofInitlog`'s boot pack drops the
        `_of_body` hop and proves the body directly.
      - `ProofEndOp.eo_open_of_batch` re-exports `⌜LB = list_to_set (map
        uint W)⌝` and the row at `list_to_set (map uint W)`;
        `eo_loop` carries it through the fuel induction (a fill writes a
        SLOT, so `home_set_not_region` kills both the `L` insert and the
        `lm_upd`); `eo_commit` takes it and spends it.
        `eo_open_to_batch` takes the row at `∅` as a PREMISE and the
        deposit site computes it with `LogInv.log_mirror_tie_deposit` —
        the arithmetic belongs where the chain is held, not inside the
        packing lemma.
      - **The log's commit contract**, `FsCrash.fs_commit_L_seq_permit`
        (with `fs_commit_L_sector0_rec` under it), replacing
        `fs_commit_named_seq_permit` / `fs_commit_v_sector0_rec`.  It takes
        NO client premise; its two new pure premises are the log's own
        rows, stated at the caller's off-header view `V` (the sibling
        `fs_clear_keep_seq_permit`'s style, and it makes the sector-1-first
        landing order free):
        `∀ b ∈ fs_home_set cov ls, b ∉ Ws → L !! b = Some (V b)` and
        `∀ i b, Ws !! i = Some b → L !! b = Some (V (log_slot_bno ls i))`.
        Conclusion: the receipt is at
        `fs_restrict (dv_of_D L) (fs_home_set cov ls)` — the LOGGED VIEW on
        the home set.  The install arithmetic is
        `FsCrash.fs_install_is_logged` and never leaves `FsCrash.v`.
      - DELETED: `FsCrash.fs_commit_pres`, `end_op_pres`,
        `end_op_pres_placeholder`; the `Hcli`/`Hpres` threading through
        `FsCrash`/`ProofEndOp`; `SpecEndOp`'s `end_op_pres` premise; and its
        30 call sites across 16 files.  `end_op` now has NO FS-facing pure
        premise.  `end_op_fin` / `end_op_fin_placeholder` are untouched
        (1d's).
      - DEVIATION, and it is a simplification: **no `⌜dom L = cov⌝` was
        added to `log_state`.**  It is not needed.  The two row premises
        above pin `L` at every home block — row (b) on `home ∖ Ws`, the
        slot equation on `Ws` — which IS the domain fact on `home`, in the
        two pieces it splits into, and `home` is all the conclusion reads.
        So the boot distribution (`FsBoot`/`FsCfgBoot`/`FirstTok`) was not
        touched at all, and `log_state` gained no conjunct.
      - NOT DONE (it was conditional): `eo_minst` was NOT re-pointed at
        `LogDefs.lm_install`.  The two are the same pass at
        `Ws = map uint W`, but `lm_install` indexes with `Ws !!! t` where
        `eo_minst` uses `uint (W !!! t)`, so the bridge is a real lemma plus
        a rewrite at ~10 sites inside `eo_commit`'s tail — churn with no
        statement change, on top of a change that already moves
        `FsCrash`/`LogInv`/`ProofEndOp`.  Worth doing on its own; the three
        readings (`eo_minst_miss`/`_hdr`/`_hit`) map one-to-one onto
        `lm_install_miss`/`_hdr`/`_hit`.
- [x] **1c. Byte-keyed logged view with FULL-element clients; bio's share
      moves to the block CACHE map.**  LANDED (byte layer + consumer flip).
      Design: `fs-log.md` §"The ghost state"; the layer table is
      `fs-ghost-state.md` §1.
      - The block-keyed map is the CACHE map (`fs_cache`, parked half
        `fs_chalf`, initial map `fs_C0`).  The LOGGED VIEW is byte-keyed:
        `byte_range gL b off bs` / `fsblock gL b bs` over a
        `ghost_map Z (bv 8)` at dfrac 1, riding `DiskImg.diskImgG` (the
        tree's UNIQUE `ghost_mapG Σ Z (bv 8)`; a second field in `fsLogG`
        breaks the disk image's own auth/fragment pairing).  Its gname is
        the FOURTH field of `fs_names`, `fs_bytes`.
      - `fs_bytes_inv gL gc home` at `logN`: the byte auth, the home
        blocks' parked cache halves, `bytes_tie`, `bytes_dom`.  Body
        TIMELESS.  Crossings: `fs_bytes_agree` (a bread client's `fsblock`
        against the handle's payload half), `fsblock_update` (log_write's
        ghost step), `byte_range_update` (the stage-2-ready engine),
        `fs_bytes_alloc` (the mint).
      - **THE MINT** is `FsBlocks.fs_alloc E L0 home`: it allocates the
        three block-layer ghosts AND the byte view, and splits its
        per-block output along the home/log-region line -- `fsblock` for a
        home block, `fs_chalf` for a log-region one, with the machinery
        halves, the log-side dirty halves and the `blk_own` tokens handed
        out undivided.  `FsBoot.fs_boot_ghosts`/`fs_boot_bundle` take
        `home` (the caller passes `fs_home_set cov logstart`) and
        re-export the split plus the persistent row; `FsCfgBoot`'s kit and
        `FirstTok.first_fsinit` carry `fsblock` for block 1 and for the
        coverage remainder, `fs_chalf` for the header and the slots.
      - **THE THREE CARRIERS OF THE ROW.**  `LogInv.log_ctx` (named, at
        `fs_home_set cov logstart`), `BitmapInv.bitmap_inv` (named, same),
        `InodeRegion.ireg_inv` (bound: `fs_bytes_any γfs`).  Every bread
        client above the log holds one of the three; the two that hold
        none -- `readi` (takes no `log_ctx` by design) and `bmap` (whose
        `bm_kit` is `None` on the read path) -- take `fs_bytes_any γfs` as
        an explicit premise.
      - **HOLDING THE RUN IS BEING A HOME BLOCK.**  `FsBlocks.fsblock_home`
        derives `b ∈ home` from the byte auth and `bytes_dom` (two block
        ranges that share a byte are one block), so NEITHER crossing takes
        a membership premise and no consumer ever names a `gset Z`.  That
        is what kept the flip out of the syscall contracts.
      - **`fsblock` IS `Typeclasses Opaque`** -- a bare `iFrame` at a goal
        holding one unfolds a 1024-element `big_sepL` and does not come
        back (measured: `bitmap_res_close` past ten minutes).  See
        `fs-ghost-state.md` §1.
      - THE FREEZE is untouched: the cache AUTH stays in `log_state`
        outright and the invariant holds only the parked HALF, so
        write_head, install_trans and end_op's write_log are unaffected by
        the re-keying.
      - **RULING (2) WAS DEVIATED FROM, deliberately, and the orchestrator
        should ratify or reverse it.**  `ireg_inv` did NOT gain a
        `home : gset Z` parameter.  Measured before deviating: `ireg_inv`
        appears in the STATEMENT of **203 definitions across 74 files**,
        nearly all syscall-level contracts (`wp_sys_open_sconf_body`,
        `SpecKexec.fs_fabric`, `FsSyscalls.fs_world_all`) that have no
        business naming the block layer's home set and no way to obtain
        one -- and `IcacheRef.v`'s own header already records that
        "[ireg_inv], whose arity is fixed by 30-odd fs contracts" is why
        the `icfg` class exists.  Instead `ireg_inv` gained a persistent
        CONJUNCT, `InodeRegion.ireg_bytes γfs = fs_bytes_any γfs`, whose
        home set is existentially bound.  Nothing is weakened: the ghost
        names are explicit (`fs_bytes γfs`, `fs_cache γfs`), the set is a
        `gset Z` no consumer needs (membership is derived, above), and a
        second invariant at `logN` over one `fs_bytes γfs` cannot exist
        because its body demands the byte map's single AUTH.
      - **THE RECOVERING INSTALL DOES NOT HOLD NOTHING** (step 5's open
        point, answered).  1a made recovery a ghost no-op for the MIRROR,
        not for the block layer's two content maps: the mint indexes the
        byte view at the CRASHED disk, and recovery really does change
        each home block's content, so both maps must follow it.
        `ProofInstallTrans`'s recovering arm therefore holds each home
        block's `fsblock` and moves it with `fsblock_update` (opening
        `logN` at `⊤`); `it_ghost_step` became a `={⊤}=∗` and its
        recovering arm no longer needs `it_pay_bs` -- `fsblock_update` is
        what learns the payload's bytes.  The commit arm is untouched.
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

- [x] **2a. `FsState.v`** — LANDED, as FIVE files (1687 lines), all in
      `iris/_CoqProject` after `BitmapEnc.v`.  The "as built" section is
      `fs-state.md` §7; only what a reader of this list needs is here.
      - `FsStateDefs.v` (164): `fs_view_names` (`fsΦ`/`γlink`/`γtop`; the
        field is `fsΦ`, not `Φ`, so it does not shadow the proofmode's
        binder), `byte_range`, `blk_owned`, and the two properties of an
        ABSTRACT `fsΦ` that consumers need and cannot prove — `phi_excl`
        (a `Prop` premise, the lifted `fsblock_excl`) and the class
        `GTimeless`.  `byte_range`/`blk_owned` are `Typeclasses Opaque`
        from day one.
      - `FsStateLink.v` (327): `linkUR := gmapUR Z (authR natUR)` — one
        auth-of-nat per inum in ONE element at `γlink`.  `natUR`'s `op` is
        `+` and its `≼` is `≤`, so the law `link_auth Γ i n ∗ (k tokens)
        ⊢ k ≤ n` IS `auth_both_valid_discrete` + `nat_included` (stated at
        both `link_toks Γ i k` and a `[∗ list]` of `link_tok`s).
        `link_mint`/`link_return` are the two moves.  ONE camera keyed by
        inum (not one gname per inum) is what lets the mint allocate every
        auth and every token in a single `own_alloc`.  Two new
        CAPACITY-ONLY classes, `fsLinkG` here and `fsTopG`
        (`ghost_mapG Σ Z fs_node`) in `FsState.v`; neither is an
        `Xv6G.xv6G` member, so binding both is not a second instance path.
        Nothing duplicates the tree's unique `ghost_mapG Σ Z (bv 8)`.
      - `FsStateInode.v` (713): `fs_node = { rec ; ent ; blk }` over EVERY
        nonzero `addrs` entry regardless of `size` (F3), `inode_local`
        (15 clauses, every one about ONE inode; the only inum it mentions
        is the "." entry's, which is the inode's own), `rec_owned`,
        `ind_owned`, `inode_phi`, `ent_toks`, `inode_ghost`,
        `inode_owned = inode_phi ∗ inode_ghost`, `dir_owned`, the readings
        (`fn_file_bytes`, `dir_entries`, `fn_orphan`), and the encode
        lemmas — every one an ACCESSOR, since at an abstract `fsΦ` there
        is no update to make and the log's `byte_range_update` is what
        moves the bytes.
      - `FsStateBitmap.v` (172): `free_bitmap Γ sb u`, indexed by the USED
        set; `bitmap_alloc` and `bitmap_free`, the latter deriving "the bit
        reads allocated" from `phi_excl` — the "freeing a free block"
        panic arm is dead by exclusivity, not by a clause.
      - `FsState.v` (311): `sb_owned`, `fs_inodes` (the one `∗`),
        `fs_state`, `fs_view`, `top_frag`, and THE MINT.
      - **THE MINT IS A TRANSPORT.**  `fs_state_split : fs_state Γ S ⊣⊢
        fs_footprint Γ S ∗ fs_ghost Γ S` factors the Φ-only half from the
        Φ-free half; `fs_ghost_split` factors that again into
        `fs_links (γlink Γ) I ∗ fs_pure S` (persistent).  `fs_state_mint`
        reads `⌜✓ link_elem I⌝` off the durable instance's own `own`
        (`fs_links_valid`), allocates the new family, and reuses the pure
        half.  THAT IS THE ONLY PLACE the cross-inode fact "#tokens ≤ nlink
        everywhere" is ever produced — it is not a clause, is not
        maintained, and the logged instance inherits it from the committed
        one.  `fs_view_mint` additionally allocates `γtop` at `S`'s inode
        map and hands back one `top_frag` per inode.
      - DEVIATIONS from §2 (full list in `fs-state.md` §7): the geometry
        (`sb`) is a parameter of `rec_owned`/`inode_owned`/`fs_inodes`/
        `free_bitmap`; a directory's TOKENS live inside `inode_owned`
        (§2 hangs them off `dir_owned`, which would put them outside
        `fs_state`, since `fs_inodes` iterates `inode_owned`), and
        `dir_owned` is the reading `inode_owned ∗ ⌜is_dir⌝`; the abstract
        state carries the superblock's RAW BYTES beside the parsed record
        (there is no encoder in the tree, only `fs_parse_sb`, and the
        footprint must be a function of `S`); `free_bitmap` is indexed by
        the used set (`bm_bytes`' argument), not the free set; the mint's
        fresh gnames come out existentially, since `own_alloc` cannot
        target a given gname.
      - NOT DONE, and it belongs in `FsTree.v`: the dirent-INSERT view
        equation.  `FsTree` proves the removal delta outright
        (`dir_view_zero`) but has no
        `dir_view data' nrec' = <[s := t]> (dir_view data nrec)`, only the
        uniqueness preservation `dir_names_unique_write`.  So
        `ent_toks_insert`/`dir_owned_link` take the entry-map delta as a
        premise — the shape a caller has anyway.  Small, self-contained,
        and `FsTree`'s to prove.
      - NOT DONE, deliberately: speculative `inode_local` preservation
        lemmas.  Each mover takes `inode_local i n'` as a premise; which
        ones stage 3's arms actually need is stage 3's evidence, and
        writing the cross-product now is the near-duplicate family the
        guiding principle warns about.
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
