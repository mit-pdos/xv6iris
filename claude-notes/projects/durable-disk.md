# durable-disk — the crash predicate owns the disk; `P_fs` as the cross-era loop invariant

Design of record: [`../design/crash.md`](../design/crash.md) §"The durable
disk: ONE fixed gname, owned by the crash predicate" (ruled by the owner,
2026-08-22). Read it first. This file is the WORKLIST, written so an agent
can pick any stage up cold: every item names its file:line in the tree at
`739654bc`. Subsumes [`fs-log.md`](fs-log.md)'s items (1)/(3) (stage D).

## 0. Why, in one paragraph (so nobody re-derives it)

`SystemAdequacy.xv6_power_adequacy` (`:290`) is VACUOUS: its premise
`Himg : fs_boot_image_eras` (`:146`) is `∀ g', boot_facts g' → fs_boot_image_wf
(v_disk g') …`, `boot_facts` (`RiscvLang.v:1087-1128`) constrains the disk
only by `∃ v0, dvirtio = virtio_reset v0`, so a `boot_facts` state with a
zeroed disk (exists: `PowerBoot.boot_shape_boot_gstate`, then zero the disk)
refutes conjunct (10) of `fs_boot_image_wf` (`FsCfgBoot.v:1838`, the
superblock parse). The premise existed because a booting era could not tie
the crash invariant's `dk` to its own disk: the two `disk_tie` halves sit in
`crash_inv`'s body (`RiscvPtsto.v:668`) and in `state_interp`
(`fs_tie_interp`, `:1866`), and only the DMA completion (`WpUart.v:935-965`)
ever holds both. The ruling removes the tie by construction.

## 1. The three principles (the ruling)

1. **No mortal owner holds durable state.** Threads, sleepers and era
   invariants die at a crash; a resource inside them is gone. Fragments of
   the durable disk are owned by `P_fs` only, forever. Any site that today
   owns a durable fragment is rewritten to a fupd / logically-atomic access
   of `crashN` at the instant it touches durable state (a DMA completion).
2. **One fixed-layer gname for the durable bytes.** The machine layer holds
   the AUTH at `v_disk` in `state_interp` (fixed conjunct; both power arms
   preserve `v_disk`, so nothing is re-minted or re-associated). Auth/frag
   agreement IS the tie. `riscv_crash_pred` loses its `dk` index.
3. **Adequacy assumes exactly `v_disk g = fsimg_dk` at era 0.** `HPc`
   establishes `P_fs` from `fs.img` once; `P_fs` is the loop invariant
   across eras; `Himg` is deleted and never returns.

What STAYS: the per-era image map (`era_disk_name`, `disk_img_auth` in
`era_interp`, whole fragments in `power_boot_res`) — it is the driver/bio
layer's IN-MEMORY picture, owned by mortals, dying with the era, and that is
fine under principle 1 because `P_fs` does not depend on it. What a client
learns about the DURABLE bytes comes only through the permits at DMA
completions (principle 1) or from `P_fs`'s own pure content (opening
`crashN` in any fupd).

## 1½. STATE AT THE FOURTH CHECKPOINT (handoff point)

Everything below is on `main` and VM-green with `make audit-only` at the
8-entry baseline after every commit. Landed, in order:

- **Stages A, B, D1, D2** (see the stage sections): the fixed-gname
  durable disk, `hdr_wf`, general `initlog`/`install_trans` at the log
  layer (the L-moving recovering arms — superseded in design by ruling
  2.4, rebuilt at stage H2).
- **Stage E complete** (E1/E2/E2'/E3): the widened mirror (`lm_view`,
  one total block view pinned pointwise on the durable extent — NOT
  total on all of Z: `P_fs_rec_agree` forces the scoping), the
  `P_wf` conjunct riding `fs_rec_wf` (`FsWf.fs_durable_wf`, placeholder
  body, gate lemma `fs_durable_wf_placeholder` — every use site is the
  switch-on rework list), and the value-chained permit primitives
  (`fs_logfill_permit_v`, `fs_install_permit_v`,
  `fs_commit_permit_named` — concludes at the NAMED committed view,
  takes the client preservation premise, receipt AT it —
  `fs_clear_permit_keep` — preserves `fr_D` off the chained caught-up
  fact). The at-form permits remain the consumers' interface until G3.
- **Stage F1**: `fs_durable_wf_body` is real (FsWf.v), with the
  reachable-dir ticket W9, the orphans-empty clause, `fs_inodes_dwf`
  (link floor removed — orphans), W6 scoped to reachable dirs, the
  agreement suite, `fs_links_eq` + its image check (22.3 s), and the
  mkfs discharge `FsWfImg.fsimg_durable_wf`.
- **Stage F2, 8/8 pending merge**: seven semantic-effect update lemmas
  landed (`FsEffBase.v` + one file per effect — the one-file-per-effect
  split is an OWNER RULING, keep it), preconditions as discovered (see
  the F2 entry: mkdir fuses the dots block; unlink-dir needs
  `nlink i = 1` and `..` pinned to the parent; free_inode fuses
  trunc+bfree+type:=0; alloc splits direct/indirect-entry arms). The
  EIGHTH effect (fused indirect-block allocation at `fbn = 12`) is IN
  FLIGHT on an agent worktree branch (see "In flight" below).
- **Stage H0**: the adequacy pure-projection hook
  (`Ppure`/`Hproj` on `wp_power_loop` + `riscv_power_adequacy`,
  `FsCrash.P_fs_project`, `SystemAdequacy.fs_boot_pure`) — the channel
  that stage I uses to delete `Himg`. `xv6_boot_era` receives the
  proven per-era fact and does not use it yet. NOTE: the projected
  payload names `fs_durable_wf` (the placeholder), so it strengthens BY
  NAME at the switch-on with no re-plumbing.

**In flight at handoff (Opus worktree agents; when one finishes,
review its report against the spec in this file, cherry-pick its
worktree-branch commits onto main linearly, run one combined VM build +
audit, push):**
- branch `worktree-agent-a771acd0806be1fdd`: the FsEff
  build-performance pass (next-steps item 1; statements frozen,
  proof-internal only, before/after measurements required).
- branch `worktree-agent-aed3d383025baf0eb`: G1-impl (`log_state`
  fusion + row (b) + `op_pending` + the `fs_links_eq` boot threading;
  spec = the G1-impl item; row (a) EXCLUDED by staging; premise-debt,
  if any, must be a named carrier with its discharger recorded).

**Next steps, in order (all specs live in this file):**
1. **FsEff build-performance pass FIRST** (owner's ruling): the F2
   files are slow to build and every later stage iterates on them.
   Proof-internal optimization only (statements identical), per
   optimization.md's rules; measure before/after per file. Only THEN:
2. **Effect 8** (`eff_alloc_ind_block`, spec = the F2 entry's deferral
   note) on the optimized base.
3. Merge the G1-impl branch (above) when it reports.
4. **G2**: the per-op preservation lemmas, STANDALONE (pure statements
   composing the F2 effects per op; no log_state dependency; fully
   parallelizable — one Opus agent per op batch). The 12 ops and their
   26 exit arms are enumerated in the 2026-08-22 survey (§Stage G);
   each op = a composition of effects (e.g. sys_mkdir =
   eff_create_dir_entry; filewrite = eff_alloc_file_block* +
   eff_write_file_data* (+ eff_alloc_ind_block at the boundary);
   sys_unlink = eff_unlink_entry (+ trunc/free on the nlink=0 path)).
5. **The row-(a) flip + G3** (one coordinated sweep): add row (a) to
   `log_state`, wire the G2 lemmas into the 26 arms, re-point
   `ProofEndOp` at the value-chained primitives (threading the chained
   `M` through write_log/commit/installs/clear — this discharges any
   G1-impl premise-debt), `SpecEndOp` gains the client fupd.
6. **H1–H3**: the boot re-founding (mint at `D` off `fs_boot_pure`,
   dirty-at-boot blocks, ghost-no-op recovery arms replacing D1/D2's
   L-moving ones, orphan routing to ireclaim, D3's clean-header
   deletion). H0's channel is already there.
7. **The switch-on**: `fs_durable_wf := fs_durable_wf_body`, delete
   `fs_durable_wf_placeholder`; its use sites (grep) are exactly the
   rework list; E4's image discharge closes via `FsWfImg`.
8. **Stage I**: delete `Himg`/`fs_boot_image_eras`/
   `fsimg_at_every_era`; adequacy assumes only era 0's `fs.img`;
   audit unchanged.

**Working rules that proved out (keep):** design on the orchestrator,
focused execution on Opus agents with pinned specs; agent worktrees for
parallel lanes (run-on-gcp mirrors $PWD, so each worktree gets its own
VM mirror — no build collisions); linearize agent merge commits
(reset + cherry-pick) before pushing; verify the MERGED tree on the VM
before every push to main; grep build logs for plain `Error` (the
`File …`/`Error:` pair spans two lines — anchored patterns miss it).

## 1¾. Ruling 2 (owner, 2026-08-22): fr_D is the interface; recovery is logically invisible

Recorded in full in [`../design/crash.md`](../design/crash.md) §"The split
crash predicate". The four decisions:

1. **`P_fs` splits into `P_disk ∗ P_wf` inside the one `crashN` body**,
   sharing the committed map `D` (= `fr_D`) through one binder
   (a `ghost_var` handle only when an outside holder must name `D`,
   e.g. the contents layer's sync receipts). `P_disk` (log/WAL layer):
   physical fragments, `fs_recovery (blocks dk) D`, `hdr_wf`,
   mirror/custody, history. `P_wf` (FS layer): `⌜fs_durable_wf D⌝`, and
   EVENTUALLY the higher-level durable ghosts (directory/file CONTENTS
   abstracting away from the disk-like `D`) — not built yet, but the
   target shape. Only the commit permit (and the boot swap) touches
   `P_wf`; logfill/install/clear/recover FRAME it.
2. **The era knows the committed view BY VALUE, through a widened
   mirror.** `log_mirror`'s payload grows from header+slots to the era's
   full picture of the durable extent (home blocks included);
   `log_mirror_ok` pins it to the physical disk on `cov ∪ log_region`.
   Maintainable because the WAL's own writes are the only writes to the
   durable extent (installs know the bytes they write), and the custody
   arm's per-era `ghost_var` + boot swap already solve the mortality
   problem for exactly this shape. `fr_D` is then a pure function of the
   mirror picture, the commit fupd concludes `D' = L` (the batch's
   logged values over the old view), and NO bio-layer fact is needed at
   the `∅`-mask instant — the "receipt cannot NAME its state" note
   (FsCrash.v:1508) dies.
3. **The clear permit PRESERVES `D`** (no re-base): install permits hand
   back per-block "home block caught up" receipts; clear consumes them
   via `fs_recovery_clear_keeps`.
4. **The era mint runs at `D`, not at the raw disk**; the logged view
   `fs_L` is minted at `D`; recovery installs move NO ghost state (a
   dirty-log boot is the post-commit pre-install steady state: logged =
   slot content, home block physically stale, dirty-at-boot true).
   `initlog` is a physical catch-up with an empty exposed ghost effect.
5. **The FS layer never sees a machine permit.** Commit is the ONLY write
   kind that moves `D` (logfill/install/clear/recovery are `P_wf`-framing
   by 1–4), so every `P_disk`-side permit is derived ONCE, in the WAL
   layer, from its own state (mirror halves, custody, caught-up
   receipts). `end_op`'s client-facing premise is a single
   logically-atomic update of the durable view:
   `∀ D, P_wf D ==∗ P_wf D'` at `D' =` the batch's logged values over
   the old view — a FUPD, not a pure premise, because the eventual higher-level durable
   ghosts (directory/file contents) must move in the same instant. It is
   built at `end_op` time (invariants openable at ⊤ there), consumed at
   the DMA completion's `∅`-mask opening, so it must be a basic ghost
   update; `⌜fs_durable_wf D⌝` of the OLD view arrives from the invariant body
   at fire time. Group commit means the fupd covers the WHOLE group's
   batch: it is assembled generically from `⌜wf(L)⌝ + ⌜D' = L⌝` (the
   batch's entries are exactly the blocks written since the last commit;
   clean blocks have logged = physical = committed), so no exit arm ever
   states install-arithmetic — each op only maintains "the logged view
   stays well-formed" (stage G1).

**`fs_durable_wf`** is THE well-formedness invariant of the durable
committed view: the content sweeps stated generally (`fsimg_wf`'s W9 as
written is an mkfs artifact — `z = ROOTINO` is false after one successful
mkdir — and log cleanliness is no part of it). `fs.img` is merely the
base case: `fsimg_wf -> fs_durable_wf` is the era-0 discharge.

## 2. Stage A — the machine layer (`RiscvPtsto`, `RiscvExec`, `WpUart`, `PermInv`, `RiscvAdequacy`)

Footprint (grep `disk_tie\|fs_tie_interp\|riscv_crash_pred\|disk_write_permit`):
`RiscvPtsto.v` 24, `RiscvAdequacy.v` 17, `PermInv.v` 8, `CrashProto.v` 8
(a standalone proto — touch only if it breaks), `WpUart.v` 4,
`SystemAdequacy.v` 4, `RiscvExec.v` 2, plus one-liners in
`SpecVirtioDiskRw.v`, `VirtioQueue.v`, `VirtioProto.v`, `SpecBwrite.v`,
`SpecWriteHead.v`/`ProofWriteHead.v`, `SpecInstallTrans.v`/`ProofInstallTrans.v`,
`ProofBread.v`, `BootShared.v`, `SpecMain.v`.

- [x] **A1. `riscvFixedGS`** (`RiscvPtsto.v:405-460`): delete
      `riscvF_fstieGS`/`riscv_fstie_name` (the `ghost_var (Z -> bv 8)`), add
      `riscv_disk_name : gname` typed by the existing fixed-layer
      `riscvF_diskGS :: diskImgG Σ` (`:420` — the `ghost_mapG Σ Z (bv 8)`
      instance is ALREADY fixed-layer; only the NAME was per-era). Change
      `riscv_crash_pred : (Z -> bv 8) -> iProp Σ` (`:454`) to `iProp Σ`.
- [x] **A2. `state_interp`**: `fs_tie_interp g := disk_tie (v_disk …)`
      (`:1866`) becomes `disk_fixed_interp g := disk_img_auth riscv_disk_name
      (v_disk (dvirtio (gdev g)))`; same slot in `power_interp` (`:1870`).
      Delete `disk_tie`, `disk_tie_agree`, `disk_tie_update` (`:648-662`).
      `crash_inv := inv crashN riscv_crash_pred` (`:668`).
- [x] **A3. The permits** (`RiscvPtsto.v:680-700`, `PermInv.v:63,145,189,
      239,254`): `disk_write_permit gd w Q` becomes
      `∀ dk n, start_auth n -∗ ⌜n = gd+1⌝ -∗ disk_img_auth riscv_disk_name dk
      -∗ ▷ riscv_crash_pred ={∅}=∗ disk_img_auth riscv_disk_name (wr_apply w dk)
      ∗ ▷ riscv_crash_pred ∗ start_auth n ∗ Q`. The AUTH IS LENT FOR THE
      INSTANT: the client's view shift does agreement (learns `dk`), updates
      its fragments with the write, re-establishes. Reads (`w = None`) get the
      same shape with `wr_apply None dk = dk`; a read's `Q` may be stated at
      the bytes `disk_read dk off n` — that is the phase-D2 READ PERMIT, for
      free. `disk_write_permit_trivial` (`SpecVirtioDiskRw.v:131`) survives
      (return the auth untouched).
- [x] **A4. The completion** (`WpUart.v:869-975`, the only opener of
      `crashN`): drop the tie agree/update (`:941,:962`); pass the
      `disk_img_auth riscv_disk_name` conjunct from `wp_disk_step` into the
      permit and take it back. `RiscvExec.wp_disk_step` (`:624-640`): replace
      the `disk_tie` rows by the fixed auth rows (the era auth row stays).
      The three other lifting rules (`RiscvExec.v:359,473,598`) rewrite
      `/fs_tie_interp` → the new name; they frame it.
- [x] **A5. Adequacy** (`RiscvAdequacy.v`): `riscv_pre_fstieGS` (`:135`)
      goes; `boot_fixedGS` (`:1142`) takes `γdisk` instead of `γtie`;
      `HPc` (`:452,:1160`) becomes `∀ γdisk γsw γreg γst, disk_img_bytes γdisk 0
      (disk_read (v_disk g) 0 ndisk) -∗ mono_nat_auth_own γsw 1 0 ⊢ |==> Pc
      γdisk γsw γreg γst` (the FULL fragments of era 0's disk, minted by
      `DiskImg.disk_img_alloc` at `:1041`'s sibling, handed to the client
      once); the crash-invariant allocation (`:605-611`, `:1226-1232`) holds
      `Pc` alone; the fixed conjunct is the auth. `Hboot` (`:1164-1192`): the
      `F = boot_fixedGS …` equation carries `γdisk`; `boot_facts g'` says
      nothing about the disk — AS IT SHOULD. Check `power_boot_res` (`:857`,
      `:909`) still hands the era's own whole fragments (the per-era map).
- [x] **A6. Build; `make audit-only` baseline must be unchanged (eight).**

## 3. Stage B — `FsCrash.P_fs` (`FsCrash.v:931-1066`)

- [x] **B1.** `P_fs γs cov ls` (no `dk` argument) `:= ∃ dk, disk_img_bytes
      γdisk 0 (disk_read dk 0 ndisk) ∗ ∃ r, fs_hist_auth … ∗ ⌜fs_rec_wf r
      (fs_blocks dk) cov ls⌝ ∗ fs_arm γs ls dk`; `fs_crash_names` gains the
      disk gname (or take `riscv_disk_name` ambiently — `P_fs_named`
      (`:947`) already takes the three fixed names explicitly, so add a
      fourth). `ndisk` is `SystemAdequacy.XV6_DISK_BYTES`; `P_fs` is stated
      below it, so it takes `ndisk` as a parameter.
- [x] **B2.** `fs_crash_seam` (`:1505` area) back to an equation on the
      field (`riscv_crash_pred = P_fs_any …`). `P_fs_any_timeless` (`:1061`)
      must still hold (fragments are timeless).
- [x] **B3.** The five permits (`fs_logfill_permit`, `fs_commit_permit`,
      `fs_install_permit`, `fs_clear_permit`, `fs_swap_permit`) and the
      recovery-side three (`fs_era_custody`/`fs_recover_permit`/
      `fs_boot_head_permit`, `:1543-1700`) restated at A3's shape: each opens
      with agreement against the lent auth, updates the written block's
      fragments (`DiskImg.disk_img_bytes_update`), re-packs.
- [~] **B4.** (PARTIAL — only `hdr_wf` landed; the rest of the claim is
      WRONG, see §1½: the content sweeps are NOT permit-invariant.)
      Original text: `P_fs` carries mkfs's geometry as PURE content: add to
      `fs_rec_wf` (or beside it) `fs_parse_sb (fs_blocks dk) = Some sb ∧
      fsimg_wf-minus-log-clean` — everything `FsCfgBoot.fs_boot_image_wf`
      (`:1811-1840`) says EXCEPT `fs_log_clean`. It is invariant under every
      permit because no permit writes block 1.
- [x] **B5.** `HPc` at the image: `FsAdequacyImg` proves `P_fs` from
      `disk_img_bytes γdisk 0 (disk_read fsimg_dk 0 ndisk)` — the only place
      `fsimg_dk` is named (`fsimg_image_wf` `:96` already has the pure half).

## 4. Stage E — the crash layer under ruling 2 (`FsCrash.v`, no FS-proof dependencies)

**Coordinate with [`sector-atomic-disk.md`](../completed/sector-atomic-disk.md)** (ruled
the same day): once that campaign lands, the write permit fires PER SECTOR
(any order), so E2's mirror update becomes a per-sector landing and the
commit's `D`-move rides the header write's sector 0 alone (the on-disk
header is 124 bytes, inside sector 0 — that is exactly why xv6's commit is
atomic on such a disk). Whichever campaign lands second restates the other's
permits at its granularity; neither design changes shape.

**LANDED FIRST (sector-atomic, 2026-08-22, `b227bb54`; record in
`../completed/sector-atomic-disk.md`).** The machine permit is now
`disk_seq_permit` (`RiscvPtsto.sperm`: a `∧` over the sectors still to land,
each branch returning the residual). In `FsCrash.v` the block-level
`disk_write_permit` wrappers (`fs_{swap,logfill,commit,install,clear,
boot_head}_permit`, E2''s `fs_{logfill,install}_permit_v`,
`fs_commit_permit_named`, `fs_clear_permit_keep`) are DELETED — no client can
consume a block-indexed permit any more — and EVERY `_rec` form is kept; the
six sequential builders `fs_*_seq_permit` chain them via
`fs_rec_permit_mono`. Stage G composes `_rec` forms into sequential builders
the same way. E2's mirror did NOT change shape: the receipt chains through
`log_mirror_at`, so no intermediate picture is ever named.

- [x] **E1. The split (as landed).** `P_wf`'s content rides `fs_rec_wf`
      as its fourth conjunct `fs_durable_wf (fr_D r)` — stated about the
      COMMITTED VIEW only, never about the physical image, which is what
      makes it invariant under re-indexing and under every
      view-preserving permit. `FsWf.v` holds the predicate (body = the
      F1 placeholder `True`; its `fs_durable_wf_placeholder` lemma is
      the GATE — every use marks a site F1's real body will surface as
      an error: the re-basing swap/clear/recover arms (stage H), the
      compat commit (stage G), `P_fs_alloc` (E4)). `P_wf` becomes a
      separate iProp conjunct of `P_fs` when the contents layer adds
      durable ghosts.
- [x] **E2. The widened mirror (ruling 2.2).** `log_mirror` carries the
      era's full durable picture (`RiscvPtsto.v:163` — header + slots +
      homes, or one `Z -> list (bv 8)` view with derived readings);
      `log_mirror_ok` pins it on `cov ∪ log_region_set ls`; every permit
      re-establishes it at the post-write image (installs update the
      home entry — they know their bytes; `mirror_of` generalizes).
      `log_mirror_at` exposes as much of the value as its holder needs
      (the header reading stays for the existing call sites).
- [x] **E2'. The value-chained primitives (as landed).** Four new
      permits in `FsCrash.v` beside the at-forms:
      `fs_logfill_permit_v`, `fs_install_permit_v` (Q returns the half
      at `lm_upd M0 <blk> bs` — the chaining), `fs_commit_permit_named`
      (pre-image clean per the picture; concludes at the NAMED
      `D' = fs_install (lm_view M0) ls Ws (restrict …)`; takes the
      client's preservation premise — pure while `P_wf` is, the fupd
      when the contents ghosts arrive; receipt AT `D'`), and
      `fs_clear_permit_keep` (E3). The at-forms stay for the current
      consumers; **stage G re-points `ProofEndOp` at the primitives**
      and threads the chained `M` value through `write_log`/commit/
      installs/clear — `SpecEndOp`'s client-fupd premise enters THEN
      (one 26-arm sweep, not two).
- [x] **E3. Preserving clear (as landed).** `fs_clear_permit_keep`:
      the caught-up premise is pure on the chained mirror value
      ("home = slot" at every entry, true BY COMPUTATION after the
      install chain), discharged into `fs_recovery_clear_keeps`; NO
      history extension, `fs_durable_wf` framed. The re-basing
      `fs_clear_permit` stays for the current consumer until G adopts
      the primitives. Recovery-side permits keep re-basing until
      stage H makes them ghost no-ops.
- [ ] **E4.** `P_fs_alloc`/`FsAdequacyImg`: establish `⌜fs_durable_wf⌝` at the
      literal image (a `FsImgCheck`-style computation, cheap — the
      sweeps already run there).

## 5. Stage F — the pure layer: `fs_durable_wf` and the image-level update lemmas

`FsImg.v` has the full decode vocabulary and ZERO update lemmas (survey
2026-08-22); the fragment-level laws exist (`BitmapEnc.bm_bytes_*`,
`InodeRegion.diblk_wf_insert`, `FsTree.dir_written_at`/`dir_zeroed_at`,
`InodeInv.blkmap_wf_*`). This stage is the join, and it is parallelizable
and iris-free:

**F runs decoupled from G/H:** the real sweeps land under their own name
(`fs_durable_wf_body` in `FsWf.v`), with the update lemmas and the image
discharge stated about IT; `fs_durable_wf := True` and its placeholder
lemma survive until the SWITCH-ON (after G3 and H2), which equates the
two and deletes the placeholder — its use sites are the exact rework
list.

- [x] **F1.** DONE. `FsWf.fs_durable_wf_body` (real body under its own
      name; `fs_durable_wf`/placeholder untouched, switch-on still gated
      on G3+H2) = parse + W1 + W3-minus-link-floor + W4/W5 +
      W6-scoped-to-reachable + W7 + W8 + region-at-`nib` + W9-general.
      Two REFINEMENTS the pinned sweep list needed to be closed under
      the write shapes (both recorded at the definition, FsWf.v):
      (1) W3 sweeps `FsImg.fs_inodes_dwf` (= `fs_inodes_wf` minus the
      `1 <= nlink` floor, additive family with `fs_inode_dok` and
      `fs_inodes_wf_dwf`): a committed orphan is LIVE at `nlink = 0`,
      exactly the state the W9 arm names; (2) the per-dir `fs_dir_ok`
      bundle binds only REACHABLE dirs (one `∃ rd` shared with W9): an
      orphan dir's ".." dangles once its emptied parent is unlinked, and
      H1 routes orphans to `ireclaim` anyway — an orphan owes only W8's
      dots and `fs_orphans_empty` (empty-but-dots BY INDEX, xv6's
      `isdirempty`). W9 shape: `fs_rdirs` pins an existential `gset` of
      reachable live dirs (`fs_reachable` = `∃ p, path_at (tree_of_disk
      …) ROOTINO p = Some z`); `fs_rtick` counts a `bool_decide`-filtered
      supply (locality = `fs_all_tickets`'s: one mjoin segment per dir).
      The agreement suite (FsWf §5–7: the sweeps read block 1 +
      `[inodestart, size)` only; decoder-level `*_ext` at one-block
      footprints) is F2's foundation. `FsImg.fs_links_eq` (file-nlink
      EQUALITY sweep) + `FsImgCheck.fsimg_links_eq` (vm_compute, 22.3 s
      at `Qed` — W9's own ballpark); the committed-view discharge
      `FsWfImg.fsimg_durable_wf` concludes `fs_durable_wf_body
      (fs_restrict P (fs_home_set cov logstart))` from `fsimg_wf +
      fs_links_eq + fs_region_wf + parse + cov ⊇ [1, size)` — E4
      consumes it (`FsWfImg.v` is new: `FsCrash` Require-Exports `FsWf`,
      so the `fs_restrict`-level statement cannot live in `FsWf.v`).
- [~] **F2.** LANDED except one arm: per-effect files `iris/FsEffBase.v`
      + `FsEff{WriteData,Trunc,FreeInode,LinkEntry,UnlinkEntry,
      CreateEntry,AllocBlock}.v`. The base file holds the single-block
      `fs_upd` combinator, the dinode-block RE-ENCODE effect
      (`eff_dinode` writes `diblk_bytes (<[islot i := dn']> (fs_iblk …))`
      so an op postcondition at `diblk_bytes (<[…]> ds)` matches after
      one `fs_dinode_of_diblk`), the per-inode locality suite, the
      ticket segment arithmetic (`tick_omap_*`/`tick_mjoin_*`), the
      `rch` reachability toolkit (edge insert/delete/no-in-edge), and a
      common-ground section (`Set Default Proof Using "All"`) that each
      effect file rebinds with a uniform local-notation block. Every
      effect is a composition of `fs_upd`s from the EXISTING encoders
      (`bm_bytes` over `fs_bmap_set` of the old block, `dirent_bytes
      (de_of_name …)` under `fs_splice` = `wi_splice`'s pure body); each
      `eff_*_wf` is proved in-section and each `eff_*_wfv` wrapper is
      the G2-facing `fs_durable_wf_view P -> preconds ->
      fs_durable_wf_view (eff_… P sb …)` form (`sb` pinned by
      `fs_parse_sb`; the fresh-block premise is the CLEARED BITMAP BIT —
      balloc's own postcondition — since `u` is existential in the
      view). STATEMENT DELTAS vs the briefed seven, each forced and
      recorded at its lemma: (1) create splits into `eff_create_entry
      (d k name i ty maj min)` (mknod's device pair is part of the
      written record) and `eff_create_dir_entry (d k name i fb)` — a
      typed dir without its dots block has NO wf intermediate, so
      mkdir's arm carries the fresh block, its bit and `dirblk_bytes
      ([de "." i; de ".." d] ++ zeros)` in one effect; (2) unlink is one
      definition with file/dir-arm LEMMAS; the dir arm takes
      `nlink i = 1` (only then is the deleted dirent provably i's ONLY
      in-edge — the invariant alone admits a dir with two parents) and
      `".." of i names d` (the invariant does not pin ".." to the
      parent, and stranding the ".."-target must strand only i);
      (3) `eff_trunc` takes type ≠ T_DIR (a truncated typed dir breaks
      W8); the dir reclaim is `eff_free_inode`, trunc+type:=0+bfree
      FUSED, with `nlink = 0` DERIVED from unreachability;
      (4) the dirent effects compute the size move as
      `Z.max sz (16(k+1))` under a reuse-or-append precondition;
      (5) `eff_alloc_file_block (i fbn fresh sz')` covers the direct
      and indirect-ENTRY arms with `fbn ≠ 12`; (6) dirent-writing
      effects take `i < 65536` (the record stores a bv 16; nothing
      bounds ninodes). LEFT: the fused indirect-block allocation
      (`fbn = 12`, TWO fresh blocks in one effect — an eighth effect;
      until it lands G2 cannot cross a file's 12-block boundary).

## 6. Stage G — the op sweep: every transaction preserves `fs_durable_wf`

The long pole: the formal content of "xv6 never corrupts its FS".
Surface (survey 2026-08-22): 9 `log_write` sites (balloc ×2, bfree,
ialloc, iupdate, iput-free, writei ×2, bmap-indirect), 12 spans / 26
`end_op` exit arms (sys_link, sys_unlink, sys_open, sys_mkdir,
sys_mknod, sys_chdir, filewrite, fileclose, kexec ×2, kexit, ireclaim).

- [ ] **G1.** The vehicle (VALIDATED against `log_res` 2026-08-22).
      Two facts rule out simpler shapes: the ghost ledger keeps only
      INEQUALITIES (`ireg_link_ok` L1 is `w <= nlink`) and a checked-out
      inode's content is in no invariant — so `wf(L)` is not derivable
      from the resource layer at commit; and the last-to-end op cannot
      know its group's other deltas — so a bare `out = 0 -> wf(L)` row
      is not locally re-establishable. The shape that IS local, with NO
      new ghost: two pure rows on `log_res`'s `cmt = false` branch,
      re-established at each log-lock release:
      (a) `∃ A, dom A = fs_home_set cov ls ∧ fs_durable_wf_body A ∧
      ∀ b ∈ home ∖ pending(om), L !! b = A !! b`, where `pending(om)`
      is the union of the open ops' ledger sets `e.1.2` — every
      `log_write` adds its block to its op's set in the same critical
      section, so the row is FREE at all 9 write sites (the domain only
      shrinks); the whole burden is the 26 `end_op` arms: an ending op
      must produce `A' := A ⊕ (L on its own blocks)` and prove
      `fs_durable_wf_body A'` from its own carried postconditions (the
      per-op preservation lemmas, F2's update lemmas composed). At
      `out = 0` pending is empty, `L = A` on homes, `wf` falls out.
      (b) the mirror tie, on the strengthened `log_mirror_clean` row
      (the mirror half and the batch meet in `log_res`):
      `∀ b ∈ home ∖ LB, lm_view M b = L b` — maintained freely
      (log_write moves b into LB; the installs' chained `lm_upd`s
      restore it; clear resets LB). At commit: `D_old = restrict
      (lm_view M) home` (clean header), `D' = restrict(L) home` via (b)
      + `HLw`, `= restrict(A)` via (a), wf — the commit fupd for
      `fs_commit_permit_named` assembles generically, no exit arm
      states install-arithmetic.
- [ ] **G1-impl.** The rows, as Coq (execution-ready once F2 lands;
      Opus lane). `LogInv.v`: `Definition op_pending (om) : gset Z :=
      map_fold (fun _ e acc => e.1.2 ∪ acc) ∅ om`; FUSE
      `log_batch ∗ log_mirror_clean` into one bundle
      `log_state bn γfs cov ls n LB (pend : gset Z)` binding
      `∃ W L D M A` with the existing log_batch rows plus:
      `log_mirror_half M ∗ ⌜lm_hdr M ls = (0,[])⌝`,
      (a) `⌜dom A = fs_home_set cov ls⌝ ∗ ⌜fs_durable_wf_body A⌝ ∗
      ⌜∀ b ∈ fs_home_set cov ls, b ∉ pend -> L !! b = A !! b⌝`,
      (b) `⌜∀ b ∈ fs_home_set cov ls, b ∉ LB -> lm_view M b =
      <the bytes of L at b>⌝`. `log_res` passes `pend := op_pending om`.
      Touch points: the four `log_*_step` transitions; `ProofLogWrite`'s
      repack (free: the written block is in its op's `e.1.2` after
      `log_record_step`, so `pend` grows — row (a)'s domain shrinks;
      row (b): b joins LB); `ProofBeginOp`/`ProofEndOp`
      checkout/deposit (`eo_open_of_batch`/`eo_open_to_batch` now
      destructure `log_state`; at the commit checkout `out = 0` gives
      `pend = ∅`, hence `L = A` on homes); `ProofSysSync`; the boot
      establishment (A₀ := the boot image's home restriction, `wf_body`
      via `FsWfImg.fsimg_durable_wf` — which needs `fs_links_eq` ADDED
      to `FsCfgBoot.fs_boot_image_wf` as conjunct (13), discharged at
      the image by `FsImgCheck.fsimg_links_eq`, threaded through
      `BootShared`/`SystemAdequacy`/`FsAdequacyImg` premises).
      STAGING (corrected): a per-arm escape cannot gate on a false
      lemma (`fs_durable_wf_body` is REAL since F1), so row (a) flips
      on in ONE commit. Order: (i) G1-impl lands `log_state` with row
      (b), `op_pending`, and the boot `fs_links_eq` threading — green,
      real content, no row (a); (ii) G2's 26 per-op preservation
      lemmas are proven STANDALONE first (pure statements against F2's
      effect vocabulary — no `log_state` dependency, fully
      parallelizable across agents); (iii) the flip commit adds row
      (a) and wires the prepared lemmas into the arms in one sweep.
- [ ] **G2.** Thread the F2 side conditions from the 9 write sites
      (their AU suppliers already carry the abstract content) to the
      per-op obligation; discharge at the 26 arms.
- [ ] **G3.** `ProofEndOp` discharges E2's premise from G1's row.

## 7. Stage H — boot re-founding: mint at `D`, recovery a ghost no-op

- [x] **H0. The adequacy-layer pure-projection hook** — LANDED, and the
      channel `Himg` will be deleted through (stage I). The era fupd
      cannot identify `P_fs`'s existential `dk` with the real disk (the
      fixed auth lives in `state_interp`, which no era entailment ever
      holds); `wp_power_loop`'s PowerOn arm does hold it, so THAT is
      where the agreement runs. As landed:
      `wp_power_loop`/`riscv_power_adequacy` take
      `Ppure : (Z -> bv 8) -> Prop` and
      `Hproj : ∀ dk, ⊢ disk_fixed_auth dk -∗ ▷ riscv_crash_pred -∗
      ◇ (disk_fixed_auth dk ∗ ▷ riscv_crash_pred ∗ ⌜Ppure dk⌝)`
      (a `◇`, not a fupd: the arm runs it inside the step's own
      `|={⊤,∅}=>`; at `riscv_power_adequacy` it is quantified over the
      four gnames exactly as `HPc` is, at
      `disk_img_auth_sized γdisk ndisk`). The PowerOn arm opens `crashN`
      at ⊤ BEFORE the mask shrink, runs `Hproj` against `state_interp`'s
      own `Htie` conjunct, closes, and `Hboot` gains
      `Ppure (v_disk (dvirtio (gdev g')))` — sound because
      `virtio_reset` keeps `v_disk` (`Hdk2`, hoisted to where the arm
      destructures `boot_shape`), so the fact extracted at the dying
      machine IS the fact at the reset one.
      FS SIDE: `FsCrash.P_fs_project` (with `P_fs_rec_named_wf` and
      `P_fs_named_timeless`) — lend the auth to `disk_img_sized_read`,
      re-index the record with `P_fs_rec_agree` to the machine's `dk`,
      read the pure fact (persistent ⇒ non-destructive), re-index back;
      the `▷` strips under the `◇`. The payload is
      `SystemAdequacy.fs_boot_pure cov ls dk` :=
      `fs_extent cov ls XV6_DISK_BYTES ∧ ∃ D, fs_recovery (fs_blocks dk)
      D cov ls ∧ fs_durable_wf D ∧ hdr_wf (fs_blocks dk) cov ls` —
      Himg's SHAPE, PROVEN from the loop invariant instead of assumed.
      `xv6_boot_era` takes it as a premise and DOES NOT USE IT YET
      (H1 is what mints from it; `Himg` stays until I1).
- [ ] **H1.** `fs_cfg_alloc` (and `FsBoot.fs_boot_ghosts`) run at `D`
      read out of `P_fs` in the era fupd (open `crashN` at ⊤); the
      raw-disk premises become `fs_durable_wf D` + geometry from `P_fs`.
      `BootShared.boot_shared_alloc` loses the image premise.
      ORPHANS AT THE MINT: the ledger's boot count must be the
      REACHABLE-ticket count (F1's supply) — counting all-live tickets
      would violate L1 at any parent of a committed orphan dir (the
      orphan's ".." ticket has no `nlink` paying for it). Orphan dirs
      (live, unreachable, empty-but-dots) are excluded from the normal
      pool stocking and routed to the `ireclaim` path's resources.
- [ ] **H2.** Blocks where physical ≠ `D` (the committed log's homes)
      are minted dirty-at-boot: logged = slot content, bio holds them
      out of the clean pool; `initlog`/`install_trans` recovering arms
      restated as ghost-no-ops (no `it_rec_L`; the memmove is
      content-preserving at the logical level). Supersedes the
      D1/D2 L-moving arms; keep the `Bh` plumbing with `Bh i := Lw i`.
- [ ] **H3.** (= old D3) `SpecFsinit.v:318` and `FirstTok.v:275` drop
      `hdr_n = 0`; forkret's boot arm threads the general form.
- [ ] **H4.** (= old C1, if still needed after H1/H2) the read-permit
      premise through `SpecBread` for boot-time reads that must learn
      durable facts at the completion instant.
- [ ] **H5.** (= old C4) audit: no `disk_img_bytes` at the FIXED name
      outside `P_fs` (`FsBoot.v` 22 sites, `BioInv.v` 5 — expected all
      at the era map).

## 8. Stage I — the theorem (= old C3)

- [ ] **I1.** Delete `fs_boot_image_eras` (SystemAdequacy.v:147) and
      the `Himg` premises; `xv6_boot_era`'s image premise becomes the
      `P_fs` read; delete `FsAdequacyImg.fsimg_at_every_era` (:157);
      `xv6_power_adequacy_fsimg` takes `v_disk g = fsimg_dk` at era 0
      ONLY.
- [ ] **I2.** `make audit-only`: baseline unchanged (eight + the
      PrimString/PrimInt63 ten on the fsimg corollary).

## 9. Gates and rules

- Build on the VM (`QUIET=1 ./gcp-rocq/run-on-gcp make -k -j 192`), rebase
  before whole-tree builds, `make audit-only` after A, C and D.
- No contract widening that a single-file check cannot see: stage A changes
  `wp_disk_step`'s and the permits' SHAPE, so expect every virtio proof
  (`ProofVirtioDisk*.v`) and the four FS permit consumers to recompile.
- Per-file < 5 min; if a proof crosses it, split (optimization.md).
