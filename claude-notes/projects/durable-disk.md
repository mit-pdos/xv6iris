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

## 1½. STATE AT THE THIRD CHECKPOINT (A+B+D1+D2 landed; ruling 2 issued)

**Stages A and B are DONE and committed** (8fc5a036, 37de0fef;
tree green on the VM, `make audit-only` at the 8-axiom baseline).
**D1+D2 are DONE at the log layer** (65ca41d7): general `initlog` +
`install_trans`, the L-moving recovering arm. **Ruling 2 (below) supersedes
the L-moving shape** — stage H rebuilds the recovering arms as
ghost-no-ops — but the landed general specs, the `Bh` home-half plumbing,
the `printk_gen_contract` premise and the custody strip all survive; only
the `it_rec_L` movement and the recovering post's L-case are replaced.

**The old stage C was BLOCKED on an honest wall, now resolved by ruling 2.**
B4's claim ("`fsimg_wf`-minus-log-clean is permit-invariant because no
permit writes block 1") was WRONG: W3–W9 and `fs_region_wf` are content
sweeps over exactly the blocks `fs_commit_permit` moves. Making them a
`P_fs` conjunct means proving every committed batch preserves FS-level
consistency — that campaign is now stages F+G below, sized by the
2026-08-22 tree survey: 9 `log_write` call sites in 8 functions (all
already stating their written content abstractly), 12 `begin_op..end_op`
spans with 26 `end_op` exit arms, and ZERO image-level update lemmas in
`FsImg.v` (the missing join). Old stages C and D are re-cut as stages E–I
below; `Himg` is deleted in stage I, last.

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

**Coordinate with [`sector-atomic-disk.md`](sector-atomic-disk.md)** (ruled
the same day): once that campaign lands, the write permit fires PER SECTOR
(any order), so E2's mirror update becomes a per-sector landing and the
commit's `D`-move rides the header write's sector 0 alone (the on-disk
header is 124 bytes, inside sector 0 — that is exactly why xv6's commit is
atomic on such a disk). Whichever campaign lands second restates the other's
permits at its granularity; neither design changes shape.

- [ ] **E1. The split.** `P_fs := P_disk ∗ P_wf` with `D` a `ghost_var`
      halved between them (new fixed gname beside `fcn_hist`); `fr_D`
      leaves the record (the record keeps the history, last element tied
      to the ghost var). Timelessness of both conjuncts must survive
      (`P_fs_any_timeless`).
- [ ] **E2. The widened mirror (ruling 2.2).** `log_mirror` carries the
      era's full durable picture (`RiscvPtsto.v:163` — header + slots +
      homes, or one `Z -> list (bv 8)` view with derived readings);
      `log_mirror_ok` pins it on `cov ∪ log_region_set ls`; every permit
      re-establishes it at the post-write image (installs update the
      home entry — they know their bytes; `mirror_of` generalizes).
      `log_mirror_at` exposes as much of the value as its holder needs
      (the header reading stays for the existing call sites).
- [ ] **E2'. Commit names its state and takes the client fupd.**
      `fs_commit_permit` concludes `D' =` the batch's logged values over
      the old view (both named via E2) and is DERIVED from the client's
      D-update fupd (ruling 2.5); `SpecEndOp` gains that fupd as its one
      crash-facing premise (trivial until G lands, since `P_wf`'s body
      starts at `⌜True⌝`). The other permits take no client input and
      become internal.
- [ ] **E3. Preserving clear.** `fs_install_permit` returns a per-block
      caught-up receipt; `fs_clear_permit` consumes the family and
      keeps `D` via `fs_recovery_clear_keeps` (FsCrash.v:630, today
      unused). Same for the recovery-side install/boot-head permits.
- [ ] **E4.** `P_fs_alloc`/`FsAdequacyImg`: establish `⌜fs_durable_wf⌝` at the
      literal image (a `FsImgCheck`-style computation, cheap — the
      sweeps already run there).

## 5. Stage F — the pure layer: `fs_durable_wf` and the image-level update lemmas

`FsImg.v` has the full decode vocabulary and ZERO update lemmas (survey
2026-08-22); the fragment-level laws exist (`BitmapEnc.bm_bytes_*`,
`InodeRegion.diblk_wf_insert`, `FsTree.dir_written_at`/`dir_zeroed_at`,
`InodeInv.blkmap_wf_*`). This stage is the join, and it is parallelizable
and iris-free:

- [ ] **F1.** Define `fs_durable_wf` over a block view: the general
      content sweeps, no log-cleanliness conjunct, closed under the
      five write shapes. Prove `fsimg_wf -> fs_durable_wf` (the image
      discharge for E4). The W9 general form (validated against the
      ledger 2026-08-22): FILE `nlink = tick_count` (a committed orphan
      has both 0, so no extra arm); DIR `nlink = tick_count + 1` at
      the root, `= tick_count` elsewhere (self-tickets excluded, as
      `fs_rec_ticket` already does) — and the ticket supply must be
      counted over REACHABLE directories only (`tree_of_disk` from
      root): a committed unlinked-but-unfreed dir still carries a ".."
      record naming its parent whose `nlink` the unlink already
      decremented, so an all-live-dirs count breaks at the parent.
      xv6's own boot orphan sweep (`ireclaim`, fs.c:412) exists because
      such orphans persist across a crash. NOTE the ghost ledger keeps
      only `w <= nlink` (L1) — the EQUALITY is a new pure invariant,
      maintained by G1's abstract view, not read off the ledger.
- [ ] **F2.** The five update lemmas, one per written-block kind:
      bitmap set/clear (`bitmap_bytes`), dinode-at-slot
      (`diblk_bytes` insert, alloc/update/free arms), dirent
      write/zero (writei splice on a dir block), file/indirect data
      (splice + `ind_bytes` insert), fresh-block zero. Each:
      `fs_durable_wf P -> <side conditions> -> fs_durable_wf (<[b := bytes]> P)`.
      The side conditions are what stage G threads.

## 6. Stage G — the op sweep: every transaction preserves `fs_durable_wf`

The long pole: the formal content of "xv6 never corrupts its FS".
Surface (survey 2026-08-22): 9 `log_write` sites (balloc ×2, bfree,
ialloc, iupdate, iput-free, writei ×2, bmap-indirect), 12 spans / 26
`end_op` exit arms (sys_link, sys_unlink, sys_open, sys_mkdir,
sys_mknod, sys_chdir, filewrite, fileclose, kexec ×2, kexit, ireclaim).

- [ ] **G1.** The vehicle (sketched 2026-08-22; VALIDATE before
      building — a wrong vehicle costs the whole sweep). Two facts rule
      out simpler shapes: the ghost ledger keeps only INEQUALITIES
      (`ireg_link_ok` L1 is `w <= nlink`), and a checked-out inode's
      content is in no invariant — so `wf(L)` is NOT derivable from the
      resource layer at the commit instant; and the last-to-end op of a
      group cannot know the other ops' deltas — so a bare
      `out = 0 -> wf(L)` row is not re-establishable locally. The shape
      that is local: an ABSTRACT-VIEW row on `log_res`,
      `∃ A, ⌜wf(A)⌝ ∗ ⌜∀ b ∉ pending(om), L b = A b⌝`, where each op
      updates `A` in SEMANTIC CHUNKS (e.g. "allocate block b to inode
      i" is ONE `A`-update, fired at a `log_write` AU under the
      object's lock, where the preconditions are in hand), `wf(A)`
      preserved per chunk, and each op's pending blocks are finalized
      (`L = A` there) by its `log_end_step`, tied to its op token. At
      `out = 0` the pending set is empty, so `L = A` and `wf(L)` falls
      out; mid-op inconsistency lives only in the residue, never in
      `A`. Plus the bookkeeping row `⌜install of the batch over D = L⌝`
      (dirty set = batch set; clean blocks logged = committed) from
      which `ProofEndOp` assembles the commit fupd generically.
- [ ] **G2.** Thread the F2 side conditions from the 9 write sites
      (their AU suppliers already carry the abstract content) to the
      per-op obligation; discharge at the 26 arms.
- [ ] **G3.** `ProofEndOp` discharges E2's premise from G1's row.

## 7. Stage H — boot re-founding: mint at `D`, recovery a ghost no-op

- [ ] **H1.** `fs_cfg_alloc` (and `FsBoot.fs_boot_ghosts`) run at `D`
      read out of `P_fs` in the era fupd (open `crashN` at ⊤); the
      raw-disk premises become `fs_durable_wf D` + geometry from `P_fs`.
      `BootShared.boot_shared_alloc` loses the image premise.
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
