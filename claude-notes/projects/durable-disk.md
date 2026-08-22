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

## 1½. STATE AT THE 2026-08-22 CHECKPOINT (branch `durable-disk`, NOT on main)

**Stage A is done and compiles** (883 files rebuilt clean above `FsCrash.v`):
`RiscvPtsto.v` has `riscv_disk_name`/`riscv_disk_size`, `riscv_crash_pred :
iProp Σ`, `crash_inv := inv crashN riscv_crash_pred`, `disk_fixed_auth` /
`disk_fixed_interp`; `disk_tie`/`fs_tie_interp` are gone; the permit lends
`disk_fixed_auth` (A3 as written); `RiscvExec.wp_disk_step`, `PermInv`,
`WpUart.wp_disk_loop` (the one opener) and both `RiscvAdequacy` theorems
are adapted (`boot_fixedGS` takes `γdisk ndisk`; `HPc` takes the full
`disk_img_bytes γdisk 0 (disk_read (v_disk g) 0 ndisk)`; `Pc` has four
gname arguments). `DiskImg.v` gained `disk_img_auth_sized` + `_alloc` /
`_read` / `_write` (the owner of the whole [0,N) fragment moves the image
to ANYTHING — no range side condition on writes, that is the point of the
domain bound). `SystemAdequacy.v` instantiates `Pc` at the new
`P_fs_named γd XV6_DISK_BYTES …` with the extent from
`FirstTok.fs_extent_of_image` (at `PowerBoot.boot_gstate g` — `Himg` is
still there; stage C deletes it).

**Stage B is mid-rewrite in `FsCrash.v` and DOES NOT COMPILE yet.** What is
in the file: `P_fs_rec_named` (the old record), `fs_extent`, the new
`P_fs_named γd N …` (fragments ∗ extent ∗ record), `fs_blocks_agree`,
`fs_restrict_agree`, `P_fs_rec_agree`, `P_fs_rec`/`P_fs_any` (no `dk`),
`fs_crash_seam` as a `□` pair on the field, `fs_rec_permit` and
`fs_permit_of_rec` (the one place the disk bookkeeping happens), and every
permit split into `fs_X_permit_rec` (record-only; old proof with the seam
lines removed) + `fs_X_permit` (wrapper = `fs_permit_of_rec`).

**THE OPEN POINT, found while proving `P_fs_rec_agree`:** `hdr_dec` is
UNBOUNDED (`n := le_word bs 0`, any 32-bit value), so `fs_recovery` of a
garbage header reads log slots `log_slot_bno ls j` for `j` up to `n-1`,
i.e. possibly beyond the log region and beyond the disk's extent — and the
machine's `dk` beyond `[0, N)` is pinned by no fragment. So "two images
agreeing on the durable bytes carry the same record" is FALSE unless the
record carries `length (hdr_dec (P (log_hdr_bno ls))).2 <= LOGBLOCKS` as
an INVARIANT (`fs_recovery_install` already takes it as a hypothesis,
`FsCrash.v:536`). That is true of every header the permits ever write
(swap/clear write `n = 0`; commit writes its own `(n, W)` with `Hdec`;
logfill/install leave the header alone) EXCEPT `fs_recover_permit` (5a),
which is stated "at ANY write identity" — it must gain a premise that the
write does not corrupt the header (e.g. `w` is not a header write, or
`hdr_len_ok` is preserved), and `SpecInstallTrans`'s uniform generator must
supply it. Do this next: add the conjunct to `fs_rec_wf`, re-establish it
in the six `_rec` permits, then `P_fs_rec_agree` goes through with
`fs_install_ext_P` (slots `< length W ≤ LOGBLOCKS` are in the extent).

Also pending from the first compile attempt: the two `set_solver` calls
in `P_fs_rec_agree` were replaced by explicit membership lemmas (`Hhdr`,
`Hslot`) after a `coqc` on `FsCrash.v` ran >20 min — keep `set_solver`
away from `log_region_set` (a 30-element `list_to_set`).

## 2. Stage A — the machine layer (`RiscvPtsto`, `RiscvExec`, `WpUart`, `PermInv`, `RiscvAdequacy`)

Footprint (grep `disk_tie\|fs_tie_interp\|riscv_crash_pred\|disk_write_permit`):
`RiscvPtsto.v` 24, `RiscvAdequacy.v` 17, `PermInv.v` 8, `CrashProto.v` 8
(a standalone proto — touch only if it breaks), `WpUart.v` 4,
`SystemAdequacy.v` 4, `RiscvExec.v` 2, plus one-liners in
`SpecVirtioDiskRw.v`, `VirtioQueue.v`, `VirtioProto.v`, `SpecBwrite.v`,
`SpecWriteHead.v`/`ProofWriteHead.v`, `SpecInstallTrans.v`/`ProofInstallTrans.v`,
`ProofBread.v`, `BootShared.v`, `SpecMain.v`.

- [ ] **A1. `riscvFixedGS`** (`RiscvPtsto.v:405-460`): delete
      `riscvF_fstieGS`/`riscv_fstie_name` (the `ghost_var (Z -> bv 8)`), add
      `riscv_disk_name : gname` typed by the existing fixed-layer
      `riscvF_diskGS :: diskImgG Σ` (`:420` — the `ghost_mapG Σ Z (bv 8)`
      instance is ALREADY fixed-layer; only the NAME was per-era). Change
      `riscv_crash_pred : (Z -> bv 8) -> iProp Σ` (`:454`) to `iProp Σ`.
- [ ] **A2. `state_interp`**: `fs_tie_interp g := disk_tie (v_disk …)`
      (`:1866`) becomes `disk_fixed_interp g := disk_img_auth riscv_disk_name
      (v_disk (dvirtio (gdev g)))`; same slot in `power_interp` (`:1870`).
      Delete `disk_tie`, `disk_tie_agree`, `disk_tie_update` (`:648-662`).
      `crash_inv := inv crashN riscv_crash_pred` (`:668`).
- [ ] **A3. The permits** (`RiscvPtsto.v:680-700`, `PermInv.v:63,145,189,
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
- [ ] **A4. The completion** (`WpUart.v:869-975`, the only opener of
      `crashN`): drop the tie agree/update (`:941,:962`); pass the
      `disk_img_auth riscv_disk_name` conjunct from `wp_disk_step` into the
      permit and take it back. `RiscvExec.wp_disk_step` (`:624-640`): replace
      the `disk_tie` rows by the fixed auth rows (the era auth row stays).
      The three other lifting rules (`RiscvExec.v:359,473,598`) rewrite
      `/fs_tie_interp` → the new name; they frame it.
- [ ] **A5. Adequacy** (`RiscvAdequacy.v`): `riscv_pre_fstieGS` (`:135`)
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
- [ ] **A6. Build; `make audit-only` baseline must be unchanged (eight).**

## 3. Stage B — `FsCrash.P_fs` (`FsCrash.v:931-1066`)

- [ ] **B1.** `P_fs γs cov ls` (no `dk` argument) `:= ∃ dk, disk_img_bytes
      γdisk 0 (disk_read dk 0 ndisk) ∗ ∃ r, fs_hist_auth … ∗ ⌜fs_rec_wf r
      (fs_blocks dk) cov ls⌝ ∗ fs_arm γs ls dk`; `fs_crash_names` gains the
      disk gname (or take `riscv_disk_name` ambiently — `P_fs_named`
      (`:947`) already takes the three fixed names explicitly, so add a
      fourth). `ndisk` is `SystemAdequacy.XV6_DISK_BYTES`; `P_fs` is stated
      below it, so it takes `ndisk` as a parameter.
- [ ] **B2.** `fs_crash_seam` (`:1505` area) back to an equation on the
      field (`riscv_crash_pred = P_fs_any …`). `P_fs_any_timeless` (`:1061`)
      must still hold (fragments are timeless).
- [ ] **B3.** The five permits (`fs_logfill_permit`, `fs_commit_permit`,
      `fs_install_permit`, `fs_clear_permit`, `fs_swap_permit`) and the
      recovery-side three (`fs_era_custody`/`fs_recover_permit`/
      `fs_boot_head_permit`, `:1543-1700`) restated at A3's shape: each opens
      with agreement against the lent auth, updates the written block's
      fragments (`DiskImg.disk_img_bytes_update`), re-packs.
- [ ] **B4.** `P_fs` carries mkfs's geometry as PURE content: add to
      `fs_rec_wf` (or beside it) `fs_parse_sb (fs_blocks dk) = Some sb ∧
      fsimg_wf-minus-log-clean` — everything `FsCfgBoot.fs_boot_image_wf`
      (`:1811-1840`) says EXCEPT `fs_log_clean`. It is invariant under every
      permit because no permit writes block 1.
- [ ] **B5.** `HPc` at the image: `FsAdequacyImg` proves `P_fs` from
      `disk_img_bytes γdisk 0 (disk_read fsimg_dk 0 ndisk)` — the only place
      `fsimg_dk` is named (`fsimg_image_wf` `:96` already has the pure half).

## 4. Stage C — no mortal owner holds durable state; `Himg` deleted

Sites that own DURABLE fragments today are exactly the ones that take bytes
from `P_fs`/the crash layer rather than from the era map. Audit rule: a
`disk_img_bytes`/`disk_bytes`/`disk_block` at the ERA name
(`disk_img_name`/`dn_img`) is fine; anything stated at the FIXED name outside
`P_fs` is a violation.

- [ ] **C1.** `SpecFsinit`/`SpecInitlog`/`ProofInitlog` read block 1 and the
      log header through `bread` → the era map; what they need from the
      durable side is the READ PERMIT's `Q`: "the bytes I got are `P_fs`'s
      `dk` at this block", established at the completion. Thread a
      read-permit premise through `SpecBread` (`:~130`, beside the
      write-permit premise `SpecBwrite.v:130` already takes) so a reader can
      learn durable facts at the instant; `ProofBread.v` applies it.
- [ ] **C2.** `fs_cfg_alloc` (`FsCfgBoot.v:1308`) mints `fscfg`/`icfg` from
      `P_fs`'s pure content (B4), opening `crashN` in the era fupd (mask ⊤),
      instead of from `fs_boot_image_wf (v_disk g')`. `BootShared.
      boot_shared_alloc` (`:1235`) loses the `Himg` premise.
- [ ] **C3.** `SystemAdequacy`: delete `fs_boot_image_eras` (`:146`) and the
      `Himg` premise of `xv6_boot_era`/`xv6_power_adequacy`/`_xv6Σ`
      (`:160-170,:308,:414,:488`); `xv6_boot_era`'s `Hcp` becomes the
      equation on the field. `FsAdequacyImg`: delete `fsimg_at_every_era`
      (`:157`); `xv6_power_adequacy_fsimg` (`:179`) takes `v_disk g =
      fsimg_dk` ONLY. `FirstTok.first_fsinit_pures` (`:268-278`) drops
      `hdr_n … = 0` (it becomes stage D's read-permit fact, not a premise).
- [ ] **C4.** `FsBoot.v` (22 fragment sites) and `BioInv.v` (5): confirm they
      are at the ERA map (expected — `bv_gd V` is the era's `dn_img`); if any
      is at the fixed name, rewrite per the audit rule.
- [ ] **C5.** `make audit-only`: the baseline loses nothing and gains
      nothing; `Print Assumptions` of `xv6_power_adequacy_fsimg` is the
      eight plus the PrimString/PrimInt63 ten (as today).

## 5. Stage D — the dirty-log boot (was `fs-log.md` (1)/(3))

`P_fs` allows `hdr_n > 0` (the commit permit writes it), so after C the boot
obligation is dischargeable only on the `n = 0` arm; the theorem is TRUE but
its boot WP is unproved on the dirty-log arm until:

- [ ] **D1.** `SpecInitlog.v:164` drops `hdr_n bs_hdr = 0`; `:204`'s
      `log_mirror_full` becomes `fs_era_custody`; `ProofInitlog`'s header
      copy loop goes live (`ProofWriteHead.wh_loop` `:1028` is the template).
- [ ] **D2.** `SpecInstallTrans.v:160` loses `recovering = false ∨ n = 0`;
      `ProofInstallTrans` proves the recovering arm (its printk needs the
      `SpecPrintkGen` footprint for that one function).
- [ ] **D3.** `SpecFsinit.v:316-319` and `FirstTok.v:276` stop requiring a
      clean header; forkret's boot arm threads the read-permit fact instead.

## 6. Gates and rules

- Build on the VM (`QUIET=1 ./gcp-rocq/run-on-gcp make -k -j 36`), rebase
  before whole-tree builds, `make audit-only` after A, C and D.
- No contract widening that a single-file check cannot see: stage A changes
  `wp_disk_step`'s and the permits' SHAPE, so expect every virtio proof
  (`ProofVirtioDisk*.v`) and the four FS permit consumers to recompile.
- Per-file < 5 min; if a proof crosses it, split (optimization.md).
