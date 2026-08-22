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

## 1½. STATE AT THE 2026-08-22 CHECKPOINT (second checkpoint: A+B on main-track, D1+D2 done)

**Stage A is done and committed** (8fc5a036; 883 files rebuilt clean).
Details of what landed are in the stage-A worklist below (all items hold in
the tree as described).

**Stage B is DONE and committed** (37de0fef; tree green on the VM, `make
audit-only` at the 8-axiom baseline). The open point of the first
checkpoint was closed exactly as sketched: `hdr_wf P cov ls` (decode
length ≤ LOGBLOCKS ∧ NoDup entries ∧ every entry ∈ cov ∖ log_region_set)
is the third conjunct of `fs_rec_wf`; the six `_rec` permits re-establish
it (`fs_commit_permit(_rec)` gained `(nn <= LOGBLOCKS)` / `NoDup Ws` /
membership premises, discharged in `ProofEndOp` by `eo_hdr_in` from its
own `Hwok`/`Hnd`; `fs_recover_permit(_rec)` gained a header-preservation
premise on the generator's write, discharged in `ProofInitlog` by
`hdr_wf_wr_out` + `home_ne_hdr`); `P_fs_alloc` takes `hdr_wf` of the
initial image, which `SystemAdequacy` gets from `Himg` via
`FsImg.fsimg_wf_log` + `hdr_wf_zero`. `P_fs_rec_agree` holds. Keep
`set_solver` away from `log_region_set` (30-element `list_to_set` — it
runs >20 min); use the explicit membership lemmas.

**Stage D1+D2 are DONE at the log layer** (the stage-D commit): general
`install_trans` — the recovering arm is live: the logged-view authority
MOVES per entry (`it_rec_L`, with `_step/_upto/_nil` lemmas), no `bunpin`
and no dirty-half movement (`bslots (2+0)`), the in-loop printk proved
against `printk_gen_contract γpr γu γd` (a Prop premise on the spec; the
□`printk_env` row rides the contract) — and general `initlog` — the
clean-image premise `hdr_n bs_hdr = 0` is GONE, the header-copy loop is
live (`il_copy`, ∀CID inside the induction like `it_loop`), the
recovering install runs with home client halves supplied as a `Bh : nat →
list (bv 8)` family, custody strips through `fs_recover_permit`, and the
final `write_head` uses `fs_boot_head_permit`. Callers are re-wired at
the clean arm: `ProofFsinit` instantiates `Bh := fun _ => []` (via
`hdr_dec_zero` + `initlog_dirty_all_false`), `ProofEndOp` instantiates
`recovering := false` with vacuous `HD`/`Hpk` (`ltac:(intros Hab;
discriminate)`) and a dummy `γpr := 1%positive`.

**D3 is OPEN**: `SpecFsinit`/`FirstTok.first_fsinit_pures` still require
the clean header, so the system-level boot WP still runs only over the
clean-log image; lifting it is caller plumbing (thread the read-permit
fact for the header bytes through forkret's boot arm), not log-layer work.

**Stage C is BLOCKED on an honest wall — B4's invariance claim is WRONG
as written.** B4 says the `fsimg_wf`-minus-log-clean content is
"invariant under every permit because no permit writes block 1". That
covers only the superblock-parse conjunct. `fs_boot_image_wf`'s other
conjuncts are CONTENT SWEEPS over the data region (inode-table shape,
bitmap/dirent consistency, …), and `fs_commit_permit`/`fs_install_permit`
move exactly those blocks to client-chosen bytes. Making the sweeps
invariant means every FS-layer writer proves it preserves fs-level
consistency — an FS-consistency campaign, a separate project of its own
size. Until that lands, `P_fs` cannot carry B4's pure content, C2 cannot
mint `fscfg` from `P_fs`, and `Himg` STAYS (C3 undone): the adequacy
theorem keeps its refutable per-era premise, and the honest restatement
remains the iProp lend of the crash predicate at PowerOn (notes commit
a09e4cdc, and fs-log.md's baseline section).

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

- [x] **D1.** `SpecInitlog.v:164` drops `hdr_n bs_hdr = 0`; `:204`'s
      `log_mirror_full` becomes `fs_era_custody`; `ProofInitlog`'s header
      copy loop goes live (`ProofWriteHead.wh_loop` `:1028` is the template).
- [x] **D2.** `SpecInstallTrans.v:160` loses `recovering = false ∨ n = 0`;
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
