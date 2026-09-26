> **USER RULINGS (2026-09-25):** D35 = fully Rocq-literal. D37 = generic application slot, as Rocq. D36, D38–D45 = approved as recommended.

# Brief: reinstating the crash layer (wave C)

**Why this wave exists.** The user ruled D23 (2026-09-25): the final theorem is Rocq's full
`SystemAdequacy.xv6_fs_adequacy_xv6Σ`, which includes the crash-durability corollary. That
reverses D11 (fs7_file_layer.md §8), under which the port dropped `fs_crash_seam`, `gen_cert`,
the durability permits, the mirror, the bank, the snapshot law and block 1's park. This brief
plans how to put them back.

Numbering continues from wave8_top.md's D34. Every item carries a recommendation. "(user)" marks
a scope or process-layer decision, which goes to the user under rule 3.

Surveyed Sept 25 2026 against `lean-v2` @ `671c69a5e` and `/shared/xv6rocq/iris`.

---

## DECISIONS

| # | decision | recommendation |
|---|---|---|
| **D35** (user) | **How literal.** Rocq's crash story has four parts. (i) The crash predicate `P_fs` is over a record `fs_rec`: the committed map `D`, a mono-list history, a per-generation custody arm squeezed by `swap_lb`, and a durable snapshot conjunct. (ii) Each group commit mints a FRESH durable fs instance (`P_dur_at`, `snap_ok S D`) and transports the resources into it (`FsDurXfer`). (iii) Permits are SEQUENTIAL and per sector (`sperm`/`disk_seq_permit`), because a 1 KiB block tears across two 512-byte sectors. (iv) A per-era mint is taken from the snapshot (`FsCfgSnap`) instead of the image. | **Rocq-literal in all four.** Each one exists for a reason that Lean's own model reproduces. The Lean virtio model drains one sector at a time (`MachCSL/Dev/Virtio.lean:416`), so the block tears exactly as in Rocq. Later eras boot on whatever was last committed, so the image-decoding mint cannot be reused past era 0 (Rocq's FsCfgBoot header: "asserting it at EVERY era is refutable"). By the user rule, a simplification such as "one durable instance updated in place" needs the full picture first, and Rocq already tried and deleted that shape |
| **D36** | **Rocq gunk in the crash layer** (§1.4 lists it) | **Do not port it**, and record "not ported, uses checked: none" in each header. That covers: about 60 dead declarations (per file in §1.2); the whole files FsCollectImg, IregClean, FsDurSyscall and the five `Fs*Pin*` files (the pin files are the echo-application cone only); the `fs_boot_tok` family; `perm_collect_kq`; `P_fs_rec_named`; the non-`_at` `P_dur_tie*`; `fs_state_xfer` (the q=1 form, superseded by `_tok`); and stale references to FsFlushed.v and `fs_cfg_alloc`. FsDurAlloc's carve (997 lines, era 0 only) **is ported** (D41) |
| **D37** (user) | **The application slot.** The machinery is generic in an opaque guest `G`, and `app_guest := app_dur_raw app_pred` is its one value. `FsCollectAll.fs_snap_law_build` takes `app_xfer`, and `xv6_slot` pairs `P_fs` with `app_dur_raw`. Rocq's `xv6_fs_adequacy_xv6Σ` is the `unit` application of `xv6_power_adequacy_gen`. Lean has AppCfg/AppInv but dropped `fsabs_env` from `first_done` (FirstTok deviation 1) | **(a) Generic, as Rocq.** Port AppDur (127 lines). Add `fsabs_env`/`app_xfer` back to `firstDone`/`firstFsinit` (the FirstTok deviation-1 reversal). Instantiate at `unit` only in SystemAdequacy. The cost is small and every crash file keeps Rocq's shape. (b) would fix `G := fun _ => emp` and specialise ~6 files, diverging from Rocq for no saving that matters |
| **D38** | **Where `fs_crash_seam`/`gen_cert` ride.** In Rocq, `fs_ready` carries both (`FsReady.v:295`), and the sys_* contracts list them as separate premises beside the other constituents. In Lean, the sys_* contracts take `fsReady` in place of the constituents (fs7 D1) | **Put both in `fsReady`** (additive conjuncts plus the projections `fsReady_seam`/`fsReady_gen`). Keep them as **explicit premises only where Rocq's contract is pre-`fs_ready`**: `end_op`, `ireclaim`, `initlog`, `fsinit`, `main`. Then no sys_*, file-layer or kexec contract changes (§3). Checked: every end_op call-site lemma except two already works from `fsReady` |
| **D39** | **The MachCSL fixed-disk layer.** Rocq's `riscvFixedGS` has `riscv_disk_name`/`size` (the durable disk, whose auth is in `power_interp`), `riscv_crash_pred` as a FIELD, `riscv_swap_name`, and a per-era `era_mirror_name`. Lean's `MachFixedGS`/`powerInterp` have none of these (`Resources.lean:164,942`) | **Rocq-literal: fields, not parameters.** Add `diskName`/`diskSize`/`crashPred`/`swapName` to `MachFixedGS` and `mirrorName` to `EraGS`. Add a `diskFixedInterp` conjunct, last in `powerInterp`. Add `crashN`/`crashInv`, `swapAuth`/`swapLb`, `diskWritePermit`/`sperm`/`diskSeqPermit`, and the permit channel. **Name the channel `crashPerm*`**, because `DiskInvDefs` already uses `permAuth`/`permTok` for the unrelated *serve* permits |
| **D40** | **Where a permit is spent in the Lean model.** Rocq opens `crashN`+`permN` at the device's DRAIN step (`VirtioProto.v:4542,5576`, `WpUart.wp_disk_loop`). In Lean, drain is ghost-inert today (`DiskInv.lean:371` `diskProto_drain`; `Virtio.drain` preserves `cacheView`) | **Same place: `Virtio.drain`**, under xv6's negotiated write-through mode (CONFIG_WCE declined, so every sector drains before completion). This needs a MachCSL device-step rule that LENDS `diskFixedAuth` and `startAuth (gen+1)` to a local DevM step that changes `v.disk`. That is the one new rule shape in WpDev (§4, C-M) |
| **D41** | **Era-0 mint.** FsDurAlloc (value-first carve) plus FsDurImg (`img_state`, `img_snap_ok` over the image wf) are Rocq's only era-0 route | **Port both literally.** One inventory agent suggested minting era 0 through the transport from a directly built `fs_state`. That is exactly a simplification made without the full plan, so it is recorded as a possible later cleanup and not taken. `Himg` stays a premise (D34) |
| **D42** | **The fsinit / initlog header premise.** Lean `SpecFsinit.lean:88` says `hhdr0 : hdrN bsHdr = 0` is "AS ROCQ'S premise (g)". That is **stale**: Rocq's `SpecFsinit.v:346–348` says "the CLEAN-IMAGE premise `hdr_n bs_hdr = 0` IS GONE". Rocq's (g) is `hdr_wf`, plus (g') mirror/L agreement and (g'') exception-set slot values. `firstFsinitPures` also carries `hdrN bsHdr = 0` | **Drop `hhdr0` and restate Rocq's (g)/(g')/(g'')**. This is forced, because era n>0 boots on a dirty header. `initlog` is already general in `n` (its `hxslot` returns to Rocq's `M`-form once the mirror exists) |
| **D43** | **FsState.v's remainder.** FsDurXfer/FsDurSnap are stated over `fs_state Γ dq S`, `fs_state_rec`, `fs_footprint`, `fs_links`, `fs_pure` and `fs_geom`. Lean ported only the `top_frag` family (`FsStateTop.lean`) and the per-piece `FsState*` files | **Port the rest as `Xv6/FsState.lean`** (Rocq FsState.v minus :229–300, about 700 lines). It is the first file of the wave |
| **D44** | **`sys_sync`'s receipt.** Lean's SpecSysSync returns only `a0 = 0` (its header records the drop) | **Restore Rocq's post** `flushedSync γ e`. The proof edit is one call (`flushed_sync_of_res`, ProofSysSync). **Separately: wave8_top §2.2's arm split has no arm for sync** (the arm files list 21 entries). Add sync to `SyscallArmsProc` or `SyscallArmsFd`, and do it after C-2b so the arm is written against the receipt form |
| **D45** | **Execution model.** Most of the reinstatement edits landed files: logInv rows, DiskInvDefs slot rows, virtio/bwrite/write_head/install_trans/end_op/initlog/fsinit contracts, fsReady, FirstTok, and MachCSL | **Three serial worktrees for the landed edits** (C-M, C-2, C-4 in §4). **Parallel main-tree agents for the ~18k lines of new theory files** (C-0, C-1, C-3). Every worktree commit runs the full `lake build Xv6 MachCSL` |

---

## 1. (a) What Rocq's crash layer is

### 1.1 Shape in one paragraph

- **The machine.** It keeps a durable disk ghost whose authority is in the fixed state interpretation, and an opaque crash predicate `riscv_crash_pred` that owns all of that disk's fragments forever. The predicate is sealed as `crash_inv := inv crashN riscv_crash_pred`. The only thread that opens it is the disk device, at each 512-byte sector drain, where it spends one link of the writer's sequential permit (`disk_seq_permit`). A permit is a view shift over `disk_fixed_auth dk ∗ ▷ riscv_crash_pred`, pinned to the live era by `start_auth (gen+1)`.
- **The file system.** It instantiates the crash predicate as `P_fs_comp` through the persistent **seam** `fs_crash_seam_at G cov ls`, which is `□(riscv_crash_pred ⇔ P_fs_comp G cov ls)`. `P_fs` is the pure recovery relation (log header replay over the home blocks) plus a committed history, plus a custody arm tying this era's mirror half to the disk, plus the **durable snapshot** `P_dur_at gt D`. The snapshot is a FRESH fs instance minted at each group commit by the **snapshot law** (`snap_law`, parked in `log_ctx`, built once by `fsinit` from the collection `FsCollectAll`).
- **The log.** Four permit instantiations drive `D`: logfill, commit, install and clear. The commit permit consumes the law's fresh `dur_pair`. The log banks a durability receipt (`log_flushed_bank`) that `sys_sync` copies out.
- **Across a power cycle.** Adequacy projects `fs_boot_pure`. It swaps the custody arm to the new era and lends a clone of the snapshot. The new era's fs configuration is minted from that snapshot (`FsCfgSnap`).

### 1.2 Files (theory / definitional), in the cone of `xv6_fs_adequacy_xv6Σ`

| file | lines | contents | load-bearing exports | dead (D36) |
|---|---|---|---|---|
| **FsCrash.v** | 3792 | pure recovery relation, `hdr_wf`, sector algebra, `fs_rec`, history, custody arm, `P_fs_at`, alloc/project/swap, the seam, the permits | `fs_blocks`:86, `hdr_wf`:349, `fs_recovery`:460 (+`_det`/`_total`/`_clean`), `log_mirror_ok`:503, `mirror_of`:509, WAL-step recovery lemmas :1048–1138, `fs_rec`:1494, `fs_rec_wf`:1506, `fs_crash_names`:1666, history :1712–1747, `fs_custody`:1825, `fs_arm`:1832, **`fs_arm_acc`**:1917 (the squeeze), **`P_fs_at`**:1991, `P_fs_named_at`:2052, `P_fs_dur_acc`:2264, `P_fs_lend_at`:2297, `P_fs_project`:2368, `P_fs_swap`:2431, `P_fs_alloc`:2556, `P_fs_comp`:2659, **`fs_crash_seam_at`**:2666, `fs_crash_seam`:2675, `fs_rec_permit`:2697, `fs_permit_of_rec`:2706, **`fs_bank`**:2768, seq permits **`fs_logfill_v_seq_permit`**:3284, **`fs_install_v_seq_permit`**:3407, **`fs_commit_L_seq_permit`**:3523, **`fs_clear_keep_seq_permit`**:3670 | 17 names + `fs_boot_tok` family + `fs_commit_receipt` |
| **FsDurSnap.v** | 1817 | the pure tie `snap_ok`, the epoch, clone, read-back, commit swap | `snap_bytes`:261, **`snap_ok`**:521, **`snap_holds`**:545, `fs_snap`:835, `snap_guest`:850, **`P_dur_at`**:893, `dur_pair`:911, `P_dur_alloc_xfer`:937, `P_dur_at_clone`:999, `fs_snap_read_ok`:1368, `dsnap_step_xfer`:1473 | 8 (the EraHome section is nearly dead) |
| FsDurBytes.v | 388 | `fs_dbytes` theory, `snap_gamma` | `fs_dbytes_blocks`:263, `snap_gamma`:369 | 1 |
| FsDurRead.v | 385 | `snap_auth`, run and block reads | `snap_auth`:254, `snap_blk_read`:334 | 0 |
| FsDurXfer.v | 1357 | transport `fs_state Γ q S ==∗ … ∗ fs_state Γ' 1 S` | **`fs_state_xfer_tok`**:1315, `fs_state_install`:1173 | 9 |
| FsDurAlloc.v | 997 | value-first carve, era 0 | `P_dur_alloc`:985 | 2 |
| FsDurImg.v | 1696 | `img_state`, **`img_snap_ok`**:1382, `img_P_dur_alloc`:1678 | — | 0 |
| FsCfgSnap.v | 1377 | **per-era fs mint from the snapshot** (`fs_cfg_alloc_snap`:814, about 540 lines) | — | 1 |
| FsCollect.v | 1852 | pure collection at quiescence | `col_view`:396, `col_geom`:539, `col_agree`:777 | 6 + ClaimBox/Corpse/PoolWitness sections |
| FsCollectAll.v | 2014 | opens app/ftop/ireg/bitmap/sb_park/ipool/escrows at one step; mints the next epoch | `col_bodies_acc`:1400, `fs_collect_dur`:1799, **`fs_snap_law_build`**:1950 | 1 |
| FsFlushedCore.v | 339 | receipt `flushed b D` | `flushed`:281, `flushed_receipt_any`:289, `flushed_of_bank`:331 | 4 + 2 transitive |
| LogSnapLaw.v | 183 | the law as `log_ctx` parks it | `snap_law_out`:91, `snap_law_at`:98, **`snap_law`**:120, `_intro`:135, `_run`:153 | 0 |
| SbPark.v | 191 | block 1 at fraction 1 in `inv sbN` | `sb_parked`:99, `sb_park_alloc`:107, `sb_parked_bno_ne`:172 | 0 (**Lean already has `Xv6/SbPark.lean`, 213 lines, unwired**) |
| AppDur.v | 127 | the application's durable claim | `app_dur_raw`:56, `_open`/`_pack`/`_clone`, `app_guest`:126 | 1 |
| FsBootParams.v | 100 | `XV6_DISK_BYTES`, **`fs_boot_pure`**:57 | — | 0 |
| FsCfgBoot.v | 765 | `fs_boot_image_wf`:585, `fs_boot_snap_wf`:671, `fs_boot_supply`:715 (the image-decoding mint `fs_cfg_alloc` has been deleted; comments naming it are stale) | — | — |
| FsCfgKits.v | 518 | kits carrying `fs_crash_seam_at app_guest` (:335) | — | (fs-lean-design: no reusable kit) |
| PermInv.v | 440 | the non-timeless permit channel (disk_inv must stay timeless) | `perm_slot`:77, `perm_inv`:100, `perm_tok`:112, `perm_step_kq`:321, `perm_consume_kq`:340, `perm_deposit_kq`:358 | `perm_collect_kq` |
| DiskImg.v | 442 | durable-disk byte ghost map | `disk_img_auth`:56, `disk_img_bytes`:94, sized read/write :406/:416 | — |

**Sizes.** The theory cone is 16,615 lines, plus PermInv, FsCfgBoot, FsCfgKits and DiskImg, for about 18.8k lines. Add FsState.v's unported remainder (~700, D43). After D36's cuts, expect about 16–17k Rocq lines to port. That is the size of the fs-leaf waves together.

**Skipped by D36 (out of cone): 3,690 lines.** FsCollectImg 379 (nothing imports it), IregClean 102 (dead), FsDurSyscall 665 (echo cone only), FsInitPin 541, FsInitPinBoot 388, FsShPin 476, FsEchoPin 471, FsConsPin 668 (all echo cone).

### 1.3 Crash rows inside files Lean already has

| Rocq | rows | Lean counterpart |
|---|---|---|
| RiscvPtsto.v | fixed fields `riscv_disk_name`/`size`, `riscv_crash_pred`:500, `riscv_swap_name`; `era_mirror_name`:342; `swap_auth`/`swap_lb`:901; `gen_cert`:937 (**Lean has `genCert`**, `MachCSL/Resources.lean:1229`); `crashN`:952, `crash_inv`:961; `disk_fixed_auth`:1158; **`disk_write_permit`**:1185; `sperm`:1302; **`disk_seq_permit`**:1320; `power_interp`:2866 with `disk_fixed_interp` | `MachFixedGS`/`powerInterp` lack the disk, crash, swap and mirror pieces (D39) |
| RiscvAdequacy.v | `riscv_power_adequacy`:1593 with hooks `HPc`:1619, `Hproj`:1636, `Mof`:1651, `Hswap`:1659; the `Hobs` disk lend :705 | `wp_power` (`Power.lean:422`) has only `Hobs`/`Hboot` and records the missing lend (:417). No Lean adequacy yet (W8-G) |
| VirtioProto.v / WpUart.v | slot row `perm_pend` keyed by `vs_perm`; `slot_perms_done`:2946; drain opens `crashN`/`permN` (:4542, :5576) | `DiskInvDefs.lean:147` "No crash permits"; `DiskInv.lean:3138` drain arm |
| LogDefs.v | `log_mirror_half`:405, **`log_mirror_born`**:430 | pure picture ported (`LogDefs.lean` `LogMirror`, `lmUpd`, `lmCommitted`, `lmInstall*`); resource dropped |
| LogInv.v | `log_flushed_bank`:447 (+`_mk`/`_recycle`/`_le`); `log_mirror_tie_body`:1040 (**ported pure**, `LogInv.lean:369`); `log_state` rows :1120–1163 (`uint w ≠ SB_BNO`, mirror half, header clean, tie); `log_res` bank :1268; `log_ctx` :1403 = lock ∗ cells ∗ **`swap_lb (S gen_id)`** ∗ `fs_bytes_at` ∗ **`sb_parked`** ∗ **`snap_law`** ∗ `exc_sealed`; `log_ctx_snap_law_of_ops`:1723; `log_res_flushed`:~1290 | `logCtx` (:539) = lock ∗ `logFrozen` ∗ `fsBytesAnyAt`. The byte view and exception seal are present; swap/park/law are missing |
| FsBlocks.v | `exc_own`/`exc_sealed`:780 | **ported** (`FsBytesInv.lean:142`) |
| FsReady.v | `fs_ready` :295 carries seam + `gen_cert`; `fs_ready_seam`:480, `fs_ready_gen`:483 | dropped (FsReady deviation 1) |
| FirstTok.v | `first_boot_persist`:245 (seam, cert); `first_fsinit_pures`:295 (`hdr_wf (fs_blocks dk)`); `first_fsinit`:404 (`log_mirror_born (mirror_of …)`); `first_fsinit_open`:417 (`fs_crash_seam_at app_guest`, `exc_own`); producers `fs_extent_of_image`, `col_geom_of_config`:878 … | dropped (FirstTok deviations 2 and 8) |

### 1.4 Per-function obligations (what shape)

| layer | function | Rocq contract rows | real crash work in the Rocq proof? |
|---|---|---|---|
| virtio | `virtio_disk_rw` (Spec 197) | pre `disk_seq_permit gen_id (wr ? Some (1024·bno, bs_buf) : None) Q` (:153); post `▷ Q`; `Q` a module parameter | **yes, local**: `perm_deposit_kq` at enqueue, `perm_collect` after wake (ProofVirtioDiskRwF :1879, :897). (Rocq's `*CSeam`/`*DSeam` files are proof-phase seams, not crash) |
| bio | `bwrite` (180) | pre `disk_seq_permit … (Some (1024·bno, bs)) Q` (:143), post `▷ Q` | none (pass-through) |
| bio | `bread` | none; calls rw at `None` via `disk_write_permit_trivial` (ProofBread :902) | trivial |
| log | `write_head` (214) | pre: a FAMILY `∀ bs', ⌜len, hdr_n, hdr_dec⌝ -∗ disk_seq_permit … (Q bs')` (:157); post `▷ Q bs'`. Takes `log_frozen`, not `log_ctx` | pass-through |
| log | `install_trans` (495) | pre `□ (∀ i w, … -∗ ▷ R i -∗ disk_seq_permit … (R (S i))) -∗ ▷ R 0` (:428); post `▷ R n`. Also byte view + `exc_own` on the recovering arm (**already in Lean**) | pass-through (exc bookkeeping only) |
| log | **`end_op`** (205) | pre `fs_crash_seam cov ls -∗ gen_cert -∗` (:157); **no other fs-facing premise; no crash post** | **the heart**, in ProofEndOp (5427): `eo_snap_law_of_auth`:836 (law run under `fsbN`), the four permits (:3606, :2145, :2348, :2480), mirror algebra (`lm_upd`×31, `lm_install`×19), bank bump (`log_epoch_bump`:1835, `log_flushed_bank_mk`:1843; `_recycle` on the empty path :5166) |
| log | **`initlog`** (446) | pure `hdr_wf`, `D !! b = Some false`, `L !! b = lm_view M b`, `Xv b = lm_view M (slot i)`, `fs_parse_sb`/`fs_sb_ok`; resources seam (:292), cert, `log_mirror_born M` (:304), `fs_bytes_inv`, `exc_own (hdr_dec …).2`, `fsblock SB_BNO` at fraction 1, `□ (sb_park -∗ snap_law)` (:389); post `log_ctx` | **yes**, in ProofInitlog (2784): recovery permits (:2158), `exc_seal` (:2178), clear permit (:2377), genesis bank (:2693), `sb_park_alloc` (:2748) |
| log | `log_write` (768) | none in the statement; the proof fires `sb_parked_bno_ne` at the append arm | small |
| log | `begin_op` | none | none |
| fs leaves / inode / dir | balloc, bfree, bmap, readi, writei, itrunc, ialloc, iupdate, iget, ilock, iput, dirlink, dirlookup, namex, the Era walks | **none** (they take `log_ctx` only) | none |
| inode | `ireclaim` | pre seam + cert (:242), handed to end_op | pass-through |
| file | `filewrite` | `filewrite_fs_env` = `log_ctx ∗ seam ∗ cert ∗ …` | pass-through |
| file | fileclose, fileread, filestat | via `fs_ready` / none | none |
| syscalls | sys_open, sys_mknod, sys_chdir, sys_unlink, sys_mkdir, sys_link, sys_exit, kexit | pre seam + cert (explicit, beside the other constituents) | pass-through to end_op tails |
| syscalls | exec/kexec, write, syscall, userinit, forkret | inside bundles (`fs_fabric`, `fs_ready`) | none |
| syscalls | **`sys_sync`** (370) | pre `log_ctx`, `log_epoch_lb γ e`; **post `flushed_sync γ e`** (:212) | one call, `flushed_sync_of_res` |
| boot | **`fsinit`** (556) | seam_at `app_guest`, `app_xfer`, cert, `log_mirror_born M`, byte view, block 1, `exc_own`, and (g) `hdr_wf`, (g') and (g'') | **yes**: the only call of `fs_snap_law_build` (ProofFsinit :614), plus `fs_crash_seam_of_at` (:587) |
| boot | `main` (861) | `fs_boot_snap_wf`, `log_mirror_born (mirror_of (fs_blocks dk))`, cert, seam (:676–710); the seam comes from `xv6_boot_era`'s `Hcp` equation | pass-through into `first_tok` |
| boot | forkret | pure `hdr_wf`/`fs_blocks` bookkeeping (ProofForkret :1153–1231) | small |

### 1.5 The top

- **`xv6_fs_adequacy_xv6Σ`** (SystemAdequacy :2314). Premises: `ggen = 0`, `gpow = false`, and `v_disk = fsimg_dk`. Conclusion: every `rtc erased_step` from `[PowerLoopE]` reaches only reducible threads, and `xv6_trace_pure cov ls g2` holds (:445). `xv6_trace_pure` is `fs_boot_pure cov ls (v_disk …) ∧ (gpow → resv_ok g)`. `fs_boot_pure` (FsBootParams :57) is `fs_extent ∧ ∃ D, fs_recovery (fs_blocks dk) D cov ls ∧ hdr_wf ∧ ∃ S, snap_ok S D`.
- **The ladder**:
  1. `xv6_power_adequacy_gen` :1138, with `Himg` as the only disk hypothesis (D34).
  2. It applies `riscv_power_adequacy` with these hooks:
     - `HPc` := `P_fs_alloc` + `img_P_dur_alloc` + `Happ_init`
     - `Hproj` := `xv6_slot_project`
     - `Mof` := `mirror_of ∘ fs_blocks`
     - `Rb` := `P_fs_lend_at ∗ ▷ app_dur_at ∗ app_boot`
     - `Hswap` := `P_fs_swap`
     - `Hboot` := `xv6_boot_era` :518, which takes the `Hcp` equation `riscv_crash_pred = P_fs_comp (app_dur_raw A) cov ls` and builds the seam by conversion (:792)
  3. Then `xv6_power_adequacy` (unit app) :1728 → `xv6_power_adequacy_xv6Σ` :2253 → `xv6_fs_adequacy_xv6Σ`.
- **The slot** `xv6_slot` (:362) is `∃ gt, P_fs_named_at gt γd XV6_DISK_BYTES γsw γreg γst cov ls ∗ app_dur_raw (app_fs c) gt`.
- **BootShared** (2428): `boot_shared_alloc` :1605 carries `crash_inv`, cert and `log_mirror_born` through `power_boot_res_unpack` :1373, and calls `fs_cfg_alloc_snap` (:2274).

---

## 2. (b) Every Lean site where D11 (or its predecessor, the disk-layer drop) removed something

"Rocq name" is what is missing. Line numbers are at `671c69a5e`.

### 2.1 MachCSL

| file:line | dropped |
|---|---|
| `MachCSL/Resources.lean:164` (`MachFixedGS`), `:942` (`powerInterp`) | fixed durable-disk ghost, `riscv_crash_pred` field, swap counter; the per-era mirror name in `EraGS` |
| `MachCSL/Power.lean:355` (`powerBootRes`), `:417–421` (deviation text) | the `Hobs` durable-disk lend (`disk_fixed_auth`); the `Hproj`/`Mof`/`Rb`/`Hswap` hooks; boot rows (mirror half, `swapLb`, `Rb`, `crashInv`) |
| (absent) | `crashN`/`crashInv`, `diskWritePermit`, `sperm`, `diskSeqPermit`, PermInv channel, DiskImg camera, the drain-lend step rule |

### 2.2 virtio / bio

| file:line | dropped |
|---|---|
| `Xv6/DiskInvDefs.lean:147–148` | "No crash permits, no `Q`, no `disk_seq_permit`": the slot's `perm_pend` token row and `slot_perms_done` |
| `Xv6/DiskInv.lean:371` (`diskProto_drain`), `:3138` (drain arm), completion arm | permit step and consume at drain and completion |
| `Xv6/SpecVirtioDiskRw.lean:1–4` | pre `diskSeqPermit … Q`, post `▷ Q` |
| `Xv6/SpecVirtioDiskInit.lean:1–3` | the permit channel's allocation (`perm_inv` rides the live arm) |
| `Xv6/SpecBwrite.lean:1–4` | pre permit, post `▷ Q` |
| (bread) `ProofBread`/`BreadScan`/`BreadTail` | the trivial `None` permit at its rw call |

### 2.3 log

| file:line | dropped |
|---|---|
| `Xv6/LogDefs.lean:36–45` | `log_mirror_half`, `log_mirror_born` (resource; the pure picture is ported) |
| `Xv6/LogInv.lean:25–51` (header) and `logStateAt` :399 | `log_state`'s mirror half, `lm_hdr M = (0,[])`, the tie row (b) (`logMirrorTieBody` :369 is ported, **unused**), and `uint w ≠ SB_BNO` |
| `Xv6/LogInv.lean` `logResAt` :418 | `log_flushed_bank γ E` |
| `Xv6/LogInv.lean` `logCtx` :539 | `swap_lb (S gen_id)`, `sb_parked`, `snap_law` |
| `Xv6/SpecWriteHead.lean:39–46` | the permit family and `Q bs'` |
| `Xv6/SpecInstallTrans.lean:53–55` | the `□` permit generator and `R` |
| `Xv6/SpecEndOp.lean:29–35`; `Xv6/EndOpDefs.lean:8–12, :771` | seam, `gen_cert`, durability fupds, `eo_open`'s mirror row, `snap_law_out`, `fs_bank` / bank deposit |
| `Xv6/SpecInitlog.lean:30, :46, :54` | seam, cert, `log_mirror_born`, block 1's park, the law premise; `hxslot` read off `L` rather than `M` |
| `Xv6/SpecLogWrite.lean:136–139` | `sb_parked_bno_ne` at the append arm |
| `Xv6/SpecSysSync.lean:15–28`; `ProofSysSync.lean:37` | post `flushed_sync γ e` |

### 2.4 fs leaves, inode, dir

| file:line | dropped |
|---|---|
| `Xv6/SpecIreclaim.lean:89–90` | pre seam + cert |
| `Xv6/FsCfgDefs.lean:18–20` | (note only: per-era config; stays correct) |
| — | the leaves (balloc…namex, Era walks) have no crash rows in Rocq, so **nothing was dropped** |

### 2.5 file layer

| file:line | dropped |
|---|---|
| `Xv6/FsReady.lean:3–4, :61–63` (deviation 1) | `fs_crash_seam fsc_cov fsc_logst`, `gen_cert`, `fs_ready_seam`/`fs_ready_gen` |
| `Xv6/SpecFilewrite.lean:81` | seam and cert in `filewrite_fs_env` (restored through `fsReady`, D38) |
| `Xv6/SpecFileclose.lean:78–79` | (through `fsReady`) |

### 2.6 syscalls and process

| file:line | dropped |
|---|---|
| `Xv6/SpecSysOpen.lean:110–111`, `SpecSysLink.lean:83–84`, `SpecSysChdir.lean:86–87`, `SpecSysMknod.lean:88–89`, `SpecSysMkdir.lean:74–75`, `SpecSysUnlink.lean:85–86`, `SpecKexit.lean:59` | seam + cert premises (restored through `fsReady`, D38; only the deviation text changes) |
| `Xv6/KexecDefs.lean:80–81` (`fsFabric`) | same (through `fsReady`) |
| `Xv6/FirstTok.lean:51–60` (deviation 2), `:116–122` (deviation 8), deviation 1 (`fsabs_env`) | `first_boot_persist`'s seam and cert; `first_fsinit`'s `log_mirror_born`, `fs_crash_seam_at app_guest`, `app_xfer`, exc slot values, `col_geom`, sb ties, `hdr_wf`; `Rspent`/`Pb`/coverage remainder; the pure producers `fs_extent_of_image`, `col_geom_of_config`, … |
| `Xv6/SpecFsinit.lean:73–95` (deviations 2, 3, 4) | block 1 parked, not returned; seam_at/app_xfer/cert/mirror/law geometry; **`hhdr0` (stale claim, D42)** |
| `Xv6/FsinitCalls.lean`, `FsinitTail.lean`, `FsinitLog.lean`, `ProofFsinit.lean` | the law build (`fs_snap_law_build`) and the park allocation |
| wave8_top.md rule 4, §5.1 (`fs_boot_supply` "drop Rspent/Pb/crash rows") | **rescind**: the rule and the trimmed FsCfgBoot plan are superseded by this brief |

### 2.7 Landed Lean that already anticipates the crash layer (reuse, do not redo)

- `Xv6/SbPark.lean` (213): Rocq SbPark, whole, unwired.
- `Xv6/LogDefs.lean` `LogMirror`/`lm*`, and `LogInv.lean` `logMirrorTieBody` + `logMirrorTie_deposit`.
- `Xv6/FsBytesInv.lean` `excOwn`/`excSealed` and the byte-view invariant; `SpecInitlog` general in `n`; `SpecInstallTrans`'s recovering arm is Rocq's `emp` row.
- `Xv6/FsBytesGamma.lean`, `FsStateDefs.lean` (`FsViewNames`, `phiExcl`): the abstract Γ record, so the durable instance can be stated. fs-lean-design's "COLLAPSE" option was not taken, which is good.
- `Xv6/AppCfg.lean`, `Xv6/AppInv.lean` (whole).
- `MachCSL`: `genCert`/`genCertAt`, `startAuth`/`genStarted`, eras, `bootShape` (disk survives reset), and a sector-drain virtio model.

---

## 3. (c) Can it be layered on?

**Mostly yes.** Rocq itself confined the crash layer to persistent bundles (`log_ctx`, `fs_ready`) and to a handful of log/boot contracts, with the explicit design goal "not one call site moves" (LogInv :1416–1454). Lean inherits that. Contracts that change fall into four kinds: an *additive persistent conjunct* in a bundle, a *new premise*, a *new post*, or a *real re-proof*.

| layer | contract changes | proofs that must be re-opened | estimate |
|---|---|---|---|
| **MachCSL** | `MachFixedGS` fields (4), `EraGS.mirrorName`, a `powerInterp` conjunct, `powerBootRes` rows, `wp_power` hooks (`Hproj`/`Mof`/`Rb`/`Hswap`, the `Hobs` disk lend), a new WpDev drain-lend rule | `Power.lean` PowerOff arm (frame the disk auth) and PowerOn arm (swap, lend); `Wp.lean`/`WpDev.lean` sites that destructure `powerInterp` (append the conjunct LAST so positional patterns survive); new files PermInv, DiskPermit, DiskImg | **invasive but local**: ~1.5k new Lean lines + edits to 4 files |
| **virtio / bio** | rw: +permit, +`▷Q`; bwrite: same; bread: none (`None` permit internally); virtio_disk_init: allocates the channel | **DiskInvDefs** (slot row + `slot_perms_done`, D40), **DiskInv** device loop (drain arm steps the chain; completion consumes the leaf), **ProofVirtioDiskRw A–F** (deposit at enqueue, collect after wake; ~3.7k lines, mostly frames), ProofBwrite (pass-through), bread call site (trivial) | **re-proof, medium**. The frames grow by one persistent (`crashPermInv`) and one linear resource. The real steps are 3 lemma calls |
| **log** | write_head: +permit family; install_trans: +`□` generator, `▷R`; end_op: +seam +cert; initlog: +seam, cert, mirror_born, block 1, law premise, Rocq's `M`-form pures; sys_sync: +post. `logCtx`: +3 conjuncts (last); `logStateAt`: +3 rows; `logResAt`: +bank | **ProofEndOp + EndOpDefs** (real: 4 permits, mirror, law, bank), **ProofInitlog/InitlogHead/LogBoot** (real: recovery permits, genesis bank, park alloc), ProofWriteHead/ProofInstallTrans (pass-through), ProofLogWrite (SB_BNO arm), ProofBeginOp (`logResAt`/`logStateAt` opener patterns, mechanical), ProofSysSync (one call), **BallocBzero.lean:281** (`iintro ⟨-, -, H⟩` on `logCtx` must switch to the projection lemma) | **the biggest re-proof**: ~6k Lean lines re-opened, of which ProofEndOp is the hard one. Unfolders of `logResAt`/`logStateAt`: EndOpDefs, ProofEndOp, LogBoot, LogInv, ProofBeginOp, ProofLogWrite, ProofSysSync |
| **fs leaves** | none | none | **zero** |
| **inode / dir** | ireclaim: +seam +cert | ProofIreclaim (pass-through), `IreclaimDefs.ireclaim_end_op` (:327) call lemma | small |
| **file layer** | none (through `fsReady`) | call lemmas `FilewriteCalls.fwr_end_op` (:80), `FsCallSitesOp.endOp_callF`/`_callR` (:138/:216), consumer `FilecloseInode` (`endOp_callF`) | small, mechanical |
| **syscalls** | none (through `fsReady`) except sys_sync's post | call lemmas `SysfileCalls.sysfile_end_op` (:406; 14 consumer files, **untouched** because the lemma takes `sysfileEnv ⊇ fsReady`), `KexecTail.kxc_call_endop` (:708, `fsFabric ⊇ fsReady`) | **near zero**: only the call-lemma bodies project the two new rows |
| **process / boot** | FsReady +2 conjuncts; FirstTok (`firstBootPersist` +2, `firstFsinit` rows, `firstFsinitPures` `hdr_wf`, `firstDone` +`fsabs_env` (D37)); SpecFsinit (Rocq's full premise set, block 1 parked); SpecMain/BootShared/SystemAdequacy written with crash rows from the start | fsinit stages (FsinitCalls/Log/Tail + ProofFsinit: the law build, park); FirstTok's destructors; **every consumer of `firstTok`/`firstDone`** (8-P's files; forkret) | medium; must be **serialised with 8-P** (both edit FirstTok) |

**Conclusion.** Nothing above the log layer is re-proved beyond call-lemma bodies. The re-proofs are confined to:
- the disk driver (device loop plus rw);
- the log's commit and boot (end_op, initlog, fsinit);
- MachCSL's power thread.

The theory (~16k Rocq lines) is new files.

---

## 4. (d) Ordering and agent split

### 4.1 Relation to wave 8

The crash layer gates:
- **the final theorem** (8-5: SystemAdequacy, BootShared);
- **the statements** of `SpecMain` (W8-I), `FsCfgBoot` (W8-H) and MachCSL `Adequacy` (W8-G);
- the **sync arm** of the dispatch (D44).

It does **not** gate the syscall dispatch (other arms), usertrap, uservec/userret, the Uexec* slot layer, or ParkCap. Wave-8 changes:

| wave-8 item | change |
|---|---|
| rule 4 ("crash layer stays dropped") | **rescinded** |
| W8-G `MachCSL/Adequacy.lean` | state Rocq's `riscv_power_adequacy` (Pc/HPc/Hproj/Mof/Hswap/phi), **after C-M** |
| W8-H | **FsCfgBoot moves to C-0-D** (Rocq-literal, with `fs_boot_snap_wf`); FsBoot/DiskBoot stay in W8-H |
| W8-I `SpecMain` | written with the crash rows; waits for C-1's `log_mirror_born`/seam statements |
| 8-P (FirstTok, forkret park) | **C-4 runs after 8-P merges**, in its own worktree (both touch FirstTok). Alternatively, fold C-4's FirstTok rows into 8-P if it has not started |
| W8-S* arms | add the sync arm (D44), after C-2b |
| 8-5 BootShared/SystemAdequacy | after C-5 |

### 4.2 Dependency DAG

```
C-0 (new files, main tree, START after D35/D43)
  FsState ─► FsDurBytes ─► FsDurRead ─► FsDurXfer
  FsCrashPure (pure half of FsCrash) ; FsCfgBoot vocab ; FsBootParams
C-M (worktree, MachCSL) : fixed disk + crashPred + swap + mirror + permits + channel + drain rule + wp_power hooks
        │                                      │
C-1 (new files) FsDurSnap ─► FsDurAlloc ─► FsDurImg ;  FsCrash (resource half, needs C-M) ─► FsFlushedCore, LogSnapLaw ; AppDur
        │
C-2a (worktree) DiskInvDefs/DiskInv permit rows + device loop ; SpecVirtioDiskRw/Proof* ; bwrite ; bread call   (needs C-M)
C-2b (worktree, after C-2a + C-1) LogInv/LogDefs rows ; write_head ; install_trans ; log_write ; begin_op ; end_op ; initlog ; sys_sync
C-3 (new files, after C-1) FsCollect ─► FsCollectAll
C-4 (worktree, after C-2b + C-3 + 8-P) FsReady rows ; FirstTok rows ; SpecFsinit + fsinit stages ; ireclaim ; call lemmas
C-5 (with wave 8's 8-5) FsCfgSnap ; BootShared/SystemAdequacy crash wiring ; xv6_slot
```

### 4.3 Agents (disjoint files, bottom-up)

| batch | agent | files | where | needs |
|---|---|---|---|---|
| C-0 | **CA** | `Xv6/FsState.lean` (D43), `FsDurBytes.lean`, `FsDurRead.lean` | main | D35, D43 |
| C-0 | **CB** | `FsDurXfer.lean` (split per the few-seconds rule: `FsDurXferRuns`, `FsDurXferPool`, `FsDurXfer`) | main | CA's FsState |
| C-0 | **CC** | `FsCrashPure.lean` (FsCrash.v :1–1480: `fs_blocks`, `hdr_wf`, `fs_recovery*`, `log_mirror_ok`, `mirror_of`, sector algebra, WAL-step recovery lemmas; **pure, no MachCSL**), `FsBootParams.lean` | main | D35 |
| C-0 | **CD** | `FsCfgBoot.lean` (`fs_boot_image_wf`, `fs_boot_snap_wf`, `fs_boot_supply`; the `img_node*` readings) | main | D35; taken from W8-H |
| C-M | **CM** | MachCSL: `Resources.lean` (fields, `powerInterp`, `swapAuth`/`swapLb`, `crashInv`), new `DiskImg.lean`, `DiskPermit.lean` (`diskWritePermit`, `sperm`, `diskSeqPermit` + `_nil`/`_cons`/`_two`, `_trivial`), `CrashPermInv.lean` (PermInv), `WpDev.lean` drain-lend rule, `Power.lean` hooks. `EraGS.mirrorName` + `log_mirror` camera (one instance, rule 1) | **worktree** | D39, D40 |
| C-1 | **CE** | `FsDurSnap.lean` (split: `FsDurSnapBytes` = `snap_bytes`/`snap_ok`; `FsDurSnap` = epoch/clone/read/step) | main | CB |
| C-1 | **CF** | `FsDurAlloc.lean`, `FsDurImg.lean` | main | CE, CD; FsImg decoding (IcacheBoot* landed) |
| C-1 | **CG** | `FsCrash.lean` (resource half: `fs_rec`, history camera (Rocq `fsCrashG`: one mono-list instance in `Xv6G`), arm, `P_fs_at`, alloc/project/swap, seam, `fs_rec_permit`, bank, the four seq permits), `FsFlushedCore.lean`, `LogSnapLaw.lean`, `AppDur.lean` | main | CC, CE, **CM merged** |
| C-2a | **CH** | `DiskInvDefs`, `DiskInv`, `SpecVirtioDiskInit`/proof (channel alloc), `SpecVirtioDiskRw` + `ProofVirtioDiskRw*` + `VirtioDiskRwDefs*`, `SpecBwrite`/`ProofBwrite`, bread's call (`BreadScan`/`BreadTail`/`ProofBread`) | **worktree** | CM merged |
| C-2b | **CI** | `LogDefs`, `LogInv` (rows; bank), `SpecWriteHead`/`ProofWriteHead`, `SpecInstallTrans`/`ProofInstallTrans`/`LinkInstallTrans`, `SpecLogWrite`/`ProofLogWrite`, `ProofBeginOp`, `SpecEndOp`/`EndOpDefs`/`ProofEndOp`, `SpecInitlog`/`InitlogHead`/`ProofInitlog`/`LogBoot`, `SpecSysSync`/`ProofSysSync`, `BallocBzero` (pattern fix) | **worktree** (serial; one agent, or split end_op / initlog after the LogInv commit) | CH merged, CG |
| C-3 | **CJ** | `FsCollect.lean` (split by section), `FsCollectAll.lean` | main | CG; statements of ireg/bitmap/escrow/ipool/AppInv (landed) |
| C-4 | **CK** | `FsReady` (+seam/cert, projections), `FirstTok` (deviations 1, 2 and 8 reversed; producers `fs_extent_of_image`, `col_geom_of_config`), `SpecFsinit` + `FsinitCalls`/`FsinitLog`/`FsinitRead`/`FsinitTail`/`ProofFsinit`, `SpecIreclaim`/`IreclaimDefs`/`ProofIreclaim`, call lemmas (`FsCallSitesOp`, `SysfileCalls`, `FilewriteCalls`, `KexecTail`, `FilecloseInode`); deviation text in the 7 sys_* Specs | **worktree** | CI, CJ merged; **8-P merged** |
| C-5 | **CL** | `FsCfgSnap.lean` (split: vocab / `fs_cfg_alloc_snap`) | main | CK, CF |
| C-5 | (wave 8, 8-5) | `BootShared`, `SystemAdequacy` (`xv6_slot`, hooks) | — | CL, W8-G |

**Parallelism.** CA/CC/CD/CM start together, with CB after CA. CE/CF/CG follow. CH runs beside C-1 once CM merges. CI, CJ, then CK and CL. The two long poles are CM → CH → CI (the re-proofs) and CA → CB → CE → CJ (the theory).

---

## 5. Risks

1. **ProofEndOp.** Rocq's commit proof is 5,427 lines, against Lean's current 2,325. The four permit instantiations are value-chained through the mirror (`lm_upd` per sector). Plan it the way kexec was planned: one vocabulary file (`EndOpCrash.lean`: the permit instantiations at end_op's shapes), then phase stages, with no theorem over a few seconds.
2. **The drain-lend rule (D40).** Lean's `DevM` local steps are `LocalR`-relational, and the drain is inside the device body. The rule must lend `diskFixedAuth` and `startAuth (gen+1)` at a step whose effect is `v.disk := diskWrite …`, under the ambient `genCert`. Spike this first in CM, before CH depends on it.
3. **Timelessness.** `diskInv`'s body must stay timeless: it is opened inside MMIO AU accessors, exactly Rocq's reason for PermInv. The slot carries only the ghost-map token (`crashPermTok`), and the iProp lives in the channel's invariant. Collecting costs `▷` (`▷Q` in rw's post, `▷▷Q` at fupd level). Keep Rocq's two forms.
4. **Big literals.** FsDurImg reads the image decoder (`img_state`) and must never force the 2 MB literal: `Himg` is a premise (D34). Run CF under `timeout 300` (NOT `ulimit -v`: it makes Lean abort with "failed to create thread") (memory note lean-runaway-memory).
5. **`sperm` recursion.** Rocq uses explicit fuel (`size todo`) over `gset`. In Lean, use `Finset`/`List` fuel and prove `sperm_nil`/`sperm_cons` once. The ∧-over-branches shape (not ∗) is essential, because the mirror half travels down the chain.
6. **Positional patterns.** Append every new bundle conjunct LAST (`logCtx`, `logResAt`, `powerInterp`, `fsReady`, `firstBootPersist`), as Rocq did. Known breakage: `BallocBzero.lean:281`. Grep `unfold logCtx|logResAt|logStateAt|fsReady|powerInterp` per commit (current unfolders are listed in §3).
7. **Stale texts to fix as part of the wave:** SpecFsinit deviation 4 (D42); the `LogInv.lean`/`LogDefs.lean` headers; fs-rocq-summary §2b(E)/§5 ("no byte view"/"no superblock layer", both stale); fs-lean-design :836 and :1101 ("out of scope indefinitely"); wave8_top rule 4 and §5.1's "D11-trimmed" FsCfgBoot.
