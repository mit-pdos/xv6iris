# Union wave U0 — residuals handed to later lanes

Collected from the U0 agent reports (Sept 26 2026). Each item names the lane that owns it.

## U1-T (image pins)
- `EchoFsPure`, `FileFsPure` (U0-2) wait on `FsInitPinBoot`, `FsShPin`, `FsEchoPin`, `FsCatPin`,
  `FsGrepPin`, `FsSeccPin`.
- Rest of `Xv6/FileName.lean` (existing file → worktree lane): `sys_names`, `name_laws`,
  `txt_laws`, `txt_sys_ok`, `txt_img_ok`, `nl_ne_sys`, `nl_ne_console`, three `era0_*` lemmas.
  Needs `fname_*` pins (missing from `FsImgCheck`), `fname_console`, `TreeImg.img_root_ents`,
  `FsInitPin`.
- `UNamePath.cat_words_head` needs `fname_cat` (then `rfl`).
- When porting `UserConsole`: reuse the kernel's `consSwallow` / `consStoredLb` (as `ReadRec`
  does) instead of redefining Rocq's `ucons_*` duplicates.

## MachCSL/ObsTrace
- `obs_ins` missing (U0-1 defined `consIns` directly by recursion); `open_seg_prefix_of_boots`
  missing (copy lives at `EchoOutPure.openSeg_prefix_boots`). Fold back when convenient.

## U4 (seal)
- `EchoOutG` (new camera class, one field: era map `GhostMapG GF Nat EraPins RegMapF`) needs a
  slot in `xv6GF` / `unionGF`.

## U0-5 (union model) — CLOSED
- Anti-vacuity demos done in `Xv6/UnionDemo.lean` (`demo_disc : lmDisc ulmG hist`, thread demo,
  admission demos) via the round-trip `ulineOfU_body`. Those general lemmas (`ulineOfU_body`,
  `parseLine_pipe_none`, `plParse_pipe_body`) live in UnionDemo; move to UnionDisc if a lane
  needs them.

## K3 (seccomp) — DONE (branch k3-secc: S0, S2k–S2k3, exec mask pin, whole-table view)
- `LinkRec.lkWildNone` is deliberately distinct from K3's `wildNone`; K3 changes no U0-C statement.
- Landed: `MachFixedGS.wild`/`rdwild` slots + `wildNone` (MachCSL); `AppIface.wild`/`wild_lic`/`rdwild`,
  `wildNone_lic`, `consLicenceAt_of_wild` (takes the wild/consRes slot equations: Rocq reads
  riscvF_app_iface); `ConsLog.wildEv`; `UartLinks.consLicenceAt` (+`_of_licence`),
  `outLink_of_licenceAt`, `consReadPay_trivAt`; `AppInv.appRdcred` (+`_of_sup`/`_of_rdwild`/`_elim`)
  at the console escrow; `AppLaws.al_programs`/`al_echo` take `wild`/`rdwild` slot equations.
- S2k: `ConsNames.era`, `consEra`, `consPlaced`, `consSwallowPlaced`, `consoleCaps`/`consoleReadyApp`
  carry `era = genId + 1` (`consoleReadyApp_era`); consoleread/fileread marked arms relayed at
  `genId + 1`. DEVIATION: `consResCur` got only relax-d2's `nrd ≤ cur` (Rocq's `cons_dlcnt`/`ndl ≤ nrd`
  still unported, pre-existing).
- S5b (`ep_rpos`): nothing kernel-side; EchoOut/LinkRec/GenLinksLine/ReadRec already at the pin (U0-C).
- Exec mask pin: `execSlotPre`/`execAuPre … cw secc …`, `initBootBundle cw secc sts`,
  `EraInitBoot` at `ROOTINO seccAll fdt0`, `parkMode`/`parkPkg` carry `secc`.
- Whole-table view: UserFd camera is `GhostMapG GF (Option Nat) UfdCell UfdMapF` (FileG slot 64);
  `ustdAt`, `tabLe`, `ushViewOk`, `ustdOk`, `uallocV`; `uslot_of_urun_all_at`/`_ro_at`,
  `UkFork.wp_uk_ecall_fork_at`, `UConsOpen.ukOpenFdArmAt`/`initCons_fail_std_at`.
- Left for U1-T: UConsOpen `init_cons_any_std(_at)`; UInitFd `ufd_alloc0_v`, `ufd_headL*`,
  `ufd_head1*`, `ufd_head*`, `ufd_row`, `ufd_head_open_row`, `ufd_head_of_row` (no non-`_at` forms yet);
  ExecEntry/ExecBundle's `image_entry_taint` two key pins (Rocq 3e7fee0d2, union-side).
- Left for U1-R/K4: UkRun `udepwf_std*`. For U1-P: `UexecSecc.ush_view_secc_rows`.
- For P-secc / P-init: `UkFork.wp_uk_ecall_fork_at` is now Rocq's view-keeping leaf (`ustdAt l v`);
  the plain-ledger statement is `wp_uk_ecall_fork`, which InitMainFork / ProofSeccMain now call.
  Retire UkSeccDefs deviation 5 (`seccTabFork`) and the `Obl` mask parameter onto the `_at` leaf and
  `uvis_secc` (`UkSeccLit.secc_mask_masked`).

## UkShPipes* / UShUPipes wave (after DU8 repoint)
- `Xv6/PipesCut.lean` (U0-3) is partial: 15/37 reached decls. The other 22 are statements about
  the shell's lexer/parser (`UkSh.ush_line_at`, `UkShPipesLex`/`UkShPipesCmd`/`UkShParseCmd`/
  `UkShMain`/`UkShEcho`, `UmodeAbi.ubyte0`); only consumer is UShUPipes.
- U0-2 owner note: FileDiscLine's trim dropped `all_cats`, but it is reached via `adm_echo`;
  U0-3 defines `allCats` in PipesDisc.

## K4 (PQ-b, after the bump) — absorbs the rest of PQ-a
- K2 landed only PQ-a steps 1–2 (PipeNames/PipeQueue/PipeReg defs, `Xv6G.pipeqG` slot 94,
  `FdType.pipe γp`, `fdstateOk … γp`, `Xv6/PipeQstep.lean` ghost steps). The re-proofs of
  pipealloc/pipewrite/piperead/pipeclose/sys_pipe and the fileread/filewrite pipe arms are
  BLOCKED on PQ-b: `pipeQres` must enter `pipeResAt`, and then pipeclose's flag store needs
  `pipe_cpay`, which only fileclose_cpay → sys_close/kexit deposits → syscall close arm /
  usertrap exit+kill / UexecExecInst rows 2, 21 can pay. The kill path needs Rocq's KILL-TAINT
  kill row (Lean `killRow` has no taint). So K4 = rest of PQ-a + PQ-b in one worktree lane.
- Interim deviations to retire in K4: PipeInvDefs (queue not in payload), SpecPipealloc dev 4
  (no `pipe_qfrag … pst0` handed out), SpecSysPipe, PipeReg dev 1; PipeReg §4 (fileclose_cpay).
- Name watch: K2 added `fdstNopipe` in FileDefs (Rocq FdSlots name) — U1-R / U0-6 must reuse it.

## U1-T (post-bump remainder; pre-bump part landed: UImgWordDefs, UStrImg, UserConsole, UInitFd partial, PinnedObs, UConsOpen partial)
- TreeView/TreeObs/AppTree: 0 reached decls — nothing to port. UConsLine's alias = `UkShLineDefs.ushLineIs`.
- fs.img literal (after bump): TreeImg (`img_root_blk/ents/nrec_leb/blk_agree/ents_eq`), PinnedExec, PinnedOpen, all Fs*Pin.
- Seccomp key (`uvis_secc`, bump ckpt 1 / K3): ExecEntry (`image_entry_at`, `image_entry`, `_taint`,
  `_taint_intro`, `_taint_all_elim`, `_of_at`, `_at_of`); ExecBundle (`ex_node_id`,
  `exec_slot_of_entry_at`, `sys_exec_slot_of_entry`, `exec_bundle_of(_at)`).
- K3 UserFd whole-table view (edits `UserFd.ustd`): UInitFd `ufd_alloc0_v`, `ufd_headL*`, `ufd_head1*`,
  `ufd_head*`, `ufd_row`, `ufd_head_open_row`, `ufd_head_of_row`; UConsOpen `uk_open_fd_arm_at`,
  `init_cons_fail_std_at`, `init_cons_any_std_at`.
- UConsOpen waiting on UInitCons (I-init) + FsConsPin: `init_cons_elems_len/_hd`, `cons_hop_dead`,
  `cons_walk_dead`, `cons_open_bundle_dead`, `cons_open_dead_recv`, `init_cons_absent_fam`,
  `cons_sup_absent`, `init_cons_console_fam`, `cons_sup_console`; on Xfam after K4 + `utext_img`:
  `xfam_open`, `sbundle_at_open_intro_at`, `spost_at_open_elim_at`, `cons_ro_sub`; on `wp_triv`: `fupd_wp_triv`.
- `pobs_elend_aents` proved directly; repoint at K5's `FsAbsEraState.elend_aents` when convenient.

## U1-R (post-K3/K4 remainder; pre-bump part: UkRunLeaf/Mem/Br, UkCode, UkStub, echo walk, UkFork, UkRunExecRef, UEchoKernel)
- UkRunSys, UkRunSecc (K3's secc key/rows are in; still need K4 close/exit deposits).
- Restore `wp_uk_sb_denied`'s self-minted exit deposit (Rocq `udep_exit_run`; now from `UprogSG.psok USYS_exit`).
- UkFork / UkRunExecRef: pipe rows (`urun_rows`/`urun_nopipe`, K4). (`ustd_at`: done in K3; the seccAll
  pins are Rocq-faithful -- Rocq's run keys are at secc_all -- so no mask change is owed.)
- Syscall-number premise is on the register file (`extractLsb' 0 32 (m 17#5)).toInt = USYS_…`); switch to
  UkRunSys's `usysno`.
- UkFork kill price is `□ (uKillCred -∗ Q (-1))` vs Rocq `app_taint` (process-layer deviation; K4's KILL-TAINT).
- `stubRet` lives in UkStub (Rocq: UkTree) — H-tree's UkTree must reuse it.
- Axiom baseline note for U4: echo walks show `MachCSL.nthByte_lo0/lo1._native.bv_decide` via UserHeap.uinstrIs_ukInstr.

## P-printf run interface — CLOSED by the printf bridge (UlibRunUk/UlibUkProg; cat/init/secc `*_linked_ulib`, grep `wp_grep*_ulib`; hart rides in a ghost var). Remaining: grep's `kgrepPaySeq` → `ulibUkPaySeq_of`; stale 'pending' notes in UkCatDefs/UkInitDefs/UkSeccDefs/Link* headers.
## (old text)
- `UlibRunP` (the printf lane's stand-in run interface) has one fixed `goal`, but the real leaves
  re-quantify the hart (`∀ h', … wpLoop h'`), and `UlibRunP.ofUkRun` doesn't exist. Until fixed, cat
  takes `HF : CAT_FPRINTF` (Rocq's `wp_kcat_fprintf(_s)` verbatim over `urun`) as a parameter and has its
  own `kcatPaySeq`. Fix: make UlibRunP carry the hart (or build it from `urun`/UK_LEAVES), then discharge
  `CAT_FPRINTF` from `ulibFprintf_link`; same for grep/init/seccomp.
- UkCatTree's Iris half (23 decls, `cat_prog` … `wp_kcat_start_env`) waits for H-tree (UkTree/UkHandler).

## U1-T post-bump — remaining
- PinnedOpen: DONE by K6-B (Xv6/PinnedOpen.lean: the 7 reached + `pinned_open_bundle_dead_lin`; the 3 over PinnedObs' unported spending dead walk stay out).
- ExecEntry, ExecBundle, PinnedExec's `pobs_node_id` / `pinned_exec_bundle_boot(_at)`: need K3's seccomp key.
- FileName.lean / UNamePath.lean still say PENDING for items now in FileNamePins / UNamePathCat — update their
  headers when convenient.

## Exec entries (lane U1-T-exec, landed) — follow-ups
- P-init analogue of the P-secc follow-up: move init's walks off the pre-K3 heads in UkInitDefs
  (`kinitHeadL` & co.) onto UInitFdHead's `ufdHead*` at the table view.
- `urun_rows` lend (K4) in `udepwAtRefR` / the exec supply: one extra persistent premise when K4 lands.
- Seccomp's printing arms still on the plain ledger `ustd` (UkSeccDefs dev 4) until the write leaf is ported.
- Stale headers to point at the new files: ExecRun "DEFERRED", UInitFd/UConsOpen "not ported yet",
  UkSeccLit "pending K3". The rest of `UexecSecc` must import UexecSeccMasked (seccB/seccMasked).

## sh-exec (landed) — follow-ups
- `UshExecEnv` (Xv6/UshExecDefs) is a parameter record to instantiate when sh-run (ushcmd/ush_cmd/jtab/
  cmd_addr/cmd_exec/wp_kshr_entry) and sh-main (ush_Dg, fd1p/fd2p, execfail law/bytes/paid) land; the
  seam field `ush_cmd_of_ref` from UkShSeam's Iris half.
- `ushf_child_law_holds_at_D` owed once sh-run's UkShFork exists (glue over `shChildEcho_holds`).
- PipesCut: 6 left (`pipes_lpg`, `pipes_lpcg`, `pipes_lpg0`, `pipes_lpcg_bytes`, `pipes_lpg_of_at`,
  `pipes_lpcg_of_at`) — portable now (ushLineAt landed); PipesCutSh header's "STILL LEFT (13)" is stale.
