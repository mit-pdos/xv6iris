# K6 — the fs-syscall contract re-spec (Rocq drift, union prerequisite)

Source: the K5 lane's audit (Sept 26 2026). Lean's create/open/mknod/mkdir/unlink/read/write
contracts were ported from Rocq before ~35 later Rocq re-spec commits (Sept 16–24). The
union cone's remaining K5 names are stated over the NEW contracts, so K6 ports those commits,
Rocq-literally (Rocq is the authority). K5's additive half (landed separately, branch
`k5-pre-bump` 8e96c3417) already holds the pure pieces: FsAbsCreateNm (minus bridges),
SysOpenPermit, SysOpenKept, FsAbsState/EraState, OffGv `offLink*`/`offRet*`, `nparCur*`,
`wchunkAt*`, ObsTrace `obsIns*`.

## The commits, oldest first (Rocq diff size; files are Lean counterparts)

1. `4fab0298e` open never installs a pipe end (+127/−11): `fdst_nopipe`/`fdv_nopipe*` (K2 already
   added `fdstNopipe`), no-pipe conjunct on SpecSysOpen's fd arm. FileDefs/FdTable, SpecSysOpen,
   UsysMemOk. **Bump conflict: high.**
2. `fec45648e` TL-3K parent cursor `Pd` (+775/−153): `Pd d` premise+return on
   `acre_commit_at_gen`/`acre_commit_at`/`uent_commit_at`; open_au_pre_create/open_au_create_at
   carry `npar_cur`; SpecCreate arms, mknod/unlink posts return it. FsAbs{Create,Mknod,Unlink,Inv}Fire,
   SysMknodDefs, SysOpenDefs, SysUnlinkDefs, Spec{Create,SysMkdir,SysMknod,SysOpen,SysUnlink};
   proofs Create{Alloc,Found,Mkdir,SharedBody,Defs}, ProofSysMknod, SysMknodTails,
   SysOpen{CreArm,EntryC,Parts}, ProofSysMkdir, SysUnlinkW1/W2/W3/W5D/W5F/Shared, SysLinkDefs.
   Needed by every FsAbsCreateNm bridge.
3. `84090c137` TL-3C(D) dot-name credential (+39/−19): FsAbsCreateFire, FsAbsMknodFire,
   CreateAlloc, CreateMkdir, ProofSysMknod.
4. `3e3a157ae` mkdir + `88cc6612c` unlink path-fixed bundles (+214/−53, +233/−84): also
   ProofSyscall, SyscallArmsPath, UexecExecInst. **Bump conflict: high.**
5. `abae4c71e` F-OPEN-2 keyed truncate — done by K5 (SysOpenPermit).
6. `52b0eb67b` READ-RELAY (+579/−110): read's −1 arm carries copyout's reason. FsAbsReadFire,
   SysReadDefs, Spec/ProofReadi, Spec/ProofFileread, FilereadInode(Arm). Needed by
   `read_arms_mapped`.
7. `39cb7fced` F-OPEN-3 (+1196/−312): `open_trunc_piece` gains `Kt`; `fsabs_trunc_piece`
   changes. SysOpenDefs, SpecSysOpen, FsAbsInvFire, FsAbsOpenFire,
   SysOpen{CreArm,EntryC,Join,Shared,Stores,Walk,Alloc}, ProofSysOpen. Needed by
   `cre_fail_kept`, keyed-piece lemmas.
8. `40de8468f` F-OPEN-6 (+385/−224): 0x601 fd arm becomes one arm. SysOpenDefs, SpecSysOpen,
   SysOpenCreArm, SysOpenEntryC.
9. OFF-LINK / WRITE-RELAY chain: `f5100b989` RELAY 3, `5c48aa727` SKELETON (`off_ret` returned
   by the commits), `340152449` RELAY 4 (partly in Lean), `bb7d140b3`+`e274708f7` (UserOff
   `off_link`/`off_settle`), `4919630d6` (commits lent `off_link`; FileOffCell taint arm),
   `8e4ffb667`+`237b50d21` OFF-LINK-4, `53860d4ab`+`fc69d2631`+`4f9be67fd` OFF-LINK-5 (`*_adv`,
   `aread_in_om`). OffGv, FileOffCell, UserOff, FsAbsReadFire, FsAbsWriteFire, Spec/Proof
   Fileread/Filewrite, FilewriteChain/Fire, FileOffProto, SysOpenParts, SpecCopyin
   (`ubytes_at_inj`). `378b23778` (parked discipline removed) also UsysMemOk, KexecImageOk,
   SpecKexec, ProofKfork — **bump conflict: high.**
10. `94a649b1a` L2 (+263/−196): `fdstate_ok` keyed on offset mode. FileDefs, Spec/ProofFileclose,
    Proof{Fileread,Filewrite,Filestat,Pipealloc}, SysOpenParts, SysOpenPub.
11. `abe94870d` L4 open publishes at caller's mode (+438/−283): `foff_pub`. SpecSysOpen,
    UserOff, UsysMemOk, UexecExecInst, ProofSyscall, SyscallArmsPath, all SysOpen* stages.
    **Bump conflict: high.**
12. `566f4b75d`+`8c510da3b` FsAbsCreateNm (done by K5 minus bridges); `96f841c7d`+`1a1b4633d`
    thread `Nm`/`Nd` into mknod/create/mkdir/open AUs and proofs.
13. `0478e04bc` WR-TB (+217/−85): `wr_tb`. Also ProofSyscall, SyscallArmsFd, UexecExecInst.
    **Bump conflict: high.**
14. `48f7343d9`+`aae081f4c` EFQ: redefine `awrite_*_adv`.
15. `8438e5583` NM-OPEN (~150 kernel lines): create leg becomes
    `acre_commit_at_nm … (npar_nm) (npar_cur)`.
16. `f23a85c44` TRUNC-PERMIT (+719/−363): plain surface keyed by terminal cursor,
    `plain_trunc_key`. SysOpenDefs, SpecSysOpen, ProofSysOpen, SysOpen*.

Deferred K5 names that land with K6: FsAbsCreateNm's four bridges to `acreCommitAtGen` (2);
`plain_trunc_key`, `cre_fail_kept*`, `open_trunc_piece_*`, `open_trunc_at_of_permit(_at)` (7, 16);
`aread_commit_adv`, `aread_in_om`, `awrite_*_adv`, `read_arms_mapped` (6, 9, 14). `elend_agrees`/
`elend_reads` stay deferred under D15. FsImgCheck `fname_*` waits for the bump (K5 remainder).

## Lane split (after the 7b2c1b1b bump lands)

None of these touch fs.img. High-conflict commits (1, 4, 9's 378b23778, 11, 13) hit ProofSyscall,
SyscallArms*, UexecExec*, UsysMemOk, SpecKexec, Kfork — they go after the bump.

- **K6-A create/unlink cursor:** 2, 3, 4, 12, 15 (+ the FsAbsCreateNm bridges).
- **K6-B open truncate:** 1, 7, 8, 16 (then 11 after K6-C's 10).
- **K6-C offset link / read-write relay:** 6, 9, 10, 13, 14, then 11.

A and B both edit SpecSysOpen/SysOpen* stages; C edits file layer + SysOpenParts/Pub. Run A and C
in parallel, then B (or B after A lands). Each is a worktree lane; full build on the VM per commit.
