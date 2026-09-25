> **DECISIONS (user + coordinator, Sept 24 2026):** D1–D6, D9–D13 approved as recommended (D6 default:
> leave the two off-box classes). **D7: Rocq-literal process block, one record edit (A3).** **D5b:
> port Rocq's console ghost into consoleread FIRST, then a Rocq-literal fileread.** **D8: PORT the
> fork/exit generation machinery in wave 7** (user: "we'll have to port it eventually; do whatever is
> more efficient" — kfork/kexit/kwait/kkill are re-proved in this wave anyway by A3/C, so port it with
> them rather than re-proving twice).

> **COORDINATOR DECISIONS PENDING.** §8 lists them (D1–D13). W7-A (§7.2) needs D1–D4 and D7 answered.
> W7-D needs D5b and D10. Wave 7b needs D9. D7 and D8 are process-layer changes, so they also go to
> the user (rule 3).

# Brief: wave 7: the FILE LAYER and the fs reconnect

Read these first; their rules apply unchanged:
- notes/briefs/fs0_common.md
- notes/briefs/fs1_leaves.md (§1 templates and vocabulary, §7 report)
- notes/briefs/fs2_bmap_ialloc_itrunc.md (§0 standing rules, the layering rules)

The project rules are unchanged:
- Build only your own modules (`timeout 1800 lake build Xv6.<Module>`). Never run a bare `lake build`.
- No `sorry`. No git unless the coordinator says so. `tools/check_layering.sh` must stay green.
- One kernel function per file triple (`Spec<Fn>`, `Proof<Fn>`, `Link<Fn>`), with stage files that
  have no `Proof` prefix. A stage file belongs to ONE function.
- No theorem may take more than a few seconds. Use `set_option maxHeartbeats N in` on single theorems only.
- Name every helper after its function (`fclose_…`, `fread_…`, `sysopen_…`).

Wave 7 has one difference from waves 1–6: **most of its work edits LANDED files**, including the
process layer, the file table, and pipe/sys_pipe/sys_close/kfork/kexit. §6 gives the blast radius
and §7 the batching. Agents that edit landed files run in `isolation: "worktree"`. Agents that only
add new files run in the main tree.

## 0. Standing rules (the user's words, verbatim; they bind every agent in this wave)

- "for process abstractions in particular, look at how Rocq specs are set up; don't reinvent the
  wheel."
- "the file system is a tricky piece of spec/proof. It's important to consult the Rocq version
  whenever you might be possibly in doubt…"
- "some cleanup is helpful … but the big ideas should be taken from there."
- "it's not a good idea to simplify without having the full picture or plan…"

**Design rules from this session.** These are binding. An agent may not relax any of them on its own.

1. **ONE capacity instance per camera type** (commit 3bceb3216).
   - Never add a ghost field to a per-subsystem class when a same-typed camera already exists.
   - A new camera type goes in `Xv6G` (Xv6/UartTrace.lean:27) or in the one class that owns that
     type, never in two places.
   - Wave 7's new camera types are the CInv camera (`CInvG`, for `inode_pay`'s cancellable invariant,
     §2.2) and possibly `FPNames` growing fields (not a new camera).
   - Check `Xv6G` and every `*G` class for an existing instance before declaring one.
2. **Every new contract is interrupt-generic, as Rocq's are.**
   - That means `eb`-generic: `trapCsrsExt cpu k.sie` / `cpuClaimExt cpu k.sie k.proc` in and out,
     depth 0 where Rocq has `cpu_own 0 eb`, and a crossing of the literal `wpNext true` for anything
     that can park. The structure field is named `wp_X_eb`.
   - A pinned `sie = false` instance is DERIVED, not stated (`FsEntryEb.pinned` is the template,
     Xv6/FsEnv.lean).
   - Several Rocq sysfile contracts pin `eb = true` instead (§5.0). D5 decides what to do with them.
3. **Flag every process-layer deviation from Rocq to the coordinator.** That means every change to
   `ProcPriv`, `procPriv*`, `procDormant`, `fdFrags`, KFORK/KEXIT/USERINIT/KKILL/PREPARE_RETURN, and
   `ForkretIs`. Do not invent a process abstraction. Copy Rocq's `ProcInv.v` / `ProcDefs.v` shape.
4. **The sanctioned block form is `procPrivExt`** (Xv6/EitherDefs.lean:87).
   - It is `procPrivRun` with the address-space descriptor `P'` named. `procPrivExt_eq_run` is `rfl`.
   - COPYIN/COPYOUT return `P.extSz psz P'` (Rocq `uptd_ext_sz`), so the block comes back whole.
   - Every conjunct wave 7 adds to the block (cwd reference, fd table) must be threaded through
     `procPrivExt` and `ecRest` (EitherDefs.lean:399–432) in the SAME change, so that the 14 files
     using it keep one form.

## 1. Where wave 7 starts from (verified against the tree, Sept 24 2026)

**fs.c status.**
- Landed through wave 5: every fs.c function except `namex`, `namei`, `nameiparent` and
  `fsinit`.
- `dirlink` LANDED during this survey (8c4756aa8: eb-generic from the start, `wp_dirlink_gen_eb`,
  SpecDirlink.lean:68).
- IN PROGRESS (untracked): `namex`: `Xv6/SpecNamex.lean` plus `Namex{Calls,Defs,Elem,Exit,Frame,
  Level,Look,Loop,Parts,Scan,Start,Tail}.lean`.
- `namei` (+`namei_root`, `namei_root_boot`), `nameiparent` and `fsinit` (wave 6) have NO Lean files
  yet. All their callees are landed or in progress.
- Wave 7's sysfile half (§5) needs all of them. Its file-layer half (§2–§4) needs none of them.

**The fs contracts wave 7 consumes are landed and eb-generic** (sweeps 1–11, commits
fc8ea6e9d…9762b1654):
- `BEGIN_OP.wp_begin_op_eb`, `END_OP.wp_end_op_eb`
- `IPUT.wp_iput_gen_eb` (SpecIput.lean:415)
- `ILOCK`, `IUNLOCK`, `IUNLOCKPUT`, `READI`, `WRITEI`, `DIRLOOKUP`, `IALLOC`, `ITRUNC`, `IUPDATE`,
  `STATI`, `IDUP`
- Their callers pass the pid cell (`wordPointsTo (pPid k.proc) 4 dqp pidv`) where Rocq passes
  `proc_priv_bare`. That is the Lean fs layer's recorded convention, and wave 7 keeps it.

**The ASSUMED boundary to retire: `Xv6/FsEnv.lean` (153 lines).**
- It declares `class FsEnv` with the fields:
  - `fileclose`, `begin_op`, `end_op`, `iput`, `namei` as `FsEntryEb`;
  - `filedup`, `idup`, `nameiBoot` as `FsEntryNB`;
  - `fsSlots = 64`.
- These are sleep-shaped or balanced "some word back" contracts that carry NO fs resources.
- Users (19 files):
  - Xv6.lean, FsEnv
  - SpecFileclose, SpecFiledup, SpecIdup, SpecIput (the last three for the address defs only)
  - SpecKfork, ProofKfork, LinkKfork
  - SpecKexit, ProofKexit
  - SpecSysFork, ProofSysFork, SpecSysExit, ProofSysExit
  - SpecUserinit, ProofUserinit, LinkUserinit
  - SpecForkret
- Call sites:
  - ProofKexit.lean:291 (`kx_loop`, fileclose), 627/654/667 (begin_op, iput, end_op), 1182
  - ProofKfork.lean:1609 (idup), 2815 (filedup)
  - ProofUserinit (nameiBoot)

**Rocq has no such abstraction.**
- `LinkKfork.v`: `Module Kfork := KforkProof Myproc AllocprocGen Uvmcopy Freeproc Release Acquire
  Filedup Idup Safestrcpy.`
- `LinkKexit.v`: `Module Kexit := KexitProof Myproc Fileclose BeginOp Iput EndOp Acquire Reparent
  Wakeup Release Sched Panic.`
- `LinkUserinit.v`: `Module Userinit := UserinitProof Allocproc NameiRootBoot Release
  ForkretParkPaid.`
- `LinkForkret.v`: `Module Forkret := ForkretProof Myproc Release PrepareReturn Fsinit Kexec Panic
  UserretClosedD.`
- **So the retirement is: the real `FILEDUP`/`IDUP`/`FILECLOSE`/`BEGIN_OP`/`IPUT`/`END_OP`/
  `NAMEI_ROOT_BOOT` become functor ARGUMENTS of `kfork_proof`/`kexit_proof`/`userinit_proof`, and
  their Specs gain the resources those callees need** (§3). After that, `FsEnv.lean` is deleted.
  `SpecForkret`'s use goes with the forkret port (§5), or stays as its one remaining assumption.

## 2. The file table: re-port `FileInvDefs` Rocq-literally

### 2.1 What Lean has vs Rocq

Rocq files:

| file | lines |
|---|---|
| FileInvDefs.v | 2008 |
| FileInv.v | 827 |
| FileOffCell.v | 128 |
| FileOffProtocol.v | 319 |
| OffBox.v | 581 |
| FdSlots.v | 1048 |
| FdPark.v | 537 |
| InodeRef.v | 41 |

Lean files:

| file | lines |
|---|---|
| FileDefs | 317 |
| FileInv | 380 |
| FileFrac | 565 |
| FileGeom | 41 |
| FileOffCell | 121 |
| OffBox | 783 |
| OffBoxCam | 91 |
| OffGv | 172 |
| FdTable | 488 |
| InodeRef | 50 |
| FtableLock | — |

`FileOffCell`, `OffBox`, `OffBoxCam`, `OffGv` and `InodeRef` are faithful and landed. `IcacheBox`
already carries the per-inode `offRows`.

| Rocq (FileInvDefs.v line) | Lean today | wave 7 |
|---|---|---|
| `file_fields` 900: SIX cells, no `off` | `fileFieldsAt` (FileDefs:~165): six cells **plus `∃ off, aFoff k ↦{q} off` at every fraction** | drop the 7th conjunct. `off` moves to `file_core_off` |
| `file_core_noff` 1445: pipe arm `is_pipe ∗ pipe_ref ∗ **iref_frac q**`; INODE/DEVICE arm **`inode_pay …`**; else **`iref_frac q`** | `fileCore`: pipe arm without `irefFrac`; every other arm `emp` | Rocq-literal. `irefFrac` exists (IrefSlots.lean:202) |
| `file_core_off` 1572: FD_INODE → `off_fd k q (fp_obox pn) (fp_ooff pn) C`; else `off_free k q` | none | new. `off_fd`/`off_fd_at` (1516/1527) over Lean OffBox's `offBox`/`offMember`/`offRegd`/`offCnt`/`offRefStamps`; `off_free` over `byteMapped` ×4 (OffBox deviation 2) |
| `file_core` 1577 = noff ∗ off | `fileCore` | rename-compatible |
| `inode_core` 863 (cinv body), `inode_ref_side` 1156, **`inode_pay`** 1166, `_split` 1192, **`_cancel`** 1208, **`_alloc`** 1281, `_not_dev` 1322 | none | new (§2.2) |
| `fpnames` 269: `fp_lock fp_pipe fp_icv fp_iq fp_ig fp_inum fp_obox fp_ooff` | `FPNames`: `lock pipe inum ooff` | add `icv : GName`, `iq : Qp`, `ig : GName`, `obox : BoxNames` |
| `fdstate_ok` 540 (FdInode `n g om`, **`OffParked` pin**) | `fdstateOk` (FdInode `n g`, no offmode) | see D4: add `offmode`, or record its absence |
| `fref_tok` / `ftable_auth` (frac×positive auth) | half-element ghost map (`frefTok`, `fslotAt` with lists `L`) | KEEP Lean's algebra (landed, proven; same laws). Record it |
| `flive_tok` in `file_ref`, `fliveUR`, `flive_*` steps | absent | DROP, and record it (§2.3) |
| `file_rest` / `fslot` 1817/1845 | `fileRestAt` / `fslotAt` | follow the payload change only |
| `file_off_reclaim` (FileInv.v:326), `file_close_last_step`, `file_rest_join/_absorb` | in FileFrac / ProofFileclose | add `file_off_reclaim` over `offLastClose` (OffBox.lean:750) |
| FileOffProtocol.v `proto_*` (skeleton chain) | none | port ONLY the steps a proof calls (`proto_publish` for sys_open, `proto_read_checkout/park` for fileread/filewrite); the rest is Rocq's day-one type-check gunk |

### 2.2 The inode arm (`inode_pay`). Port it exactly; it is the design.

A share of an inode reference cannot be the reference, because two `inode_held` compose to a
count of 2. So:
- the reference, SHORT by `fp_iq`, goes into a **cancellable invariant** (`cinv fileipN γx
  (inode_core v Q inum)`);
- the fraction is the cancel token;
- a proportional `inode_ref_side v (q*Q)` and `inode_shr_held_gen v (q*Q) g inum` travel with every
  share;
- a persistent type witness `∃ ty, ity_shot g ty ∗ ⌜wr → ty ≠ T_DIR⌝ ∗ ⌜fdty = FD_INODE → ty ≠
  T_DEVICE⌝` travels too.

`inode_pay_cancel` (the last closer, `q = 1`) returns a WHOLE `inodeHeld v` for iput through
`inode_ref_gather_genlo`. `inode_pay_alloc` is sys_open's publish.

Lean prerequisites:

| Rocq name | Lean status |
|---|---|
| `inodeHeld`, `inodeShrHeldGen` | IcacheHeld.lean:121/238 |
| `inodeRefShortGenlo`, `icLentStamps`, `inodeIdent`, `liveGenlo` | IcacheRef.lean |
| `irefFrag` | IcacheInvAlg / IcacheRefGhost |
| `runitAny` | IcacheRefLink |
| `ityShot` | IcacheRefDefs |
| `slhTok` | SleepLockDefs |
| `inode_ref_gather_genlo` | **grep before writing it**. IcacheHeld's header says the gather goes through it; its Lean name may be `inodeRef_gather`/`…_genlo` in IcacheRef.lean |
| `ity_shot_agree` | same: grep for it |
| `live_genlo_agree`, `ientry_inj` | present |
| **cancellable invariants** | iris-lean HAS them (`.lake/packages/iris/Iris/Iris/Instances/Lib/CInvariants.lean`, `class CInvG`, `cinv`, cancel/alloc). **Nothing in Xv6/ or MachCSL/ uses them yet.** D2: the `CInvG` instance goes in `Xv6G` (one bundle, rule 1), not in `FileG` |

The Lean pipe layer does not use cinv. Its `isPipe` has a hand-rolled dead arm. Do not re-port
pipes onto cinv; that would be an unrequested change.

### 2.3 Cleanups proposed (the coordinator approves or rejects them, D3)

1. **Drop `flive`.** Rocq's own FileInvDefs.v note says the counter exists to refute a stale off
   checkout at the last close, and the OffBox design refutes that with the box's Σ-mass instead (Lean
   OffBox.lean:~740, "a stale reader would hold mass > 0 beside it: refuted by Σ").
   - Uses checked: `flive_tok` in FileInvDefs/FileInv/FileOffProtocol, where it is only threaded
     through ProofFileread.v (1 use, stale comment about the old off ledger), ProofSysOpenPub/Parts/
     Stores (5+2).
   - `flive_excl_last` / `flive_close_last` have no users outside FileInv.v.
   - Lean never had flive. Record this in FileDefs's header.
2. **Keep Lean's reference algebra** (half ghost-map elements + per-slot lists `L`, `qsum`) in place
   of Rocq's `authUR (gmapUR nat (frac × positive))`.
   - It is landed and proven, and provides the same three laws (only-holder-has-everything via
     `qsum L = 1`, dup, close).
   - Re-porting it would touch FileFrac/FileInv/ProofFile{alloc,dup,close}/ProofPipealloc for no
     gain. Record it as a deviation.
3. **Do NOT port FileOffProtocol.v's `proto_*` chain** as a file. It is Rocq's "rule-0" day-one
   skeleton. Port each step as a lemma only where a proof calls it. Uses to check: ProofSysOpen*,
   ProofFileread, ProofFilewrite, ProofKfork (`proto_fork_child_read`).

### 2.4 Where each piece goes

- **`Xv6/FileDefs.lean` (edit, worktree):**
  - `FPNames` grows;
  - `fileFieldsAt` loses `off`;
  - `fileCoreNoff`/`fileCoreOff`/`fileCore` Rocq-literal;
  - `inodeCore`, `inodeRefSide`, `inodePay`, `offFd`, `offFdAt`, `offFree`.
  - Imports grow: `Xv6.OffBox`, `Xv6.IcacheHeld`, `Xv6.IrefSlots`, `Iris.Instances.Lib.CInvariants`.
  - The `FileGeom` split already prevents the cycle: OffBox → FileOffCell → FileGeom.
  - `FileG` loses nothing. The `CInvG` capacity goes to `Xv6G` (D2).
- **`Xv6/FileFrac.lean` (edit):** `inodePay_split`, `offFd_split`, `fileCoreNoff/Off_split`,
  `fileCore_none`, `inodePay_cancel`, `inodePay_alloc`, `fileOffReclaim`, `inodePay_notDev`.
  - If FileFrac passes ~900 lines, put the inode-arm lemmas in a new definitional
    `Xv6/FilePay.lean` instead.
- `OffBox`, `OffBoxCam`, `OffGv`, `FileOffCell`: unchanged.
- **D6 (coordinator):** OffBoxCam's `OffboxBoxG` + OffGv's `OffboxG` are two classes where Rocq has
  one (`offboxG`). They are distinct camera types, so rule 1 is not violated. The merge is optional
  and should be recorded either way.

## 3. filealloc / filedup / fileclose: re-prove over the new payload

Rocq files:

| function | Spec | Proof | Parts | Link |
|---|---|---|---|---|
| filealloc | 108 | 1080 | — | 5 |
| filedup | 118 | 635 | — | 5 |
| fileclose | 592 | 1750 | 644 | 11 |

Lean files:

| function | Spec | Proof |
|---|---|---|
| filealloc | 58 | 509 |
| filedup | 50 | 299 |
| fileclose | 83 | 741 |

Image: fileclose 0x8000421c, 194 B; filedup 0x800041d6; filealloc 0x80004178.

**filealloc and filedup.**
- Their contract shapes are already Rocq's: balanced, `wpNext k.sie`, spinlock-only. Rocq has no
  `trap_csrs_ext` on either.
- Only the payload changes:
  - `fileallocPost`'s `fileRef … .closed` now carries `irefFrac 1 ∗ offFree k 1` inside;
  - filedup's split needs `fileCore_split` for the inode arm (`inodePay_split`, `offFd_split`).
- Their proofs should move only at the ghost-step lemmas.
- **Remove `import Xv6.FsEnv`** from SpecFiledup (it is used for `filedupAddr` only; define the
  address locally as SpecIdup/SpecIput must also do).

**fileclose: the one real re-spec. Rocq `wp_fileclose_sconf_body` is the target, clause for
clause.**
- **Premises:** `8 + K_end_op ≤ K` (Lean: `8 + endOpSlots`; check `iputSlots` is below it).
- **Pre:**
  - `n + 1 < 2^31`, `a0 = fnode k`, `locks_below lks "log"`
  - `cpu_own n eb`, **`trap_csrs_ext eb` ∗ `cpu_claim_ext eb p`** (TOP-LEVEL, on every arm)
  - `kernel_text`, `kernel_data`, `panic_env`, `is_ftable`, `file_ref γf k q st`
  - **`proc_priv_bare p pidv Upr`**, which is Lean's pid cell `wordPointsTo (pPid k.proc) 4 dqp pidv`
    by the Lean fs convention (§1). Record it.
  - **`iref_slot`**, borrowed. The last close deposits one unit into the freed slot before iput
    returns one. It is repaid on every arm.
  - **`fileclose_env fn on n eb p st`**, keyed on the STATE:
    - `FdClosed` → `emp`;
    - pipe → `fileclose_pipe_env` (`procs_inv`, the kmem lock, `kalloc_avail on`, `n + 2 < 2^31`);
    - inode/device → `fileclose_fs_env` (`n = 0`, `p = proc_addr j`, `procs_inv`,
      **`FsReady.fs_ready`**, `bslots 3`).
- **Crossing: `wp_next true`.**
- **Post:** `callee_saved`, `fd_slot`, `iref_slot`, `fileclose_env_out fn on st`, the block, and the
  complement back.
- Port the whole env algebra verbatim (SpecFileclose.v 150–400):
  - `fileclose_env_none`, `_pipe_env_out`, `_fs_env_out`, `_env_out_of_env`
  - `_pipe_env_reuse`, `_fs_env_reuse`, `_env_split`, `_env_frame`, `fileclose_loop_open`
- kexit's loop, sys_close and sys_pipe consume exactly these.
- **`fcStateOk` and `fclosePost` are retired.**

The **inode arm** follows Rocq ProofFileclose.v `wp_fileclose_sconf` (l.146):
1. `file_close_last_step` + `file_rest_join` produce the whole slot;
2. `file_off_reclaim`;
3. `f->type = FD_NONE`, and the iref unit is deposited;
4. release;
5. on type FD_INODE/FD_DEVICE (the `addiw -2; bgeu` test Lean currently refutes as dead at +0x5a…):
   `inode_pay_cancel` → `inodeHeld ff.ip` → **begin_op** → **iput** (`wp_iput_gen_eb`) → **end_op**,
   iput returning `irefSlot`.

The **callee budget clash is real**:
- Lean `iput` is the *credited set-form* `wp_iput_gen_eb` (it takes `logOpSe … e0 ∗ txPin`), while
  `begin_op` gives `logOp γ MAXOPBLOCKS`.
- Check how Lean's landed `ireclaim` (commit 6f1adf7e4, `Xv6/Ireclaim*.lean`) bridges
  `BEGIN_OP → IPUT → END_OP`. It is the only landed Lean caller of that triple.
- Copy its bridge (as a copy, or as a promotion candidate). Do not invent one.

The **FS arm's environment `fs_ready` does not exist in Lean** (D1, §7 W7-A2). Without it,
fileclose's inode arm would have to take `iput`'s dozen constituents (`iregInv`, `isItable2`,
`itableInv`, `icEscrows`/sleeplocks, `logCtx`, `bioCtx`, the disk fabric, the sb cells, `bitmapInv`,
…) as its own premises, and so would sys_close, kexit and sys_pipe (for arbitrary descriptors).

Split fileclose's proof into stage files: `FilecloseParts` (pure/frame), `FilecloseLast` (the
critical section and slot free), `FilecloseInode` (the begin_op/iput/end_op arm), `FilecloseTail`,
and `ProofFileclose`.

The new `Link` is `fileclose_proof AC RE PC BO IP EO`, matching Rocq `FilecloseProof Acquire Release
Pipeclose BeginOp Iput EndOp`.

**Blast radius of the fileclose/payload change** (grep; each file needs an edit):

| file | change |
|---|---|
| FileDefs, FileFrac, FileInv, FtableLock | the payload |
| ProofFilealloc, ProofFiledup | ghost steps |
| SpecFileclose, ProofFileclose, LinkFileclose | re-spec |
| ProofPipealloc (1059; `fileFieldsAt` at :569/:581; fileclose on `.closed` files) | payload + fileclose env `FdClosed` + `iref_slot` row (Rocq SpecPipealloc.v:209/224 takes `iref_slot`); Rocq pipealloc is eb-generic (`trap_csrs_ext` ×2): SpecPipealloc changes shape |
| SpecPipealloc, LinkPipealloc | same |
| SpecSysPipe, SysPipeAlloc/Copy/Parts/Tails, ProofSysPipe, LinkSysPipe | fileclose pipe env + `iref_slot` row (Rocq SpecSysPipe.v:342–383); Rocq sys_pipe eb-generic |
| SpecSysClose, ProofSysClose, LinkSysClose | the `hpipe` restriction goes; `fileclose_env_split` over both bundles; Rocq sys_close eb-generic |
| ProofSysDup | only the `fileRef` payload shape, likely nothing |
| FdTable, ProofFdalloc, ProofArgfd | `fdFrags` gains `foff_rows` (D4); otherwise untouched |
| kexit (ProofKexit `kx_loop`) | §4 |

## 4. The process layer: re-align to Rocq before the reconnect

Everything below is a **process-layer deviation**. Rule 3: the coordinator rules on each (D1, D7,
D8), and the user is told.

### 4.1 The block (the root of the kfork/kexit/namex gaps)

- **Rocq** (ProcDefs.v / ProcInv.v 3687):
  - `pprivate` has `pv_fdg`:49, `pv_cwd`:50, `pv_cwi`:62, `pv_gen`:72, `pv_chg`:84, `pv_lazy`:112.
  - `proc_priv γf pa pid U := proc_priv_core ∗ proc_ofiles γf (pv_fdg) pa (pv_ofile)` (ProcInv:1430).
  - `proc_priv_core` (1331) = bare ∗ lazy ∗ **`cwd_ref_at (pv_cwd) (pv_cwi)`** (:1225, `=
    inode_held_at`, no null arm) ∗ `first_tok` ∗ `∃Q, gen_kq ∗ my_pay` ∗ half `p->xstate` ∗
    `gen_halves_priv`.
  - `proc_priv_nocwd` (1540) is allocproc's. `proc_priv_split_cwd` is the six-way split.
  - `proc_dormant` (ProcDefs.v:623/737) parks `fd_slots FDSPARE`, `iref_slots (1+IREFSPARE)`,
    `bslots 3`, `kstack_free`, `ch_frag ∅` and the gen halves.
- **Lean:**
  - `ProcPriv` (ProcDefs.lean:99) has no `fdg`/`cwi`/`gen`/`chg` ("Left out: … `pv_fdg`, the cwd inum
    `pv_cwi`").
  - `procPriv`/`procPrivNoctxAt` (SchedCtx:789) = `proc_priv_core` minus `cwd_ref_at`, first_tok, the
    gen pair, the xstate half and gen_halves. The ofile array is raw `ofileCells`.
  - The fd-aware form `procPrivFd γ γd` (FdTable.lean:477) is used only by sys_close/sys_dup/sys_pipe,
    with `γd : Nat → GName` passed from outside.
  - `fdFrags` (FdTable:120) lacks `foff_rows`.
  - `procDormant` (ProcDefs:218) parks none of the allowances ("not ported").
  - `IREFSLOTS = NPROC*(1+IREFSPARE)+NFILE+IREFBOOT` (IrefSlots:116) already ASSUMES the per-process
    parking the dormant block does not do.

**Wave-7-BLOCKING re-alignments** (recommended Rocq-literal):

| # | change | why wave 7 needs it | blast radius |
|---|---|---|---|
| P1 | `ProcPriv.cwi : Nat`; `inodeHeldAt V.cwd V.cwi` in `procPriv`/`procPrivNoctxAt`/`procPrivCoreNoctxAt`/`procPrivExt`/`procPrivRun`/`ecRest`; `procPrivNocwd` + split lemma | kfork's `idup(p->cwd)`, kexit's `iput(p->cwd)`, namex (sys_open/chdir/exec/…), userinit's `cwd = namei("/")` | `ProcPriv` record: 75 files rebuild (`{V with …}` proofs survive); `procPrivNoctxAt` 35 files, `procPrivExt` 14, `procPrivCoreNoctxAt` 13, `procPriv` 10 |
| P2 | ONE block form `proc_priv = core ∗ procOfiles`, i.e. `procPrivFd` becomes the block; `pv_fdg` IN `ProcPriv` (one gname) in place of the external `γd : Nat → GName` | the real filedup/fileclose need the `fileRef` payloads; kfork/kexit today hold raw ofile words | kfork, kexit, sys_close/dup/pipe, fdalloc, argfd, and every syscall that holds the block |
| P3 | `procDormant` Rocq-literal (`fdSlots FDSPARE`, closed `fdStAuth`, `irefSlots (1+IREFSPARE)`, `bslots 3`) | kfork's child pays idup's `irefSlot` and the ofile dups' `fdSlot` from it; kexit re-parks `bslots 3` and iput's unit | SchedCtx, ProcDefs, allocproc, freeproc, kfork, kwait, kexit, procinit/boot (8 files) |
| P4 | `fdFrags` gains `foff_rows sts` (FdSlots.v:693) | fileread/filewrite's `foff_row st` premise (SpecFileread.v, "the descriptor's offset row") | FdTable, SpecSysClose/Dup/Pipe, SysPipe*, ProofSysDup |

**Order.**
- P1 → P2 → P3 are ONE agent in a worktree ("W7-PROC"), because each changes `ProcPriv`/`procPriv*`
  and they must be edited once.
- Before starting, the agent posts a short plan listing, for each Rocq conjunct, whether it is added
  or deferred, and the coordinator approves it.
- **Reserve the deferred fields now** (`gen`, `chg` in `ProcPriv`, as Rocq's record order has them),
  even with no predicate over them, so the 75-file record is touched once. That is the fork's
  recommendation. It is D7.

**Deferrable** (recorded divergences; not needed to reconnect fs):
- **D8: the fork/exit generation machinery.**
  - Rocq pieces: `uslot`, `Rc`, exit payload `Q`/`my_pay`/`gen_kq`/`child_tok`, `ch_frag`,
    `first_tok`/`first_done`, `park_world`/`park_token` (Lean: `ForkretIs`), `init_ident`,
    `kill_shot`, kwait's reap payload.
  - Rocq files: ChildTok 853, FirstTok 1081, ParkCap 696, SyscParkEnv 168, UexecRet 2683, WaitInv
    1925, SlotGen 877, KforkChild 413 (about 9.7k lines).
- kkill's `□ riscv_kill_cred` (Rocq SpecKkill.v, RiscvPtsto.v:592) is already recorded at
  SpecSysKill.lean:28, and rides with D8.
- prepare_return's "SIE quarter" (`ghost_var sie_gname (1/4)`, SpecPrepareReturn.v:279), `kpt_on`
  and `kpt_inv`:
  - Lean replaces the SIE ghost by `KCtx.sie` (SpecPrepareReturn.lean:54–57, documented).
    Recommendation: keep it.
  - Its post's block must follow P1/P2.
  - There are no callers until forkret/usertrap.
- consoleread's console ghost (`cons_pay`, `cons_read_pay`, post `cons_tagged`/`cons_stored_lb`
  (ConsoleInv.v:1563)/`cons_window`/`cons_out` (:2032)) is needed only by a Rocq-literal fileread
  FD_DEVICE arm (D5b).

### 4.2 kfork / kexit / userinit / sys_fork / sys_exit: the reconnect proper

**kfork.**
- **Rocq SpecKfork.v 447.** `K_kfork = 56`. Not eb-generic in Rocq (`cpu_own lvl eb`, no
  `trap_csrs_ext`); it is balanced and non-parking.
- The fs part of its pre: `is_ftable`, `printk_env`, `is_itable2`, `itable_inv`, `ireg_inv`, and
  `proc_priv γf …` (cwd inside), `fd_frags (pv_fdg) stsP`.
- Post: the block and `fd_frags` back.
- Wave 7 adds exactly these (plus P1–P3). It deletes `[FsEnv]`, and `kf_nbcall`'s `FsEntryNB` calls
  become `IDUP.wp_idup…` and `FILEDUP.wp_filedup`.
- `kforkSlots` becomes Rocq's 56, replacing `8 + fsSlots` = 72.
- LinkKfork applies `Filedup Idup` as Rocq does.
- ProofKfork is 2879 lines. The edits are at `kf_publish` (:1524), `kf_ofile_copy` (:2815) and the
  idup call (:1609), plus the budget `omega`s (~20 sites that `unfold fsSlots`).
- **Keep `[ForkretIs]`** (D8).

**kexit.**
- **Rocq SpecKexit.v 426.** `K_kexit = 94`, sized by fileclose at 88. eb-generic
  (`trap_csrs_ext` ×2).
- The fs part of its pre: `fileclose_pipe_env`/`fileclose_fs_env_nopid` material, i.e. `fs_ready`,
  `bslots 3`, the kmem lock + `kalloc_avail`, `is_ftable`, `panic_env`, `log_geom_ok`,
  `locks_below "log"`, `proc_priv γf pj pid U`, `fd_frags_any (pv_fdg)`, `fd_slots FDSPARE`,
  `iref_slots IREFSPARE`.
- Lean `kexitSlots = 6 + 64 = 70` is too small for the real fileclose (88), so `sysExitSlots`
  (SpecSysExit.lean:54) grows with it.
- `kx_loop` (ProofKexit:291) becomes Rocq's `fileclose_loop_open` loop. The `kx_fs` calls
  (:627/654/667) become the real begin_op/iput/end_op, reusing fileclose's inode-arm bridge (§3).
- The `procDormantNoctx` park payment (`kexit_park_pay`) now includes the P3 allowances.

**userinit.**
- **Rocq SpecUserinit.v 330.** `K_userinit = 4 + K_namei_root_boot`. It calls **`namei_root_boot`**
  (wave 6, not in Lean) and takes `is_itable2`, `itable_inv`, `ic_escrows`, `ireg_reg`,
  `first_*`, `is_ftable`, `console_ready_app`, `init_boot_bundle`, ….
- Its FsEnv retirement is gated on namei's wave 6.
- Until then `FsEnv` shrinks to `{ nameiBoot }` (or `SpecUserinit` keeps an explicit hypothesis
  structure).

**sys_fork, sys_exit.**
- They forward kfork's/kexit's new resources.
- Lean's eb-generic `sys_exit` is stronger than Rocq's `eb = true` pin. Keep it.

## 5. The sysfile layer and the trap path

### 5.0 Four facts that change the plan in notes/fs-rocq-summary.md §7.8/§7.9

1. **The era walk layer is NOT optional for sysfile. Survey §7.9 is wrong.** The Rocq Link lines
   were checked:
   - `SysOpen := SysOpenProof Argint Argstr BeginOp NameiEra Ilock …`
   - `SysChdir := SysChdirProof Myproc BeginOp Argstr NameiEra …`
   - `Create := CreateProof NparWrap Ilock Iunlockput Dirlookup …`
   - `SysUnlink := SysUnlinkProof Argstr BeginOp NparWrap …`
   - kexec takes both `Namei` and `NameiEra`.
   - Only `sys_link` uses the plain `Namei`/`Nameiparent`.

   The era chain:

   | contract | Spec | Proof |
   |---|---|---|
   | NamexEra | SpecNamexEra 312 | ProofNamexEra 5335 |
   | NparEra (a SECOND proof of the namex code, at nameiparent = 1) | SpecNparEra 369 | ProofNparEra 5898 |
   | NparWrapEra | SpecNparWrapEra 259 | ProofNparWrapEra 509 |
   | NameiEra | SpecNameiEra 294 | ProofNameiEra 580 |

   That is about 13.5k Rocq lines, and none of it exists in Lean (SpecNamex.lean:111 notes the
   NparEra twin). D9.
2. **The FsAbs/app "fire" layer is in the syscall STATEMENTS, not only in their proofs.**
   - The statement hooks: `pf_at … commit_at`, `cre_commits`, `link_commits`, `mknod_au_at`,
     fileread's `fileread_in`/`fileread_arms`, filewrite's `awrite_chain`/`write_arms_at`, `app_sup`.
   - The defining files (Rocq line counts):

     | file | lines |
     |---|---|
     | FsAbsCreateFire | 924 |
     | FsAbsMknodFire | 844 |
     | FsAbsReadFire | 779 |
     | FsAbsWriteFire | 1008 |
     | FsAbsLinkFire | 371 |
     | FsAbsUnlinkFire | 530 |
     | FsAbsOpenFire | 424 |
     | FsAbsDelta | 938 |
     | FsAbsEra | 1007 |
     | FsAbs | 1000 |
     | FsAbsInvFire | 476 |
     | FsLookup | 996 |
     | FsRep | 372 |

   - Each family has a trivial instance (`link_commits_unit` at `pfam_triv … True`).
   - Lean has `FsAbsDefs` (659), `AppInv` (506, with `appSupRaw_triv`), `AppCfg`, `FsTree` and the
     `FsState*` files. D10.
3. **The crash layer** (`fs_crash_seam`, `gen_cert`) appears in sys_open/chdir/link/unlink/mkdir/
   mknod, fsinit, main and Rocq's `fs_ready`. Lean already drops it as a recorded deviation
   (SpecEndOp header, SpecIreclaim deviation 3). Carry that deviation into every wave-7 Spec (D11).
4. **Rocq pins `eb = true` (the "PARKING PREMISE") on 16 contracts** where Lean's rule 2 wants
   eb-generic:
   - dirlink, create, fileread, filewrite, filestat;
   - sys_read, sys_write, sys_fstat, sys_open, sys_link, sys_unlink, sys_mkdir, sys_mknod,
     sys_chdir, sys_exec;
   - syscall (`cpu_own 0 true pj true`).

   Rocq IS eb-generic on namei, nameiparent, NameiEra, NparWrapEra, fsinit, kexec, forkret,
   fileclose, pipealloc, sys_pipe, sys_close and kexit. The landed Lean dirlink already
   generalises Rocq's pin (`wp_dirlink_gen_eb`, SpecDirlink.lean:68), and every Lean callee is
   eb-generic, so the generalisation is feasible. D5.

### 5.1 Per-function inventory

All symbols are present in `Xv6/KernelImage.lean`. `readsb`, `skipelem` and `loadseg` are inlined.
Rocq line counts are `wc -l`. "Σ proofs" is the total over the Proof files.

| fn | image (addr, size) | Rocq files | Rocq Link (callees) | Lean | Rocq eb |
|---|---|---|---|---|---|
| namei (+root, root_boot) | 0x80003b84, 26 B | SpecNamei 448, ProofNamei 663, ProofNameiRoot 448, SpecNameiRootBoot 205, LinkNameiRootBoot 73 | `Namex`; `NamexRoot`; RootBoot is an in-Link lemma | none | generic |
| nameiparent | 0x80003b9e, 24 B | Spec 385, Proof 605 | `Namex` | none | generic |
| fsinit | 0x80003634, 112 B | Spec 556, Proof 1587, FsInitPin 541, FsInitPinBoot 388 | `Bread Memmove Brelse Initlog Ireclaim` | none (callees landed) | generic |
| NamexEra / NparEra / NparWrapEra / NameiEra | — | §5.0(1) | NamexEra/NparEra: `Myproc Idup Iget Memmove Ilock Iunlock Iunlockput Dirlookup Iput` | none | generic |
| filestat | 0x800042de, 102 B | Spec 571, Proof 1462, Parts 878 | `Myproc Ilock Stati Iunlock Copyout` | none (callees landed) | pinned |
| fileread | 0x80004344, 206 B | Spec 1852, SysReadDefs 411, Proof 3482, Parts 807 | `Piperead Ilock Readi Iunlock Consoleread Panic` | none (callees landed; console ghost missing) | pinned |
| filewrite | 0x80004412, 318 B | Spec 1088, SysWriteDefs 94, Proof 5505, Chain 201, Parts 1734 | `Pipewrite Ilock Writei Iunlock BeginOp EndOp Consolewrite Panic PrintkGen` | none (callees landed) | pinned |
| create | 0x80004caa, 356 B | Spec 1316, CreateBudget 491; Proof{,Alloc,Fail,FailMkdir,Found,FreshTy,Mkdir,Parts,Shared} Σ 14260 | `NparWrap Ilock Iunlockput Dirlookup Ialloc Iupdate Dirlink` | none | pinned |
| sys_read / sys_write / sys_fstat | — | 529+1042 / 370+1054 / 279+881 | `Argaddr Argint Argfd Fileread` / `… Filewrite` / `Argaddr Argfd Filestat` | none | pinned |
| sys_open | 0x8000520c, 342 B | Spec 1687, SysOpenDefs 777, SysOpenBudget 268; 13 Proof files Σ 11896 | `Argint Argstr BeginOp NameiEra Ilock Iunlock Iunlockput EndOp Fileclose Itrunc Filealloc Fdalloc Create` | none | pinned (3 bodies) |
| sys_link | 0x80004f68 | Spec 634, SysLinkBudget 228, Proof 4081+973+2309 | `Argstr BeginOp Namei Nameiparent Ilock Iunlock Iupdate Dirlink Iput Iunlockput EndOp` | none | pinned |
| sys_unlink | 0x8000508c | Spec 681, SysUnlinkBudget 284, SysUnlinkDefs 355; 10 Proof files Σ 12501 | `Argstr BeginOp NparWrap Ilock Namecmp Dirlookup MemsetArray Readi Writei Iupdate Iunlockput EndOp Panic` | none | pinned |
| sys_mkdir / sys_mknod | — | 456+1534 (+FsSyscalls 576) / 856+116+2504 | `BeginOp Argstr Create Iunlockput EndOp` (mknod + `Argint`) | none | pinned |
| sys_chdir | 0x8000540a | Spec 547, Proof 2498 | `Myproc BeginOp Argstr NameiEra Ilock Iunlock Iput Iunlockput EndOp` | none | pinned |
| kexec | 0x800048b6, 858 B | SpecKexec 1368, SpecKexecB2 907; 11 Proof files Σ 24256; Defs (KexecDefs 582, KexecBuilt 2051, Elf* 1582, …) | `Myproc BeginOp Namei NameiEra Ilock Readi Iunlockput EndOp ProcPagetableGen ProcFreepagetable Walkaddr Flags2perm Uvmalloc Uvmclear Strlen Copyout Safestrcpy Panic` | none (every non-fs callee landed) | generic |
| sys_exec | 0x8000548a | Spec 499, SysExecDefs 180, Proof 793+4784 | `Argaddr Argstr MemsetArray Fetchaddr Kalloc Fetchstr Kfree Kexec` | none (all but kexec landed) | pinned |
| syscall | 0x8000297e | Spec 1155, Proof 8600 | 22 `Sys*` + `Myproc PrintkGen` | none; Lean has 12 of the 22 sys_* | pinned |
| usertrap | 0x80002698 | Spec 2018, Proof Σ ~6300, UsertrapRes 2460, UserTrap 1577 | `Syscall PrintkGen Myproc Killed Setkilled Devintr Vmfault Yield PrepareReturn Kexit Kernelvec` | none | raw CSRs |
| forkret | 0x800019ba | Spec 553 (+Park 132, ParkPaid 391), Proof 2331+476+422 | `Myproc Release PrepareReturn Fsinit Kexec Panic UserretClosedD` | ASSUMED (`SpecForkret.lean`, `class ForkretIs`) | generic |
| main (+secondary) | 0x80000ece | SpecMain 861, ProofMain 2656 (+256/846) | 19 init callees + `Userinit Scheduler Kernelvec` | none | boot |

Rocq's user-mode return layer, which forkret/usertrap/syscall stand on (well over 15k lines), is
**absent from Lean**:
- Userret 230/1285/795/1371/446
- UserretClosed 245/1077
- Uservec 581/2072/509/804/553
- Uexec* (Apply 1537, Ret 2683, SG 722, Slot 378, ExecInst 1560, …)
- UsertrapRes 2460, UserFd 818

`SpecForkret.lean` says so. D12.

### 5.2 What the sysfile contracts need from wave 7's first half

- **All of them:**
  - the fs client bundle, as `fs_ready` (D1) or as its constituents;
  - `procsInv`;
  - the block with `cwd_ref_at` (P1) and the fd table (P2);
  - `fdFrags` with `foff_rows` (P4).
- **sys_open:**
  - `fd_frags`, `fd_slot`, `is_ftable`;
  - `inode_pay_alloc` (§2.2), `proto_publish` (OffBox birth), `open_trunc_piece`;
  - calls Fileclose/Itrunc/Filealloc/Fdalloc directly.
- **create:**
  - `ity_shot`, `off_rows`, `ic_loaded`, `ic_tx_dep`, `ifreeze_off`;
  - `inode_ref_short_genlo`, `runit_any`;
  - `cre_*` (FsAbsCreateFire), `log_tx`.
- **fileread / filestat:**
  - `file_ref`, `file_pay_st`, `foff_row`, `inode_shr_gen` from the payload, `carve_off`;
  - `proc_priv_core`.
  - fileread also needs the console ghost: ConsoleInv 2663 lines vs Lean ConsoleDefs 86; D5b.
- **filewrite:**
  - `awrite_chain`, `write_arms_at`, `write_cons_arms`;
  - its proof imports FsStateEra/FsStateInode/FsAbsDelta/FsAbsOpenFire/FsAbsWriteFire/WriteiBudget.
- **sys_chdir:** changes `pv_cwi` (this is where `cwd_ref_at` is live). syscall's post has
  `(num = 9 ∧ ret = 0) ∨ pv_cwi' = pv_cwi`.
- **kexec:** `fs_fabric` (KexecDefs:494) and `my_pay` (ChildTok; D8).
- **syscall / usertrap / forkret:** `ch_frag`, `uslot`/`ustate`, `riscv_kill_cred`, `first_done`,
  `park_globals`. These are all D8/D12 material.

## 6. Blast radius summary (landed files wave 7 edits)

| change | landed files touched | who |
|---|---|---|
| `CInvG` in `Xv6G` (D2) | UartTrace.lean (the class). There is no instance site in the tree (`Xv6G` is only ever assumed; grep checked). Everything rebuilds | W7-A1, first commit |
| file payload (§2) | FileDefs, FileFrac, FileInv, FdTable (FdState offmode, `fdFrags` + `foff_rows`), ProofFilealloc, ProofFiledup, ProofPipealloc, ProofFileclose (payload only), SpecSysDup/ProofSysDup, SysPipe* (payload only), SpecFiledup (drop FsEnv import) | W7-A1 (worktree) |
| process block P1 + P3 + reserved fields | ProcDefs (`ProcPriv`, `procDormant`), SchedCtx (`procPrivNoctxAt`, `procPrivCoreNoctxAt`), EitherDefs (`procPrivExt`, `procPrivRun`, `ecRest`), allocproc, freeproc, kwait, kexit, kfork (dormant/nocwd only), procinit; the 75 files naming `ProcPriv` rebuild | W7-A3 (worktree) |
| process block P2 (`procPrivFd` becomes the block, `pv_fdg` in the record) | FdTable (`procPrivFd`), the sys_close/dup/pipe Specs, fdalloc/argfd; every block holder that must now carry `procOfiles` | W7-C0 (worktree, after A1 + A3 merge) |
| fileclose re-spec (§3) | SpecFileclose, ProofFileclose, LinkFileclose, SpecPipealloc/ProofPipealloc/LinkPipealloc, SpecSysPipe/SysPipe*/ProofSysPipe/LinkSysPipe, SpecSysClose/ProofSysClose/LinkSysClose | W7-B (worktree) |
| FsEnv retirement (§4.2) | SpecKfork/ProofKfork/LinkKfork, SpecKexit/ProofKexit/LinkKexit, SpecSysFork/ProofSysFork, SpecSysExit/ProofSysExit, SpecIdup/SpecIput/SpecFiledup (address defs), FsEnv (shrinks to `nameiBoot`, then deleted), Xv6.lean | W7-C (worktree) |
| userinit off `FsEnv.nameiBoot` | SpecUserinit/ProofUserinit/LinkUserinit | after namei_root_boot (wave 6) |

NEW files (main tree, no conflicts):
- `Xv6/FsReady.lean`
- `Xv6/FilePay.lean` (if split out)
- the fileclose stage files
- all of §5's Spec/Proof/Link triples and their Defs/Budget files
- FsAbs*Fire, ConsoleInv

## 7. Dependency DAG and batch schedule

### 7.1 DAG (callee/prerequisite → consumer; ✓ landed, ◐ in progress, ★ absent layer)

```
CInvG∈Xv6G ─┐
FsReady ────┼──────────────────────────────┐
A1 payload (FileDefs/FileFrac/FdTable P4) ─┼→ filealloc✓/filedup✓ re-proof (in A1)
            │                              ├→ B fileclose re-spec ─→ pipealloc/sys_pipe/sys_close adapt (in B)
            │                              └→ filestat ─→ sys_fstat
A3 block P1+P3 ─→ C0 block P2 (procPrivFd = block, pv_fdg) ─┐
                                                              ├→ C kfork/kexit/sys_fork/sys_exit real links; FsEnv → {nameiBoot}
B fileclose ─────────────────────────────────────────────────┘
A5 FsAbs fire defs + ConsoleInv (D5b/D10) ─→ fileread, filewrite ─→ sys_read, sys_write
namex◐ ─┬→ namei, nameiparent, namei_root(+boot) ─→ userinit re-link (FsEnv deleted), sys_link
        └→ [D9] NamexEra, NparEra ─→ NameiEra, NparWrapEra
dirlink✓, ialloc✓, NparWrapEra ─→ create ─→ sys_mkdir, sys_mknod
NameiEra, create, B fileclose, filealloc, fdalloc✓, itrunc✓ ─→ sys_open
NameiEra ─→ sys_chdir;  NparWrapEra ─→ sys_unlink
ireclaim✓, initlog✓ ─→ fsinit
Namei, NameiEra, Kexec defs (Elf*, KexecDefs…) ─→ kexec ─→ sys_exec
22 sys_* ─→ syscall ─→ usertrap;  fsinit, kexec, prepare_return✓, userret★ ─→ forkret ─→ main
```

### 7.2 Batches

Worktree agents edit landed files. Each worktree merges only when every module in its rebuild list
builds. Main-tree agents only add files.

**W7-A (start once D1–D4 and D7 are answered; parallel):**
- **A1 (worktree): the file payload.**
  - `CInvG` into `Xv6G` (first commit, alone).
  - Then §2.4: FileDefs/FileFrac Rocq-literal payload; FPNames; `offFd`/`offFree`/`inodePay` + laws.
  - FdState offmode + `fdFrags` `foff_rows` (P4).
  - Re-prove filealloc/filedup and adapt ProofPipealloc/ProofFileclose/SysPipe*/ProofSysDup to the
    payload ONLY (fileclose's contract is unchanged here; its inode arm stays refuted by
    `fcStateOk`).
  - Rebuild list: every importer of FileDefs.
- **A2 (main tree): `Xv6/FsReady.lean`**, Rocq FsReady.v (660) minus the crash seam and `gen_cert`
  (D11).
  - The projections: `fs_ready_bio/_log/_disk/_icache/_region/_kmem/_kalloc/_geom/_sb/_bitmap/_all`.
  - `fsGeomOk` is already in FsCfgDefs.
  - `fs_ready_seal`/`_establish` wait for fsinit, but the predicate and projections do not.
  - Check each constituent against the ACTUAL premise lists of the landed IPUT/BEGIN_OP/END_OP/
    ILOCK/READI/WRITEI (and the untracked SpecNamex's deviation 2 list). The predicate must project
    onto exactly those Lean forms.
- **A3 (worktree): the block, P1 + P3 + the reserved `ProcPriv` fields** (`fdg`, `cwi`, `gen`, `chg`,
  in Rocq's order; D7).
  - It first posts a Rocq-conjunct → add/defer table for coordinator approval (rule 3).
  - It must not touch FdTable (A1 owns it).
- **A4 (main tree): the fileclose inode-arm bridge**, begin_op → `logOp_openS` → `iput_gen_eb` →
  `logOpS_op` → end_op, copied from IreclaimOrphanB/C.
  - Staged as `FilecloseInode.lean` against the landed callee Specs.
  - It needs A1's `inodePay_cancel` statement only, so it can start from the A1 statement once
    frozen.
- **A5 (main tree; only if D5b = (a) and D10 = port): definitional files for fileread/filewrite.**
  - FsAbsReadFire, FsAbsWriteFire (+ FsAbsDelta, FsAbsOpenFire, FsAbsInvFire as their imports need),
    SysReadDefs, SysWriteDefs, ConsoleInv (split it; 2663 lines).
  - Two or three agents, one per file family.

**W7-B (after A1 + A2 merge; worktree, 1 lead + 2 helpers on disjoint files):**
- Lead: fileclose re-spec (§3) + stage files, with A4 folded in.
- Once `SpecFileclose` is frozen (the lead announces the statement):
  - helper 1: pipealloc + sys_pipe;
  - helper 2: sys_close (over `fileclose_env_split`).

**W7-B' (after A1; main tree, parallel with B): filestat.**
- The smallest consumer of the inode arm (no console, no FsAbs). It validates `inode_pay`'s read
  path (`inode_shr_gen` → ilock).
- Then sys_fstat (needs P2 for `fd_frags … pv_fdg`, so it lands after C0).

**W7-C0 (after A1 + A3 merge; worktree): the block, P2.**
- `procPrivFd` becomes the block; its holders are updated.

**W7-C (after B + C0; worktree): the reconnect.**
- kfork (real FILEDUP/IDUP, `kforkSlots` → 56), kexit (real FILECLOSE loop + begin_op/iput/end_op,
  `kexitSlots` → Rocq 94), sys_fork, sys_exit.
- `FsEnv` shrinks to `nameiBoot`.
- `SpecIdup`/`SpecIput`/`SpecFiledup` get their own address defs.

**W7-D (after A5 + C0; main tree, parallel):** fileread, filewrite. Then sys_read and sys_write.

**Wave 7b (proposal: a separate brief once wave 6 lands).**
- namei/nameiparent/namei_root(+boot)/fsinit (wave 6 proper).
- Then userinit's re-link, which deletes FsEnv.
- Then (D9) NamexEra ∥ NparEra → NameiEra ∥ NparWrapEra.
- Then create, sys_link, sys_chdir, sys_unlink → sys_open, sys_mkdir, sys_mknod.
- kexec + sys_exec are a parallel long pole (about 24k Rocq proof lines; start its definitional
  files, KexecDefs/KexecBuilt/Elf*, early).

**Wave 8 (proposal; D12):** syscall (8600), usertrap, forkret (retiring `ForkretIs`) and main,
together with the user-mode return layer if it is ported.

**Critical path of wave 7:** A1 → B → C. The critical path of 7b is NamexEra/NparEra → NparWrapEra →
create → sys_open.

## 8. Decisions the coordinator (and, for the process layer, the user) must make

| # | decision | recommendation |
|---|---|---|
| D1 | Port Rocq `FsReady.fs_ready` as `Xv6/FsReady.lean` and make it the fs environment of every process-level contract (fileclose's FS arm, kexit, sys_close, the sysfile syscalls) | **Yes.** Without it every such contract threads a dozen fs constituents (IPUT alone takes `pd pav pu γil γisl …`). The fs-leaf contracts keep their constituent forms, as in Rocq |
| D2 | Where the `CInvG` capacity (for `inode_pay`'s cancellable invariant) lives | **`Xv6G`** (one bundle, rule 1). Not `FileG` |
| D3 | The three §2.3 cleanups: drop `flive`; keep Lean's half-element reference algebra; no `proto_*` chain file | **Approve all three** and record them in FileDefs's header |
| D4 | Port FdSlots' `offmode` (`OffParked`/`OffHeld`, the `OffParked` pin in `fdstate_ok`) and `fd_frags`' `foff_rows` | **Yes, Rocq-literal.** fileread/filewrite/sys_read/sys_write take `foff_row st` |
| D5 | Rocq pins `eb = true` on 16 contracts (§5.0(4)) | **Generalise to eb-generic** (rule 2; every Lean callee is already eb-generic; the Lean dirlink precedent). Record "stronger than Rocq" in each header |
| D5b | fileread's FD_DEVICE arm: (a) port ConsoleInv's console ghost into consoleread first (consoleread's `cons_pay`/`cons_stored_lb`/`cons_out` post), then a Rocq-literal fileread; or (b) ship fileread with consoleread's current thin post and record the deviation | (a) if sys_read's console semantics are in scope for this project; otherwise (b) **as a recorded, flagged deviation**. The user should choose |
| D6 | Merge `OffboxBoxG` + `OffboxG` into Rocq's single `offboxG` class | Optional (distinct camera types, so rule 1 is not violated). Default: leave as is, recorded |
| D7 | Process block: P1 (`cwi` + `cwd_ref_at`), P2 (one block `core ∗ procOfiles`, `pv_fdg` in the record), P3 (Rocq `proc_dormant` allowances), P4 (above); and reserve `gen`/`chg` in `ProcPriv` now | **All Rocq-literal**, one record edit (A3). **Flag to the user** (rule 3): this touches 75 files' `ProcPriv` |
| D8 | Keep the fork/exit generation machinery (uslot, Rc, Q/my_pay/child_tok, ch_frag, first_tok/first_done, park_world/park_token, kill_shot, riscv_kill_cred, kwait's reap payload, ~9.7k Rocq lines) DEFERRED, with `ForkretIs` still assumed | **Defer**, but record each one as a named process-layer divergence in SpecKfork/SpecKexit/SpecKkill/SpecKwait (most already are). **Flag to the user** |
| D9 | Port the era walk layer (NamexEra, NparEra, NparWrapEra, NameiEra, ~13.5k lines) for sys_open/chdir/unlink/create/kexec | **Port it** (wave 7b). Stating those syscalls over plain namex would be exactly the premature simplification the user warned against. It also means correcting fs-rocq-summary §7.9 |
| D10 | FsAbs fire families: port the definitions and the fire lemmas the kernel proofs call, or only definitions with trivial instances | Port the definitions and every lemma a kernel PROOF calls (the contract shape needs the families either way). The generic dischargers (`fsabs_*_in`) wait for the user-safety lane |
| D11 | Drop `fs_crash_seam`/`gen_cert` from `fs_ready` and every wave-7 contract | **Yes**, following the existing SpecEndOp/SpecIreclaim deviation |
| D12 | Scope: does wave 7 include syscall/usertrap/forkret/main and Rocq's user-mode return layer (Userret/Uservec/Uexec*/UsertrapRes/UserFd, >15k lines)? | **No.** Wave 7 = file layer + reconnect + fileread/filewrite/filestat + sys_read/write/fstat. Wave 7b = the namei/era/create/sys_open family + kexec. Wave 8 = the trap path, with its own decision on the user-mode layer |
| D13 | Where `SpecIdup`/`SpecIput`/`SpecFiledup` get their entry-address defs once FsEnv shrinks | Local `def idupAddr := KA.«idup»` etc. in each Spec (the SpecIdup header already anticipates this) |

## 9. Risks

1. **The three worktrees A1/A3/C0 overlap on FdTable and the block.** The ownership rule is:
   - A1 owns FileDefs/FileFrac/FileInv/FdTable;
   - A3 owns ProcDefs/SchedCtx/EitherDefs and the proc.c Specs;
   - C0 starts only after both merge.

   Any agent that finds it needs a file another worktree owns stops and reports the exact edit.
2. **fileclose's budget.**
   - Rocq's `8 + K_end_op` makes kexit 94 and grows sys_exit's and sys_close's budgets.
   - Re-derive every `omega` over `fsSlots` in ProofKfork/ProofKexit (~25 sites) from the new slot
     constants. Do not keep `fsSlots = 64` as a shim.
3. **The begin_op → iput log-budget bridge.**
   - Lean `iput` is the credited set form (`logOpSe … e0 ∗ txPin`); `begin_op` gives
     `logOp MAXOPBLOCKS`.
   - The only landed caller of the triple is ireclaim (IreclaimOrphanB:122 `logOp_openS`, OrphanC:125
     `logOpS_op`). Copy that bridge. Do not invent one.
4. **`inode_pay` canonical pairing.**
   - `fp_iq` must be a per-slot CONSTANT, not an existential, or `inode_pay_cancel`'s gather fails
     and the inode becomes unfreeable (FileInvDefs.v header above `fpnames`).
   - Do not "simplify" it to `∃ q`.
5. **`fileFieldsAt` loses `off` at every fraction.** Every landed proof that destructs the 7-tuple
   (ProofFileclose:290–305, ProofPipealloc:569/581, FileFrac's split/join) changes arity. Grep for
   `Hoff`/`aFoff` in them.
6. **iref-unit conservation.**
   - Rocq's file_core parks one `iref_frac` per untyped/pipe slot. fileclose, pipealloc and sys_pipe
     borrow an `iref_slot` across the call.
   - Lean's `IREFSLOTS` already counts `NFILE` for this. Check that the boot/`fileinit` resource (and
     A3's dormant `irefSlots (1+IREFSPARE)`) mint exactly Rocq's numbers, or the supply bound
     (`irefSlots_no_overflow`) breaks.
7. **Rebuild cost.** Editing `Xv6G` (A1's first commit) and `ProcPriv` (A3) rebuilds essentially the
   whole tree. Batch each into ONE commit per worktree and do not iterate on them.
8. **Stale Rocq prose.** Among others:
   - ProofFileread.v's header describes the retired off LEDGER (`ioff_checkout`, `off_mark`), not the
     box;
   - SpecSyscall's header says "ASSUMED … Axiom" (it is linked);
   - LinkFileread.v calls consoleread an Axiom.

   The CODE and the Spec bodies are the reference.
9. **The survey is wrong in two places.** fs-rocq-summary §7.9 (the era layer "optional") and §7.8
   (fileclose "with `fcStateOk` dropped": the contract changes shape, eb-generic with an env algebra,
   not just an arm). Correct them when wave 7b is briefed.

## 10. Report (per agent)

As fs1 §7, plus the following:
- Every process-layer deviation (rule 3), as Rocq name → Lean form → reason.
- Every eb pin that differs from Rocq's, with the reason.
- For each landed file edited: the exact list of changed statements and the rebuild list checked
  (the modules built after the edit).
