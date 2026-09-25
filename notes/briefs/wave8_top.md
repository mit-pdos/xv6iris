> **USER RULINGS (2026-09-25):** D23 = **full Rocq final theorem INCLUDING the crash-durability corollary** (reverses D11; crash layer to be reinstated — see notes/briefs/crash_layer.md once written). D34 follows D23 (Himg premise per Rocq). D24 = SpecUser.USER as explicit parameter now; user-mode layer ported as wave 9. D25, D26, D29 = approved as recommended. D27 (keep KCtx index form), D28 (accept sie=false pin), D30 (concrete syscallEnv, Rocq content), D31 (adapters at dispatch), D32 (syscall eb-generic), D33 (new KexecNe.lean) = approved as recommended. BootReset (Rocq's symbolic Sail boot run proving the reset values) = port in WAVE 9 with the user-mode layer; until then MachCSL's stated reset table (bootFacts/resetVal) is a recorded trusted assumption.

> **DECISIONS PENDING (user + coordinator). Numbering continues from fs7b's D22.** "(user)" marks a
> process-layer or scope decision; by rule 3 those go to the user. Every item has a recommendation.
> Batch 8-0 (§8.0) is definitional and needs none of these decisions, so it can start now.
>
> | # | decision | recommendation |
> |---|---|---|
> | **D23** (user) | **What the final theorem is.** Rocq's top-level theorem is `SystemAdequacy.xv6_fs_adequacy_xv6Σ`. It covers power cycles, the crash/durability slot (`xv6_slot`, `snap_ok`), a pluggable APPLICATION (`CT`/`app_fs`/`app_boot`/`Ores`/`Ires`), and the literal mkfs image. Lean dropped the crash layer (D11) and has no application layer (FirstTok deviation 1). | **(a) Port `xv6_power_adequacy` at the GENERIC application with no crash slot**: starting from `PowerLoop`, every reachable configuration has only reducible threads, and `phi` holds. Keep the `phi`/trace slot. Instantiate it at the obs-trace well-formedness corollary (Rocq `xv6_obs_wf_xv6Σ`, over Lean's `MachCSL/ObsTrace`). Drop the fs-durability corollary (`xv6_fs_adequacy`, whose `phi` is `fs_boot_pure`) as a recorded D11 consequence. (b) Restore the crash layer to state (a) plus durability. That reverses D11 and costs roughly FsCrash/FsDur*/AppDur/SbPark wiring plus `log_mirror_born`. (c) A single-era corollary only. Rocq deleted its own single-era theorem ("a special case, nothing used it", RiscvAdequacy:17–22), so (c) is not Rocq-literal |
> | **D24** (user) | **The user-mode machine tower.** Rocq `SpecUser.USER` (`wp_user_exec_closed`) says arbitrary user code, run forever, only exits by trapping to `stvec`. It is proved by about 84k lines in the theorem's cone: WpUmode*, Umode*, User{Mem*,Fetch*,Step*,Classify*,Csr,TotalU,ActiveClass,…}, Upt*, TransPt, and the Uk* runner framework. MachCSL has **no U-privilege tier at all**: no trap out of U, no `sret` to U, no user-table satp switch, and `KTier` is only `bare`/`kpt` | **(a) Wave 8 STATES `SpecUser.lean` and takes `USER` as an explicit structure PARAMETER of the final theorem**, the way Lean's links take `PRINTK`/`DISK_INIT_WM` today. The whole kernel side (the loop, usertrap, uservec/userret, forkret, main, adequacy) is proved against it. Porting the tower is wave 9, a MachCSL wave of its own. Rocq itself carried `stvec_handler_wp` as an assumption for a long time (SpecUser header). (b) Port the tower inside wave 8. That roughly doubles the wave and serialises it on a new MachCSL tier |
> | **D25** (user) | **The newborn park drops the child's fd table and cwd reference** (SpecForkret, SpecKfork deviation 2, SpecUserinit). The cause is that the file-layer predicates have no `CtxMorph` (FsReady deviation 8). Separately, **`ForkretIs` is an assumed class** threaded through kfork/sys_fork/userinit | **Fix, Rocq-literal.** (i) Port `EnvMorph.v` (131 lines) plus the deferred `fs_ready_morph`/`fs_sb_cells_morph` and `CtxMorph` instances for `procOfiles`/`fdFrags`/`cwdRefAt`, so the record parks the WHOLE `procPrivFd`. (ii) Port `ParkCap.park_token`, the guarded fixpoint that ties the park→forkret→trap-loop→kfork→park knot. It replaces the `[ForkretIs]` instance argument of kfork/sys_fork/userinit: kfork consumes the token from `syscallEnv`, and only main's cone proves it (`park_token_intro`). The top-level theorem NEEDS this. Without the child's block, a forked child's first syscall has no `procPrivFd` to hand the dispatch |
> | **D26** (user) | **D8 families still missing from landed contracts**: `first_tok`/`GenId` in the block (in flight); `chFrag` in sys_fork/sys_wait; `myPay`/`initIdent` in sys_exit (Lean has only `chFrag … ∅`); `killCred` in sys_kill; kfork's `child_tok`/`Q`; userinit's `first_boot` deposit and `init_pid_tok` | **Land them as batch 8-P** (worktree, after D8's block lands), before the dispatch seal. Rocq's syscall post rows `sysc_fork_out`/`sysc_wait_out`/`sysc_ch_ok`/`sysc_ret_pid`, the uslot key (`uvis` carries gen/ch/pid), and forkret's first-arm split (by `first_tok`) all consume them. The top-level theorem needs every one of them |
> | **D27** (user) | **No SIE ghost.** Rocq splits `sie_gname` ½/¼/⅛/⅛. `prepare_return` returns the ¼ dangling and usertrap's `csrw stvec` folds it back. Lean encodes the same fact in the `KCtx` index (`sie = false`, no `intrRes`), as the landed SpecPrepareReturn does | **Keep Lean's index form**, and restate UsertrapRes's quarter and sret-mirror rows as `KCtx` facts. No top-level consequence: the ghost never leaves usertrap's residue in Rocq. Record it as a deviation |
> | **D28** | **sie-pinned `uartintr`** (and `devintr`/`kerneltrap` at `sie = false`) | **Accept.** Both callers enter with interrupts off: usertrap's device arm runs before `intr_on`, and kerneltrap runs under the trap. Rocq's usertrap also calls devintr at `false`. Nothing at the top needs `b`-generic |
> | **D29** (user) | **`UserFd.v`/`ufdG`**, the program's own descriptor-view camera, which D17 dropped. It is a binder of every file on the loop's path: UexecRet/`uslot`, UexecExecMint, UsertrapRes, ParkCap, SpecUsertrap, SpecForkret, SpecMain, and SystemAdequacy's `Hufd` | **Port `UserFd.lean` in 8-0.** By one-instance-per-camera, if `ufd_map`'s camera type already has a capacity instance (a ghost map), reuse it and name only the gname. Otherwise add ONE field to `Xv6G`, and not a `UfdG` class |
> | **D30** | **`syscall_env`.** Rocq keeps it an abstract `Parameter` of `Module Type SYSCALL` and defines it in ProofSyscall (:912), with four families pulled out (`bslots 3`, the initproc cell, `fd_slots FDSPARE`, `iref_slots IREFSPARE`) because `ut_own` shares them | **Rocq-literal content, but CONCRETE**: `Xv6/SyscallEnv.lean` defines `syscallEnv` (the union, indexed like Rocq's by `γf pj bn fn`), and the four families stay explicit. A Lean structure cannot hide a definition, and the Rocq parameter has exactly one instance |
> | **D31** | **Entry-shape adapters.** getpid/sbrk/wait take `procPrivNoctxAt`. kill/pause take raw `tfp ws`. sync takes the `pPid` cell. dup/getpid/sbrk/uptime/kill are `sie`-generic (no trap bundle) | **Bridge at the dispatch, no re-specs.** Add one `procPrivFd ⊢ procPrivNoctxAt ∗ (procPrivNoctxAt -∗ procPrivFd)` accessor (none exists; checked `FdTable.lean:677/708`) and per-arm adapters in the arm stages. Rocq has the same raw shapes for kill/pause/uptime |
> | **D32** | **syscall's `SIE` index.** Rocq pins `eb = true`, since its one call site follows `intr_on` | **eb-generic** (rule 2). It costs nothing here, because every Lean entry is eb- or sie-generic, and the exit arm's closer is already at `trapRes k.sie`. Fallback: pin `true` with Rocq's justification recorded. usertrap's entry is `sie = false` by the trap itself (not a choice) |
> | **D33** | **Where `exec_slot_pre_ne`/`exec_au_pre_ne` go.** SpecKexec deviation 5 deferred them to wave 8. Their only consumers are `sys_exec_*_ne` and then UexecExecInst's `exec_sbundle_ne` (contractivity of `uslot_F`) | **New file `Xv6/KexecNe.lean`**, split from SpecKexec (the D21 precedent), plus `SysExecNe` beside it if SpecSysExec has landed. The alternative is appending to SpecKexec, which is a landed edit and needs a worktree |
> | **D34** (user) | **The disk-image hypothesis.** Rocq discharges `Himg` by computation over the literal 2 MB image (`fsimg_image_wf`, FsImgCheck sweeps). Lean's FsImg is superblock-only, and big literals have blown up the elaborator before (memory: lean-runaway-memory) | **Keep `Himg` (the image wf) as a PREMISE of the wave-8 theorem.** Discharging it (the rest of FsImg W3–W8 plus a bounded computation) is a separate later step run under `ulimit` |

# Brief: wave 8: the TOP of the kernel (syscall dispatch, the trap loop, forkret, main, adequacy)

Read these first; their rules apply unchanged:
- `notes/briefs/fs7b_era_create_open_exec.md` §0 (the standing rules, verbatim, which bind every
  wave-8 agent) and its D14–D22.
- `notes/briefs/fs7_file_layer.md` §5.0 (the eb facts) and D1–D13.
- `notes/briefs/fs0_common.md` (porting rules) and `fs1_leaves.md` §1 (idioms, the LAYERING rule).

Wave-8 specific rules:
1. **One Lean file per Rocq file, same name.** Rocq Proof files become stage files (no `Proof`
   prefix); only the seal is `Proof<Fn>.lean` (7b rule 2). Rocq `Code*.v` decode files are not
   ported; they come from `KernelImage` plus the `k_step` family.
2. **The addresses are Lean's.** The image is the two-UART kernel 163d39be. Rocq's offsets
   (`syscall` @ 0x80002872) do NOT match: here `KA.«syscall»` is 0x8000297e, 100 bytes, and
   `KA.«syscalls»` is 0x80007798 (0xb8 bytes = 23 slots). Re-derive every offset from `KernelImage`.
3. **The knot is tied in the logic (ParkCap), never by an assumed class.** No new `…Is` class and no
   new assumed structure, except `USER` if D24(a) is taken.
4. The crash layer stays dropped (D11). Carry the SpecEndOp/SpecIreclaim deviation text wherever
   Rocq mentions `fs_crash_seam`/`gen_cert`/`log_mirror_born`/`xv6_slot`.

## 1. Where wave 8 starts from (verified against the tree, Sept 25 2026, `2402efd53`)

### 1.1 The 22 syscall entries (the `syscalls[]` table)

**Sealed, meaning Spec/Proof/Link all present in `Xv6/` (19):** fork, exit, wait, pipe, kill,
fstat, chdir, dup, getpid, sbrk, pause, uptime, open, mknod, unlink, link, mkdir, close, sync.

**In flight (3):**
- **sys_read**: needs fileread, which lives in worktree `agent-a0cd3651…` (`SpecFileread` and its
  stages). Only `SysReadDefs.lean` is in main.
- **sys_write**: worktree `agent-a3b0f4b4…` (`SpecSysWrite`/`SysWriteParts`/`ProofSysWrite`/
  `LinkSysWrite`). filewrite is sealed in main.
- **sys_exec**: kexec is sealed (`bc66ac0e6`). Only `SysExecDefs.lean` (45 lines, the pure part)
  is in main.

The contract form of each entry. **eb** = `trapCsrsExt`/`cpuClaimExt` at `k.sie` with
`hnoff : k.noff = 0`. **sie** = `wpNext k.sie` with no trap bundle and `k.noff + 1 < 2^31`.
**Fd** = `procPrivFd`. **Noctx** = `procPrivNoctxAt curCtx`.

| # | entry | Lean structure.field | form | block / pieces | gap vs Rocq's dispatch (ProofSyscall arm) |
|---|---|---|---|---|---|
| 1 | fork | `SYSFORK.wp_sys_fork_eb` | eb (crossing `wpNext k.sie`) | Fd + `fdFrags` | **no `chFrag`, no child token / `Q`/`Rc` deposit (`sysc_fork_in`/`_out`); takes `[ForkretIs]`** (D25/D26) |
| 2 | exit | `SYSEXIT.wp_sys_exit_eb` | eb | Fd, `∃ sts fdFrags`, `chFrag V.chg _ ∅`, inline stack wand | **only an empty child set; no `myPay`/`initIdent`** (D26) |
| 3 | wait | `SYSWAIT.wp_sys_wait_eb` | eb | Noctx | **no `chFrag`** (D26) |
| 4 | pipe | `SYSPIPE.wp_sys_pipe_eb` | eb | Fd + `fdFrags` + slot singletons | dispatch splits `fdSlots FDSPARE` |
| 5 | read | — (in flight) | — | — | armed deposit (`sys_read_arms`) |
| 6 | kill | `SYSKILL.wp_sys_kill` | sie | raw `tfp ws v dqt` | **no `killCred`** (Rocq deposit row 6) (D26) |
| 7 | exec | — (in flight) | — | — | AU (`sys_exec_au_pre`); `_ne` lemmas (D33) |
| 8 | fstat | `SYSFSTAT.wp_sys_fstat_eb` | eb | Fd + `filestatFsEnv` | — |
| 9 | chdir | `SYSCHDIR.wp_sys_chdir_eb` | eb | Fd, `chdirAuPre`, `irefSlots 2` | receipt `chdir_receipt` (UexecExecInst) |
| 10 | dup | `SYSDUP.wp_sys_dup` | sie | Fd + `fdFrags` + `isFtable` | adapter (D31) |
| 11 | getpid | `SYSGETPID.wp_sys_getpid` | sie | Noctx | adapter (D31) |
| 12 | sbrk | `SYSSBRK.wp_sys_sbrk` | sie | Noctx + kmem | adapter (D31) |
| 13 | pause | `SYSPAUSE.wp_sys_pause_eb` | eb | raw `tfp ws` | same as Rocq |
| 14 | uptime | `SYSUPTIME.wp_sys_uptime` | sie | tickslock only | same as Rocq |
| 15 | open | `SYSOPEN.wp_sys_open_eb` | eb | Fd + `fdFrags` + `fdSlot` + `irefSlots` | receipt `open_receipt` |
| 16 | write | — (in flight) | — | — | armed deposit |
| 17 | mknod | `SYSMKNOD.wp_sys_mknod_eb` | eb | Fd, `mknodAuAt` | — |
| 18 | unlink | `SYSUNLINK.wp_sys_unlink_eb` | eb | Fd, `unlinkAuPre` | — |
| 19 | link | `SYSLINK.wp_sys_link_eb` | eb | Fd, `linkCommits` | — |
| 20 | mkdir | `SYSMKDIR.wp_sys_mkdir_eb` | eb | Fd, `mkdirAuPre` | — |
| 21 | close | `SYSCLOSE.wp_sys_close_eb` | eb | Fd + `fdFrags` + `irefSlot` + pipe/fs env | — |
| 22 | sync | `SYS_SYNC.wp_sys_sync_eb` | eb | raw `pPid` cell + `logCtx`/`logEpochLb` | Rocq `sync_witness_0` |

The AU/armed shape family matches Rocq on every sealed entry (no AU-vs-landed flip).

**The argument helpers are all sealed:** argraw, argint, argaddr, argfd, argstr, fetchaddr and
fetchstr, plus `ArgLemmas`/`ArgPath`. **No dispatch file exists.** There is no table-word lemma
for `syscalls[]`; the only precedent is argraw's `.rodata` jump table (`SpecArgraw.lean:10`).

### 1.2 The trap path and the top

| item | Lean state |
|---|---|
| `prepare_return` | **sealed** (`SpecPrepareReturn` 173, `ProofPrepareReturn` 200, `PrepareReturnStores` 277, `LinkPrepareReturn`). Post: raw `sepc`/`scause`/`stval`, `stvec ↦ uservecTvec`, `procPrivNoctxAt` with the four kernel trapframe words re-armed, context at `sie = false`, no `intrRes`. Deviation: no SIE ghost (D27) |
| `usertrap` | **absent**. Every callee is sealed: myproc, killed, setkilled, devintr (proved; `LinkDevintr`), vmfault, yield, kexit, kernelvec, prepare_return, printk. The one missing callee is `syscall` |
| `kerneltrap`/`kernelvec` | sealed. The SpecKerneltrap header still says "ASSUMED as an interface"; it is stale, since `ProofKerneltrap`/`LinkKerneltrap` exist |
| uservec / userret (trampoline @ `KA.«_trampoline»` 0x80006000; `userret` 0x8000609c) | **absent**, and so is the machine support they need (§3.2) |
| `forkret` @ 0x800019ba | **ASSUMED**: `SpecForkret.lean` `class ForkretIs` over `wp_forkret_body` (a resumed kctx at `forkretAddr`, `procPriv` WITHOUT the fd layer, `liveAllow`, `chFrag … ∅`). No first-process arm and no user return. Consumed by SpecKfork/ProofKfork/LinkKfork, SpecSysFork/ProofSysFork, SpecUserinit/ProofUserinit/LinkUserinit, ForkretRecord, FirstTok |
| `main` @ 0x80000ece (+ secondary harts) | **absent**. All 19 of Rocq's `LinkMain` callees are sealed in Lean: cpuid, consoleinit, printkinit, printk, kinit, kvminit, kvminithart, procinit, trapinit, trapinithart, plicinit, plicinithart, binit, iinit, fileinit, virtio_disk_init, userinit, scheduler, kernelvec. The image's main also calls `memset`/`kalloc` and reads/writes `started` (0x8000a330) |
| boot `_entry`/`start` → `main` | **sealed** (`SpecBoot`/`ProofBoot`/`LinkBoot`, `SpecEntry`, `SpecStart`) |
| power thread | `MachCSL/Power.lean`: `wp_power` (:422) is PROVED over a client `Hboot` (`powerBootRes`, :355). **Nothing discharges `Hboot`**, and **nothing applies Iris adequacy**. The package has `wp_strong_adequacy_gen` (`.lake/packages/iris/Iris/Iris/ProgramLogic/Adequacy.lean:174`), and `MachCSL/Lang.lean:551` has `Language Expr GState Obs Val`. Lean-side deviations already recorded there: no fixed disk-auth lend (no crash layer), no echo window token, no init turn |

**Residual assumed parameters the top must discharge:**
- `DISK_INIT_WM` (`DiskAcc.lean:1375`; a parameter of `VirtioDiskInit`). It is main's
  `__sync_synchronize(); started = 1` edge, i.e. Rocq `StartedInv`.
- bioInit's `bdBss` / `0 ∉ V.cov`. These come from the boot carve (BootCarveMain).

### 1.3 Definitional material already landed that wave 8 consumes

- D8's definitional files, all imported in `Xv6.lean`:
  - `ChildTok` 730 (`myPay`, `genKq`)
  - `FirstTok` 513 (`firstBoot`/`firstDone`/`firstTok`)
  - `SlotGen` 775
  - `UserChildren` 354
  - `WaitInv` 736 (`chFrag` :404) and `WaitInvTies` 808
  - `KillRow` 328
- `UexecSlot` 108: the MINIMAL `Uvis`/`uvisOf`/`tfResumePc` (D17). It defers `tf_resume_gpr`,
  `TfUser` and the Uexec* layer to wave 8.
- `UserPerm` 166, `SbPark` 213, `ForkretRecord` 253 (`ctx_fresh`, `forkret_resume`, `newbornPay`,
  `forkret_record`), `FsImg` 382 (superblock only).
- `SpecKexec`'s `execSlotPre` (:119) and `execAuPre` (:135). Their `_ne` lemmas are deferred (D33).
- MachCSL: `killCred` (`Resources.lean:230`), `CtxMorph` (`CtxLaws.lean:54`), `wireInvAt`, and
  the `ObsTrace` history.

**Absent (Rocq name → nothing in Lean):**
- `park_token` (ParkCap), `park_globals`, `ut_own`/`ut_res` (UsertrapRes)
- `uslot`/`uexec_wp` (UexecRet/UexecWp), `uexecSG` (UexecSG)
- `UserFd`/`ufdG`, `TfUser`, `UsysMemOk`, `SyscParkEnv`, `EnvMorph`, `StartedInv`, `TimerCap`
- `KptExecMap`, `UptTree`/`UptWalkPt`/`UptWalkTramp`/`TransPt`
- `InitBoot` (`init_boot_bundle`), `FsCfgBoot` (`fs_boot_supply`)
- `BootHart`/`BootBridge`/`BootCarve*`/`BootShared`/`BootChain`, `RiscvAdequacy`, `SystemAdequacy`

## 2. syscall() dispatch

### 2.1 Rocq inventory

| file | lines | contents |
|---|---|---|
| SpecSyscall.v | 1155 | header :1–101 explains the abstract env and the four pulled-out families. Pure: `sysc_num`:218, `sysc_sbrk_ok`:238, `sysc_mem_ok`:247, `sysc_pipe_ok`:318, `sysc_fd_ok`:328. Section SyscExec :355–701: `sysc_sys_in`:379, `sysc_sys_out`:413, `sysc_fork_in`:455, `sysc_pay_in`:494, `sysc_fork_out`:526, `sysc_wait_out`:550, `sysc_ch_ok`:584, `sysc_ret_pid`:599, `sysc_exec_out`:686, and `*_ne`/`*_quiet`. `K_syscall = 4 + K_sys_exec`:708. **`wp_syscall_sconf_body`:709–1038** (exit slot = `wp_next … ∧ kstack_closer`). `Module Type SYSCALL`:1040 (`syscall_env`:1059, `_park`:1098, `_world`:1122, `_fsabs_keep`:1131, `_token`:1136) |
| ProofSyscall.v | 8600 | functor over 22 `SYS*` + MYPROC + PRINTK_GEN. Sections: **Vocab** 562–2753 (`sysc_proc_ties`:547, `syscall_env`:912, `syscall_env_park`:980, `sysc_trap_ext_true`:1273, `sysc_table_word`:1324, `sysc_target`:1282, `sysc_arm_pre`:1627, `sysc_exit_ty`:1857, `sysc_epilogue_tail`:1993, iref/bslot split/join, per-callee env builders 2479–2745). **Ret** 2766–3058 (`sysc_ret_tail`). **Arms** 3066–7997 (one `sysc_arm_<name>` per entry, `sysc_dep_*`, `sysc_out_*`, **`sysc_arm_dispatch`:7572** (22-way `decide`), `sysc_fallback`:7659). **Main** 8001–8599 (`wp_syscall_sconf`:8018). The header :1–301 is partly stale |
| LinkSyscall.v | 57 | `SyscallProof SysFork … SysUnlink Myproc PrintkGen`; axiom-free |
| UsysMemOk.v / UsysMemOkSpec.v | 1256 / 322 | the post-row tables over the trapframe word list (`usys_fd_ok`, `usys_pipe_ok`, `usys_sbrk_lazy`, `usys_cwd_ok`). **Needed**: SpecSyscall's rows are defined through them, and UexecExecInst sharpens them |
| SyscParkEnv.v | 168 | `sysc_park_extra`: nextpid lock, `procs_avail`, tickslock, `console_ready_app`. Needed by `syscall_env_park` (fork/userinit), not by the dispatch proof |
| FsSyscalls.v / LinkFsSyscalls.v / FsDurSyscall.v | 576 / 27 / 665 | not needed (friendly wrappers; durability) |

### 2.2 Lean file plan

| file | from | kind | batch |
|---|---|---|---|
| `UsysMemOk.lean` (+ `UsysMemOkSpec.lean`) | UsysMemOk.v, UsysMemOkSpec.v | definitional | 8-0 |
| `SyscallDefs.lean` | SpecSyscall pure part (`sysc_num`, `sysc_*_ok`, `syscallSlots`) | definitional | 8-0 |
| `SyscallEnv.lean` | ProofSyscall Vocab's `syscall_env`/`_park` + SyscParkEnv (D30) | definitional; needs 8-P's statements | 8-1 |
| `SpecSyscall.lean` | SpecSyscall.v | Spec | 8-1 |
| `SyscallTable.lean` | Vocab's `sysc_table_word`/`sysc_target`/bltu lemmas over `.rodata` | stage | 8-1 |
| `SyscallRet.lean` | §SyscallRet | stage | 8-1 |
| `SyscallArmsProc.lean` | arms fork, exit, wait, kill, getpid, sbrk, pause, uptime (+ D31 adapters) | stage | 8-2 |
| `SyscallArmsFd.lean` | arms pipe, dup, close, fstat, read, write | stage | 8-2 |
| `SyscallArmsPath.lean` | arms open, mknod, unlink, link, mkdir, chdir | stage | 8-2 |
| `SyscallArmsExec.lean` | arm exec, `sysc_fallback` (printk), `sysc_arm_dispatch` | stage | 8-2 |
| `ProofSyscall.lean`, `LinkSyscall.lean` | SyscallMain | seal/link | 8-3 |

The arms files may be split further per the few-seconds rule; they stay one function's stages.

## 3. The trap loop: usertrap, prepare_return, uservec, userret, the closed loop

### 3.1 Rocq inventory (all on SystemAdequacy's path)

Path: `SystemAdequacy` → `LinkUserinit` → `LinkForkretParkPaid` → `LinkForkret` →
`LinkUserretClosed` → {`LinkUsertrap`, `LinkUservec`, `LinkUserret`}.

| group | files (lines) | key items |
|---|---|---|
| usertrap | SpecUsertrap 2018; ProofUsertrap 1487; ProofUsertrapArms 1543; ProofUsertrapSys 1236; ProofUsertrapTail 1979; ProofUsertrapParts 66; UsertrapAux 154; LinkUsertrap 28 | `wp_usertrap_body`:1641, `usertrap_post`:1448, `ut_round`:223, `ut_sys_in/out`:466/498, `ut_exec_out`:519, `ut_fork_out`:558, `USERTRAP_RES`:1750 (~20 open/close params), `USERTRAP`:2006. Link: `UsertrapProof Syscall PrintkGen Myproc Killed Setkilled Devintr Vmfault Yield PrepareReturn Kexit Kernelvec`. `K_usertrap = 4 + kv_frame_slots + (4 + K_sys_exec)` (UsertrapRes:122) |
| the residue | UsertrapRes 2460; UtResFits 265 | `ut_trap`:158, `ut_trap_parked`:217, `ut_names`:477, `ut_caps`:656, **`ut_own`:801** (bslots, fd/iref spares, `proc_priv`, `fd_frags`, `ch_frag`), `ut_env`:853, **`ut_res`:1009**, `park_globals`:2042, `park_env`:2238, `ut_park_intro_body`:2262 |
| prepare_return | Spec 300; Proof 1064; Parts 310; Link 6 | **Lean sealed.** Rocq's post also returns the ¼ SIE quarter (D27) |
| uservec | SpecUservec 581; ProofUservec 2072; UservecDefs 509; UservecPt 804; UservecExitPt 553; LinkUservec 9 | `wp_uservec_pt_body`:411, `uservec_post`:212. `UservecProof (UT : USERTRAP_PARK) (UR : USERRET)`: 44 instructions, then usertrap, then userret |
| userret | SpecUserret 230; ProofUserret 1285; UserretDefs 795; UserretPt 1371; UserretEntryPt 446; LinkUserret 7 | `wp_userret_pt_body`:82: 38 instructions, the user satp, `sret` to U |
| the closed loop | SpecUserretClosed 245; ProofUserretClosed 1077; LinkUserretClosed 30; UserretUser 380 (side lane) | **`stvec_handler_loop`:280, `iLöb`:330**; `wp_userret_closed_body`:133. Link: `UserretClosedProof Userret (Uservec Usertrap Userret) (UexecGen UserProof)` |
| U→S bridges | UserTrap 1577; UserKernelBridge 207; TfUser 85; TransPt 1826; UptTree 921; UptWalkPt 751; UptWalkTramp 456; KptExecMap 177 | the trap out of U (`utrap_ms`), `tf_ueq`, the trampoline fetch through both tables |
| the slot fixpoints | UexecWp 202 (`uexec_wp := fixpoint uexec_F`:153); ProofUexecWp 106 (`uexec_wp_gen`:58, from USER); UexecRet 2683 (**`uslot := fixpoint uslot_F`:1897**, `uexec_ret`:1898, `ukill_cred_at`:1589); UexecSG 722; UexecExecInst 1560 (`exec_sbundle`:466, `xv6_sbundle`:525, `uexecSG_xv6`:1038, `exec_sbundle_ne` uses `sys_exec_au_pre_ne` :480); UexecExecMint 331 (`uslot_mint`:259); UexecApply 1537; UexecRound 197; UexecCond 408; UexecSlot 378 (Lean has the minimal part) | the kernel is parametric in the slot. The generic application mints it once (`uslot_mint` + `uexec_wp_gen`) |
| user-exec contract | SpecUser 81; ProofUser 81 (+ ~84k lines of tower in the cone) | `wp_user_exec_closed_body`: `hw_config -∗ minstret_inv -∗ wire_inv -∗ user_inv C pt Rut -∗ ▷ stvec_handler_wp C pt Rut -∗ WP Loop` (D24) |
| descriptor view | UserFd 818 | `ufd_map`:93, `ufdG`:213 (D29) |

### 3.2 Machine support Lean lacks (MachCSL)

Present: `WpSmodeSret` (S→S only, `sretMs`), `WpTrap` (a supervisor interrupt taken in S only),
`WpSmodeSatp` (Bare→Kpt at kvminithart only), `WpSmodeSfence`, `WpSmodeStvec`. `KTier` =
`bare | kpt` (`Ctx.lean:152`).

Wave 8 needs the following even with `USER` assumed (D24(a)):
1. **Satp switch to a user root and back, with the fetch continuing through the trampoline
   page.** The page is mapped at `TRAMPOLINE` in both tables (Rocq UptWalkTramp/TransPt/
   UserretEntryPt/UservecExitPt). This needs a user-table tier or an explicit "fetch at
   TRAMPOLINE under root r" rule.
2. **`csrrw sscratch` leaves.**
3. **`sret` with `SPP = U`**, landing in `user_inv` (Rocq `usret_*`, UserretPt:606+).
4. **The `user_trap_frame` state at uservec's first instruction**, as the precondition shape
   (supervisor, pc = stvec base, trap CSRs written, same table). Only USER's PROOF needs the U→S
   trap step itself (Rocq UserTrap.v); with D24(a) it is part of the assumed interface.

These are MachCSL edits. They run in a worktree, as the invasive batches of the device waves did.

### 3.3 Lean file plan

| file | from | batch |
|---|---|---|
| `TfUser.lean`; `UexecSlot.lean` (append `tfResumeGpr*`, worktree) | TfUser.v; UexecSlot.v remainder | 8-0 |
| `UserFd.lean` | UserFd.v (D29) | 8-0 |
| `SpecUser.lean` | SpecUser.v (the `USER` structure; D24) | 8-0 |
| `UexecWp.lean`, `UexecSG.lean`, `UexecRet.lean` (`uslot` fixpoint via iris-lean `fixpoint`/`Contractive`; `wp.pre` in `WeakestPre.lean:87` is the precedent), `UexecRound.lean`, `UexecApply.lean`, `UexecCond.lean`, `ProofUexecWp.lean` (seal of `uexec_wp_gen` over `USER`) | Uexec*.v | 8-0 / 8-1 (UexecRet needs UserFd + ChildTok) |
| `KexecNe.lean` (+ `SysExecNe`) | SpecKexec :970–1000, SpecSysExec :276–310 (D33) | 8-1, after sys_exec lands |
| `UexecExecInst.lean`, `UexecExecMint.lean` | UexecExecInst.v, UexecExecMint.v | 8-3, after the 9 AU entries' statements |
| MachCSL: `WpSmodeSretU.lean`, `WpSmodeSatpU.lean` (trampoline fetch), `WpSmodeSscratch.lean`; Xv6: `UptTree`/`UptWalkTramp`/`TransPt` subset | §3.2 | 8-M (worktree) |
| `UsertrapRes.lean` (D27 restatement) | UsertrapRes.v, UtResFits.v | 8-2, after 8-P |
| `SpecUsertrap.lean`; stages `UsertrapArms`, `UsertrapSys`, `UsertrapTail`, `UsertrapParts`; `ProofUsertrap.lean`, `LinkUsertrap.lean` | usertrap group | 8-3 (Spec in 8-2) |
| `SpecUservec.lean`, `UservecDefs`, `UservecPt`, `UservecExitPt`, `ProofUservec`, `LinkUservec` | uservec group | 8-3, after 8-M |
| `SpecUserret.lean`, `UserretDefs`, `UserretPt`, `UserretEntryPt`, `ProofUserret`, `LinkUserret` | userret group | 8-3, after 8-M |
| `SpecUserretClosed.lean`, `ProofUserretClosed.lean` (the Löb), `LinkUserretClosed.lean` | closed loop | 8-4 |

## 4. forkret, the park, and the knot

### 4.1 Rocq inventory

| file | lines | key items |
|---|---|---|
| SpecForkret.v | 553 | `forkret_closer`:290, `wp_forkret_gen_body`:399 |
| SpecForkretParkPaid.v | 391 | `forkret_park_pkg`:143, `forkret_park_paid_body`:284, `FORKRET_PARK_PAID` (with `park_token_intro`). `steady : bool`: steady carries the whole `proc_priv` plus `first_done`; boot carries `proc_priv_nocwd ∗ cwd_ref_at ∗ first_boot ∗ gen_kq … ∗ my_pay … ∗ gen_halves_priv ∗ ½ p_xstate`, with payload `init_boot_bundle ∗ cons_reader` |
| SpecForkretPark.v | 132 | the old assumed park. **Do not port** (gunk) |
| ProofForkret.v | 2331 | `fkr_tail`:219, `fkr_boot`:927 (fsinit, `first = 0` store, kexec("/init") at `fkr_init_path` 0x80007188 (Rocq address; re-derive), panic tail), `wp_forkret`:1927 |
| ProofForkretPark.v / ProofForkretParts.v | 476 / 422 | `forkret_park_paid`:236, **`park_token_intro`:441**; address facts |
| ParkCap.v | 696 | **`park_token γs`**, a guarded fixpoint (both self-occurrences under `▷`). kfork consumes it from `syscall_env`; only main's cone proves it |
| EnvMorph.v | 131 | `CtxMorph` for the parked environment bundles (D25) |
| FdPark.v | 537 | pure `fdst_park`/`fdv_park`, "currently vacuous" per its header. **Skip** unless a consumer appears |
| TimerCap.v | 113 | `timer_cap`, a row of the park closer |
| LinkForkret.v / LinkForkretParkPaid.v | 20 / 10 | `ForkretProof Myproc Release PrepareReturn Fsinit Kexec Panic UserretClosedD`; `ForkretParkProof Forkret` |

### 4.2 Lean plan (D25)

- **8-0:** `EnvMorph.lean` plus the `fs_ready_morph`/`fs_sb_cells_morph` instances. These are
  new-file instances where possible; an instance that must sit beside its predicate is a landed
  edit (worktree). Also `TimerCap.lean`.
- **8-P (worktree, landed edits):**
  - `ForkretRecord`/`SpecForkret` park the whole `procPrivFd` ∗ `fdFrags` (steady) or the boot arm.
  - `SpecKfork`/`ProofKfork*`/`SpecSysFork`/`ProofSysFork`/`SpecUserinit`/`ProofUserinit`/
    `LinkKfork`/`LinkUserinit` replace `[ForkretIs]` with a `park_token` premise, plus the D26
    rows.
- **8-2:** `ParkCap.lean` (needs UsertrapRes, UexecRet, UserFd, InitBoot).
- **8-4:** `SpecForkret.lean` is re-stated as Rocq's `wp_forkret_gen_body`. Then come
  `SpecForkretParkPaid.lean`, the stages `ForkretParts`/`ForkretTail`/`ForkretBoot`,
  `ProofForkret.lean`, `ProofForkretPark.lean` (the `park_token_intro` seal), and the Links.
  **`ForkretIs` is deleted.**

## 5. main and the boot chain

### 5.1 Rocq inventory

| file | lines | key items |
|---|---|---|
| SpecMain.v / ProofMain.v | 861 / 2656 | `main_locks_raw`:247, `main_sb_raw`:298, `main_globals_raw`:316, `main_hart_raw`:474, **`wp_main_boot_sconf_body`:481** (diverges into `WP Loop`). Call groups `mn_boot_entry`:255, `mn_grp_printk`:424, `mn_grp_kvm`:997, `mn_grp_trap`:1402, `mn_grp_fs`:1568, `mn_grp_started`:2203; seal :2412 |
| SpecMainSecondary.v / ProofMainSecondary.v | 256 / 846 | `ms_entry`, `ms_spin` (on `started`), `ms_printk`, `ms_inithart_sched`; seal :796 |
| StartedInv.v | 649 | `started_body P := ∃v, started ↦₄ v ∗ (⌜v=0⌝ ∨ P)`, `started_alloc`:182, `started_store_open`:229, `started_inv_claim`:252. **It discharges Lean's `DISK_INIT_WM`** |
| InitBoot.v | 166 | `init_boot_bundle`:134, `init_boot_bundle_triv`:148 (generic: `uslot_mint` + `uexec_wp_gen`) |
| FsCfgBoot.v / FsBoot.v / DiskBoot.v / IcacheBoot.v | 765 / 531 / 357 / 1704 | `fs_boot_supply`:715 (drop `Rspent`/`Pb`/crash rows per D11); IcacheBoot is **already ported** (IcacheBoot{Decode,Region,Table}) |
| BootHart / BootBridge / BootConfig / BootReset / ColdBoot / PowerBoot | 440 / 529 / 662 / 878 / 409 / 195 | per-hart geometry and reset residue; M-mode → sconf bridge; reset config; `boot_gstate` reducibility witness |
| BootCarve / BootCarveMain | 1943 / 2424 | memory carve into text, data, stacks, and main's precondition vocabulary (discharges bioInit's `bdBss`) |
| BootShared.v | 2428 | per-era allocation: `boot_bss_carve`:497, `power_boot_res_unpack`:1373, `boot_hart_pre`:1544, **`boot_shared_alloc`:1605** |
| BootChain.v | 534 | `boot_entry_bridge`:114, `boot_hart_secondary`:274, **`boot_hart_primary`:329** |
| RiscvAdequacy.v | 2154 | `power_boot_res`:461, `wp_power_loop`:690 (**Lean has `wp_power`**), `boot_fixedGS`:1229, **`riscv_power_adequacy`:1593**, `riscv_trace_adequacy`:2037 |
| SystemAdequacy.v | 2509 | `xv6_boot_era`:518, `init_boot_of_triv`:1114, **`xv6_power_adequacy_gen`:1138**, `xv6_power_adequacy`:1728, `xv6_trace_adequacy`:1827, `xv6Σ`:2060, corollaries :2253–2442 |
| App*/AppDur/UInitBoot*/Uk*Main | — | application lane. **Out** (D23) |
| SystemAssumptions.v | 73 | the audit. Lean analogue: `#print axioms` on the final theorem, expected to be the Lean core axioms plus `USER` as a hypothesis (D24) |

### 5.2 Lean file plan

| file | batch |
|---|---|
| `StartedInv.lean` | 8-0 |
| `InitBoot.lean` (generic bundle only) | 8-3 (needs UexecExecMint) |
| `FsCfgBoot.lean` (D11-trimmed `fsBootSupply`), `FsBoot.lean`, `DiskBoot.lean` | 8-1 |
| `SpecMain.lean`, stages `MainPrintk`/`MainKvm`/`MainTrap`/`MainFs`/`MainStarted`, `ProofMain.lean`, `LinkMain.lean` (retires `DISK_INIT_WM`) | Spec 8-2; proof 8-4 (needs the `park_token_intro` seal through userinit) |
| `SpecMainSecondary.lean`, `ProofMainSecondary.lean`, `LinkMainSecondary.lean` | 8-2 (depends only on sealed callees and StartedInv) |
| `BootHart`, `BootBridge`, `BootConfig`, `BootReset`, `PowerBoot` | 8-1 |
| `BootCarve`, `BootCarveMain` | 8-2 (memory-heavy: run under `ulimit -v 40000000`) |
| `BootShared.lean`, `BootChain.lean` | 8-4 |
| MachCSL `Adequacy.lean` (RiscvAdequacy analogue: `wp_strong_adequacy_gen` on `Expr.power`, over `wp_power`) | 8-1 (independent of Xv6) |
| `SystemAdequacy.lean` (D23, D34) | 8-5 |

## 6. Deviations already accumulated that wave 8 must confront

"Grep" = where the flag lives. "Top needs fix?" = whether Rocq's top-level chain consumes the
missing piece.

| # | deviation | grep | top needs fix? | action |
|---|---|---|---|---|
| 1 | **Newborn record drops the child's fd table, fragments and cwd ref** (no `CtxMorph` for file-layer predicates) | SpecForkret.lean:43; SpecKfork.lean:77 (dev 2); SpecUserinit.lean:39; FsReady dev 8 | **YES**. `ut_own` needs `proc_priv` + `fd_frags` for the child's first syscall | D25, batch 8-P |
| 2 | **`ForkretIs` assumed class** | SpecForkret.lean:97; 11 consumers | **YES**. It must become `park_token` plus a proved forkret | D25 |
| 3 | **Block's D8 conjuncts absent** (`first_tok`, `∃Q gen_kq ∗ my_pay`, `½ p_xstate`, `gen_halves_priv`, `GenId`) | ProcInv dev 2, ProcPrivAcc dev 1, FdTable:42, every `SpecSys*` "PROCESS LAYER" dev 4, SpecKexec dev 2 | **YES**. forkret branches on `first_tok`, and uslot/exit/exec pay through `my_pay` | in flight (D8 wiring); must land before 8-P |
| 4 | **kfork lacks the generation machinery** (`child_tok`/`Q`, `ch_frag`, `first_tok`, kill wand, `uslot`/`park_world`/`park_token`) | SpecKfork.lean dev 3 | **YES** (`sysc_fork_in/out`, child's slot) | D26, 8-P |
| 5 | **sys_fork/sys_wait lack `chFrag`; sys_exit has only `chFrag … ∅` and no `myPay`/`initIdent`; sys_kill lacks `killCred`** | SpecSysFork/Wait/Exit/Kill (survey §1.1) | **YES** (dispatch post rows `sysc_ch_ok`/`sysc_wait_out`/`sysc_ret_pid`; `uslot_mint` takes `□ kill_cred`) | D26, 8-P |
| 6 | **userinit lacks the `first_*` deposit, `init_pid_tok`, the six park rows, the exec bundle** | SpecUserinit.lean:39–45 | **YES** (forkret's boot arm; `init_boot_bundle`) | 8-P |
| 7 | kfork mints the child's descriptor ghost at the copy loop, not allocproc | SpecKfork dev 1 | no (internal) | keep, recorded |
| 8 | **U = (V, M)**: Rocq `ustate` is the Lean pair; `uvisOf` takes `(V, M)` | UexecSlot dev 1, SpecKexec dev 2, ProofKexec dev 2, ProcPrivAcc dev 3 | no (representation) | keep. Every wave-8 `ustate` binder is `V M`; `urun_eq`/`uround_ok` are stated on pairs |
| 9 | **No SIE ghost** | SpecPrepareReturn.lean:56–60 | no | D27 |
| 10 | **sie-pinned `uartintr`** (plus devintr/kerneltrap at `false`) | SpecUartintr.lean:28 | no | D28 |
| 11 | `ufdG` binder dropped | SpecKexec dev 5, UexecSlot header (D17) | **YES** (uslot, the mint, `Hufd`) | D29 |
| 12 | `exec_slot_pre_ne`/`exec_au_pre_ne` deferred | SpecKexec dev 5 | **YES** (uslot contractivity) | D33 |
| 13 | Crash layer dropped | D11; SpecEndOp/SpecIreclaim/FirstTok dev 2 | only for the durability corollary | D23 |
| 14 | No application layer (`fsabs_env`/`app_inv` dropped from `first_done`) | FirstTok dev 1 | no, at the generic application | D23 |
| 15 | `procPrivCwd` split instead of cwd inside the block | ProcInv dev 1 | no (frame-stronger; the dispatch holds the whole block) | keep |
| 16 | `DISK_INIT_WM` parameter on VirtioDiskInit | DiskAcc.lean:1375 | **YES** (a link parameter left on the final theorem) | StartedInv in main (8-4) |
| 17 | bioInit's `bdBss` / `0 ∉ V.cov` premises | BioInit.lean | **YES** | BootCarveMain (8-2) |
| 18 | Stale "ASSUMED" header on SpecKerneltrap | SpecKerneltrap.lean:1–5 | no | fix the header text in any 8-M worktree commit (report old → new) |
| 19 | SpecUserinit's `hsie` pin (allocproc's post does not return `sieArm`) | SpecUserinit.lean:30 | no (main calls it with interrupts off) | keep |

## 7. Dependency DAG

✓ = landed, ◐ = in flight, ★ = absent.

```
D8 block wiring ◐ ──► 8-P (park/kfork/userinit/sys_fork/wait/exit/kill re-specs) ──┐
sys_read ◐, sys_write ◐, sys_exec ◐ ──► KexecNe/SysExecNe ──────────────────────────┤
8-0 defs (UsysMemOk, SyscallDefs, TfUser, UserFd, SpecUser, UexecWp/SG, StartedInv, │
          EnvMorph, TimerCap) ─────────────────────────────────────────────────────┤
                                                                                    ▼
SyscallEnv ─► SpecSyscall ─► Syscall{Table,Ret,Arms*} ─► ProofSyscall/LinkSyscall
UexecRet(uslot) ─► UsertrapRes ─► SpecUsertrap ─► Usertrap stages ─► ProofUsertrap ◄─ LinkSyscall
8-M MachCSL (satp-U, sret-U, sscratch) ─► Uservec*, Userret* ─► SpecUserretClosed ─► ProofUserretClosed (Löb)
UexecExecInst/Mint ─► InitBoot ─► ParkCap ─► SpecForkretParkPaid ─► ProofForkret(+Park) ─► park_token_intro
LinkMain ◄─ userinit(8-P) + park_token_intro + StartedInv;  MainSecondary ◄─ ✓ callees + StartedInv
MachCSL Adequacy ─┐
Boot{Hart,Bridge,Config,Reset,Carve*,Shared,Chain} ─► SystemAdequacy (USER param, Himg premise)
```

## 8. Agent split (disjoint files)

### 8.0 Batch 8-0: definitional, START NOW (main tree; no decision needed except the D24/D29 statement shapes)

| agent | files | notes |
|---|---|---|
| W8-A | `UsysMemOk.lean`, `UsysMemOkSpec.lean`, `SyscallDefs.lean` | pure; over `V.tf` words |
| W8-B | `StartedInv.lean`, `TimerCap.lean` | StartedInv then retires `DISK_INIT_WM` in 8-4 |
| W8-C | `TfUser.lean`, `UserFd.lean`, `SpecUser.lean`, `UexecWp.lean`, `UexecSG.lean` | D24/D29 shapes: post the statement plan first |
| W8-D | `EnvMorph.lean` (+ new-file `CtxMorph` instances) | report which instances must sit beside their predicate (landed edits → 8-P) |

### 8.1 Batch 8-P: process-layer re-align (ONE worktree, serial; after D8's block lands)

One agent, because the edits overlap: ForkretRecord, SpecForkret (record half), SpecKfork/
ProofKfork*/LinkKfork, SpecSysFork/ProofSysFork, SpecSysWait/ProofSysWait, SpecSysExit/
ProofSysExit, SpecSysKill/ProofSysKill, SpecUserinit/ProofUserinit/LinkUserinit, FsReady
(`fsReady_morph`). Contract changes are reported old → new. `ForkretIs` stays until 8-4 retires it,
but the park rows are Rocq's from here on.

### 8.2 Batch 8-1: after 8-0 (parallel; main tree unless noted)

| agent | files |
|---|---|
| W8-E | `SyscallEnv.lean`, `SpecSyscall.lean`, `SyscallTable.lean`, `SyscallRet.lean` (Spec after 8-P's statements are frozen) |
| W8-F | `UexecRet.lean`, `UexecRound.lean`, `UexecApply.lean`, `UexecCond.lean`, `ProofUexecWp.lean` |
| W8-M (worktree) | MachCSL `WpSmodeSretU`, `WpSmodeSatpU`, `WpSmodeSscratch`; Xv6 `UptTree`/`UptWalkTramp`/`TransPt` subset |
| W8-G | MachCSL `Adequacy.lean` (Iris adequacy on `Expr.power`) |
| W8-H | `BootHart`, `BootBridge`, `BootConfig`, `BootReset`, `PowerBoot`, `FsCfgBoot`, `FsBoot`, `DiskBoot` |
| W8-X | `KexecNe.lean`, `SysExecNe.lean` (after sys_exec seals) |

### 8.3 Batch 8-2

| agent | files |
|---|---|
| W8-S1 | `SyscallArmsProc.lean` |
| W8-S2 | `SyscallArmsFd.lean` (after sys_read/sys_write seal) |
| W8-S3 | `SyscallArmsPath.lean` |
| W8-S4 | `SyscallArmsExec.lean` (after W8-X) |
| W8-R | `UsertrapRes.lean`, `UtResFits.lean`, `SpecUsertrap.lean` |
| W8-I | `SpecMain.lean`, `SpecMainSecondary.lean`, `ProofMainSecondary.lean`, `LinkMainSecondary.lean` |
| W8-J | `BootCarve.lean`, `BootCarveMain.lean` (bounded memory) |

### 8.4 Batch 8-3

| agent | files |
|---|---|
| W8-E2 | `ProofSyscall.lean`, `LinkSyscall.lean` |
| W8-T | `UsertrapArms`, `UsertrapSys`, `UsertrapTail`, `UsertrapParts`, `ProofUsertrap`, `LinkUsertrap` |
| W8-U | `SpecUservec`, `UservecDefs`, `UservecPt`, `UservecExitPt`, `ProofUservec`, `LinkUservec` |
| W8-V | `SpecUserret`, `UserretDefs`, `UserretPt`, `UserretEntryPt`, `ProofUserret`, `LinkUserret` |
| W8-K | `UexecExecInst.lean`, `UexecExecMint.lean`, `InitBoot.lean` |

### 8.5 Batch 8-4

| agent | files |
|---|---|
| W8-L | `SpecUserretClosed`, `ProofUserretClosed`, `LinkUserretClosed` |
| W8-P2 | `ParkCap`, `SpecForkretParkPaid`, `SpecForkret` (Rocq form), the Forkret stages, `ProofForkret`, `ProofForkretPark`, the Links; deletes `ForkretIs` (worktree: it edits the consumers' binders) |
| W8-N | `MainPrintk`/`MainKvm`/`MainTrap`/`MainFs`/`MainStarted`, `ProofMain`, `LinkMain` |

### 8.6 Batch 8-5

`BootShared.lean`, `BootChain.lean`, `SystemAdequacy.lean`. The final theorem is followed by
`#print axioms`.

## 9. Risks

1. **The size of the U-loop.** The kernel side of the loop (usertrap + uservec + userret + closed
   + Uexec*) is about 25k Rocq lines, before the ~84k of D24's tower. Plan the stage splits the
   way the disk and kexec waves were planned: one vocabulary file, then per-phase files.
2. **Contractivity in Lean.** `uslot_F` and `park_token` need `OFE.Contractive` proofs over
   `IProp` families. iris-lean's `wp.pre` contractivity (`WeakestPre.lean:87–132`) is the only
   in-tree precedent. `exec_sbundle_ne` needs `NonExpansive` of the AU bundles in `S`. Budget a
   spike in W8-F before committing to the Rocq shape.
3. **8-P churn.** It re-opens kfork (3308-line proof) and five sys_* proofs. Keep one agent, and
   run the full `lake build Xv6 MachCSL` after each commit.
4. **MachCSL U-tier (8-M) is invasive.** It may touch `KTier` and `SConfPhys`. Isolate it in a
   worktree and merge before the uservec/userret stages start.
5. **Boot carve memory.** BootCarve/BootCarveMain enumerate kernel-sized data (memory:
   lean-runaway-memory). Run them under `ulimit -v 40000000; timeout 300`.
6. **The dispatch's 22-way arm.** Rocq ends in `exfalso; lia` after a `decide`. In Lean, keep
   each arm a separate theorem so no single `decide` over the table blows the few-seconds budget.
7. **Stale Rocq headers.** ProofSyscall :1–301 says read/write are unwired. LinkUsertrap says
   "not reachable from SystemAdequacy". LinkMain lists assumed callees. All three are out of date:
   trust the code, not the header.

## 10. Report (per agent)

As in fs7b §11: files/commits, contract shapes (old → new for edits), the Rocq lemmas mirrored,
deviations (process-layer ones flagged), cleanups with checked uses, reused names, what's left.
