# Lean xv6 port — coordinator status (RESUME HERE)

Last updated: 2026-09-25, origin/lean-v2 = e707b09be (full `lake build Xv6 MachCSL` 1587 jobs, layering ok).

A new coordinator session should read, in order: this file; `notes/coord/wave7b_prompt.txt`
(the binding rules every agent prompt starts from); `notes/briefs/wave8_top.md` and
`notes/briefs/crash_layer.md` (USER RULINGS at the top of each are final);
`notes/coord/pending_edits.txt` (queued cleanups and deferrals).

## ROCQ SOURCE (2026-09-25): use /shared/xv6rocq-main (detached worktree of Rocq origin/main,
f22c1c9ca; refresh with `git -C /shared/xv6rocq fetch && git -C /shared/xv6rocq-main checkout --detach origin/main`).
NOT /shared/xv6rocq: that checkout is the user's stale WIP branch `sail-upstream-bump` (forked from main
Sept 16, 1466 commits behind). Everything landed before 2026-09-25 was ported against that Sept-16 base.
User ruling: bump the kernel now (to xv6 verified 3e9926ea = Rocq main's XV6_REV); AUDIT the landed
contracts against Rocq main LATER (after wave 8) -> notes/briefs/rocq_drift.md (to be written).

## CURRENT USER DIRECTIVE (2026-09-25)
Do NOT start new subagents; only land results from the agents already running (usage limits are
near). Resume launching the NEXT list only when the user says so.

## Workflow (how every result lands)
- Main-tree agents write new files in /shared/lean-xv6 (no git, no Xv6.lean edits); the
  coordinator appends `import Xv6.<M>` to Xv6.lean, commits, then VERIFIES in the clean worktree
  `.claude/worktrees/verify` (`git -C … status` first; `git checkout --detach <sha>`;
  `timeout 3500 lake build Xv6 MachCSL`; `tools/check_layering.sh`) and pushes `<sha>:lean-v2`.
- Worktree agents commit on `worktree-agent-<id>`; coordinator checks it is based on the current
  tip (else cherry-picks onto it), verifies in `verify`, pushes, `git merge --ff-only` the main tree.
- Tell main-tree agents explicitly: edit only /shared/lean-xv6, never files under
  .claude/worktrees/ (the coordinator's cd into `verify` leaks into agents' environment).
- `notes/coord/d8_binder_sweep.py` is NOT idempotent: only on never-swept files, explicit list.
- If an agent is killed (API limit), resume it with SendMessage (same session) or relaunch
  with the same brief + "resume: files X exist, finish Y".

## Done (all pushed)
- All of fs.c, log.c, bio.c, virtio, uart/console/plic, pipes, file layer, kalloc/vm, proc,
  trap (kerneltrap/devintr/prepare_return), kexec, and ALL 22 sys_* (sys_exec sealed 46d43a76c).
  182/194 kernel text symbols have Spec/Proof/Link. Missing: syscall, usertrap, forkret
  (ForkretIs assumed), main; userret DONE (9afea77e3), uservec DONE (2ef4ec0f0; continuation abstract at
  usertrap entry; caller must re-form whole-page kernel stack at kernel_sp — W8-R/W8-L obligation).
- Wave 8 so far: W8-A/B (UsysMemOk, SyscallDefs, StartedInv), W8-C (TfUser, UserFd, UexecSG,
  UserExec, SpecUser, UexecWp), W8-D (CtxAmb, FileMorph, FsReadyMorph, EnvMorph), W8-F
  (UexecRet/Round/Apply/Cond, ProofUexecWp), W8-G (MachCSL/Adequacy), W8-H (Boot*, DiskBoot,
  FsBoot), W8-J (BootCarve, BootCarveMain), W8-M (MachCSL user-mode rules + UptTree/TransPt/
  UserKernelBridge), W8-V (userret), W8-X (KexecNe, SysExecNe).
- Crash layer (D23 reversal of D11): CA/CB (FsState, FsDur*), CC/CD (FsCrashPure/Sector,
  FsBootParams, FsCfgBoot), CN (FsImg* chain + FsImgBridge), CE (FsDurSnap*), CF (FsDurAlloc,
  FsDurImg), CM (MachCSL fixed disk, crashInv, CrashPermInv, DiskPermit, WpDevDisk D40 lend,
  Power/Adequacy hooks), CG (FsCrash*, FsFlushedCore, AppDur, LogSnapLaw, LogMirrorHalf).

## IN FLIGHT at checkpoint time (check each; relaunch if dead)
| work | where | state / what to do with result |
|---|---|---|
| W7-C: rest of D8 (block wiring, first_tok/GenId conjuncts, deviations 1 & 3) | branch `worktree-agent-aa0189482f79f21cd` | long-running; when done: rebase on tip, verify, push. UNBLOCKS 8-P. |
| CH crash C-2a: disk driver/bwrite/bread on crashPermInv (replaces TEMP premise `diskDrainEnv` in Xv6/DiskInv.lean) | branch `worktree-agent-a48f64363af3b49d9` | verify+push; unblocks C-2b (CI). |
| Camera fixes: drop FsBytesG.gmBytes → MachFixedGS.diskImgG; add Xv6G.mlHistG : MonoListG GF BlockMap; FileG.gmUfdG (D29) | branch `worktree-agent-a180d1701b15e8512` | verify+push. |
| MachCSL boot image tie: Hboot learns image = g₀.image; riscvPowerAdequacy takes BootImage-style premise; + report on emitting .data in dump_kernel.py | branch `worktree-agent-a18ac9de1787aa490` | verify+push. |
| CJ crash C-3: FsCollect*, FsCollectAll | main tree, untracked Xv6/FsCollect* | commit+verify+push. |

## NEXT (dependency order)
1. 8-P (ONE serial worktree, after W7-C lands): Rocq-literal process-layer re-align (D25/D26):
   remaining D8 conjuncts in sys_fork/wait/exit/kill, kfork, userinit; `PipeInvDefs.pipeSlackAt`
   + `isPipe_morph` (from W8-D report, exact edit in notes/coord/pending_edits.txt); newborn keeps
   fd table + cwd; `procPrivFd ⊢ procPrivNoctxAt ∗ (… -∗ procPrivFd)` accessor (D31);
   W8-F's landed-file moves (tfResumeGpr* → UexecSlot, UexecRet §0 → UserExec, exitXs → ProcGeom).
2. W8-E (SyscallEnv concrete per D30, SpecSyscall eb-generic D32, SyscallTable, SyscallRet),
   then 8-2: W8-S1..S4 syscall arms (adapters D31; add sync arm D44 after C-2b), W8-R
   (UsertrapRes as KCtx facts D27, UtResFits, SpecUsertrap), W8-I (SpecMain + secondary; needs
   crash statements); 8-3: W8-E2 (ProofSyscall/Link), W8-T (usertrap), W8-K (UexecExecInst/
   Mint, InitBoot); 8-4: W8-L (userret closed loop; supplies trampoline kmapAt claim), W8-P2
   (ParkCap, forkret Rocq form, delete ForkretIs; worktree), W8-N (main); 8-5: BootShared,
   BootChain, SystemAdequacy + `#print axioms`.
3. Crash: C-2b CI (one serial worktree after CH: LogInv/LogDefs rows, write_head, install_trans,
   log_write, begin_op, end_op (hardest), initlog, sys_sync receipt D44, BallocBzero); C-4 CK
   (worktree after CI+CJ+8-P: fsReady seam/cert D38, FirstTok rows, fsinit drop hhdr0 D42,
   ireclaim, call lemmas); C-5 CL (FsCfgSnap) then BootShared/SystemAdequacy crash wiring.
4. Deferred to wave 9 (user rulings): user-mode machine layer (D24; USER is a parameter now),
   BootReset (reset table is a trusted assumption until then), uptWf G=0 on user leaves.
5. Big cleanups queued (notes/coord/pending_edits.txt): Rocq-literal block for the user-copy
   chain (~45 files); T1 short-write reason via either_copyin (~12 files).

## User rulings summary
D1–D22 (fs waves; in fs7/fs7b briefs). D23 full Rocq theorem incl. crash; D24 USER parameter,
user mode wave 9; D25/26/29 approved; D27 KCtx index form (no SIE ghost); D28 accept sie=false
uartintr; D30 concrete syscallEnv; D31 dispatch adapters; D32 syscall eb-generic; D33 KexecNe
file; D34 Himg premise; D35 crash fully Rocq-literal; D36–D45 approved; BootReset → wave 9.
Standing rules: Rocq is the authority (clean up gunk only with full picture); one function per
Spec/Proof/Link triple; one capacity instance per camera; eb-generic contracts; full root build
before every push; keep the agent pipeline full.
