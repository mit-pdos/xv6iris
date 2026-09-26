# Lean xv6 port — coordinator status (RESUME HERE)

MILESTONE 2026-09-26 (origin/lean-v2 = 455450293): **the xv6 system theorem is proved.**
`Xv6.xv6FsAdequacy_xv6GF : USER → g.gen = 0 → g.pow = false → diskOf g.m.devs = fsImgDisk → NSteps … →
 (∀ threads reducible) ∧ xv6TracePure fsimgCov fsimgSb.sbLogstart g2`
at the concrete functor list xv6GF and the literal mkfs fs.img (Himg discharged by kernel decide), kernel image a
language constant (D47). Axioms: 6 Sail externs + propext/Classical.choice/Quot.sound + 416 bv_decide certs
(notes/adequacy_axioms_baseline.md). Every kernel function proved and linked. Crash durability (D23) included.

USER RULING 2026-09-26: apply build parallelism NOW (quiet tree); THEN bump the kernel to xv6 7b2c1b1b (seccomp: new sys_seccomp, per-proc syscall mask; Rocq main's XV6_REV); prove USER and union adequacy IN PARALLEL (surveys -> notes/briefs/user_layer.md, notes/briefs/union.md).
IN FLIGHT (2026-09-26): import-graph speedups (wt); USER U0 = U0-M Sail stub impl (wt, D51), U0-B runRW spike, U0-C decode spike, U0-T trap tower, U0-D footprint audit + hw_config refactor (wt, D52/D53); union U0 = U0-X cone audit, U0-6 run core+UK_LEAVES, U0-7 user images (echo spike, DU3), U0-8 printf-once spike (DU4), U0-A app laws. QUEUED: kernel bump 7b2c1b1b (after import speedups); union U0-1..U0-5 pure models, U0-C claims, K1 era turn (wt), K2 pipe queue (wt); then U1+.
REMAINING (user rulings): (1) PROVE `USER` (user-mode machine layer, ~84k Rocq lines) — next;
(2) UNION adequacy (Rocq UUnionBootAdequacy via App.xv6_app_adequacy at AppUnionRec.app_union) — the real target;
(3) Rocq drift audit vs main (base 0be24e13b); (4) build parallelism: apply the exact-import edit set
(notes/import_graph_report.md; 5:39 → ~4:50 clean on GCP) and the definition moves (~4:00).
Coordination files: notes/coord/ (wave7b_prompt.txt = agent rules incl. GCP VM builds + autoImplicit off;
pending_edits.txt). Rocq source: /shared/xv6rocq (on main).

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
