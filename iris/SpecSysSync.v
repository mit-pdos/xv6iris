(* SpecSysSync.v -- the public interface of sys_sync, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     uint64 sys_sync(void) {
       acquire(&log.lock);
       if (log.committing || log.outstanding > 0) {
         int n = log.ncommit + 1;
         while (log.ncommit < n) {
           sleep_prepare(&log);
           release(&log.lock);
           sleep();
           acquire(&log.lock);
         }
       }
       release(&log.lock);
       return 0;
     }

   ========================== ONE CONTRACT ============================

   [Module Type SYS_SYNC] is sys_sync's only seal.  Its durability clause
   (sync K3-4, claude-notes/design/sync.md §4.3 item 4): the caller hands
   in an OPTIONAL HOOK, [hook_opt gen_id oQ] -- nothing at [oQ = None],
   the era's [riscv_sync_hook gen_id Q] at [oQ = Some Q] -- and gets
   [Q_opt oQ] back ([Q] at [Some Q]).  The hook is fired EXACTLY ONCE, at
   a GHOST COMMIT ([LogGhostCommit.log_ghost_commit]: a commit with no
   disk write, which rebuilds the crash invariant's durable copy from the
   running claim at the unchanged committed map) whose durable state covers
   every change linearised before the call:
     - FAST branch ([!committing && outstanding == 0] at the acquire): the
       log is quiescent, so this call runs the ghost commit itself, with the
       quiescent loan and the era's sync token out of [LogInv.log_res]'s
       idle arm, and returns [Q];
     - SLOW branch: the hook is DEPOSITED in [log_res]'s helping slot
       ([LogHelp.log_help_deposit]) at the [ncommit] word the wait loop
       watches, and the call sleeps (the C is unchanged).  The first commit
       tail after the deposit ([ProofEndOp.eo_tail], [committing] still set,
       "log" held) extracts every pending hook, runs the ghost commit on all
       of them, and leaves each [Q] in its waiter's escrow before it moves
       [ncommit]; the waiter, woken with [ncommit] past its word, collects
       [▷ Q] ([LogHelp.log_help_collect]) and strips the later at its next
       instruction.  One commit suffices: a waiter depositing while a commit
       is in flight does so after that commit's collection, and commits are
       serialised.
   The syscall dispatcher's arm 22 passes the PROCESS's hook through: the
   deposit's row 22 ([UexecExecInst.xv6_sbundle]) is [hook_opt gen_id
   (sy_oQ f)] and the post's row 22 ([xv6_spost]) is [Q_opt (sy_oQ f)], at
   the families [f] the process deposited ([ProofSyscall.sysc_arm_sync],
   through [sysc_dep_sync] / [sysc_out_sync]).  A process that deposits no
   hook sits at [sy_oQ f = None], where both rows are [emp] -- so 22 stays a
   free number ([UexecSG.free_num]).  [/sync]'s ecall leaf
   ([UkSync.ksync_leaf]) is discharged at any [oQ] at the xv6 instance
   ([UkSyncEntry.ksync_leaf_xv6]); the union's [Some Q] is lane SY3-A's.

   SAFETY ONLY: with operations outstanding, quiescence needs [out = 0]
   and [begin_op] admits new operations into the open group, so a
   continuous operation stream defers the commit unboundedly.  There is NO
   termination claim here and none is intended; the WP is a parking WP.
   Note that sys_sync never runs [begin_op]: it is not a transaction, it
   only watches the counter, which is what keeps it from delaying the very
   group it waits on.

   NO DISK FABRIC, NO BIO_CTX, NO OPERATION TOKEN.  Like begin_op, sys_sync
   touches only the "log" spinlock and sleeps on the log itself; it never
   breads, bwrites or talks to virtio.  So it takes [log_ctx] plus the
   running-process bundle and nothing else.  The [bio_names] and [fs_names]
   binders are there only because [log_ctx] names them; no bio or FsBlocks
   RESOURCE crosses this interface.

   It DOES sleep (the wait loop parks), so it threads the full
   running-process bundle exactly as SpecBeginOp.v does and enters/returns
   at noff 0, taking the [trap_csrs_ext eb] / [cpu_claim_ext eb pj]
   COMPLEMENT in and out: at [eb = true] its own acquire mints the pair the
   interior sleep needs (the complement is [emp] and no caller gains an
   obligation); at [eb = false] the acquire mints nothing and the pair can
   only come from the caller, who holds it because the TRAP handed it over.
   Since it PARKS, its crossing is the literal [true], not [b]
   (SpecAcquiresleep.v's note). *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import BioDefs.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Export SyncHook.       (* [hook_opt] / [Q_opt] -- the optional hook *)
Require Import CtxIdDefs.
Import Defs.

(* sys_sync's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its deepest
   callee is sleep, whose interface demands 22 available below it
   (SpecSleep.v's [22 <= av]).  acquire / release / sleep_prepare want only
   10.  Same budget as begin_op, and for the same reason. *)
Notation K_sys_sync := (26%nat) (only parsing).

(* ====================================================================== *)
(*  THE CONTRACT                                                          *)
(*                                                                        *)
(*  The machine half is the whole-function frame: the budget              *)
(*  [K_sys_sync], the order premise, the parking crossing (the literal     *)
(*  [true], because sys_sync sleeps), the callee-saved and [a0 = 0]        *)
(*  postconditions, and the [trap_csrs_ext] / [cpu_claim_ext] complement   *)
(*  in and out.  The durability half is two clauses:                      *)
(*    (in)  [hook_opt gen_id oQ] -- the caller's optional hook.            *)
(*    (out) [Q_opt oQ] -- the hook's [Q], fired once at a ghost commit.    *)
(*  No disk fabric, no [bio_ctx], no operation token: this takes           *)
(*  [log_ctx] plus the running-process bundle and nothing else.            *)
(* ====================================================================== *)
Definition wp_sys_sync_sconf_body
    `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string)
    (oQ : option (iProp Σ)) :=                        (* the caller's hook  *)
  let pcE : mword 64 := mword_of_int KernelSyms.sys_sync in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_sync <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  locks_below lks "log" ->
  sie_cap_gpr KT1 m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* THE CALLER'S OPTIONAL HOOK (sync K3-4): fired exactly once, at a ghost
     commit covering every change linearised before the call. *)
  hook_opt gen_id oQ -∗
  procs_inv γs -∗
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ -∗
      sie_cap_gpr KT1 mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      (* THE HOOK'S [Q] *)
      Q_opt oQ -∗
      pc_is ret_tgt -∗
      mWP (Loop : expr riscv_lang)) -∗
  mWP (Loop : expr riscv_lang).

Module Type SYS_SYNC.
  Parameter wp_sys_sync_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (oQ : option (iProp Σ)),
      wp_sys_sync_sconf_body γs j γl bn γ γfs cov logstart dev m K eb b lks oQ.
End SYS_SYNC.
