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

   THE CONTRACT IS EMPTY, AND THAT IS THE HONEST STATE OF THE INTERFACE.
   sys_sync takes nothing log-specific in and gives nothing log-specific
   back: it opens no operation, holds no batch, and touches no client
   resource.  What it does is WAIT, and a waiting statement is only worth
   making once the thing waited for can be NAMED -- which for this function
   means a durability receipt indexed by the commit that produced it.  That
   receipt does not exist yet: [ProofEndOp] holds the commit's
   [FsCrash.fs_receipt_any] (it is what [fs_commit_permit] hands back) and
   drops it, and nothing in [LogInv] records which commit a client's writes
   landed in.  The design note (claude-notes/design/fs-log.md, item 5) has
   the two additions that would let this postcondition say something --
   [LogInv.log_mirror_at]'s partial slot record, and a faithful commit
   counter with the committer's receipt deposited beside it -- together with
   the reason a naive "the epoch advanced" postcondition is NOT enough on
   its own: sys_sync's FAST PATH returns without any commit at all, so a
   receipt about progress is unavailable on the arm where nothing was
   pending.

   So this file states what is proved TODAY: sys_sync runs to completion,
   preserves every callee-saved register, and returns 0 -- with the return
   value in a0 the one thing the caller can actually use.  Nothing here has
   to change when the receipt lands; the postcondition only grows.

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
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto.
Require Import BioDefs.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

(* sys_sync's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its deepest
   callee is sleep, whose interface demands 22 available below it
   (SpecSleep.v's [22 <= av]).  acquire / release / sleep_prepare want only
   10.  Same budget as begin_op, and for the same reason. *)
Notation K_sys_sync := (26%nat) (only parsing).
Definition wp_sys_sync_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_sync in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_sys_sync <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* acquire's order premise: sys_sync acquires and releases [log.lock]
     (possibly many times, around each wait iteration's [sleep]) but is
     BALANCED overall, so [lks] is unchanged end to end. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  (* enters at noff 0; the acquire raises it to what sleep demands *)
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM: see the header note, and
     SpecBeginOp.v, whose wait loop this one is a transcription of. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* the running-thread bundle threaded through the interior sleep *)
  procs_inv γs -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: sys_sync PARKS (its wait
     loop sleeps), and a park moves the hart with interrupts off, which has
     nothing to do with SIE (the porting guide's "a PARKING function's
     [wp_next] index is [true] UNCONDITIONALLY"). *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      (* the syscall's return value: [return 0] *)
      ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64)⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYS_SYNC.
  Parameter wp_sys_sync_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_sys_sync_sconf_body γs j γl bn γ γfs cov logstart dev m K eb b lks.
End SYS_SYNC.
