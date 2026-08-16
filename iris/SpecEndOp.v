(* SpecEndOp.v -- the public interface of end_op, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void end_op(void) {
       int do_commit = 0;
       acquire(&log.lock);
       if (log.committing) panic("log.committing");
       log.outstanding -= 1;
       if (log.outstanding == 0) { do_commit = 1; log.committing = 1; }
       else wakeup(&log);
       release(&log.lock);
       if (do_commit) {
         commit();                     // INLINED, and write_log with it
         acquire(&log.lock);
         log.committing = 0;
         log.ncommit++;
         wakeup(&log);
         release(&log.lock);
       }
     }

   Both [commit] and [write_log] are static with end_op their only caller, so
   gcc inlined them: this ONE function contains the accounting critical
   section, the wakeup arm, the whole write_log copy loop (bread the log
   slot, bread the home block, memmove, bwrite, brelse x2) and the
   write_head / install_trans(0) / write_head commit sequence.

   THE CONTRACT.  In: one operation's token, whatever budget is left on it
   ([log_op γ u] for ANY u -- callers do not track how many log_writes they
   did, exactly as the C code does not).  Out: nothing log-specific -- the
   token is RETIRED ([LogInv.log_end_step]) and the operation is over.
   Whether this particular end_op is the last one out, and therefore
   whether it runs the commit, is INTERNAL: the spec deliberately does not
   expose which, because no caller can predict it and no caller needs to.
   The commit path checks [log_batch] out of the lock resource under
   [committing = 1] and deposits it back before returning, so the batch
   never appears in the interface either.

   The "log.committing" PANIC IS DEAD: an op token in hand forces
   outstanding >= 1 ([LogInv.log_op_positive]), and log_res's pure conjunct
   [cmt = true -> out = 0] then refutes committing.

   end_op sleeps (bread / bwrite inside the commit), so it threads the full
   running-process bundle exactly as SpecBread.v does, plus the disk fabric
   and [bio_ctx]; it enters and returns at noff 0.

   SLOT ACCOUNTING, AND WHY IT CLOSES.  The interior install_trans hands
   back [bslots bn (2 + length W)] having taken 2 -- one surplus unit per
   installed block, the units log_write's bpin absorbed.  They are not
   dropped: end_op deposits them into [log_batch]'s POOL when it re-forms
   the batch at n = 0.  The arithmetic is exact -- length W = n, and the
   pool goes from [(LOGBLOCKS - n) + 2] to [(LOGBLOCKS - 0) + 2].  Nothing
   about it crosses this interface; end_op's post stays empty. *)
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
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.

(* end_op's own frame is 8 slots ([c.addi16sp sp,-64] at +0x00); its deepest
   callee is install_trans (50).  write_head wants 44, bread 40, sleep-free
   acquire/release 10. *)
Notation K_end_op := (76%nat) (only parsing).
Definition wp_end_op_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (γu : uart_names) (γd : disk_names) (γk : gname)  (* disk fabric + lock  *)
    (pd pav pu : mword 64)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (u : nat)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.end_op in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_end_op <= K)%nat ->
  (* the covered range's block-number bounds (bread's 2^31 arithmetic
     premise, and 0 is never a client block) and the fact that the log's own
     storage is covered -- the commit path breads the header and every log
     slot *)
  log_geom_ok cov logstart ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the order premise: end_op's own two critical sections both acquire
     "log" (rank 3) directly, balanced end to end, so [lks] -- the caller's
     held set -- is the SAME value at both acquire call sites.  wakeup's own
     "proc" (rank 11) order premise is a consequence at the point it is
     called (with "log" held): [locks_below_mono] lifts this bound to 11,
     [locks_below_union_singleton] pushes it across the held "log" singleton.
     commit's interior bread/bwrite/brelse run with "log" ALREADY RELEASED
     (the C releases before calling commit()) and their Spec files (SpecBread
     etc.) surface no order premise of their own for their callers to
     satisfy, so nothing about them is stated here. *)
  locks_below lks "log" ->
  sie_cap_gpr m K b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  panic_env -∗
  bio_ctx bn (fs_view γfs γd dev cov) -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* THE CRASH SEAM (phase C2b/D1 stage 4): the persistent identification of
     the machine layer's crash predicate with THIS file system's [P_fs].  It
     is what lets the commit path's four writes -- the log fills, the commit
     header, the installs and the clear -- carry REAL durability fupds
     ([FsCrash.fs_logfill_permit] and its three siblings).  The era
     certificate beside it is what identifies the crash record's checked-out
     arm as THIS era's; the swap receipt the same squeeze needs rides
     [log_ctx] already. *)
  fs_crash_seam cov logstart -∗
  gen_cert -∗
  (* the caller's own pid cell (bread's acquiresleep records it) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle *)
  procs_inv γs -∗
  (* the disk fabric *)
  dev_inv γu γd -∗
  disk_geom γd pd pav pu -∗
  is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
  (* THE operation being closed, at whatever budget it has left *)
  log_op γ u -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  This function can SLEEP
     (its bread / ilock / bwrite does), and a park moves the hart with
     interrupts off, so the crossing has nothing to do with SIE -- the
     porting guide's "a PARKING function's [wp_next] index is [true]
     UNCONDITIONALLY".  Spelled [b] the two coincide at the only instance
     the [eb = true] premise admits, which is why this went unnoticed; once
     [eb = false] is reachable the [b] form would promise the caller it
     comes back on the hart it called from, which a park makes false. *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* nothing log-specific comes back: the token is retired *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type END_OP.
  Parameter wp_end_op_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_end_op_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart dev u pidv dq m K eb b lks.
End END_OP.
