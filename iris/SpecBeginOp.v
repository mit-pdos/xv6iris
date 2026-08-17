(* SpecBeginOp.v -- the public interface of begin_op, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void begin_op(void) {
       acquire(&log.lock);
       while (1) {
         if (log.committing) {
           sleep(&log, &log.lock);
         } else if (log.lh.n + (log.outstanding + 1) * MAXOPBLOCKS > LOGBLOCKS) {
           sleep(&log, &log.lock);
         } else {
           log.outstanding += 1;
           break;
         }
       }
       release(&log.lock);
     }

   THE RESERVATION MINT.  begin_op's whole content is the ledger step
   (LogInv.v): the loop exits exactly when the C guard
   [n + (out+1)*MAXOPBLOCKS <= LOGBLOCKS] reads true, and
   [LogInv.log_reserve_ok] turns that conservative test into the exact sum
   tie the invariant needs, so the mint of a fresh full-budget entry
   ([log_begin_step]) is legal precisely there.  That IS the meaning of the
   guard.  The postcondition is one [log_op γ MAXOPBLOCKS] -- the token
   log_write spends a unit of and end_op retires.

   NO DISK FABRIC, NO BIO_CTX.  begin_op touches only the "log" spinlock and
   sleeps on the log itself; it never breads, bwrites or talks to virtio.
   So it takes [log_ctx] plus the running-process bundle and nothing else --
   the one log.c function whose contract is free of the block layer.  The
   [bio_names] binder is there only because [log_ctx] names the slot pool
   parked in [log_batch]; no bio RESOURCE crosses this interface.

   It DOES sleep (both arms of the retry loop), so it threads the full
   running-process bundle exactly as SpecBread.v does and enters/returns at
   noff 0, taking the [trap_csrs_ext eb]/[cpu_claim_ext eb pj] COMPLEMENT in
   and out: at [eb = true] its own acquire mints the pair the interior sleep
   needs (the complement is [emp] and no caller gains an obligation); at
   [eb = false] the acquire mints nothing and the pair can only come from the
   caller, who holds it because the TRAP handed it over.  Since it PARKS, its
   crossing is the literal [true], not [b] (SpecAcquiresleep.v's note).

   The [p_pid] cell is threaded for UNIFORMITY with the rest of the log
   layer (write_head / install_trans / initlog / end_op all need it, for
   the acquiresleep inside bread).  begin_op itself takes no sleeplock and
   never reads it; it is handed straight back. *)
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

(* begin_op's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its
   deepest callee is sleep, whose interface demands 22 available below it
   (SpecSleep.v's [22 <= av]).  acquire/release want only 10. *)
Notation K_begin_op := (26%nat) (only parsing).
Definition wp_begin_op_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
      !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool)
    (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.begin_op in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_begin_op <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* THE ORDER PREMISE FOR begin_op'S OWN ACQUIRE.  begin_op takes "log"
     itself (rank 3, LockRank.v) and calls nothing that acquires a
     lower-ranked lock (sleep/sleep_prepare only ever touch "proc", rank 11,
     strictly above), so the one bound at "log" covers everything this
     function needs -- [locks_below_mono] weakens it to "proc" for the
     interior sleep calls. *)
  locks_below lks "log" ->
  sie_cap_gpr kt m K b pj -∗
  (* enters at noff 0; the acquire raises it to what sleep demands *)
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM.  begin_op's own acquire
     mints the pay its interior sleeps need at [eb = true] (the complement is
     [emp] and the caller brings nothing); at [eb = false] the push_off frees
     nothing and the caller brings the pair, holding it because the TRAP
     handed it over -- see SpecSleep.v / SpecAcquiresleep.v. *)
  trap_csrs_ext kt eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* threaded, never read: see the header note *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through the two sleeps *)
  procs_inv (kt := kt) γs -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b]: begin_op PARKS (its retry
     loop sleeps), and a park moves the hart with interrupts off, which has
     nothing to do with SIE (the porting guide's "a PARKING function's
     [wp_next] index is [true] UNCONDITIONALLY"). *)
  wp_next true pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr kt mf K b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext kt eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* THE reservation: a full-budget operation *)
      log_op γ MAXOPBLOCKS -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BEGIN_OP.
  Parameter wp_begin_op_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !bioG Σ, !diskGhostG Σ,
             !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string),
      wp_begin_op_sconf_body kt γs j γl bn γ γfs cov logstart dev
                             pidv dq m K eb b lks.
End BEGIN_OP.
