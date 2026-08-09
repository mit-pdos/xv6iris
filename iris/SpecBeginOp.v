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
   noff 0: its own acquire mints the [arm_pay 0 eb _] the interior sleep
   needs and its release spends it, so no caller-held pay crosses the
   interface (see SpecBread.v's note on why a second one is
   unimplementable).

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
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* begin_op's own frame is 4 slots ([c.addi sp,sp,-32] at +0x00); its
   deepest callee is sleep, whose interface demands 22 available below it
   (SpecSleep.v's [22 <= av]).  acquire/release want only 10. *)
Definition K_begin_op : nat := 26%nat.

Definition wp_begin_op_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
      !fsLogG Σ, !logG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)          (* the running process *)
    (bn : bio_names)
    (γ : log_names) (γfs : fs_names)
    (cov : gset Z) (logstart : Z) (dev : mword 32)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.begin_op in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_begin_op <= K)%nat ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* PARKING PREMISE (hart-generic scheduler protocol), as SpecBread.v *)
  eb = true ->
  sie_cap_gpr m K b pj -∗
  (* enters at noff 0; the acquire raises it to what sleep demands *)
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  log_ctx γ bn γfs cov logstart dev -∗
  (* threaded, never read: see the header note *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through the two sleeps *)
  procs_inv γs -∗
  scheds_inv γs -∗
  running_claim j -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      running_claim j -∗
      p_pid pj ↦₄{dq} pidv -∗
      (* THE reservation: a full-budget operation *)
      log_op γ MAXOPBLOCKS -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BEGIN_OP.
  Parameter wp_begin_op_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
             !fsLogG Σ, !logG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool),
      wp_begin_op_sconf_body γs j γl bn γ γfs cov logstart dev
                             pidv dq m K eb C b.
End BEGIN_OP.
