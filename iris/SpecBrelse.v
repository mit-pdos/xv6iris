(* SpecBrelse.v -- the public interface of brelse, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void brelse(struct buf *b) {
       if (!holdingsleep(&b->lock)) panic("brelse");
       releasesleep(&b->lock);
       acquire(&bcache.lock);
       b->refcnt--;
       if (b->refcnt == 0) { <unlink b; splice after head> }
       release(&bcache.lock);
     }

   The end of a bread..brelse chain.  In the proof, the buffer's traveling
   content is parked back into the per-buffer escrow at the FIRST instruction
   (before releasesleep -- a blocked waiter's acquiresleep can return the
   moment the sleeplock frees, so the handoff must be complete by then); the
   swap returns the chain's own reference and the checkout token, the token
   goes back into the sleeplock as releasesleep's R, the reference is burned
   at the decrement, and the caller's [bslot] comes back out.  The LRU splice
   on the zero arm happens wholly inside the bcache resource.

   The panic arm is dead (token + pid agreement, as in bwrite).  The body
   calls releasesleep, which wakes every process sleeping on the lock, so
   wakeup's resources ([procs_inv], tp = cid_word) are threaded through. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
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
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto.
Require Import BcacheInv BioInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* brelse's own frame is 32 bytes (4 slots); its deepest callee is
   releasesleep (22). *)
Definition K_brelse : nat := 26%nat.

Definition wp_brelse_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname)
    (bn : bio_names) (V : bio_view Σ) (k : nat)
    (pidv dev bno : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (bs bsd : list (bv 8)) (d : bool) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.brelse in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_brelse <= K)%nat ->
  (* a0 is the buffer *)
  (k < NBUF)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = bnode k ->
  sie_cap_gpr m K b p -∗
  cpu_own 0 eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  bio_ctx bn V -∗
  (* the caller's own pid cell, agreeing with the handle's *)
  p_pid p ↦₄{dq} pidv -∗
  (* wakeup's resources (releasesleep wakes the lock's sleepers) *)
  procs_inv γs -∗
  (* the locked buffer being released.  [bio_locked] -- not [bio_held] --
     is THE brelse obligation: the bytes must be the block's logical
     content (unmodified since bread, or re-indexed by log_write), or the
     handle cannot be formed and the park swap is unavailable. *)
  bio_locked bn V k pidv dev bno bs bsd d -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b p -∗
      cpu_own 0 eb p C b -∗
      pc_is ret_tgt -∗
      p_pid p ↦₄{dq} pidv -∗
      (* the reference's slot unit comes back *)
      bslot bn -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type BRELSE.
  Parameter wp_brelse_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ}
      `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname)
      (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (bs bsd : list (bv 8)) (d : bool) (b : bool),
      wp_brelse_sconf_body γs bn V k pidv dev bno dq m K eb p C bs bsd d b.
End BRELSE.
