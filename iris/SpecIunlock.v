(* SpecIunlock.v -- the public interface of iunlock, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void iunlock(struct inode *ip) {
       if (ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
         panic("iunlock");
       releasesleep(&ip->lock);
     }

   64 bytes, 25 instructions: guard, then release.  ilock's inverse, and the
   PARK half of the icache seam -- it consumes [InodeLock.inode_locked] at
   whatever [dn']/[bm'] the holder ended with (a writei between the two
   moves them; [InodeLock.inode_keys_update] is what retags the shadow) and
   puts it back into the sleeplock as [inode_parked] at valid = 1.  The
   caller keeps ONE half of the shadow, which is the icache's record that
   this inode is now loaded.

   THE THREE PANIC TESTS ARE ALL DEAD.  [ip == 0] and [ip->ref < 1] by the
   same two premises ilock takes; [!holdingsleep(&ip->lock)] because the
   holder's bundle -- the token, the lock's pid field and the caller's own
   pid cell agreeing -- is exactly what makes holdingsleep return 1
   (SpecHoldingsleep.v is stated in that HOLDER's form for this reason).

   iunlock does NOT sleep, so it threads no parking bundle -- but
   releasesleep WAKES every process sleeping on the lock, so wakeup's
   resources ([procs_inv]) are threaded through, exactly as SpecBrelse.v
   does for the same call. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
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
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* iunlock's own frame is 32 bytes (4 slots); its deepest callee is
   releasesleep (22), holdingsleep wanting 16. *)
Definition K_iunlock : nat := 26%nat.

Definition wp_iunlock_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ,
      !fsLogG Σ, !inodeG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (gs : list gname)
    (gfs : fs_names) (gi : gname)
    (gil gisl : gname)
    (cov : gset Z) (logstart : Z)
    (ip : mword 64) (refv : mword 32)
    (dn : dinode) (bm : blkmap)
    (pidv : mword 32) (dq dqr : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlock in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlock <= K)%nat ->
  (* a0 = ip, a real inode with a live reference: two of the three dead
     panic tests *)
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  uint ip <> 0 ->
  0 < bv_unsigned refv < 2 ^ 31 ->
  sie_cap_gpr m K b p -∗
  cpu_own 0 eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  is_sleeplock gil gisl (i_lock ip) "inode"%string
               (inode_parked gfs gi cov logstart ip) -∗
  (* THE HOLDER'S BUNDLE -- the third dead panic test is exactly this *)
  sleeplocked gisl -∗
  sl_pid (i_lock ip) ↦₄ pidv -∗
  p_pid p ↦₄{dq} pidv -∗
  i_ref ip ↦₄{dqr} refv -∗
  (* wakeup's resources (releasesleep wakes the lock's sleepers) *)
  procs_inv Φ gs -∗
  (* THE LOCKED INODE, surrendered back into the lock *)
  inode_locked gfs gi cov logstart ip dn bm -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ mf : regfile,
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b p -∗
      cpu_own 0 eb p C b -∗
      pc_is ret_tgt -∗
      p_pid p ↦₄{dq} pidv -∗
      i_ref ip ↦₄{dqr} refv -∗
      (* the icache's record that this inode is loaded, and what it is *)
      inode_key gi true dn bm -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUNLOCK.
  Parameter wp_iunlock_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ,
             !fsLogG Σ, !inodeG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (gs : list gname)
      (gfs : fs_names) (gi : gname)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z)
      (ip : mword 64) (refv : mword 32)
      (dn : dinode) (bm : blkmap)
      (pidv : mword 32) (dq dqr : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (b : bool),
      wp_iunlock_sconf_body Φ gs gfs gi gil gisl cov logstart ip refv dn bm
                            pidv dq dqr m K eb p C b.
End IUNLOCK.
