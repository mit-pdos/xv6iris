(* SpecIunlock.v -- the public interface of iunlock, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void iunlock(struct inode *ip) {
       if (ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
         panic("iunlock");
       releasesleep(&ip->lock);
     }

   64 bytes, 25 instructions: guard, then release.  ilock's inverse, and the
   PARK half of the icache seam.

   ---- WHAT IT CONSUMES AND WHAT IT GIVES BACK -------------------------

   It consumes exactly what SpecIlock v2 produced -- the checked-out bundle,
   at whatever [(dn', bm')] the holder ended with (a writei between the two
   moves them) -- and it PARKS it, handing the checkout token back to the
   sleeplock inside releasesleep.  What comes out is the caller's REFERENCE,
   whole: §13.1d's deposit run backwards.  [IcacheEscrow.ic_swap_park] pins
   the returned reference's [dev] and [inum] to the two identity halves the
   holder hands back (§13.1e), so a caller can ilock the same inode again;
   only the FRACTION is existential, exactly as in [BioInv]'s brelse.

   PARKED-MEANS-FLUSHED is the one obligation this contract adds over v1's:
   [ic_loaded] carries [InodeRegion.dinode_at γi inum dn'] at the SAME [dn']
   as the metadata cells, i.e. "park only with the region record retagged to
   the record you are parking" (§13.1d).  Every writer in this kernel ends
   with iupdate -- writei's tail, itrunc's tail -- so a holder can always
   re-establish it, and WITHOUT it iget's eviction could never conclude the
   pool's allocated shape (whose [inode_ok] is about the ON-DISK record)
   from the parked arm's (about the in-memory one).  A reader that never
   writes, like fileread, gets it straight out of ilock (§13.6).

   THE THREE PANIC TESTS ARE ALL DEAD.  [ip == 0] because the entry is slot
   [k] and [IcacheInv.ientry_unsigned] says its address is
   [itable + 24 + 136k]; [ip->ref < 1] by [IcacheInv.iref_load_au] against
   [itable_inv], over a reference BORROWED from the escrow's checked-out arm
   for the duration of that one atomic update ([ic_open_out] -- the holder's
   FULL valid cell is what refutes the other two arms, §13.1d), since after
   ilock's deposit the holder owns no reference of its own;
   [!holdingsleep(&ip->lock)] because the holder's bundle -- the token, the
   lock's pid field and the caller's own pid cell agreeing -- is exactly what
   makes holdingsleep return 1 (SpecHoldingsleep.v is stated in that
   HOLDER's form for this reason).

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
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

(* iunlock's own frame is 32 bytes (4 slots); its deepest callee is
   releasesleep (22), holdingsleep wanting 16. *)
Definition K_iunlock : nat := 26%nat.

Definition wp_iunlock_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ,
      !fsLogG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}

    (gs : list gname)
    (gfs : fs_names) (gi : gname)
    (cn : ic_names)
    (gil gisl : gname)
    (cov : gset Z) (logstart : Z)
    (k : nat) (dev inum : mword 32)
    (dn' : dinode) (bm' : blkmap)
    (pidv : mword 32) (dq : dfrac)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iunlock in
  let ip : mword 64 := ientry k in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_iunlock <= K)%nat ->
  (* the entry is slot [k]: a0 = ip, and the null test dies here *)
  (k < NINODE)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = ip ->
  sie_cap_gpr m K b p -∗
  cpu_own 0 eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  (* the [ref] words, and the entry's content escrow *)
  itable_inv (icn_ref cn) -∗
  ic_escrow cn gfs gi cov logstart k -∗
  is_sleeplock gil gisl (i_lock ip) "inode"%string (ic_tok cn k) -∗
  (* THE HOLDER'S BUNDLE -- the third dead panic test is exactly this *)
  sleeplocked gisl -∗
  sl_pid (i_lock ip) ↦₄ pidv -∗
  p_pid p ↦₄{dq} pidv -∗
  (* wakeup's resources (releasesleep wakes the lock's sleepers) *)
  procs_inv gs -∗
  (* THE CHECKED-OUT ENTRY, surrendered back into the escrow.  Exactly
     SpecIlock v2's postcondition, and exactly [ic_swap_park]'s input;
     [ic_loaded]'s [dinode_at] at [dn'] IS the flushed-record obligation. *)
  i_dev ip ↦₄{DfracOwn (1/2)} dev -∗
  i_inum ip ↦₄{DfracOwn (1/2)} inum -∗
  i_valid ip ↦₄ valid_word true -∗
  ic_loaded gfs gi cov logstart k inum dn' bm' -∗
  wp_next b p (fun (CID : CpuId) =>
  ∀ (mf : regfile) (q : Qp),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf K b p -∗
      cpu_own 0 eb p C b -∗
      pc_is ret_tgt -∗
      p_pid p ↦₄{dq} pidv -∗
      (* the caller's reference, back whole and at ITS OWN device *)
      inode_ref (icn_ref cn) k q dev inum -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type IUNLOCK.
  Parameter wp_iunlock_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !diskGhostG Σ,
             !fsLogG Σ, !icacheG Σ, !irefslotG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}

      (gs : list gname)
      (gfs : fs_names) (gi : gname)
      (cn : ic_names)
      (gil gisl : gname)
      (cov : gset Z) (logstart : Z)
      (k : nat) (dev inum : mword 32)
      (dn' : dinode) (bm' : blkmap)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (b : bool),
      wp_iunlock_sconf_body gs gfs gi cn gil gisl cov logstart k dev inum
                            dn' bm' pidv dq m K eb p C b.
End IUNLOCK.
