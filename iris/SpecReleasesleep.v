(* SpecReleasesleep.v -- the public interface of Releasesleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The separation-logic lock spec, sleeplock flavour:

     { is_sleeplock γl γ slk s R ∗ sleeplocked γ slk pd ∗ R
       ∗ <thread resources> }
       releasesleep(slk)
     { <thread resources> }

   The holder surrenders the token, the pid field and the protected
   resource back into the lock.  The body wakes every process sleeping on
   the lock, so the <thread resources> include wakeup()'s: procs_inv and --
   since wakeup runs over the PROVEN myproc -- the current-process resource
   [cur_proc pme] (any pme; releasesleep does not inspect it) with
   tp = cid_word. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
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
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


(* THE GENERAL FORM, over the sleeplock's holder DEPOSIT [H] (SleepLock.v):
   the holder hands the token, the pid field and [R] back into the lock, and
   gets its own deposit [H q] out -- the same fraction it put in, which
   [sl_res_open_held_q] pins.  A client whose reference to the object is
   itself split (many [struct file]s over one inode reference) needs exactly
   that; "some fraction back" would not let it rebuild its share.

   [wp_releasesleep_sconf] below is this at the untracked instance, where
   [H q] is [emp] and the caller's token is the fraction-free [sleeplocked]. *)
Definition wp_releasesleep_gen_sconf_body `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname)
    (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
    (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.releasesleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (22 <= av)%nat ->
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m av b pme -∗
  cpu_own 0 eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock_gen γl γsl slk s R H -∗
  (* the holder's bundle, surrendered back into the lock *)
  sleeplocked_q γsl q slk pd -∗
  R -∗
  (* wakeup's resources *)
  procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b pme -∗
      cpu_own 0 eb pme b lks -∗
      pc_is ret_tgt -∗
      (* the deposit comes back, at the holder's own fraction *)
      H q -∗
          WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_releasesleep_sconf_body `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

    (γs : list gname)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.releasesleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (22 <= av)%nat ->
  (* THE ORDER PREMISE for the INNER spinlock of the sleeplock, which
     [initlock]s at the name "sleep lock" (the sleeplock itself is not a
     spinlock and has no rank): everything the caller holds ranks strictly
     below it.  [LockRank.locks_below_not_elem] recovers the non-membership
     the set algebra below needs.  No execution ever holds two "sleep lock"s
     at once (LockRank.v).  releasesleep is BALANCED -- entry and exit
     [cpu_own] carry the same [lks] -- because the C's single return path
     releases lk->lk; the wakeup() in between is itself balanced. *)
  locks_below lks "sleep lock" ->
  sie_cap_gpr KT1 m av b pme -∗
  cpu_own 0 eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle, surrendered back into the lock *)
  sleeplocked γsl slk pd -∗
  R -∗
  (* wakeup's resources *)
  procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b pme -∗
      cpu_own 0 eb pme b lks -∗
      pc_is ret_tgt -∗
          WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type RELEASESLEEP.
  Parameter wp_releasesleep_gen_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_releasesleep_gen_sconf_body γs γl γsl s R H q m pd pme av eb b lks.
  Parameter wp_releasesleep_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_releasesleep_sconf_body γs γl γsl s R m pd pme av eb b lks.
End RELEASESLEEP.
