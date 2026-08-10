(* SpecReleasesleep.v -- the public interface of Releasesleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The separation-logic lock spec, sleeplock flavour:

     { is_sleeplock γl γ slk s R ∗ sleeplocked γ ∗ sl_pid slk ↦₄ pd ∗ R
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
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_releasesleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.releasesleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (22 <= av)%nat ->
  sie_cap_gpr m av b pme -∗
  cpu_own 0 eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle, surrendered back into the lock *)
  sleeplocked γsl -∗
  sl_pid slk ↦₄ pd -∗
  R -∗
  panic_wp_any -∗
  (* wakeup's resources *)
  procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b pme -∗
      cpu_own 0 eb pme C b -∗
      pc_is ret_tgt -∗
          WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type RELEASESLEEP.
  Parameter wp_releasesleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_releasesleep_sconf_body γs γl γsl s R m pd pme av eb C b.
End RELEASESLEEP.
