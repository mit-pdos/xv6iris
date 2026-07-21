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
   the lock, so the <thread resources> include wakeup()'s: procs_inv and
   the whole per-proc lock-cpu cell array [wk_lockcells].  Unlike
   acquiresleep, no myproc() is called, so tp stays generic (the per-cpu
   cells live at [mycpu_ret (m !!! tp)], wakeup's own convention). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import SwtchCtx.
Require Import SchedCtx.
Require Import WpWakeup.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RSL := KernelSyms.releasesleep.

Definition wp_releasesleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (γs : list gname)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pd : mword 32) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.releasesleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec (zero_reg : mword 64) cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (22 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn 0 -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle, surrendered back into the lock *)
  sleeplocked γsl -∗
  sl_pid slk ↦₄ pd -∗
  R -∗
  sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
  a_noff ↦₄ (mword_of_int 0 : mword 32) -∗
  (∃ iv : mword 32, a_int ↦₄ iv) -∗
  (* wakeup's resources *)
  wk_lockcells γs -∗
  procs_inv γ root_ppn Φ γs -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mf av -∗
      intr_count γ root_ppn 0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
      a_noff ↦₄ (mword_of_int 0 : mword 32) -∗
      (∃ iv : mword 32, a_int ↦₄ iv) -∗
      wk_lockcells γs -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASESLEEP.
  Parameter wp_releasesleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pd : mword 32) (av : nat),
      wp_releasesleep_sconf_body γ root_ppn Φ γs γl γsl s R m pd av.
End RELEASESLEEP.
