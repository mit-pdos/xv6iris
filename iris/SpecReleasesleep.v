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
   the lock, so the <thread resources> include wakeup()'s: procs_inv, the
   whole per-proc lock-cpu cell array [wk_lockcells], and -- since wakeup
   runs over the PROVEN myproc -- the current-process resource
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
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpWakeup.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RSL := KernelSyms.releasesleep.

Definition wp_releasesleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.releasesleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* the hart id is the ambient CpuId (wakeup runs over the proven myproc) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (22 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  intr_count γ 0 -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle, surrendered back into the lock *)
  sleeplocked γsl -∗
  sl_pid slk ↦₄ pd -∗
  R -∗
  sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
  a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  (* wakeup's resources *)
  wk_lockcells γs -∗
  cur_proc pme -∗
  procs_inv γ Φ γs -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr γ mf av -∗
      intr_count γ 0 -∗
      pc_is ret_tgt -∗
      sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      wk_lockcells γs -∗
      cur_proc pme -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASESLEEP.
  Parameter wp_releasesleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pd : mword 32) (pme : mword 64) (av : nat),
      wp_releasesleep_sconf_body γ Φ γs γl γsl s R m pd pme av.
End RELEASESLEEP.
