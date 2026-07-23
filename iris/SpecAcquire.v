(* SpecAcquire.v -- the public interface of Acquire, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
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
From Stdlib Require Import FunctionalExtensionality.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import WpLock WpIntenaBits.
Require Import WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation AQ := KernelSyms.acquire.

Definition wp_acquire_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (n : nat) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
  let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec cpuold cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  intr_count γ n -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk0 s R -∗
  a_cpu ↦₈ cpuold -∗
  a_noff ↦₄ noffv -∗
  a_int ↦₄ intena_old -∗
  ( ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    sie_cap_gpr γ mfin av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mfin ⌝ -∗
    locked γl -∗ R -∗
    a_cpu ↦₈ cpuv -∗
    a_noff ↦₄ po_noff_store -∗
    a_int ↦₄ (if eq_vec (sign_extend' 64 noffv) zero_reg
              then po_intena_val ms else intena_old) -∗
    intr_count γ (S n) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ACQUIRE.
  Parameter wp_acquire_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (n : nat) (av : nat),
      wp_acquire_sconf_body γ Φ γl s R m cpuold noffv intena_old n av.
End ACQUIRE.
