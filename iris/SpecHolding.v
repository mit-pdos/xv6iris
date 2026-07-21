(* SpecHolding.v -- the public interface of Holding, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu SpecMycpu.
Require Import WpHolding WpHoldingInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation HD := KernelSyms.holding.

Definition wp_holding_lockinv_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (cpuold : mword 64) (dqc : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  eq_vec cpuold (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (6 <= n)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka R -∗
  a_cpu ↦₈{ dqc } cpuold -∗
  ( ∀ mh,
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn mh n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) ⌝ -∗
    a_cpu ↦₈{ dqc } cpuold -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_holding_lockinv_locked_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (cpuold : mword 64) (dqc : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  eq_vec cpuold (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = true ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (6 <= n)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka R -∗
  locked γl -∗
  a_cpu ↦₈{ dqc } cpuold -∗
  ( ∀ mh,
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn mh n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
    locked γl -∗
    a_cpu ↦₈{ dqc } cpuold -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type HOLDING.
  Parameter wp_holding_lockinv_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (cpuold : mword 64) {dqc : dfrac},
      wp_holding_lockinv_s_sconf_body γ root_ppn Φ γl lka R m n cpuold dqc.
  Parameter wp_holding_lockinv_locked_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (cpuold : mword 64) {dqc : dfrac},
      wp_holding_lockinv_locked_s_sconf_body γ root_ppn Φ γl lka R m n cpuold dqc.
End HOLDING.
