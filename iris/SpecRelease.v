(* SpecRelease.v -- the public interface of Release, stated independently of its
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
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RL := KernelSyms.release.

Definition wp_release_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (noffv intenav : mword 32) (n : nat) (av : nat) (dqi : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
  let storeval_noff := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  eq_vec cpuold cpuv = true ->
  (neq_vec nv1 zero_reg = false <-> n = 0%nat) ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  locked γl -∗
  R -∗
  a_cpu ↦₈ cpuold -∗
  a_noff ↦₄ noffv -∗
  a_int ↦₄{ dqi } intenav -∗
  intr_count γ (S n) -∗
  ( ∀ mr,
    sie_cap_gpr γ mr av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    a_noff ↦₄ storeval_noff -∗
    a_int ↦₄{ dqi } intenav -∗
    intr_count γ n -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASE.
  Parameter wp_release_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (noffv intenav : mword 32) (n : nat) (av : nat) {dqi : dfrac},
      wp_release_sconf_body γ Φ γl lka s R m cpuold noffv intenav n av dqi.
End RELEASE.
