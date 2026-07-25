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
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RL := KernelSyms.release.

Definition wp_release_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let a_cpu := add_vec lk0 (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  eq_vec cpuold cpuv = true ->
  (* the tp register holds THIS cpu's id (pop_off's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  locked γl -∗
  R -∗
  a_cpu ↦₈ cpuold -∗
  cpu_own γ (S n) eb p C -∗
  trap_csrs_pay n eb -∗
  ( ∀ mr,
    sie_cap_gpr γ mr av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    cpu_own γ n eb p C -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASE.
  Parameter wp_release_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (cpuold : mword 64) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_sconf_body γ Φ γl lka s R m cpuold n eb p C av.
End RELEASE.
