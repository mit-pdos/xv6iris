(* SpecIinit.v -- public interface of iinit(), stated independently of its proof. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes SmodeCore CalleeSaved KernelText KernelDataInv IntrDefs.
Require Import WpLock SleepLock SpecInitlock SpecInitsleeplock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation II := KernelSyms.iinit.
Definition itable_addr : mword 64 := mword_of_int KernelSyms.itable.

Definition wp_iinit_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (vlock : mword 32) (vname vcpu : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.iinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  let lk : mword 64 := itable_addr in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (6 <= K)%nat ->
  sie_cap_gpr γ m K -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name lk "itable"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type IINIT.
  Parameter wp_iinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (vlock : mword 32) (vname vcpu : mword 64),
      wp_iinit_sconf_body γ Φ m K vlock vname vcpu.
End IINIT.
