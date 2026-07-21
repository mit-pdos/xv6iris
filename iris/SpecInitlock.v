(* SpecInitlock.v -- the public interface of Initlock, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodePte.
Require Import SmodeCore.
Require Import KptTree SmodeCorePt.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpInitlock.
Require Import SRegime.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation IL := KernelSyms.initlock.

Definition wp_initlock_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (vlock : bv 32) (vname vcpu : bv 64) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.initlock in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let name := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let c_name := add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)) in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (2 <= K)%nat ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m K -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ( ∀ mr,
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mr K -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    c_name ↦₈ name -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type INITLOCK.
  Parameter wp_initlock_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (vlock : bv 32) (vname vcpu : bv 64) (K : nat),
      wp_initlock_sconf_body γ root_ppn Φ m vlock vname vcpu K.
End INITLOCK.
