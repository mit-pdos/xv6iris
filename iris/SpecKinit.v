(* SpecKinit.v -- the public interface of Kinit, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants own.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import WpMycpu WpLock.
Require Import KallocInv.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpInitlock SpecInitlock SpecFreerange.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation KI := KernelSyms.kinit.

Definition wp_kinit_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (vlock : bv 32) (vname vcpu : bv 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kinit in
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let lk : mword 64 := mword_of_int KernelSyms.kmem in
  let fl : mword 64 := mword_of_int (KernelSyms.kmem + 24) in
  let c_name := add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)) in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let endaddr : mword 64 := mword_of_int 0x80023558 in
  let phystop : mword 64 := mword_of_int 0x88000000 in
  let s1entry := add_vec (and_vec (add_vec endaddr (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv in
  (22 <= K)%nat ->
  ncnt = 0%nat ->
  eq_vec (zero_reg : mword 64) cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  prun phystop s1entry ps ->
  addr_in_data a_noff ->
  addr_in_data a_int ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m K -∗
  intr_count γ root_ppn ncnt -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  fl ↦₈ (mword_of_int 0 : mword 64) -∗
  ([∗ list] p ∈ ps, page_own p) -∗
  a_noff ↦₄ (zeros' 32 : mword 32) -∗
  (∃ iv : mword 32, a_int ↦₄ iv) -∗
  ( ∀ (γl : gname) (γk : gname * gname) (mr : regfile),
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mr K -∗
    intr_count γ root_ppn ncnt -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    is_kmem γl γk lk fl -∗
    kalloc_avail γk (Some (length ps)) -∗
    a_noff ↦₄ (zeros' 32 : mword 32) -∗
    (∃ iv : mword 32, a_int ↦₄ iv) -∗
    (∃ nm : mword 64, c_name ↦₈ nm) -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KINIT.
  Parameter wp_kinit_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) (vlock : bv 32) (vname vcpu : bv 64),
      wp_kinit_sconf_body γ root_ppn Φ m ps K ncnt vlock vname vcpu.
End KINIT.
