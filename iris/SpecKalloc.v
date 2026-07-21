(* SpecKalloc.v -- the public interface of Kalloc, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpMycpu WpLock.
Require Import KptTree.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpIntenaBits.
Require Import SpecMemsetPage SpecAcquire SpecRelease.
Require Import WpKalloc.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Notation AK := KernelSyms.kalloc.

Definition wp_kalloc_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (fl : mword 64) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (on : option nat) (n : nat) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kalloc in
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let a_cpu := add_vec (mword_of_int KernelSyms.kmem : mword 64) (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
  let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  let noff_ret := (autocast (T := mword) (subrange_vec_dec
      (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store)
         (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
      (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  (14 <= K)%nat ->
  eq_vec (cpuold : mword 64) cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> n = 0%nat) ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 po_noff_store) = false ->
  eq_vec (sign_extend' 64
     (if eq_vec (sign_extend' 64 noffv) zero_reg then (zeros' 32) else intena_old)) zero_reg = true ->
  addr_in_data a_noff ->
  addr_in_data a_int ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m K -∗
  intr_count γ root_ppn n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl (mword_of_int KernelSyms.kmem) (kmem_res γk fl) -∗
  kalloc_avail γk on -∗
  a_noff ↦₄ noffv -∗
  a_int ↦₄ intena_old -∗
  a_cpu ↦₈ cpuold -∗
  ( ∀ mr,
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mr K -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_post γk on (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    a_noff ↦₄ noff_ret -∗
    (∃ vint : mword 32, a_int ↦₄ vint) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KALLOC.
  Parameter wp_kalloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (fl : mword 64) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (on : option nat) (n : nat) (K : nat),
      wp_kalloc_sconf_body γ root_ppn Φ γl γk fl m cpuold noffv intena_old on n K.
End KALLOC.
