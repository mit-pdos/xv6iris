(* SpecWakeupLoop.v -- the public interface of WakeupLoop, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import SRegime SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpGpr.
Require Import WpMycpu.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved.
Require Import RiscvExtras.
Require Import KptTree.
Require Import IntrDefs WpIntenaBits.
Require Import IntrDefs.
Require Import SpecAcquire SpecRelease.
Require Import WpWakeup SpecWakeup WpKalloc.
From Kernel Require KernelSyms.

Definition wp_wakeup_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Rreg : s_regime) (γc : gname) (bsie : mword 1) (dq : dfrac) (Φ : mval -> iProp Σ) (m : regfile) (γs : list gname) (a0f : mword 64) (noffv : mword 32) (lvl K : nat) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
  let rettgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (18 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
  eq_vec (zero_reg : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 (wk_noff_acq noffv)) = false ->
  wk_noff_rel (wk_noff_acq noffv) = noffv ->
  (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> lvl = 0%nat) ->
  eq_vec (access_vec_dec rettgt 0) ('b"0") = true ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap_gpr γ root_ppn m K -∗
  intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗
  wk_noff_addr a0f ↦₄ noffv -∗ (∃ iv : mword 32, wk_intena_addr a0f ↦₄ iv) -∗
  wk_lockcells γs -∗ procs_inv Rreg Φ γc bsie dq γs -∗
  ( ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap_gpr γ root_ppn Mf K -∗
      intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
      kernel_text -∗ pc_is rettgt -∗
      wk_noff_addr a0f ↦₄ noffv -∗ (∃ iv : mword 32, wk_intena_addr a0f ↦₄ iv) -∗
      wk_lockcells γs -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WAKEUPLOOP.
  Parameter wp_wakeup_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Rreg : s_regime) (γc : gname) (bsie : mword 1) (dq : dfrac) (Φ : mval -> iProp Σ) (m : regfile) (γs : list gname) (a0f : mword 64) (noffv : mword 32) (lvl K : nat),
      wp_wakeup_sconf_body γ root_ppn Rreg γc bsie dq Φ m γs a0f noffv lvl K.
End WAKEUPLOOP.
