(* SpecWakeupParts.v -- the public interface of WakeupParts (the prologue and
   epilogue pieces of wakeup, not the whole function), stated independently of its
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
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import WpWakeup.
From Kernel Require KernelSyms.

Notation WK := KernelSyms.wakeup.

(* myproc is PROVEN (SpecMyproc.v / ProofMyproc.v / LinkMyproc.v), and wakeup
   threads the [cur_proc] resource so it can use [wp_myproc_sconf] directly
   (SpecWakeup.v).  There is no myproc axiom. *)

Definition wp_wakeup_prologue_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
  (8 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  sie_cap_gpr γ m K -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗
  ( ∀ (M : regfile) (vpad : mword 64),
      ⌜ M !!! Regidx (mword_of_int 9)  = proc_addr 0
      /\ M !!! Regidx (mword_of_int 18) = proc_addr NPROC
      /\ M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64)
      /\ M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64)
      /\ M !!! Regidx (mword_of_int 20) = m !!! Regidx (mword_of_int 10)
      /\ M !!! Regidx csp_rs1 = spF
      /\ M !!! Regidx (mword_of_int 1)  = m !!! Regidx (mword_of_int 1)
      /\ M !!! Regidx (mword_of_int 4)  = m !!! Regidx (mword_of_int 4)
      /\ M !!! Regidx (mword_of_int 22) = m !!! Regidx (mword_of_int 22)
      /\ M !!! Regidx (mword_of_int 23) = m !!! Regidx (mword_of_int 23)
      /\ M !!! Regidx (mword_of_int 24) = m !!! Regidx (mword_of_int 24)
      /\ M !!! Regidx (mword_of_int 25) = m !!! Regidx (mword_of_int 25)
      /\ M !!! Regidx (mword_of_int 26) = m !!! Regidx (mword_of_int 26)
      /\ M !!! Regidx (mword_of_int 27) = m !!! Regidx (mword_of_int 27)
      /\ (forall r : regidx, r ∈ dom (rf_to_gmap M)) ⌝ -∗
      sie_cap_gpr γ M (K - 8) -∗
      pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
      wk_fcell spF 7 ↦₈ (m !!! Regidx (mword_of_int 1)) -∗
      wk_fcell spF 6 ↦₈ (m !!! Regidx (mword_of_int 8)) -∗
      wk_fcell spF 5 ↦₈ (m !!! Regidx (mword_of_int 9)) -∗
      wk_fcell spF 4 ↦₈ (m !!! Regidx (mword_of_int 18)) -∗
      wk_fcell spF 3 ↦₈ (m !!! Regidx (mword_of_int 19)) -∗
      wk_fcell spF 2 ↦₈ (m !!! Regidx (mword_of_int 20)) -∗
      wk_fcell spF 1 ↦₈ (m !!! Regidx (mword_of_int 21)) -∗
      wk_fcell spF 0 ↦₈ vpad -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_wakeup_epilogue_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (M : regfile) (K : nat) (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64) :=
  let spF := M !!! Regidx csp_rs1 in
  let sp0 := add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) in
  let rettgt := ret_pc vra in
  (8 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap M)) ->
  sie_cap_gpr γ M (K - 8) -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗
  wk_fcell spF 7 ↦₈ vra -∗ wk_fcell spF 6 ↦₈ vs0 -∗ wk_fcell spF 5 ↦₈ vs1 -∗
  wk_fcell spF 4 ↦₈ vs2 -∗ wk_fcell spF 3 ↦₈ vs3 -∗ wk_fcell spF 2 ↦₈ vs4 -∗
  wk_fcell spF 1 ↦₈ vs5 -∗ wk_fcell spF 0 ↦₈ vpad -∗
  ( ∀ Mf : regfile,
      ⌜ Mf !!! Regidx (mword_of_int 1)  = vra
      /\ Mf !!! Regidx (mword_of_int 8)  = vs0
      /\ Mf !!! Regidx (mword_of_int 9)  = vs1
      /\ Mf !!! Regidx (mword_of_int 18) = vs2
      /\ Mf !!! Regidx (mword_of_int 19) = vs3
      /\ Mf !!! Regidx (mword_of_int 20) = vs4
      /\ Mf !!! Regidx (mword_of_int 21) = vs5
      /\ Mf !!! Regidx csp_rs1 = sp0
      /\ Mf !!! Regidx (mword_of_int 4)  = M !!! Regidx (mword_of_int 4)
      /\ Mf !!! Regidx (mword_of_int 22) = M !!! Regidx (mword_of_int 22)
      /\ Mf !!! Regidx (mword_of_int 23) = M !!! Regidx (mword_of_int 23)
      /\ Mf !!! Regidx (mword_of_int 24) = M !!! Regidx (mword_of_int 24)
      /\ Mf !!! Regidx (mword_of_int 25) = M !!! Regidx (mword_of_int 25)
      /\ Mf !!! Regidx (mword_of_int 26) = M !!! Regidx (mword_of_int 26)
      /\ Mf !!! Regidx (mword_of_int 27) = M !!! Regidx (mword_of_int 27)
      /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr γ Mf K -∗
      pc_is rettgt -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WAKEUPPARTS.
  Parameter wp_wakeup_prologue_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat),
      wp_wakeup_prologue_sconf_body γ Φ m K.
  Parameter wp_wakeup_epilogue_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (M : regfile) (K : nat) (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64),
      wp_wakeup_epilogue_sconf_body γ Φ M K vra vs0 vs1 vs2 vs3 vs4 vs5 vpad.
End WAKEUPPARTS.
