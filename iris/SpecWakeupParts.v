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
Require Import RegFile WpNext.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import IntrDefs.
From Kernel Require KernelSyms.
Require Import ProcGeom.

(* wakeup no longer calls myproc at all -- the scan visits every slot,
   including the caller's own (SpecWakeup.v).  Nothing here mentions it. *)

(* wakeup's own 7-entry register-save frame, at spF+8..spF+56 (written by the
   [c.sdsp] prologue, read back by the epilogue).  Cell addresses are given in
   the [c.sdsp] leaf's own form [add_vec spF (sign_extend' 64 (csdsp_imm u))],
   so the prologue's and the epilogue's cells unify without arithmetic. *)
Definition wk_fcell (spF : mword 64) (u : Z) : mword 64 :=
  add_vec spF (zero_extend' 64 (concat_vec (mword_of_int u : mword 6) ('b"000"))).

Definition wp_wakeup_prologue_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat) (b : bool) (p : mword 64) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
  (8 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  sie_cap_gpr KT1 m K b p -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗
  wp_next b p (fun (CID : CpuId) =>
      ∀ (M : regfile) (vpad : mword 64),
      ⌜ M !!! Regidx (mword_of_int 9)  = proc_addr 0
      /\ M !!! Regidx (mword_of_int 19) = proc_addr NPROC
      /\ M !!! Regidx (mword_of_int 20) = (mword_of_int 2 : mword 64)
      /\ M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64)
      /\ M !!! Regidx (mword_of_int 18) = m !!! Regidx (mword_of_int 10)
      /\ M !!! Regidx csp_rs1 = spF
      /\ M !!! Regidx (mword_of_int 1)  = m !!! Regidx (mword_of_int 1)
      /\ M !!! Regidx (mword_of_int 22) = m !!! Regidx (mword_of_int 22)
      /\ M !!! Regidx (mword_of_int 23) = m !!! Regidx (mword_of_int 23)
      /\ M !!! Regidx (mword_of_int 24) = m !!! Regidx (mword_of_int 24)
      /\ M !!! Regidx (mword_of_int 25) = m !!! Regidx (mword_of_int 25)
      /\ M !!! Regidx (mword_of_int 26) = m !!! Regidx (mword_of_int 26)
      /\ M !!! Regidx (mword_of_int 27) = m !!! Regidx (mword_of_int 27)
      /\ (forall r : regidx, r ∈ dom (rf_to_gmap M)) ⌝ -∗
      sie_cap_gpr KT1 M (K - 8) b p -∗
      pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗
      wk_fcell spF 7 ↦₈[KT1] (m !!! Regidx (mword_of_int 1)) -∗
      wk_fcell spF 6 ↦₈[KT1] (m !!! Regidx (mword_of_int 8)) -∗
      wk_fcell spF 5 ↦₈[KT1] (m !!! Regidx (mword_of_int 9)) -∗
      wk_fcell spF 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18)) -∗
      wk_fcell spF 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 19)) -∗
      wk_fcell spF 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 20)) -∗
      wk_fcell spF 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 21)) -∗
      wk_fcell spF 0 ↦₈[KT1] vpad -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_wakeup_epilogue_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (M : regfile) (K : nat) (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64) (b : bool) (p : mword 64) :=
  let spF := M !!! Regidx csp_rs1 in
  let sp0 := add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) in
  let rettgt := ret_pc vra in
  (8 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap M)) ->
  sie_cap_gpr KT1 M (K - 8) b p -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x54)) -∗
  wk_fcell spF 7 ↦₈[KT1] vra -∗ wk_fcell spF 6 ↦₈[KT1] vs0 -∗ wk_fcell spF 5 ↦₈[KT1] vs1 -∗
  wk_fcell spF 4 ↦₈[KT1] vs2 -∗ wk_fcell spF 3 ↦₈[KT1] vs3 -∗ wk_fcell spF 2 ↦₈[KT1] vs4 -∗
  wk_fcell spF 1 ↦₈[KT1] vs5 -∗ wk_fcell spF 0 ↦₈[KT1] vpad -∗
  wp_next b p (fun (CID : CpuId) =>
      ∀ Mf : regfile,
      ⌜ Mf !!! Regidx (mword_of_int 1)  = vra
      /\ Mf !!! Regidx (mword_of_int 8)  = vs0
      /\ Mf !!! Regidx (mword_of_int 9)  = vs1
      /\ Mf !!! Regidx (mword_of_int 18) = vs2
      /\ Mf !!! Regidx (mword_of_int 19) = vs3
      /\ Mf !!! Regidx (mword_of_int 20) = vs4
      /\ Mf !!! Regidx (mword_of_int 21) = vs5
      /\ Mf !!! Regidx csp_rs1 = sp0
      /\ Mf !!! Regidx (mword_of_int 22) = M !!! Regidx (mword_of_int 22)
      /\ Mf !!! Regidx (mword_of_int 23) = M !!! Regidx (mword_of_int 23)
      /\ Mf !!! Regidx (mword_of_int 24) = M !!! Regidx (mword_of_int 24)
      /\ Mf !!! Regidx (mword_of_int 25) = M !!! Regidx (mword_of_int 25)
      /\ Mf !!! Regidx (mword_of_int 26) = M !!! Regidx (mword_of_int 26)
      /\ Mf !!! Regidx (mword_of_int 27) = M !!! Regidx (mword_of_int 27)
      /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr KT1 Mf K b p -∗
      pc_is rettgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WAKEUPPARTS.
  Parameter wp_wakeup_prologue_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (K : nat) (b : bool) (p : mword 64),
      wp_wakeup_prologue_sconf_body m K b p.
  Parameter wp_wakeup_epilogue_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (M : regfile) (K : nat) (vra vs0 vs1 vs2 vs3 vs4 vs5 vpad : mword 64) (b : bool) (p : mword 64),
      wp_wakeup_epilogue_sconf_body M K vra vs0 vs1 vs2 vs3 vs4 vs5 vpad b p.
End WAKEUPPARTS.
