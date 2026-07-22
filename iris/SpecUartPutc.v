(* SpecUartPutc.v -- the public interface of UartPutc, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KptTree.
Require Import WpUart.
Require Import IntrDefs.
Require Import IntrDefs.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Notation UPS := KernelSyms.uartputc_sync.

Definition wp_uartputc_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
    (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.uartputc_sync in
  let ra0 := m0 !!! Regidx ra_idx in
  let a00 := m0 !!! Regidx a0_idx in
  let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let sb : mword 8 := autocast (T := mword)
     (subrange_vec_dec (and_vec (add_vec zero_reg a00)
        (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
  (4 <= K)%nat ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  eq_vec (sign_extend' 64 pv) zero_reg = false ->
  neq_vec (sign_extend' 64 pkv) zero_reg = false ->
  sie_cap_gpr γ m0 K -∗
  kernel_text -∗ pc_is pcE -∗
  (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
  (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
  dev_inv γd -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
  ( ∀ mf,
    sie_cap_gpr γ mf K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    uart_tx_own γd (l ++ [sb]) -∗ uart_sent γd (l ++ [sb]) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UARTPUTC.
  Parameter wp_uartputc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
      (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat) (l : list (bv 8)) (pv pkv : mword 32) {dqm dqm2 : dfrac},
      wp_uartputc_sconf_body γ γd Φ m0 K l pv pkv dqm dqm2.
End UARTPUTC.
