(* SpecMemsetPage.v -- the public interface of MemsetPage, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore KernelText.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import IntrDefs.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Notation MS := KernelSyms.memset.

Definition wp_memset_page_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (cval : mword 64) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memset in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p := m0 !!! Regidx a0_idx in
  let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (2 <= n)%nat ->
  page_valid p ->
  m0 !!! Regidx a1_idx = cval ->
  m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  sie_cap_gpr γ m0 n -∗
  kernel_text -∗ pc_is pcE -∗
  page_own p -∗
  ( ∀ mfin,
    sie_cap_gpr γ mfin n -∗
    pc_is ret_tgt -∗
    page_own p -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MEMSETPAGE.
  Parameter wp_memset_page_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (cval : mword 64),
      wp_memset_page_sconf_body γ Φ m0 n cval.
End MEMSETPAGE.
