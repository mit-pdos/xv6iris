(* SpecMycpu.v -- the public interface of Mycpu, stated independently of its
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
Require Import RegFile InstrBytes HartTp WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Definition wp_mycpu_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (b : bool) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.mycpu in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  sie_cap_gpr m0 n b -∗
  kernel_text -∗ pc_is pcE -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ m' : regfile,
    sie_cap_gpr m' n b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\
      m' !!! Regidx a0_idx = mycpu_ret (rget m0 tp_idx) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_call_mycpu_sconf_cs_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (b : bool) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
  let pcE := mword_of_int KernelSyms.mycpu in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  add_vec P (sign_extend' 64 jimm) = pcE ->
  eq_vec (access_vec_dec (pcE : mword 64) 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sie_cap_gpr m n b -∗
  kernel_text -∗ pc_is P -∗
  instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ mo,
    sie_cap_gpr mo n b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mo /\
      mo !!! Regidx (mword_of_int 10 : mword 5)
        = mycpu_ret (rget m (mword_of_int 4 : mword 5)) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MYCPU.
  Parameter wp_mycpu_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (b : bool),
      wp_mycpu_sconf_body Φ m0 n b.
  Parameter wp_call_mycpu_sconf_cs :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (b : bool),
      wp_call_mycpu_sconf_cs_body Φ P jimm m n b.
End MYCPU.
