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
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore KernelText.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import IntrDefs.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.


Definition wp_memset_page_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memset in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  page_valid p ->
  m0 !!! Regidx a1_idx = cval ->
  m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
  sie_cap_gpr kt m0 n b pcur -∗
  kernel_text -∗ pc_is pcE -∗
  page_own p -∗
  wp_next b pcur (fun (CID : CpuId) =>
    ∀ mfin,
    sie_cap_gpr kt mfin n b pcur -∗
    pc_is ret_tgt -∗
    page_own p -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE VALUE-PRESERVING FORM.  [wp_memset_page_sconf] above weakens the
   written page back to [page_own] -- contents EXISTENTIAL -- which is right
   for kalloc/kfree, whose memsets only poison, and wrong for vmfault, whose
   whole contribution to the process's memory is that the page it maps reads
   as ZERO.  This form hands the bytes back NAMED; the form above is derived
   from it by forgetting them. *)
Definition wp_memset_page_val_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memset in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  let cbyte := nth_byte (autocast (T := mword)
                 (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
  (2 <= n)%nat ->
  page_valid p ->
  m0 !!! Regidx a1_idx = cval ->
  m0 !!! Regidx a2_idx = (mword_of_int 4096 : mword 64) ->
  sie_cap_gpr kt m0 n b pcur -∗
  kernel_text -∗ pc_is pcE -∗
  page_own p -∗
  wp_next b pcur (fun (CID : CpuId) =>
    ∀ mfin,
    sie_cap_gpr kt mfin n b pcur -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 4096, (pa_add p j) ↦ₘ cbyte) -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type MEMSETPAGE.
  Parameter wp_memset_page_val_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier)
      (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64),
      wp_memset_page_val_sconf_body kt m0 n cval b pcur.
  Parameter wp_memset_page_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64),
      wp_memset_page_sconf_body kt m0 n cval b pcur.
End MEMSETPAGE.
