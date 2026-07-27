(* SpecUvmcreate.v -- the public interface of uvmcreate (kernel/vm.c), stated
   independently of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import RegFile.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmSpec.
From Kernel Require KernelSyms.

Notation UVMC := KernelSyms.uvmcreate.

(* uvmcreate(): kalloc one page, memset it to zero, return it as an empty
   root page table (a0 = the page's byte address; 0 on allocation failure).

   COUNTED-ONLY (premise ⌜on = Some nb ∧ 0 < nb⌝), as kvmmake is: with a
   positive page budget kalloc cannot fail, so the null return is dead and
   the post is unconditional.  Its one caller, proc_pagetable, runs on a
   counted budget for exactly the same reason (its own failure arms call
   uvmfree/uvmunmap, which are not verified).

   The fresh page is handed over as [ptree_own 2 1 (pt_empty_node b)] -- an
   all-zero Sv39 root, which is what the caller's first mappages consumes --
   and [page_valid] rides along so the caller can refute its own null test.

   stack_own bound 18 = own 4-slot frame + kalloc's 14 (memset needs 2). *)
Definition wp_uvmcreate_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) :=
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  lvl = 0%nat ->
  (18 <= K)%nat ->
  (exists nb, on = Some nb /\ (0 < nb)%nat) ->
  (* kalloc's push/pop addresses this cpu's cells through tp *)
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  sie_cap_gpr γ mm K -∗
  cpu_own γ lvl eb p C -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.uvmcreate) -∗
  kalloc_env γa on (mm !!! Regidx (mword_of_int 4)) -∗
  ( ∀ (mr : regfile) (b : mword 44),
    sie_cap_gpr γ mr K -∗
    cpu_own γ lvl eb p C -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) (pt_empty_node b) -∗
    ⌜mr !!! Regidx (mword_of_int 10)
       = zero_extend' 64 (concat_vec b (zeros' 12 : mword 12))⌝ -∗
    ⌜page_valid (mr !!! Regidx (mword_of_int 10))⌝ -∗
    kalloc_env γa (avail_sub on 1) (mm !!! Regidx (mword_of_int 4)) -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMCREATE.
  Parameter wp_uvmcreate_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat),
      wp_uvmcreate_sconf_body γ γa Φ mm lvl K eb p C on.
End UVMCREATE.
