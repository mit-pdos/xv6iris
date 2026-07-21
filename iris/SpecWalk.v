(* SpecWalk.v -- the public interface of Walk, stated independently of its
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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpLock.
Require Import CommonWalk PtTree KptTree.
Require Import PtBuild KvmSpec.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import WpMemsetS.
Require Import SpecMemset.
Require Import SpecKalloc.
Require Import WpWalkInstr UserBits.
Require Import WpMemsetPage.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import RiscvExec RiscvTryStep.
Import Defs.

Notation WK := KernelSyms.walk.

Definition wp_walk_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat) :=
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let sp0 : mword 64 := mm !!! Regidx csp_rs1 in
  let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
  lvl = 0%nat ->
  (22 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int 1 ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn mm K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
  kernel_text -∗
  pc_is (mword_of_int KernelSyms.walk) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
  ( ∀ (mr : regfile) (t' : ptree),
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mr K -∗ intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ptree_same_rep0 t t'⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
      \/ (exists p2 p1 w0,
           ptree_level0 t' vpn p2 p1 w0 /\
           mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WALK.
  Parameter wp_walk_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat),
      wp_walk_sconf_body γ root_ppn γa Φ mm t m K lvl.
End WALK.
