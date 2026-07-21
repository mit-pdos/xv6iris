(* SpecMappages.v -- the public interface of Mappages, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
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
Require Import WpGpr WpLock WpMmodeLeafBase.
Require Import RegFile.
Require Import CalleeSaved StackOwn.
Require Import KptTree.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import UserBits.
Require Import SpecWalk.
From Kernel Require KernelSyms.

Notation MP := KernelSyms.mappages.

Definition wp_mappages_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat) :=
  let va := mm !!! Regidx (mword_of_int 11) in
  let pa := mm !!! Regidx (mword_of_int 13) in
  let vpn0 := svpn_of va in
  let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
  let ret_tgt := update_vec_dec (mm !!! Regidx (mword_of_int 1)) 0 ('b"0") in
  lvl = 0%nat ->
  (32 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
  subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int (Z.of_nat npages * 4096) ->
  (1 <= npages)%nat ->
  mm !!! Regidx (mword_of_int 14) = mword_of_int perm ->
  mappages_perm_ok perm ->
  (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
  (uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z ->
  pt_rep0 t m ->
  (forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None) ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap_gpr γ root_ppn mm K -∗
  intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.mappages) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
  ( ∀ (mr : regfile) (t' : ptree) (k : nat),
    sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗ sie_cap_gpr γ root_ppn mr K -∗
    intr_count γ root_ppn lvl -∗ tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    kalloc_env γa (mm !!! Regidx (mword_of_int 4)) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜pt_base t' = pt_base t⌝ -∗
    ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm k)⌝ -∗
    ⌜ (k = npages /\ mr !!! Regidx (mword_of_int 10) = mword_of_int 0)
      \/ ((k < npages)%nat /\
          mr !!! Regidx (mword_of_int 10) = mword_of_int (-1)) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MAPPAGES.
  Parameter wp_mappages_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat),
      wp_mappages_sconf_body γ root_ppn γa Φ mm t m npages perm lvl K.
End MAPPAGES.
