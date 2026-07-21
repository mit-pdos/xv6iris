(* SpecFreerange.v -- the public interface of Freerange, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec RiscvExtras.
Require Import WpGpr InstrBytes WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved.
Require Import KernelText.
Require Import WpMycpu WpLock.
Require Import KallocInv.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import SpecKfree.
From Kernel Require KernelSyms.
Require Import RiscvExec RiscvTryStep RiscvFetchExec.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation FR := KernelSyms.freerange.

Definition PGSIZEv : mword 64 := mword_of_int 4096.
Definition negPGSIZEv : mword 64 := mword_of_int (-4096).   (* the ~0xfff page mask *)

(* [avail_inc] applied [k] times -- the page-count token after freeing [k]
   pages.  freerange starts at [Some 0] and ends at [Some (length ps)]. *)
Fixpoint avail_inc_n (on : option nat) (k : nat) : option nat :=
  match k with O => on | S k' => avail_inc (avail_inc_n on k') end.
Fixpoint prun (pa_end s1 : mword 64) (ps : list (mword 64)) : Prop :=
  match ps with
  | [] => zopz0zI_u pa_end s1 = true
  | p :: rest =>
      zopz0zI_u pa_end s1 = false
      /\ p = add_vec s1 negPGSIZEv
      /\ page_valid p
      /\ prun pa_end (add_vec s1 PGSIZEv) rest
  end.

Definition wp_freerange_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (ps : list (mword 64)) (K ncnt : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.freerange in
  let pa_start := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pa_end := m !!! Regidx (mword_of_int 11 : mword 5) in
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  let s1entry := add_vec (and_vec (add_vec pa_start (mword_of_int 4095 : mword 64)) negPGSIZEv) PGSIZEv in
  (20 <= K)%nat ->
  ncnt = 0%nat ->
  eq_vec (zero_reg : mword 64) cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  lk = mword_of_int KernelSyms.kmem ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  prun pa_end s1entry ps ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m K -∗
  intr_count γ root_ppn ncnt -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk (kmem_res γk fl) -∗
  ([∗ list] p ∈ ps, page_own p) -∗
  a_noff ↦₄ (zeros' 32 : mword 32) -∗
  (∃ iv : mword 32, a_int ↦₄ iv) -∗
  a_cpu ↦₈ (zero_reg : mword 64) -∗
  kalloc_avail γk (Some 0%nat) -∗
  ( ∀ mr,
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap_gpr γ root_ppn mr K -∗
    intr_count γ root_ppn ncnt -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    a_noff ↦₄ (zeros' 32 : mword 32) -∗
    (∃ iv : mword 32, a_int ↦₄ iv) -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    kalloc_avail γk (Some (length ps)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FREERANGE.
  Parameter wp_freerange_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (ps : list (mword 64)) (K ncnt : nat),
      wp_freerange_sconf_body γ root_ppn Φ γl γk lk fl m ps K ncnt.
End FREERANGE.
