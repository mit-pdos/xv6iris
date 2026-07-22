(* SpecKfree.v -- the public interface of Kfree, stated independently of its
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
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpMycpu WpLock.
Require Import KptTree.
Require Import IntrDefs.
Require Import IntrDefs.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Notation KF := KernelSyms.kfree.

Definition wp_kfree_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (on : option nat) (n : nat) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfree in
  let p := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_noff := add_vec cpuv (sign_extend' 64 (mword_of_int 120 : mword 12)) in
  let a_int := add_vec cpuv (sign_extend' 64 (mword_of_int 124 : mword 12)) in
  let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (* acquire's noff-increment store value (function of the ghost noff alone) *)
  let po_noff_a5 := sign_extend' 64 (subrange_vec_dec
      (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0) in
  let po_noff_store := (autocast (T := mword) (subrange_vec_dec po_noff_a5 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  (* release's noff-decrement store value (its pop_off restores noff = noffv);
     returned in the [a_noff] cell so a repeated caller can re-thread it. *)
  let noff_ret := (autocast (T := mword) (subrange_vec_dec
      (sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 po_noff_store)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
      (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
  (14 <= K)%nat ->
  eq_vec (cpuold : mword 64) cpuv = false ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  lk = mword_of_int KernelSyms.kmem ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (* the hardware noff counter is in lockstep with the ghost token level *)
  (neq_vec (sign_extend' 64 noffv) zero_reg = false <-> n = 0%nat) ->
  zopz0zKzJ_s zero_reg (sign_extend' 64 po_noff_store) = false ->
  eq_vec (sign_extend' 64
     (if eq_vec (sign_extend' 64 noffv) zero_reg then (zeros' 32) else intena_old)) zero_reg = true ->
  sie_cap_gpr γ m K -∗
  intr_count γ n -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk "kmem"%string (kmem_res γk fl) -∗
  kfree_pre p -∗
  kalloc_avail γk on -∗
  a_noff ↦₄ noffv -∗
  a_int ↦₄ intena_old -∗
  a_cpu ↦₈ cpuold -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    intr_count γ n -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_avail γk (avail_inc on) -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    a_noff ↦₄ noff_ret -∗
    (∃ iv : mword 32, a_int ↦₄ iv) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KFREE.
  Parameter wp_kfree_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (cpuold : mword 64) (noffv intena_old : mword 32) (on : option nat) (n : nat) (K : nat),
      wp_kfree_sconf_body γ Φ γl γk lk fl m cpuold noffv intena_old on n K.
End KFREE.
