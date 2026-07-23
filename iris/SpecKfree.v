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
Require Import IntrDefs.
Require Import ProcGeom SwtchCtx CpuOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.

Notation KF := KernelSyms.kfree.

Definition wp_kfree_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (cpuold : mword 64) (on : option nat) (n : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ) (K : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfree in
  let p := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let cpuv := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
  let a_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (14 <= K)%nat ->
  eq_vec (cpuold : mword 64) cpuv = false ->
  (* the tp register holds THIS cpu's id (acquire/release cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  lk = mword_of_int KernelSyms.kmem ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr γ m K -∗
  cpu_own γ n eb pcur C -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk "kmem"%string (kmem_res γk fl) -∗
  kfree_pre p -∗
  kalloc_avail γk on -∗
  a_cpu ↦₈ cpuold -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    cpu_own γ n eb pcur C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_avail γk (avail_inc on) -∗
    a_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KFREE.
  Parameter wp_kfree_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (cpuold : mword 64) (on : option nat) (n : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ) (K : nat),
      wp_kfree_sconf_body γ Φ γl γk lk fl m cpuold on n eb pcur C K.
End KFREE.
