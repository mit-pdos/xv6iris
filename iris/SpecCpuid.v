(* SpecCpuid.v -- the public interface of cpuid, stated independently of its
   proof.  [cpuid] (xv6-riscv/kernel/proc.c) reads the thread pointer [tp]
   (which start() initialises to the hart id) and returns it as an [int]:

     0x800018d0 <cpuid>:
       ...prologue...
       mv     a0,tp        a0 = tp
       sext.w a0,a0        a0 = sign_extend(tp[31:0])   (the [int] truncation)
       ...epilogue...

   So the return value is [cpuid_ret tp] = the sign-extension of tp's low 32
   bits.  For any legal hart id (< NCPU) the top bits are clear and
   [cpuid_ret tp = tp] ([cpuid_ret_id_small]).

   Requires only the definitional layer -- never a whole-function proof file --
   so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation CPUID := KernelSyms.cpuid.

(* the [int]-truncated hart id returned by cpuid: sign-extend tp's low 32. *)
Definition cpuid_ret (tp : mword 64) : mword 64 :=
  sign_extend' 64 (subrange_vec_dec tp 31 0 : mword 32).

Definition wp_cpuid_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.cpuid in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m0 n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  ( ∀ m' : regfile,
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn m' n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\
      m' !!! Regidx a0_idx = cpuid_ret (m0 !!! Regidx tp_idx) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* the JAL-call form (mirror of [wp_call_mycpu_sconf_cs]): a caller at [P] with
   [instr P false (JAL (jimm, ra))] whose target is [cpuid] runs the callee and
   returns to [P+4]. *)
Definition wp_call_cpuid_sconf_cs_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
  let pcE := mword_of_int KernelSyms.cpuid in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  add_vec P (sign_extend' 64 jimm) = pcE ->
  eq_vec (access_vec_dec (pcE : mword 64) 0) ('b"0") = true ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sconf γ -∗ hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m n -∗ tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is P -∗
  instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
  ( ∀ mo,
    hart_state ↦ᵣ HART_ACTIVE tt -∗ sconf γ -∗
    sie_cap_gpr γ root_ppn mo n -∗ tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mo /\
      mo !!! Regidx a0_idx = cpuid_ret (m !!! Regidx tp_idx) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type CPUID.
  Parameter wp_cpuid_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat),
      wp_cpuid_sconf_body γ root_ppn Φ m0 n.
  Parameter wp_call_cpuid_sconf_cs :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat),
      wp_call_cpuid_sconf_cs_body γ root_ppn Φ P jimm m n.
End CPUID.
