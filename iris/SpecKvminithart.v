(* SpecKvminithart.v -- the public interface of kvminithart (kernel/vm.c):
   the Bare->Sv39 switch that installs the verified kernel page table.

   kvminithart() = sfence.vma ; w_satp(MAKE_SATP(kernel_pagetable)) ;
   sfence.vma, wrapped in a 2-slot frame.  The rwx-kmap STAGE 6c
   deliverable: it DISSOLVES the translation slot's Bare arm (recovering
   the satp cell + the exact static auth [kmap_auth kmap_M0] + the stvec
   cell) and RE-SEALS it at the kernel PT (KPT arm), minting the 65
   persistent claims (trampoline + 64 kstacks) the rest of the kernel
   holds.  The receipt [strans_bit] flips '0 (Bare) -> '1 (KPT).

   Resources CONSUMED into the slot: the tlb cell, the page table
   [ptree_own], and the Bare-arm receipt's twin.  The satp cell stays
   inside the slot.  Boot-only, straight-line, no callees -> unconditional
   success, no panic_wp.  Follows SpecKvminit.v's file conventions. *)
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
Require Import RegFile.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import PtTree.
Require Import PtBuild KptPt KptExecMap KMap KptTree KvmMap.
From Kernel Require KernelSyms.

Notation KVMIH := KernelSyms.kvminithart.

(* kvminithart(): the Bare->Sv39 kernel-page-table switch.  See the header. *)
Definition wp_kvminithart_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat)
    (t : ptree) (pas : nat -> mword 44)
    (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) :=
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  let root_b := zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) in
  lvl = 0%nat ->
  (2 <= K)%nat ->
  pt_rep0 t (kvm_map_full pas) ->
  kvm_pas_ok pas ->
  sie_cap_gpr γ mm K -∗
  strans_bit strans_bit_bare -∗
  kernel_text -∗
  pc_is (mword_of_int KVMIH) -∗
  tlb ↦ᵣ tlbvec0 -∗
  (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ root_b -∗
  ptree_own 2 (DfracOwn 1) t -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr γ mr K -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    strans_bit strans_bit_kpt -∗
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ root_b -∗
    kmap_at tramp_vpn tramp_ppn KP_rx -∗
    ([∗ list] i ∈ seq 0 64, kmap_at (kstack_vpn i) (pas i) KP_rw) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KVMINITHART.
  Parameter wp_kvminithart_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat)
      (t : ptree) (pas : nat -> mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)),
      wp_kvminithart_sconf_body γ Φ mm lvl K t pas tlbvec0.
End KVMINITHART.
