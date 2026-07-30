(* SpecProcMapstacks.v -- the public interface of proc_mapstacks, stated
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
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmMap KvmSpec.
From Kernel Require KernelSyms.

Notation PMS := KernelSyms.proc_mapstacks.

(* proc_mapstacks(kpgtbl=a0): kalloc a page for each of the 64 process kernel
   stacks and kvmmap it at KSTACK(i) (RW, one page).  The stack pas are
   kalloc-chosen -- existential (as a FUNCTION [nat -> mword 44]) in the post --
   and the represented map gains the 64 kstack entries [kvm_stacks pas 64 m].
   COUNTED-ONLY (premise ⌜on = Some nb ∧ 64 + kstacks_missing t < nb⌝):
   proc_mapstacks is boot-only (kvmmake its sole caller), and its failure path is
   panic("kvminit") on a kalloc-null, so a None mode is meaningless here -- a
   deviation from the chain's dual-mode specs, justified by the absence of any
   non-boot caller.  The budget exceeds 64 (the leaf pages) plus
   [kstacks_missing t] (the naive-sum UPPER BOUND on the tables the 64 walks
   graft -- see KvmMap; the proof telescopes it), so every kalloc-null /
   kvmmap-fail branch is DEAD and the success-only post is honest -- NO panic_wp.
   stack_own bound 44 = own 10-slot frame + kvmmap's 34 (PROVISIONAL). *)
Definition wp_proc_mapstacks_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool) :=
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* the kalloc chain below keeps its transient noff increment in int
     range; [lvl] is otherwise generic (the identity pin this replaced was
     an artifact of the boot-time callers) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (44 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  pt_rep0 t m ->
  (forall i : nat, (i < 64)%nat -> m !! kstack_vpn i = None) ->
  (exists nb, on = Some nb /\ (64 + kstacks_missing t < nb)%nat) ->
  sie_cap_gpr mm K b -∗
  cpu_own lvl eb p C -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.proc_mapstacks) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env γa on -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat) (pas : nat -> mword 44),
    sie_cap_gpr mr K b -∗
    cpu_own lvl eb p C -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
    kalloc_env γa (avail_sub on (64 + g)) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜pt_base t' = pt_base t⌝ -∗
    ⌜kvm_pas_ok pas⌝ -∗
    ⌜pt_rep0 t' (kvm_stacks pas 64 m)⌝ -∗
    ⌜(g <= kstacks_missing t)%nat⌝ -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PROC_MAPSTACKS.
  Parameter wp_proc_mapstacks_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool),
      wp_proc_mapstacks_sconf_body γa Φ mm t m lvl K eb p C on b.
End PROC_MAPSTACKS.
