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
Require Import RiscvPtsto RiscvLang.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmMap KvmSpec.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


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
   kvmmap-fail branch is DEAD and the success-only post is honest -- NO panic.
   stack_own bound 44 = own 10-slot frame + kvmmap's 34 (PROVISIONAL). *)
Definition wp_proc_mapstacks_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γa : gname) (γk : gname * gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :=
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
  (* proc_mapstacks kalloc's a page for each of the 64 kernel stacks: its
     cone touches "kmem" (13) via the per-iteration kalloc call, and nothing
     lower (kvmmap's own Spec exposes no locks_below premise). *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT0 mm K b p -∗
  cpu_own lvl eb p b lks -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.proc_mapstacks) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env_at γa γk on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat) (pas : nat -> mword 44),
    sie_cap_gpr KT0 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
    kalloc_env_at γa γk (avail_sub on (64 + g)) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜pt_base t' = pt_base t⌝ -∗
    ⌜kvm_pas_ok pas⌝ -∗
    ⌜pt_rep0 t' (kvm_stacks pas 64 m)⌝ -∗
    ⌜(g <= kstacks_missing t)%nat⌝ -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PROC_MAPSTACKS.
  Parameter wp_proc_mapstacks_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γa : gname) (γk : gname * gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_proc_mapstacks_sconf_body γa γk mm t m lvl K eb p on b lks.
End PROC_MAPSTACKS.
