(* SpecKvmmake.v -- the public interface of kvmmake, stated independently of its
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


(* kvmmake(): kalloc a fresh root page, memset it, run the six kvmmap regions
   (UART/VIRTIO/PLIC RW, text RX, data RW, trampoline RX) then proc_mapstacks.
   Returns (a0) the root page's byte address.  The result table represents
   [kvm_map_full pas] and has exactly 102 table nodes.  COUNTED-ONLY (premise
   ⌜on = Some nb ∧ 166 < nb⌝): kvmmake is boot-only (kvminit its sole caller),
   so it needs no None mode -- a deviation from the chain's dual-mode specs,
   justified by the absence of any non-boot caller.  With the budget premise no
   kalloc can fail, so NO panic credential anywhere.  The premise is STRICT while the
   post's [avail_sub on K_kvmmake] is the true consumption: the chain's
   counted-arm convention (kvmmap's [missing < nb], proc_mapstacks'
   [64 + kstacks_missing < nb]) demands one spare page beyond consumption --
   a [Some 0] remainder would leave the innermost failure arm's [avail_zero]
   unrefutable.
   stack_own bound 48 = own 4-slot frame + proc_mapstacks' 44 (PROVISIONAL,
   pending the decode pass). *)
Definition wp_kvmmake_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (γk : gname * gname) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :=
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  lvl = 0%nat ->
  (48 <= K)%nat ->
  (exists nb, on = Some nb /\ (K_kvmmake < nb)%nat) ->
  (* kvmmake kallocs the root table and every kvmmap page: "kmem" (13). *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT0 mm K b p -∗
  cpu_own lvl eb p b lks -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.kvmmake) -∗
  kalloc_env_at γa γk on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t : ptree) (pas : nat -> mword 44),
    sie_cap_gpr KT0 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t -∗
    ⌜mr !!! Regidx (mword_of_int 10)
       = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
    ⌜pt_rep0 t (kvm_map_full pas)⌝ -∗
    ⌜pt_nodes t = 102%nat⌝ -∗
    kalloc_env_at γa γk (avail_sub on K_kvmmake) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜kvm_pas_ok pas⌝ -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KVMMAKE.
  Parameter wp_kvmmake_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (γk : gname * gname) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_kvmmake_sconf_body γa γk mm lvl K eb p on b lks.
End KVMMAKE.
