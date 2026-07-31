(* SpecKvminit.v -- the public interface of kvminit, stated independently of its
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
Require Import WpLock.
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmMap KvmSpec.
From Kernel Require KernelSyms.

Notation KVMI := KernelSyms.kvminit.

(* kvminit(): kvmmake() then store its result into the global
   [kernel_pagetable] cell (an identity 8-byte word at
   KernelSyms.kernel_pagetable = 0x8000a238; pre = arbitrary [kpt0], post = the
   root page's byte address).  COUNTED-ONLY like kvmmake (boot-only, STRICT
   budget premise ⌜166 < nb⌝ -- see SpecKvmmake's spare-page note), so
   unconditional success, NO panic_wp.  This is THE deliverable: the verified
   construction whose post feeds the boot switch [wp_kvminithart] through
   [kvm_bridge].
   stack_own bound 50 = own 2-slot frame + kvmmake's 48 (PROVISIONAL). *)
Definition wp_kvminit_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (kpt0 : mword 64) (b : bool) :=
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  lvl = 0%nat ->
  (50 <= K)%nat ->
  (exists nb, on = Some nb /\ (K_kvmmake < nb)%nat) ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.kvminit) -∗
  (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈ kpt0 -∗
  kalloc_env γa on -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t : ptree) (pas : nat -> mword 44),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t -∗
    (mword_of_int KernelSyms.kernel_pagetable : mword 64)
      ↦₈ zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) -∗
    ⌜pt_rep0 t (kvm_map_full pas)⌝ -∗
    ⌜pt_nodes t = 102%nat⌝ -∗
    kalloc_env γa (avail_sub on K_kvmmake) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜kvm_pas_ok pas⌝ -∗
    ([∗ list] i ∈ seq 0 64,
       page_own (zero_extend' 64 (concat_vec (pas i) (zeros' 12 : mword 12)))) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type KVMINIT.
  Parameter wp_kvminit_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (kpt0 : mword 64) (b : bool),
      wp_kvminit_sconf_body γa Φ mm lvl K eb p C on kpt0 b.
End KVMINIT.
