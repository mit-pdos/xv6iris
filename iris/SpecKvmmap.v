(* SpecKvmmap.v -- the public interface of Kvmmap, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import LockRank.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)


Definition wp_kvmmap_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string) :=
  let va := mm !!! Regidx (mword_of_int 11) in
  let pa := mm !!! Regidx (mword_of_int 12) in
  let vpn0 := svpn_of va in
  let ppn0 := (autocast (T := mword) (subrange_vec_dec pa 55 12) : mword 44) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* the kalloc chain below keeps its transient noff increment in int
     range; [lvl] is otherwise generic (the identity pin this replaced was
     an artifact of the boot-time callers) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (34 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
  subrange_vec_dec pa 11 0 = (zeros' 12 : mword 12) ->
  mm !!! Regidx (mword_of_int 13) = mword_of_int (Z.of_nat npages * 4096) ->
  (1 <= npages)%nat ->
  mm !!! Regidx (mword_of_int 14) = mword_of_int perm ->
  mappages_perm_ok perm ->
  (uint va + Z.of_nat npages * 4096 <= 2 ^ 38)%Z ->
  (uint pa + Z.of_nat npages * 4096 < 2 ^ 56)%Z ->
  pt_rep0 t m ->
  (forall i, (i < npages)%nat -> m !! vpn_at vpn0 i = None) ->
  (* COUNTED-ONLY (mirrors SpecProcMapstacks/SpecKvmmake): every caller in the
     tree already supplies [Some nb] here (kvmmake's six per-region calls,
     proc_mapstacks' boot-only call), and [nb] always dominates the missing
     nodes, so the kalloc-null / mappages-fail branch is DEAD -- NO panic.
     [on] stays [option nat] in the signature only so it keeps matching the
     dual-mode calling convention shared by [kalloc_env] and the sibling
     specs in this cone. *)
  (exists nb, on = Some nb /\ (pt_missing t vpn0 npages < nb)%nat) ->
  (* order premise at the lowest rank this cone reaches: kvmmap -> mappages
     -> walk -> kalloc ("kmem", 13). *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT0 mm K b p -∗
  cpu_own lvl eb p b lks -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.kvmmap) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env γa on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t' : ptree) (g : nat),
    sie_cap_gpr KT0 mr K b p -∗
    cpu_own lvl eb p b lks -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
    kalloc_env γa (avail_sub on g) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜pt_base t' = pt_base t⌝ -∗
    ⌜pt_rep0 t' (pt_insert_run m vpn0 ppn0 perm npages)⌝ -∗
    ⌜pt_present_mono t t'⌝ -∗
    ⌜(g <= pt_missing t vpn0 npages)%nat⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KVMMAP.
  Parameter wp_kvmmap_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (npages : nat) (perm : Z) (lvl K : nat) (eb : bool) (p : mword 64) (on : option nat) (b : bool) (lks : gset string),
      wp_kvmmap_sconf_body γa mm t m npages perm lvl K eb p on b lks.
End KVMMAP.
