(* SpecIsmapped.v -- the public interface of Ismapped, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   ismapped(pagetable, va) = walk(pagetable, va, 0) reaches a slot whose word
   has the V bit set.  Stated over the EXACT represented map [pt_rep0 t m]
   (the xv6 zero-stop-word shape): the answer is [m]'s verdict at [va]'s vpn.
   Read-only -- the tree rides through at a generic dfrac, unchanged.  No
   kalloc environment, no cpu_own: the only callee is the no-alloc walk. *)
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
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import PtTree.
Require Import PtBuild.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_ismapped_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile) (t : ptree)
    (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.ismapped in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (10 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ptree_own 2 dq t -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ptree_own 2 dq t -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
      \/ (exists w, m !! vpn = Some w /\
           mr !!! Regidx (mword_of_int 10) = mword_of_int 1) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ISMAPPED.
  Parameter wp_ismapped_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_ismapped_sconf_body mm t m K dq b p.
End ISMAPPED.
