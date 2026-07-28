(* SpecWalk.v -- the public interface of Walk, stated independently of its
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
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpLock.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation WK := KernelSyms.walk.

Definition wp_walk_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) :=
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* the kalloc chain below keeps its transient noff increment in int
     range; [lvl] is otherwise generic (the identity pin this replaced was
     an artifact of the boot-time callers) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (22 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int 1 ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  (* the kvm chain runs on the ambient CPU: kalloc's push/pop addresses
     this cpu's cells through tp *)
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  sie_cap_gpr γ mm K -∗ cpu_own γ lvl eb p C -∗
  kernel_text -∗
  pc_is (mword_of_int KernelSyms.walk) -∗
  ptree_own 2 (DfracOwn 1) t -∗
  kalloc_env γa on (mm !!! Regidx (mword_of_int 4)) -∗
  ( ∀ (mr : regfile) (t' : ptree) (g : nat),
    sie_cap_gpr γ mr K -∗ cpu_own γ lvl eb p C -∗
    pc_is ret_tgt -∗
    ptree_own 2 (DfracOwn 1) t' -∗
    ⌜pt_nodes t' = (pt_nodes t + g)%nat⌝ -∗
    kalloc_env γa (avail_sub on g) (mm !!! Regidx (mword_of_int 4)) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ptree_same_rep0 t t'⌝ -∗
    ⌜ptree_offpath_eq vpn t t'⌝ -∗
    ⌜pt_present_mono t t'⌝ -∗
    ⌜(g <= pt_missing t vpn 1)%nat⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0
         /\ avail_zero (avail_sub on g))
      \/ (exists p2 p1 w0,
           ptree_level0 t' vpn p2 p1 w0 /\
           mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WALK.
  Parameter wp_walk_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree) (m : gmap (mword 27) (mword 64)) (K : nat) (lvl : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat),
      wp_walk_sconf_body γ γa Φ mm t m K lvl eb p C on.
End WALK.

(* --------------------------------------------------------------------- *)
(* walk with alloc = 0 (ismapped's callee): a READ-ONLY descent.  The     *)
(* kalloc branch is short-circuited (`!alloc || ...`) so there is no      *)
(* kalloc_env, no cpu_own and no panic contract (the va >= MAXVA panic    *)
(* arm is dead under the canonicality premise), and the tree is taken at  *)
(* a GENERIC dfrac and returned UNCHANGED.  The result is decided by the  *)
(* represented map: a vpn blocked at L2/L1 returns 0; a path that reaches *)
(* level 0 returns that slot's address -- with the slot's current word    *)
(* either the map's leaf (mapped) or the literal zero (unmapped).         *)
(* --------------------------------------------------------------------- *)

Definition wp_walk_noalloc_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree)
    (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.walk in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (8 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  mm !!! Regidx (mword_of_int 12) = mword_of_int 0 ->
  (uint va < 2 ^ 38)%Z ->
  pt_rep0 t m ->
  sie_cap_gpr γ mm K -∗
  kernel_text -∗
  pc_is pcE -∗
  ptree_own 2 dq t -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr γ mr K -∗
    pc_is ret_tgt -∗
    ptree_own 2 dq t -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\ m !! vpn = None)
      \/ (exists p2 p1 w0,
           ptree_level0 t vpn p2 p1 w0 /\
           mr !!! Regidx (mword_of_int 10) = pt_addr0 p1 vpn /\
           (m !! vpn = Some w0
            \/ (w0 = mword_of_int 0 /\ m !! vpn = None))) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type WALK_NOALLOC.
  Parameter wp_walk_noalloc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac),
      wp_walk_noalloc_sconf_body γ Φ mm t m K dq.
End WALK_NOALLOC.
