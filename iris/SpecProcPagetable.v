(* SpecProcPagetable.v -- the public interface of proc_pagetable
   (kernel/proc.c), stated independently of its proof.  Requires only the
   definitional layer -- never a whole-function proof file -- so every function
   proof can be checked in parallel. *)
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
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import PtTree.
Require Import PtBuild KvmSpec.
Require Import ProcPt.
From Kernel Require KernelSyms.


(* [p->trapframe] -- the only field of the process this function reads -- is
   [ProcGeom.p_trapframe] (proc.h offset 88; the [ld a3,88(s2)] at
   proc_pagetable+0x34), beside [p_pagetable]/[p_sz]/[p_context]. *)

(* the table pages proc_pagetable allocates: the root, plus the l1 and l0
   tables the TRAMPOLINE walk builds (TRAPFRAME shares both -- see
   ProcPt.ppt_missing_tf_zero). *)
Definition K_proc_pagetable : nat := 3.

(* WHAT proc_pagetable RETURNS, with the resources that go with it.  [rv] is
   the returned pointer -- a0 at the [ret], and s1 at the +0x4c join where
   all four exits meet (the two error tails both end [li s1,0; j +0x4c], and
   uvmcreate's null exit reaches +0x4c straight from the [beqz] at +0x14).

   SUCCESS: the table that was built, its map, its node count, and the
   consumption ledger.

   FAILURE: a null return, and NOTHING OWED -- whatever table existed has
   gone back through the tails' uvmunmap/uvmfree.  But the COUNT is gone with
   it: uvmfree exists only at [kalloc_env _ None], so the tails reseal the
   environment ([KvmSpec.kalloc_env_seal]).  The arm carries the exhaustion
   witness that made the tail reachable in the first place -- [avail_zero
   (avail_sub on n)] for the [n <= K_proc_pagetable] pages consumed before
   the failure.  THAT CARRIAGE IS THE WHOLE POINT: it is what lets a caller
   who knows [on = Some nb] with [K_proc_pagetable < nb] refute this arm, and
   so what lets one proof serve both the counted contract below and the
   uncounted one allocproc's failure tails need. *)
Definition ppt_post `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (on : option nat) (tfp : mword 44) (rv : mword 64) : iProp Σ :=
  ((∃ t : ptree,
      ⌜rv = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ ∗
      ptree_own 2 (DfracOwn 1) t ∗
      ⌜pt_rep0 t (ppt_map tfp)⌝ ∗
      ⌜(pt_nodes t <= K_proc_pagetable)%nat⌝ ∗
      kalloc_env γa (avail_sub on (pt_nodes t)))
   ∨ (⌜rv = (mword_of_int 0 : mword 64)⌝ ∗
      ⌜exists n : nat, (n <= K_proc_pagetable)%nat /\ avail_zero (avail_sub on n)⌝ ∗
      kalloc_env γa None))%I.

(* proc_pagetable(p): build a user page table with no user memory --
   uvmcreate() an empty root, then map TRAMPOLINE (R|X, at the kernel's
   trampoline page) and TRAPFRAME (R|W, at p->trapframe).  Returns (a0) the
   root page's byte address.

   PRECONDITION ON THE PROCESS: only that [p->trapframe] holds a PAGE-ALIGNED
   address (readable at any fraction).  No proc invariant, no proc lock, and
   no claim that the trapframe page is owned or allocated -- proc_pagetable
   only reads the pointer and maps it.  The 56-bit bound is the physical
   address-width sanity condition mappages' run inherits, not a real
   constraint on the caller.

   COUNTED-ONLY (premise ⌜on = Some nb ∧ K_proc_pagetable < nb⌝), as the rest
   of the kalloc cone is: with a budget of 4 free pages neither uvmcreate's
   kalloc nor either mappages walk can fail, so both error tails -- which call
   uvmfree / uvmunmap, neither of them verified -- are DEAD.  The premise is
   strict (4 pages for a 3-page consumption) by the chain's counted-arm
   convention: a [Some 0] remainder would leave mappages' failure arm's
   [avail_zero] unrefutable.

   The post's represented map is [ppt_map tfp]; [ProcPt.ppt_bridge] turns it
   into [upt_tree_spec (pt_base t) tfp empty t], the user-table mapping
   invariant [utlb_inv_pt] is built from.  Consumption is exactly the tree
   that was built ([avail_sub on (pt_nodes t)], [pt_nodes t <= 3]).

   stack_own bound 40 = own 4-slot frame + uvmfree's 36 (mappages needs 32,
   uvmcreate 18).  uvmfree is what sets it, and uvmfree appears only in the
   ERROR TAILS -- which the counted premise makes unreachable.  The bound is
   charged anyway: a stack budget is a property of the code, not of the path
   a particular caller proves it takes. *)
Definition wp_proc_pagetable_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool) :=
  let pp := mm !!! Regidx (mword_of_int 10) in
  let tfp := (autocast (T := mword) (subrange_vec_dec tf 55 12) : mword 44) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (40 <= K)%nat ->
  (exists nb, on = Some nb /\ (K_proc_pagetable < nb)%nat) ->
  subrange_vec_dec tf 11 0 = (zeros' 12 : mword 12) ->
  (uint tf + 4096 < 2 ^ 56)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.proc_pagetable) -∗
  p_trapframe pp ↦₈{dqtf} tf -∗
  kalloc_env γa on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (t : ptree),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    p_trapframe pp ↦₈{dqtf} tf -∗
    ptree_own 2 (DfracOwn 1) t -∗
    ⌜mr !!! Regidx (mword_of_int 10)
       = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12))⌝ -∗
    ⌜pt_rep0 t (ppt_map tfp)⌝ -∗
    ⌜(pt_nodes t <= K_proc_pagetable)%nat⌝ -∗
    kalloc_env γa (avail_sub on (pt_nodes t)) -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE GENERAL CONTRACT, from which the counted one below is derived.
   Everything proc_pagetable actually does is here; the only difference is
   that the post is [ppt_post] rather than the success arm alone, so this one
   is stated at an ARBITRARY [on] -- including [None], which is where
   allocproc's own failure tails (and anything else outside the counted
   regime) have to call it. *)
Definition wp_proc_pagetable_core_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool) :=
  let pp := mm !!! Regidx (mword_of_int 10) in
  let tfp := (autocast (T := mword) (subrange_vec_dec tf 55 12) : mword 44) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  (40 <= K)%nat ->
  subrange_vec_dec tf 11 0 = (zeros' 12 : mword 12) ->
  (uint tf + 4096 < 2 ^ 56)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗ kernel_text -∗
  pc_is (mword_of_int KernelSyms.proc_pagetable) -∗
  p_trapframe pp ↦₈{dqtf} tf -∗
  kalloc_env γa on -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    p_trapframe pp ↦₈{dqtf} tf -∗
    ppt_post γa on tfp (mr !!! Regidx (mword_of_int 10)) -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PROC_PAGETABLE_GEN.
  Parameter wp_proc_pagetable_core :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool),
      wp_proc_pagetable_core_body γa mm tf dqtf lvl K eb p C on b.
End PROC_PAGETABLE_GEN.

Module Type PROC_PAGETABLE.
  Parameter wp_proc_pagetable_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile) (tf : mword 64) (dqtf : dfrac) (lvl K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (on : option nat) (b : bool),
      wp_proc_pagetable_sconf_body γa mm tf dqtf lvl K eb p C on b.
End PROC_PAGETABLE.
