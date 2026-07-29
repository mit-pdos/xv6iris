(* SpecUvmdealloc.v -- the public interface of Uvmdealloc, stated
   independently of its proof.

     uint64 uvmdealloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz) {
       if (newsz >= oldsz) return oldsz;
       if (PGROUNDUP(newsz) < PGROUNDUP(oldsz)) {
         int npages = (PGROUNDUP(oldsz) - PGROUNDUP(newsz)) / PGSIZE;
         uvmunmap(pagetable, PGROUNDUP(newsz), npages, 1);
       }
       return newsz;
     }

   STATED AT THE [proc_pt] ALTITUDE, over uvmunmap's contract: the user map
   loses the run of [uvmd_np oldsz newsz] vpns starting at PGROUNDUP(newsz),
   and their pages go back to kalloc.

   ONE POSTCONDITION, TWO ARMS.  The two C branches differ only in what they
   RETURN; both leave the table at [uptd_del_run P (svpn_of (pgroundup
   newsz)) (uvmd_np oldsz newsz)], because [uvmd_np] is [Z.to_nat] of a
   quotient that is 0 or negative exactly when the code skips the unmap
   (newsz >= oldsz, or the two page-rounded sizes coincide).  So the
   descriptor is named once and only the return value is a disjunction.  The
   [proc_pt_data_irrel] lemma is what lets a caller collapse a zero-length
   run back to its own [P].

   [uvm_maxsz] is TRAPFRAME (ProcPtOwn.v): the [+ 4096 <=] premises are what
   put every touched page strictly below it, which is uvmunmap's range
   premise. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import RegFile.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.

Notation UD := KernelSyms.uvmdealloc.

Definition wp_uvmdealloc_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmdealloc in
  let oldsz := mm !!! Regidx (mword_of_int 11) in
  let newsz := mm !!! Regidx (mword_of_int 12) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 4-slot frame + uvmunmap's 22 *)
  (26 <= K)%nat ->
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the OLD size names a page inside the user region.  Nothing is asked of
     [newsz]: on the arm where it matters it is below [oldsz] and so inherits
     this bound, and on the arm where it does not, [uvmd_np]'s guard makes
     the run empty -- which is what lets growproc call this at the wrapped
     [sz + n] an [sbrk] with a big negative argument computes. *)
  (uint oldsz <= uvm_maxsz)%Z ->
  sie_cap_gpr γ mm K -∗
  cpu_own γ 0%nat eb p C -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None cid_word -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr γ mr K -∗
    cpu_own γ 0%nat eb p C -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ ((uint newsz >= uint oldsz)%Z /\
        mr !!! Regidx (mword_of_int 10) = oldsz)
      \/ ((uint newsz < uint oldsz)%Z /\
          mr !!! Regidx (mword_of_int 10) = newsz) ⌝ -∗
    proc_pt (uptd_del_run P (svpn_of (pgroundup newsz)) (uvmd_np oldsz newsz)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMDEALLOC.
  Parameter wp_uvmdealloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_uvmdealloc_sconf_body γ γa Φ mm P K eb p C.
End UVMDEALLOC.
