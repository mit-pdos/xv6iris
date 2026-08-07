(* SpecUvmalloc.v -- the public interface of Uvmalloc, stated independently
   of its proof.

     uint64 uvmalloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz,
                     int xperm) {
       if (newsz < oldsz) return oldsz;
       oldsz = PGROUNDUP(oldsz);
       for (a = oldsz; a < newsz; a += PGSIZE) {
         mem = kalloc();
         if (mem == 0) { uvmdealloc(pagetable, a, oldsz); return 0; }
         memset(mem, 0, PGSIZE);
         if (mappages(pagetable, a, PGSIZE, (uint64)mem,
                      PTE_R | PTE_U | xperm) != 0) {
           kfree(mem); uvmdealloc(pagetable, a, oldsz); return 0;
         }
       }
       return newsz;
     }

   STATED AT THE [proc_pt] ALTITUDE: uvmalloc PRESERVES the valid-user-page-
   table predicate, growing the user map by exactly the run of pages
   [PGROUNDUP(oldsz) .. newsz).

   THE FAILURE ARM RESTORES [proc_pt P] EXACTLY.  This is the whole point of
   the uvmdealloc call in the C code, and the spec says it: out of memory,
   the caller gets back the descriptor it passed in -- not a weaker one, not
   an existential.  It is provable because the pages the loop had already
   mapped are precisely the ones uvmdealloc unmaps, and the run was fresh in
   [ud_um] to begin with ([ProcPtOwn.um_del_run_restore]).

   WHICH PAGES, AND AT WHAT PERMISSION.  The success arm cannot NAME the new
   leaves -- which pages kalloc returned is not determined -- so it gives an
   existential [P'] pinned by two facts: [uptd_ext P P'] (same root, same
   trapframe, the old map is a submap) and its DOMAIN, which is the old
   domain plus exactly [vpn_run vpn0 n].  Together those say "the map gained
   the run and nothing else".

   [xperm] is a runtime argument, so the permission cannot be a literal:
   what the invariant needs of the resulting leaf is packaged as the pure,
   ppn-independent [uvm_perm_ok (Z.lor xperm 18)] (ProcPtOwn §2c; 18 =
   PTE_R|PTE_U, which the [ori] instruction adds).  A caller discharges it by
   [vm_compute] at its own concrete permission -- the four instances xv6 uses
   are [uvm_perm_ok_18 / _22 / _26 / _30].

   AMBIGUITY NOTE: with [newsz = 0] the success arm also returns 0, so a
   caller that reads a0 = 0 as failure is being conservative rather than
   wrong; every real caller passes a positive newsz.

   Zero-fill of the new pages is deliberately not exposed (same reason as
   vmfault: [proc_pt] owns pages at existential bytes). *)
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
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KallocInv.
Require Import PtBuild KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_uvmalloc_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (xperm : Z) (K : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmalloc in
  let oldsz := mm !!! Regidx (mword_of_int 11) in
  let newsz := mm !!! Regidx (mword_of_int 12) in
  let vpn0 := svpn_of (pgroundup oldsz) in
  let n := uvma_np oldsz newsz in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 10-slot frame + mappages' 32 (kalloc 14, uvmdealloc 26, memset less) *)
  (42 <= K)%nat ->
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the permission: [ori s6,a3,18] makes the mappages perm [xperm | 18] *)
  mm !!! Regidx (mword_of_int 13) = (mword_of_int xperm : mword 64) ->
  (0 <= xperm < 512)%Z ->
  uvm_perm_ok (Z.lor xperm 18) ->
  (* every page the loop maps lies in the user region, below TRAPFRAME.  The
     bound is [<= uvm_maxsz], not [+ 4096 <=]: the last page the loop maps
     starts at PGROUNDUP(newsz) - 4096, so a size equal to TRAPFRAME is
     exactly legal -- and it is the size growproc's own check
     ([sz + n > TRAPFRAME] returns -1) lets through. *)
  (uint oldsz <= uvm_maxsz)%Z ->
  (uint newsz <= uvm_maxsz)%Z ->
  (* the run is unmapped to begin with (mappages panics on a remap, and it
     is what makes the failure arm's rollback exact) *)
  (forall i, (i < n)%nat -> P.(ud_um) !! vpn_at vpn0 i = None) ->
  sie_cap_gpr mm K b p -∗
  cpu_own 0%nat eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    cpu_own 0%nat eb p C b -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    ( (* out of memory: rolled back to exactly the table we were given *)
      (⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64)⌝ ∗
       proc_pt P)
      ∨ (* the map gained precisely the run *)
      (∃ P' : uptd,
         ⌜uptd_ext P P'⌝ ∗
         ⌜dom P'.(ud_um) = dom P.(ud_um) ∪ vpn_run vpn0 n⌝ ∗
         ⌜ ((uint newsz < uint oldsz)%Z /\
            mr !!! Regidx (mword_of_int 10) = oldsz)
           \/ ((uint oldsz <= uint newsz)%Z /\
               mr !!! Regidx (mword_of_int 10) = newsz) ⌝ ∗
         proc_pt P') ) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMALLOC.
  Parameter wp_uvmalloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (xperm : Z) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (b : bool),
      wp_uvmalloc_sconf_body γa Φ mm P xperm K eb p C b.
End UVMALLOC.
