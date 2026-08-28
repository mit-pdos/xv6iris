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

   STATED AT THE MEMORY-INDEXED [proc_ptm] ALTITUDE, and at that one only:
   uvmalloc PRESERVES the valid-user-page-table predicate, growing the user
   map by exactly the run of pages [PGROUNDUP(oldsz) .. newsz), and NAMES
   what the process's memory view becomes.  The ∃-[M] corollary this file
   used to carry beside it is gone -- every caller names the image it hands
   in.

   THE FAILURE ARM RESTORES THE VIEW IT WAS HANDED, EXACTLY.  This is the
   whole point of the uvmdealloc call in the C code, and the spec says it:
   out of memory, the caller gets back the descriptor AND the bytes it
   passed in -- not a weaker one, not an existential.  It is provable because the pages the loop had already
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
Require Import RiscvPtsto RiscvLang.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import PtBuild KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


(* ===================================================================== *)
(*  THE MEMORY-INDEXED CONTRACT.                                          *)
(* ===================================================================== *)
(* uvmalloc's whole effect on the process's memory is the SIZE MOVING:
   [umem_grow M s] is [M] with zeros over everything live at [s], and the
   union is left-biased, so not one byte the process could already read
   changes.  What makes that honest rather than vacuous is the memset:
   the pages the loop maps really do read as zero, which is what the
   lazily-backed vas at those addresses already claimed.

   THE FAILURE ARM GIVES BACK THE VIEW IT WAS HANDED, exactly -- same
   descriptor, same size, same bytes.  That is the whole point of the C
   code's uvmdealloc call, and at this altitude it is visible: the range
   the loop grew into is precisely the range the rollback deletes
   ([UserPtTree.umem_grow_del]).

   The size is [rsz], the value uvmalloc RETURNS, for the same reason
   uvmdealloc's is: that is the size the caller will store in [p->sz]. *)
Definition wp_uvmalloc_mem_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (P : uptd) (M : gmap Z (bv 8)) (xperm : Z) (K : nat) (eb : bool)
    (p : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmalloc in
  let oldsz := mm !!! Regidx (mword_of_int 11) in
  let newsz := mm !!! Regidx (mword_of_int 12) in
  let vpn0 := svpn_of (pgroundup oldsz) in
  let n := uvma_np oldsz newsz in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (42 <= K)%nat ->
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  mm !!! Regidx (mword_of_int 13) = (mword_of_int xperm : mword 64) ->
  (0 <= xperm < 512)%Z ->
  uvm_perm_ok (Z.lor xperm 18) ->
  (uint oldsz <= uvm_maxsz)%Z ->
  ((uint newsz <= uvm_maxsz)%Z \/ um_covered oldsz P.(ud_um)) ->
  (forall i, (i < n)%nat ->
     (bv_unsigned (pgroundup oldsz) + 4096 * Z.of_nat i + 4096 <= uvm_maxsz)%Z ->
     P.(ud_um) !! vpn_at vpn0 i = None) ->
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own 0%nat eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_ptm P (uint oldsz) M -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own 0%nat eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    ( (* out of memory: the view we were handed, byte for byte *)
      (⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64)⌝ ∗
       proc_ptm P (uint oldsz) M)
      ∨ (∃ (P' : uptd) (rsz : mword 64),
           ⌜uptd_ext P P'⌝ ∗
           ⌜dom P'.(ud_um) = dom P.(ud_um) ∪ vpn_run vpn0 n⌝ ∗
           ⌜forall v : mword 27, v ∈ vpn_run vpn0 n ->
              ∃ r : mword 64,
                P'.(ud_um) !! v = Some (uvm_pte (Z.lor xperm 18) r)⌝ ∗
           ⌜ ((uint newsz < uint oldsz)%Z /\ rsz = oldsz)
             \/ ((uint oldsz <= uint newsz)%Z /\ rsz = newsz) ⌝ ∗
           ⌜mr !!! Regidx (mword_of_int 10) = rsz⌝ ∗
           proc_ptm P' (uint rsz) (umem_grow M (uint rsz))) ) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UVMALLOC.
  Parameter wp_uvmalloc_mem_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (P : uptd) (M : gmap Z (bv 8)) (xperm : Z) (K : nat) (eb : bool)
      (p : mword 64) (b : bool) (lks : gset string),
      wp_uvmalloc_mem_sconf_body γa mm P M xperm K eb p b lks.
End UVMALLOC.
