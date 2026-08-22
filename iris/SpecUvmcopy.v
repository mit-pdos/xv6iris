(* SpecUvmcopy.v -- the public interface of Uvmcopy, stated independently of
   its proof.

     int uvmcopy(pagetable_t old, pagetable_t new, uint64 sz)
     {
       for (i = 0; i < sz; i += PGSIZE) {
         if ((pte = walk(old, i, 0)) == 0)  continue;
         if (( *pte & PTE_V) == 0)          continue;
         pa    = PTE2PA( *pte);
         flags = PTE_FLAGS( *pte);
         if ((mem = kalloc()) == 0) goto err;
         memmove(mem, (char * )pa, PGSIZE);
         if (mappages(new, i, PGSIZE, (uint64)mem, flags) != 0) {
           kfree(mem); goto err;
         }
       }
       return 0;
     err:
       uvmunmap(new, 0, i / PGSIZE, 1);
       return -1;
     }

   fork's workhorse: the ONE function that takes TWO process page tables.
   Both are at the [proc_pt] altitude and both stay there -- the parent is
   read-only (it comes back verbatim) and the child grows by the pages the
   parent had mapped below [sz].

   THE PERMISSION IS COPIED, NOT CHOSEN.  [flags = PTE_FLAGS( *pte)] is the
   parent leaf's own low ten bits, fed straight to mappages.  So unlike
   uvmalloc -- whose caller discharges [uvm_perm_ok] at a literal -- here
   the permission is whatever the parent's table happens to hold, and the
   spec must NOT ask the caller for anything about it.  It does not:
   [ProcPtOwn.uvm_perm_ok_of_leaf] derives [uvm_perm_ok (pte_flags10 w)]
   from what [proc_pt Pold] ALREADY guarantees about [w] (upt_map_wf's
   4K-leaf clause and upt_acc_wf's decided-access clause), because every
   predicate in either clause reads only a leaf's flag byte and extension
   bits -- both independent of the ppn.  That is the whole reason those
   two clauses were stated per-leaf-modulo-A/D rather than per-page.

   WHAT THE SUCCESS ARM SAYS.  Pointwise over the run, the child's map
   mirrors the parent's: unmapped where the parent is unmapped, and
   otherwise a leaf at the SAME permission on SOME kalloc page -- which
   page is not determined (kalloc chose it), so it is existential.
   Outside the run the child's map is untouched.  Together these pin [P']
   completely.

   ...MODULO A/D, and that is not slack -- it is what the code does.  What
   uvmcopy reads is [ *pte], the leaf as the HARDWARE last left it, i.e.
   [pte_set_ad w a d] for the parent's canonical leaf [w]; so the A and D
   bits the parent happened to have accumulated are copied into the child
   along with the permission.  The mapped case therefore reads "an A/D
   variant of [uvm_pte (pte_flags10 w) r]" rather than that leaf on the
   nose.  Every predicate the invariant asks of a leaf quantifies over all
   A/D variants ([upt_map_wf], [upt_acc_wf], [uvm_perm_ok]), so the noise
   is irrelevant to validity -- it only has to be said here.

   WHAT IT DELIBERATELY DOES NOT SAY: that the child's pages hold the same
   BYTES as the parent's.  [proc_pt] owns user pages at existential
   contents (the user-safety altitude -- SpecVmfault.v, SpecCopyin.v), so
   there is nothing at this altitude for the memmove's postcondition to be
   stated against.  Exposing it would mean giving [proc_pt] a
   contents-indexed form; that is a separate change, and every consumer so
   far wants the contents-blind one.

   THE FAILURE ARM RESTORES [proc_pt Pnew] EXACTLY, like uvmalloc's: the
   [err] label unmaps precisely [0, i), which is precisely the prefix the
   loop had mapped, and the run was fresh in the child to begin with
   ([ProcPtOwn.um_del_run_restore_sub] -- the SUBSET form, because
   uvmcopy maps only those vpns the parent had, not the whole run).

   AMBIGUITY NOTE: with [sz = 0] the frameless fast path at +0x00 returns 0
   with both tables untouched; that is the success arm at [n = 0]. *)
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
Require Import PtAdBits.
Require Import PtBuild KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Definition wp_uvmcopy_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (Pold Pnew : uptd) (K : nat) (eb : bool) (p : mword 64)
    (ilvl : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmcopy in
  let sz := mm !!! Regidx (mword_of_int 12) in
  let vpn0 := svpn_of (mword_of_int 0 : mword 64) in
  let n := uvm_np sz in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 10-slot frame + mappages' 32 (kalloc 14, uvmunmap 22, walk-noalloc 8,
     memmove 2 all fit inside it) *)
  (42 <= K)%nat ->
  (* [ilvl] is the interrupt nesting level: kfree's acquire/release keep the
     transient noff increment in int range.  It used to be pinned at 0 --
     an artifact of the boot-time callers. *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  mm !!! Regidx (mword_of_int 10) = page_base Pold.(ud_root) ->
  mm !!! Regidx (mword_of_int 11) = page_base Pnew.(ud_root) ->
  (* the copied region lies in the user area, below TRAPFRAME *)
  (uint sz <= uvm_maxsz)%Z ->
  (* the child's map is free over the run (mappages panics on a remap, and
     it is what makes the failure arm's rollback exact) *)
  (forall i, (i < n)%nat -> Pnew.(ud_um) !! vpn_at vpn0 i = None) ->
  (* uvmcopy's cone reaches kalloc/kfree directly and, via its err-path
     uvmunmap, kfree again -- all bound at "kmem" (13), the lowest rank
     the cone touches. *)
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own ilvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt Pold -∗
  proc_pt Pnew -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own ilvl eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    (* the parent's table comes back verbatim *)
    proc_pt Pold -∗
    ( (* out of memory (kalloc or mappages): the child is rolled back to
         exactly the table we were given *)
      (⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int (-1) : mword 64)⌝ ∗
       proc_pt Pnew)
      ∨ (* the child now mirrors the parent over the run *)
      (∃ P' : uptd,
         ⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64)⌝ ∗
         ⌜uptd_ext Pnew P'⌝ ∗
         ⌜forall vpn, vpn ∉ vpn_run vpn0 n ->
            P'.(ud_um) !! vpn = Pnew.(ud_um) !! vpn⌝ ∗
         ⌜forall i, (i < n)%nat ->
            match Pold.(ud_um) !! vpn_at vpn0 i with
            | None => P'.(ud_um) !! vpn_at vpn0 i = Pnew.(ud_um) !! vpn_at vpn0 i
            | Some w => exists (r w' : mword 64) (a d : mword 1),
                page_valid r /\
                P'.(ud_um) !! vpn_at vpn0 i = Some w' /\
                w' = pte_set_ad (uvm_pte (pte_flags10 w) r) a d
            end⌝ ∗
         proc_pt P') ) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  THE MEMORY-INDEXED CONTRACT.                                          *)
(* ===================================================================== *)
(* THE CHILD ENDS UP HOLDING THE PARENT'S BYTES over the copied region,
   and its own elsewhere:

     M' = umem_write Mnew 0 (4096 * n) (fun a => Mold !!! a)

   -- which is what the memmove does, said once.  The parent comes back
   with its view untouched, byte for byte.

   THE ONE PREMISE THIS ALTITUDE ADDS is that the copied region is LIVE
   IN BOTH tables.  It is not bookkeeping: where the parent has no page
   the loop copies nothing, so the child's bytes there are whatever the
   child's own view says, and the two agree only because BOTH read a
   lazily-backed zero.  fork supplies it by indexing the child at the
   parent's size, which is the size it is about to store in [np->sz].

   THE FAILURE ARM RESTORES [Mnew] EXACTLY, like uvmalloc's.  The [err]
   label unmaps the prefix the loop had mapped WITHOUT shrinking the
   child, so those vas go back to reading as lazily-backed zeros -- which
   is what they read before the copy put anything there.  That is
   [SpecUvmunmap.wp_uvmunmap_live_sconf], and it is why uvmunmap needs
   two memory-indexed contracts rather than one. *)
Definition wp_uvmcopy_mem_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (Pold Pnew : uptd) (szold sznew : Z) (Mold Mnew : gmap Z (bv 8))
    (K : nat) (eb : bool) (p : mword 64)
    (ilvl : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmcopy in
  let sz := mm !!! Regidx (mword_of_int 12) in
  let vpn0 := svpn_of (mword_of_int 0 : mword 64) in
  let n := uvm_np sz in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (42 <= K)%nat ->
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  mm !!! Regidx (mword_of_int 10) = page_base Pold.(ud_root) ->
  mm !!! Regidx (mword_of_int 11) = page_base Pnew.(ud_root) ->
  (uint sz <= uvm_maxsz)%Z ->
  (forall i, (i < n)%nat -> Pnew.(ud_um) !! vpn_at vpn0 i = None) ->
  (* THE COPIED REGION IS LIVE IN BOTH *)
  (forall a : Z, (0 <= a < 4096 * Z.of_nat n)%Z ->
     uva_live szold a /\ uva_live sznew a) ->
  locks_below lks "kmem" ->
  sie_cap_gpr KT1 mm K b p -∗
  cpu_own ilvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_ptm Pold szold Mold -∗
  proc_ptm Pnew sznew Mnew -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT1 mr K b p -∗
    cpu_own ilvl eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    (* the parent's table AND its view come back verbatim *)
    proc_ptm Pold szold Mold -∗
    ( (⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int (-1) : mword 64)⌝ ∗
       proc_ptm Pnew sznew Mnew)
      ∨ (∃ P' : uptd,
           ⌜mr !!! Regidx (mword_of_int 10) = (mword_of_int 0 : mword 64)⌝ ∗
           ⌜uptd_ext Pnew P'⌝ ∗
           ⌜forall vpn, vpn ∉ vpn_run vpn0 n ->
              P'.(ud_um) !! vpn = Pnew.(ud_um) !! vpn⌝ ∗
           ⌜forall i, (i < n)%nat ->
              match Pold.(ud_um) !! vpn_at vpn0 i with
              | None => P'.(ud_um) !! vpn_at vpn0 i = Pnew.(ud_um) !! vpn_at vpn0 i
              | Some w => exists (r w' : mword 64) (a d : mword 1),
                  page_valid r /\
                  P'.(ud_um) !! vpn_at vpn0 i = Some w' /\
                  w' = pte_set_ad (uvm_pte (pte_flags10 w) r) a d
              end⌝ ∗
           proc_ptm P' sznew
             (umem_write Mnew 0%Z (4096 * n)%nat
                (fun a => Mold !!! Z.of_nat a))) ) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UVMCOPY.
  Parameter wp_uvmcopy_mem_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (Pold Pnew : uptd) (szold sznew : Z) (Mold Mnew : gmap Z (bv 8))
      (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string),
      wp_uvmcopy_mem_sconf_body γa mm Pold Pnew szold sznew Mold Mnew
        K eb p ilvl b lks.
  Parameter wp_uvmcopy_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (Pold Pnew : uptd) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string),
      wp_uvmcopy_sconf_body γa mm Pold Pnew K eb p ilvl b lks.
End UVMCOPY.
