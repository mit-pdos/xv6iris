(* SpecUvmfree.v -- the public interface of Uvmfree, stated independently of
   its proof.

     void uvmfree(pagetable_t pagetable, uint64 sz)
     {
       if (sz > 0)
         uvmunmap(pagetable, 0, PGROUNDUP(sz) / PGSIZE, 1);
       freewalk(pagetable);
     }

   STATED AT THE **BARE** TABLE ALTITUDE ([PtFree.bare_pt]), not at
   [proc_pt].  This is forced by the code, and it is the honest reading:
   uvmfree's only caller is

     proc_freepagetable(pagetable, sz) {
       uvmunmap(pagetable, TRAMPOLINE, 1, 0);
       uvmunmap(pagetable, TRAPFRAME,  1, 0);
       uvmfree(pagetable, sz);
     }

   so by the time uvmfree runs, the trampoline and the trapframe leaves are
   GONE and the table's only leaves are the user map.  It has to be that
   way: freewalk panics on any leaf it meets, so at [proc_pt] -- where the
   trampoline is still mapped -- uvmfree would not return at all, and a
   contract claiming otherwise would describe different code.
   [bare_pt uroot um] is exactly [proc_pt] with the two fixed leaves
   removed and nothing else changed (PtFree.v §3), and the uvmunmap call
   below is uvmunmap's BARE instance ([UVMUNMAP_BARE]) -- the same proof,
   sealed at the other end of the [otf] axis.

   THE ONE PREMISE THAT MATTERS: [dom um ⊆ vpn_run 0 n].  Every page the
   table still maps must lie in the region uvmunmap is about to clear,
   because freewalk requires a table that maps NOTHING.  It covers both
   arms uniformly: at [sz = 0] the branch skips uvmunmap, and [n = 0]
   makes the premise say [um = ∅] -- which is what the skipped call would
   have had to establish anyway.  (A caller with a page mapped above
   [PGROUNDUP(sz)] would really panic in freewalk; xv6 keeps [p->sz] an
   upper bound on the user map, which is the fact this premise names.  See
   claude-notes/projects/proc-pagetable-ownership.md step 7.)

   NOTHING COMES BACK.  Both the user pages (via uvmunmap+kfree) and the
   page-table pages (via freewalk+kfree) go to the allocator; the
   postcondition is registers only.  [kalloc_env] rides at [on := None],
   so the contract says nothing about the count. *)
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
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import ProcPtOwn.
Require Import BarePt.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_uvmfree_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (mm : regfile)
    (uroot : mword 44) (um : gmap (mword 27) (mword 64))
    (K : nat) (eb : bool) (p : mword 64) (ilvl : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmfree in
  let sz := mm !!! Regidx (mword_of_int 11) in
  let vpn0 := svpn_of (mword_of_int 0 : mword 64) in
  let n := uvm_np sz in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 4-slot frame + freewalk's 32 (uvmunmap needs only 22) *)
  (36 <= K)%nat ->
  (* [ilvl] is the interrupt nesting level: kfree's acquire/release keep the
     transient noff increment in int range.  It used to be pinned at 0 --
     an artifact of the boot-time callers. *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  (* NO tp premise.  HartTp.v: the register map's tp slot is IGNORED and the
     true tp is [cid_word_of <the hart we are on>] by construction, so the
     one this used to carry was dead weight -- the same sweep SpecUvmunmap
     already had (see ProofUvmdealloc.v's note at its uvmunmap call). *)
  mm !!! Regidx (mword_of_int 10) = page_base uroot ->
  (* the size stays inside the user region, so PGROUNDUP does not wrap and
     uvmunmap's range premise holds.  [<=], NOT [+ 4096 <=]: [uvm_maxsz] is
     page-aligned, so rounding a size that reaches it up to a page boundary
     stays inside -- and the stronger form is undischargeable by the only
     caller that has a live process's [p->sz], which growproc lets reach
     TRAPFRAME exactly. *)
  (uint sz <= uvm_maxsz)%Z ->
  (* the table maps nothing above PGROUNDUP(sz): see the header *)
  dom um ⊆ vpn_run vpn0 n ->
  (* uvmfree -> uvmunmap/freewalk -> kfree *)
  locks_below lks "kmem" ->
  sie_cap_gpr kt mm K b p -∗
  cpu_own ilvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  bare_pt uroot um -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr kt mr K b p -∗
    cpu_own ilvl eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UVMFREE.
  Parameter wp_uvmfree_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (mm : regfile)
      (uroot : mword 44) (um : gmap (mword 27) (mword 64))
      (K : nat) (eb : bool) (p : mword 64) (ilvl : nat) (b : bool) (lks : gset string),
      wp_uvmfree_sconf_body kt γa mm uroot um K eb p ilvl b lks.
End UVMFREE.
