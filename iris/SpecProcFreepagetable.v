(* SpecProcFreepagetable.v -- the public interface of proc_freepagetable,
   stated independently of its proof.

     void proc_freepagetable(pagetable_t pagetable, uint64 sz)
     {
       uvmunmap(pagetable, TRAMPOLINE, 1, 0);
       uvmunmap(pagetable, TRAPFRAME,  1, 0);
       uvmfree(pagetable, sz);
     }

   THIS IS THE FUNCTION THAT DESTROYS A USER PAGE TABLE, and its contract is
   the place where that becomes visible: it CONSUMES [ProcPtOwn.proc_pt P]
   and gives nothing back.  Every page the table owned -- the user pages via
   uvmunmap+kfree, the page-table nodes via freewalk+kfree -- has gone to the
   allocator, and the postcondition is registers only.

   WHY IT COULD NOT BE STATED BEFORE.  The two [do_free = 0] calls unmap the
   trampoline and the trapframe, which is exactly what [SpecUvmunmap]'s
   [UVMUNMAP] instance is built to forbid (its range premise is what proves
   no vpn the loop clears is a fixed leaf).  The table between the two calls
   -- trampoline gone, trapframe still there -- was not even expressible:
   BarePt.v's axis was an [option], "both fixed leaves or neither".  Both
   were fixed together; the axis is the fixed-leaf MAP now, and the calls run
   on [UVMUNMAP_FIXED].  The chain the proof walks is

     proc_pt P                                    (proc_pt_uptg)
       -> uptg (upt_fixed_both tfp) root um
       -> uptg {[tf_vpn := pte_tf tfp]} root um   (unmap TRAMPOLINE)
       -> uptg empty root um  =  bare_pt root um  (unmap TRAPFRAME)
       -> (nothing)                               (uvmfree)

   THE ONE PREMISE THAT MATTERS: [um_below sz P.(ud_um)] -- the table maps
   nothing at or above [sz].  It is uvmfree's [dom um subseteq vpn_run 0 n]
   premise pulled up one level, and it is not invented here: it is the
   [p->sz]-bounds-the-user-map invariant that growproc forced into
   [ProcInv.proc_priv] (see completed/growproc.md).  A caller that has the
   process's private block has it already.

   WHAT THE CONTRACT DELIBERATELY DOES NOT SAY.

   - It says nothing about the trapframe PAGE.  proc_freepagetable unmaps
     the trapframe ENTRY but never frees the page it names: that page
     belongs to [ProcInv.proc_priv] (as [tf_page]), the caller still holds
     it, and freeproc frees it separately.  Same for the trampoline, whose
     page is global kernel text.  This is why the two calls pass
     [do_free = 0] and why the postcondition hands nothing back.

   - It says nothing about the count.  [kalloc_env] rides at [on := None],
     inherited from uvmfree: freewalk's recursion returns a data-dependent
     number of pages and counting them is not worth it.  So this contract is
     only usable in the steady-state allocator regime -- which is where
     freeproc and kexit live. *)
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
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_proc_freepagetable_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γa : gname) (mm : regfile)
    (P : uptd) (K : nat) (eb : bool) (p : mword 64)
    (ilvl : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.proc_freepagetable in
  let sz := mm !!! Regidx (mword_of_int 11) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 4-slot frame + uvmfree's 36 (the two unmaps need only 22) *)
  (40 <= K)%nat ->
  (* the interrupt nesting level: the kfree chain underneath keeps the
     transient noff increment in int range *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  (* the pagetable argument is the table [proc_pt P] describes *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the size stays inside the user region, so PGROUNDUP does not wrap.  This
     is EXACTLY [ProcInv.proc_priv]'s own size bound -- see SpecUvmfree.v for
     why the [+ 4096] form it used to have was undischargeable. *)
  (uint sz <= uvm_maxsz)%Z ->
  (* ...and the table maps nothing at or above it.  See the header: this is
     [ProcInv.proc_priv]'s [p->sz] invariant, not a new obligation. *)
  um_below sz P.(ud_um) ->
  (* proc_freepagetable -> uvmunmap/uvmfree -> kfree *)
  locks_below lks "kmem" ->
  sie_cap_gpr kt mm K b p -∗
  cpu_own ilvl eb p b lks -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr kt mr K b p -∗
    cpu_own ilvl eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PROC_FREEPAGETABLE.
  Parameter wp_proc_freepagetable_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γa : gname) (mm : regfile)
      (P : uptd) (K : nat) (eb : bool) (p : mword 64)
      (ilvl : nat) (b : bool) (lks : gset string),
      wp_proc_freepagetable_sconf_body kt γa mm P K eb p ilvl b lks.
End PROC_FREEPAGETABLE.
