(* SpecUvmunmap.v -- the public interface of Uvmunmap, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-
   function proof file -- so every function proof can be checked in parallel.

     void uvmunmap(pagetable_t pagetable, uint64 va, uint64 npages, int do_free)
     {
       if ((va % PGSIZE) != 0) panic("uvmunmap: not aligned");
       for (a = va; a < va + npages * PGSIZE; a += PGSIZE) {
         if ((pte = walk(pagetable, a, 0)) == 0) continue;
         if (( *pte & PTE_V) == 0) continue;
         if (do_free) { uint64 pa = PTE2PA( *pte); kfree((void * )pa); }
         *pte = 0;
       }
     }

   STATED AT THE [proc_pt] ALTITUDE, like vmfault / copyin / copyout: this is
   the one function that takes pages OUT of the valid-user-page-table
   predicate.  It hands back [proc_pt (uptd_del_run P vpn0 npages)] -- the
   SAME predicate at the user map with the [npages]-long vpn run starting at
   [vpn0] deleted -- and the pages those entries named have gone back to
   kalloc.  Nothing else moves: same root, same trapframe, same tree modulo
   the cleared leaves.

   THREE THINGS THE CONTRACT DELIBERATELY DOES NOT SAY.

   - It does not say which of the [npages] vpns were mapped.  The C code
     [continue]s over an unmapped one, and [um_del_run] deletes it anyway
     (deleting an absent key is a no-op), so one uniform postcondition
     covers both arms of the loop body and the caller needs no per-vpn
     information.  This is why the spec takes no "these are mapped"
     precondition either.

   - It does not cover [do_free == 0].  That arm is used by
     proc_freepagetable to drop the TRAMPOLINE and TRAPFRAME mappings, which
     are NOT in the user map and whose removal BREAKS [upt_tree_spec] -- a
     different altitude entirely, and one that would have to hand the pages
     back to the caller as loose [phys_page_own].  So [do_free] is pinned
     nonzero, which is what every user-region caller (uvmdealloc, uvmfree,
     uvmcopy's cleanup) passes.

   - It says nothing about the CONTENTS of the freed pages.  [proc_pt] owns
     user pages at existential bytes (the user-safety altitude, see
     SpecVmfault.v), and kfree's precondition is likewise contents-blind.

   THE PANIC ARM IS DEAD, not discharged by [panic_wp]: [va] page-aligned is
   a precondition (every caller rounds), so the [slli va,52 / bnez] test is
   not taken.  [kalloc_env] is threaded through only for kfree's lock and
   count; at [on := None] it is persistent, so the loop re-supplies it. *)
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
Require Import BarePt.
From Kernel Require KernelSyms.
Import Defs.

Notation UU := KernelSyms.uvmunmap.

Definition wp_uvmunmap_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (npages : nat) (K : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (ilvl : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmunmap in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn0 := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 8-slot frame + kfree's 14 (the no-alloc walk needs only 8) *)
  (22 <= K)%nat ->
  (* [ilvl] is the interrupt nesting level: kfree's acquire/release keep the
     transient noff increment in int range.  It used to be pinned at 0 --
     an artifact of the boot-time callers. *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  (* the pagetable argument is the table [proc_pt P] describes *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* va is page-aligned: the panic arm is dead *)
  subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
  mm !!! Regidx (mword_of_int 12) = (mword_of_int (Z.of_nat npages) : mword 64) ->
  (* do_free != 0 -- see the header *)
  mm !!! Regidx (mword_of_int 13) <> (mword_of_int 0 : mword 64) ->
  (* the whole run lies in the USER region, i.e. strictly below TRAPFRAME.
     This is what keeps every vpn it clears different from [tramp_vpn] and
     [tf_vpn], so the tree spec survives. *)
  (uint va + Z.of_nat npages * 4096 <= uvm_maxsz)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own ilvl eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    cpu_own ilvl eb p C b -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    proc_pt (uptd_del_run P vpn0 npages) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMUNMAP.
  Parameter wp_uvmunmap_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (npages : nat) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (ilvl : nat) (b : bool),
      wp_uvmunmap_sconf_body γa Φ mm P npages K eb p C ilvl b.
End UVMUNMAP.

(* --------------------------------------------------------------------- *)
(* THE BARE INSTANCE.  proc_freepagetable drops the trampoline and the    *)
(* trapframe (its two [do_free = 0] calls) before handing the table to    *)
(* uvmfree, so uvmfree's uvmunmap call runs on a table with no fixed      *)
(* leaves at all.  That is the OTHER end of BarePt.v's [otf] axis, and    *)
(* it is the same machine code and the same proof: uvmunmap touches the   *)
(* fixed leaves only by knowing the vpn it clears is not one of them,     *)
(* which the range premise below gives at BOTH ends                       *)
(* ([BarePt.uptg_fixed_user_none]).  ProofUvmunmap.v therefore proves one *)
(* [uptg]-generic lemma and seals it twice; every existing caller keeps   *)
(* the [proc_pt] statement above, unchanged.                              *)
(* --------------------------------------------------------------------- *)

Definition wp_uvmunmap_bare_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (uroot : mword 44) (um : gmap (mword 27) (mword 64))
    (npages : nat) (K : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (ilvl : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmunmap in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn0 := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (22 <= K)%nat ->
  (* [ilvl] is the interrupt nesting level: kfree's acquire/release keep the
     transient noff increment in int range.  It used to be pinned at 0 --
     an artifact of the boot-time callers. *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  mm !!! Regidx (mword_of_int 10) = page_base uroot ->
  subrange_vec_dec va 11 0 = (zeros' 12 : mword 12) ->
  mm !!! Regidx (mword_of_int 12) = (mword_of_int (Z.of_nat npages) : mword 64) ->
  mm !!! Regidx (mword_of_int 13) <> (mword_of_int 0 : mword 64) ->
  (uint va + Z.of_nat npages * 4096 <= uvm_maxsz)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own ilvl eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  bare_pt uroot um -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    cpu_own ilvl eb p C b -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    bare_pt uroot (um_del_run um vpn0 npages) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMUNMAP_BARE.
  Parameter wp_uvmunmap_bare_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (uroot : mword 44) (um : gmap (mword 27) (mword 64))
      (npages : nat) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (ilvl : nat) (b : bool),
      wp_uvmunmap_bare_sconf_body γa Φ mm uroot um npages K eb p C ilvl b.
End UVMUNMAP_BARE.
