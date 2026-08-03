(* SpecUvmclear.v -- the public interface of Uvmclear, stated independently
   of its proof.

     // mark a PTE invalid for user access.
     // used by exec for the user stack guard page.
     void uvmclear(pagetable_t pagetable, uint64 va)
     {
       pte_t *pte;
       pte = walk(pagetable, va, 0);
       if (pte == 0) panic("uvmclear");
       *pte &= ~PTE_U;
     }

   STATED AT THE [proc_pt] ALTITUDE.  uvmclear is the one function that
   changes a user leaf's CLASSIFICATION without changing what the table
   maps: the page stays mapped, stays owned, keeps its ppn -- it just stops
   being reachable from user mode.  So the postcondition is [proc_pt] at the
   map with that one entry's U bit cleared, and NOTHING else moves: same
   root, same trapframe, same page set ([um_ppns] is unchanged, which is why
   the ownership conjunct is literally the same resource).

   THE PANIC ARM IS DEAD, not discharged by [panic_wp].  The vpn is mapped
   (a precondition), so the no-alloc walk reaches level 0 and returns a slot
   address inside a page-table node -- which is a kalloc page, hence above
   [kmem_lo], hence nonzero.  That last step is a payoff of
   [PtTree.pt_node_claim] carrying [page_valid]: without it, "the address
   walk returned is not NULL" would not be provable at all.

   WHY THE PERMISSION IS A PREMISE.  What the invariant needs of the new
   leaf is [uvm_perm_ok] at its flag byte -- the same pure, ppn-independent
   obligation uvmalloc's caller discharges, here at the CLEARED byte
   [Z.land (pte_flags10 w) 1007] (1007 = 1023 - PTE_U).  It is not derived
   from the old leaf's, the way uvmcopy's is, because clearing a bit does
   not preserve the model's validity predicate for free: [pte_is_invalid]
   mentions U in its non-leaf disjunct, so a state-generic congruence would
   be needed, and it is not worth building for one 42-byte function.  Every
   caller knows its permission concretely -- exec maps the stack with
   PTE_W, so the leaf is at flag byte 23 and the cleared byte is 7 -- and
   [uvm_perm_ok_7] discharges it by [vm_compute].

   THE A/D BITS RIDE THROUGH.  The code reads [ *pte], the leaf as the
   hardware last left it, and writes it back with bit 4 cleared; clearing
   bit 4 commutes with rewriting bits 6 and 7, so the tree ends up holding
   an A/D variant of [pte_clear_u w] and the canonical map entry is exactly
   that.  No A/D existential leaks into the contract (unlike uvmcopy's,
   where the parent's A/D bits are copied to a DIFFERENT page).

   LIGHTEST CONTRACT IN THE FILE: the no-alloc walk needs no [cpu_own], no
   [kalloc_env] and no [panic_wp], and uvmclear allocates and frees
   nothing -- so neither does this. *)
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
Require Import KallocInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Import Defs.

Notation UCL := KernelSyms.uvmclear.

Definition wp_uvmclear_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (mm : regfile)
    (P : uptd) (w : mword 64) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmclear in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 2-slot frame + the no-alloc walk's 8 *)
  (10 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the walk's canonicality premise *)
  (uint va < 2 ^ 38)%Z ->
  (* the vpn IS mapped: what makes the panic arm dead *)
  P.(ud_um) !! vpn = Some w ->
  (* the cleared flag byte is a legal user leaf.  1007 = 1023 - PTE_U *)
  uvm_perm_ok (Z.land (pte_flags10 w) 1007) ->
  sie_cap_gpr mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    proc_pt (uptd_set P vpn (pte_clear_u w)) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UVMCLEAR.
  Parameter wp_uvmclear_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile)
      (P : uptd) (w : mword 64) (K : nat) (b : bool) (p : mword 64),
      wp_uvmclear_sconf_body Φ mm P w K b p.
End UVMCLEAR.
