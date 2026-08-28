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

   STATED AT THE [proc_ptm] ALTITUDE.  uvmclear is the one function that
   changes a user leaf's CLASSIFICATION without changing what the table
   maps: the page stays mapped, stays owned, keeps its ppn -- it just stops
   being reachable from user mode.  So the postcondition is [proc_ptm] at
   the same map, size and image with that one entry's U bit cleared, and
   NOTHING else moves: same root, same trapframe, same page set ([um_ppns]
   is unchanged, which is why the ownership conjunct is literally the same
   resource).

   THE PANIC ARM IS DEAD, not discharged by a panic credential.  The vpn is mapped
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
   [kalloc_env] and no panic credential, and uvmclear allocates and frees
   nothing -- so neither does this. *)
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
Require Import RegFile WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* ===================================================================== *)
(*  THE MEMORY-INDEXED CONTRACT.                                          *)
(* ===================================================================== *)
(* WHAT uvmclear DOES TO THE PROCESS'S MEMORY: NOTHING.  [M] is the same
   map on both sides, at the same [sz].

   That is not an approximation, it is what [ProcPtOwn.proc_ptm]
   ([UserPtTree.umem_lazy]) SAYS.  Its domain is the union of the vas the
   table MAPS and the vas below [p->sz] rounded up; the first half reads
   [ud_um]'s DOMAIN, which an insert at a key already present does not
   move, and the second half does not mention the table at all.  Its
   ownership is one byte per mapped va, at [uva_pa], which reads the
   leaf's PPN -- and clearing PTE_U leaves the PPN alone
   ([ProcPtOwn.pte_ppn_clear_u]).  So neither the domain nor a single
   byte's location moves, and the image comes back on the nose.

   THE GUARD PAGE'S BYTES STAY IN THE VIEW, and that is correct.  What
   uvmclear takes away is REACHABILITY FROM USER MODE, which lives in
   [UserPtTree.user_pt_inv] -- the predicate the satp window is stated
   over, and the one that reads the permission bits.  The kernel-side
   image is keyed on what the table maps and on [p->sz]; a page the
   kernel can still reach through its identity map, and whose bytes it
   still owns, does not leave it because the user may no longer load
   from it. *)
Definition wp_uvmclear_mem_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
    (P : uptd) (sz : Z) (M : gmap Z (bv 8))
    (w : mword 64) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uvmclear in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (10 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (uint va < 2 ^ 38)%Z ->
  P.(ud_um) !! vpn = Some w ->
  uvm_perm_ok (Z.land (pte_flags10 w) 1007) ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_ptm P sz M -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    proc_ptm (uptd_set P vpn (pte_clear_u w)) sz M -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UVMCLEAR.
  Parameter wp_uvmclear_mem_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
      (P : uptd) (sz : Z) (M : gmap Z (bv 8))
      (w : mword 64) (K : nat) (b : bool) (p : mword 64),
      wp_uvmclear_mem_sconf_body mm P sz M w K b p.
End UVMCLEAR.
