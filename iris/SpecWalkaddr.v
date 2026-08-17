(* SpecWalkaddr.v -- the public interface of Walkaddr, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

     uint64 walkaddr(pagetable_t pagetable, uint64 va) {
       if (va >= MAXVA) return 0;
       pte_t *pte = walk(pagetable, va, 0);
       if (pte == 0) return 0;
       if (( *pte & PTE_V) == 0) return 0;
       if (( *pte & PTE_U) == 0) return 0;
       return PTE2PA( *pte);
     }

   (the compiler merges the two flag tests into one [andi a3,a5,17] against
   [li a4,17], so the machine really decides [pte_vu]).

   Like [ismapped], stated over the EXACT represented map [pt_rep0 t m] --
   the xv6 zero-stop-word shape -- with the tree riding through READ-ONLY at
   a generic dfrac.  The only callee is the no-alloc walk, so there is no
   kalloc environment and no [cpu_own].

   THE FAILURE ARM CARRIES ITS REASON, and it has to.  [va >= MAXVA], "the
   walk did not reach a slot", "the slot is zero" and "the slot is not a
   valid USER leaf" collapse to the same answer 0, and for a long time no
   caller cared: copyin / copyout / copyinstr all react to 0 the same way,
   by faulting the page in or giving up, so the arm was stated as a bare
   [a0 = 0] and the header recorded the case split as buying nothing.

   IT BUYS EXACTLY ONE THING, and it turns out to be load-bearing: a caller
   that KNOWS the leaf is there and is a user leaf can REFUTE the arm.
   Without the reason it cannot -- a bare [a0 = 0] is permitted
   unconditionally, so no amount of knowledge about the map rules the
   branch out, and the fault path stays alive in the proof even where it is
   dead in the machine.

   (This used to be what generalised copyout needed: on a table that was not
   the running process's there were no [p->sz] / [p->pagetable] cells to
   give vmfault, so the call had to be shown UNREACHABLE and this
   disjunction was what showed it.  xv6 `4f2fc8b` retired that need --
   vmfault takes the size as an argument now -- so copyout no longer refutes
   the arm; see SpecCopyout.v.  The disjunction stays because it is the
   honest statement of walkaddr, and other callers still refute with it.)

   The three reasons are exactly the three tests the machine performs, in
   order, and each is a fact the caller can contradict on its own terms.
   Note the third is [~ pte_vu w], not [~ pte_valid w]: the compiler merged
   the V and U tests into one [andi a3,a5,17], so a leaf that is present and
   valid but has U CLEARED fails here -- which is not a hypothetical, it is
   precisely a [uvmclear]'d guard page ([ProcPtOwn.proc_pt_wf_clear_u] keeps
   such an entry in [ud_um]).  A caller whose premise is only "the map has an
   entry" has not ruled this out.

   THE SUCCESS ARM is what makes the answer usable: the returned address is
   the base of the page the map's leaf at this vpn names, that leaf passes
   the V&U test ([pte_vu] -- so, for a process table, its vpn is in the user
   MAP, not the trampoline or the trapframe), and [va] was below MAXVA (so
   the caller may go on to [walk] the same va, as copyout does). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import PtTree.
Require Import PtBuild.
Require Import ProcPtOwn.   (* [pte_ppn] / [page_base]: the page a leaf names *)
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.


Definition wp_walkaddr_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (mm : regfile) (t : ptree)
    (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.walkaddr in
  let va := mm !!! Regidx (mword_of_int 11) in
  let vpn := svpn_of va in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 2-slot frame + the no-alloc walk's 8 *)
  (10 <= K)%nat ->
  mm !!! Regidx (mword_of_int 10)
    = zero_extend' 64 (concat_vec (pt_base t) (zeros' 12 : mword 12)) ->
  pt_rep0 t m ->
  sie_cap_gpr kt mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ptree_own 2 dq t -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr kt mr K b p -∗
    pc_is ret_tgt -∗
    ptree_own 2 dq t -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜ (mr !!! Regidx (mword_of_int 10) = mword_of_int 0 /\
       ((2 ^ 38 <= uint va)%Z
        \/ m !! vpn = None
        \/ (exists w, m !! vpn = Some w /\ ~ pte_vu w)))
      \/ (exists w, m !! vpn = Some w /\ pte_vu w /\
            (uint va < 2 ^ 38)%Z /\
            mr !!! Regidx (mword_of_int 10) = page_base (pte_ppn w)) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WALKADDR.
  Parameter wp_walkaddr_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (mm : regfile) (t : ptree)
      (m : gmap (mword 27) (mword 64)) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_walkaddr_sconf_body kt mm t m K dq b p.
End WALKADDR.
