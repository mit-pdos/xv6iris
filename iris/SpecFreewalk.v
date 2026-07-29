(* SpecFreewalk.v -- the public interface of Freewalk, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-
   function proof file -- so every function proof can be checked in
   parallel.

     void freewalk(pagetable_t pagetable)
     {
       for (int i = 0; i < 512; i++) {
         pte_t pte = pagetable[i];
         if ((pte & PTE_V) && (pte & (PTE_R|PTE_W|PTE_X)) == 0) {
           uint64 child = PTE2PA(pte);
           freewalk((pagetable_t)child);        // RECURSIVE
           pagetable[i] = 0;
         } else if (pte & PTE_V) {
           panic("freewalk: leaf");
         }
       }
       kfree((void * )pagetable);
     }

   THE FIRST RECURSIVE FUNCTION IN THE TREE.  freewalk at a level-[lvl]
   node calls itself at level [lvl-1], so the contract is indexed by the
   level and the proof is an INDUCTION ON [lvl] -- not an iLob: the
   recursion is structurally bounded by the description, and [ptree_own]
   is indexed by exactly the same [lvl].  Sv39 tables enter at [lvl = 2].

   THE PANIC ARM IS DEAD, not discharged by [panic_wp].  [pt_free_ok lvl t]
   (PtFree.v §1) says every slot is either the literal zero word or a valid
   pointer to a node the description owns, so the [andi a4,a5,14 / bnez]
   test at +0x32 never fires.  That is the honest precondition: freewalk
   frees the PAGE-TABLE pages and nothing else, so it may only run on a
   table that maps nothing -- which is why proc_freepagetable unmaps the
   trampoline and the trapframe (and uvmfree the user pages) FIRST.  A
   table with any leaf left would really panic, and a contract that
   pretended otherwise would be describing different code.

   WHAT IT CONSUMES.  All of [ptree_own lvl 1 t] -- every node page of the
   subtree, [pt_nodes_lvl lvl t] of them, each handed to kfree.  Nothing
   comes back: the postcondition is registers only.  The [page_valid] each
   kfree needs rides in each node's own [PtTree.pt_node_claim], so no
   per-node premise appears here.

   THE COUNT.  [kalloc_env] is threaded at [on := None] (the steady state,
   where it is persistent and [avail_inc None = None]), so freewalk's
   contract says nothing about how many pages came back.  A boot-time
   [Some n] caller would need the count threaded through the recursion as
   [avail_add on (pt_nodes_lvl lvl t)]; no such caller exists. *)
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
Require Import PtTree PtBuild KvmSpec.
Require Import ProcPtOwn.
Require Import PtFree.
From Kernel Require KernelSyms.
Import Defs.

Notation FW := KernelSyms.freewalk.

Definition wp_freewalk_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
    (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
    (t : ptree) (lvl : nat) (K : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (ilvl : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.freewalk in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (* 6-slot frame per recursion level, [lvl]+1 levels deep, and kfree's 14
     on top of the deepest of them *)
  (6 * S lvl + 14 <= K)%nat ->
  (* [ilvl] is the INTERRUPT nesting level (not the page-table [lvl] above):
     kfree's acquire/release keep the transient noff increment in int range.
     It used to be pinned at 0, which was an artifact of the boot-time
     callers; proc_pagetable reaches this chain with a proc lock held. *)
  (Z.of_nat ilvl + 1 < 2 ^ 31)%Z ->
  (* the kfree chain runs on the ambient CPU (push_off cid convention) *)
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the pagetable argument is the node [t] describes *)
  mm !!! Regidx (mword_of_int 10) = page_base (pt_base t) ->
  (* the table maps nothing: the panic arm is dead *)
  pt_free_ok lvl t ->
  sie_cap_gpr γ mm K -∗
  cpu_own γ ilvl eb p C -∗
  kernel_text -∗
  pc_is pcE -∗
  ptree_own lvl (DfracOwn 1) t -∗
  kalloc_env γa None cid_word -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr γ mr K -∗
    cpu_own γ ilvl eb p C -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type FREEWALK.
  Parameter wp_freewalk_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{CID : CpuId}
      (γ : gname) (γa : gname) (Φ : mval -> iProp Σ) (mm : regfile)
      (t : ptree) (lvl : nat) (K : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (ilvl : nat),
      wp_freewalk_sconf_body γ γa Φ mm t lvl K eb p C ilvl.
End FREEWALK.
