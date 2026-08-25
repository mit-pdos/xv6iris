(* SpecKvminithart.v -- the public interface of kvminithart (kernel/vm.c):
   the Bare->Sv39 switch that installs the verified kernel page table.

   kvminithart() = sfence.vma ; w_satp(MAKE_SATP(kernel_pagetable)) ;
   sfence.vma, wrapped in a 2-slot frame.  It DISSOLVES the translation
   slot's Bare arm (recovering this hart's satp/pmp cells and the stvec
   cell) and RE-SEALS it at the kernel page table (the KPT arm), flipping
   the receipt [strans_bit] '0 (Bare) -> '1 (KPT).

   ONE HART-GENERIC CONTRACT (claude-notes/completed/kpt-share.md §5).  Every
   hart runs kvminithart, so nothing globally unique may appear below: the
   table itself lives in the SHARED invariant [KptShare.kpt_inv root], the
   root cell is read at the PERSISTENT [↦₈□], and everything else this
   contract touches -- the Bare receipt, the tlb cell, the satp/pmp cells
   inside the slot -- is per-hart, minted by that hart's own _entry ->
   start.  No [ptree_own], no [kpt_unset], no [kmap_auth], and no [ptree] in
   the statement at all: the switch only ever needs the ROOT PPN, which is
   what the satp word encodes.

   THE ONE-WAY DOOR IS THE CALLER'S.  Publishing the table -- minting the 65
   kernel-mapping claims out of the [kmap_auth kmap_M0] boot token
   ([WpKvminithart.kvm_M_mint]), allocating [kpt_inv] out of kvminit's
   exclusive tree + the [kpt_unset] one-shot ([KptShare.kpt_inv_alloc]), and
   persisting the root cell -- happens ONCE, in main's boot arm, between
   kvminit and this call.  It used to be internalized here, when the Bare
   arm still held [kmap_auth kmap_M0] at fraction 1 and kpt_inv was
   therefore unallocatable while any hart was Bare; the per-hart Bare arm
   (claude-notes/completed/bare-inv-generic.md) removed that obstruction, so
   the door moved out to its natural caller and this contract lost its last
   boot-hart-only premise.

   The TLB coherence the switching hart re-enters with is free: both
   sfence.vma's leave the TLB empty, so [tlb_ok_pt_empty] holds at any tree
   and [KptShare.kpt_inv_snapshot] supplies the snapshot ghost.

   Boot-free, straight-line, no callees -> unconditional success, no
   panic credential.  Follows SpecKvminit.v's file conventions.

   INTERRUPTS OFF, AND THAT IS LOAD-BEARING (not a convenience).  Every
   resource this contract carries from entry to exit -- [tlb ↦ᵣ], the
   [strans_bit] receipt, the satp/pmp cells inside the translation slot --
   is HART-INDEXED, and there is no transport for any of them across a
   migration: a [wp_next]-crossing hands back an unconstrained hart, and
   [tlb ↦ᵣ tlbvec0] derived at the entry hart says nothing there.  That is
   not a gap to be filled, it is the truth about the code: kvminithart
   configures THIS hart's MMU, so the function is meaningless if the hart
   can change underneath it.  xv6 only ever calls it from main(), before
   scheduler()'s [intr_on()], on every hart.  So the contract is stated at
   the literal index [false] with no [wp_next] wrapper at all -- exactly as
   SpecTrapinithart.v and SpecPlicinithart.v are, and for the same reason
   ([wp_next_off] would collapse the wrapper anyway).  Stating it at a
   generic [b] was a real over-specification: it claimed kvminithart works
   when the hart may move mid-body, which is false. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang.
Require Import RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import KptShare.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* kvminithart(): the Bare->Sv39 kernel-page-table switch.  See the header. *)
Definition wp_kvminithart_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (mm : regfile) (lvl K : nat)
    (root : mword 44)
    (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kvminithart in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  let root_b := zero_extend' 64 (concat_vec root (zeros' 12 : mword 12)) in
  lvl = 0%nat ->
  (2 <= K)%nat ->
  sie_cap_gpr KT0 mm K false p -∗
  strans_pending -∗
  kernel_text -∗
  pc_is pcE -∗
  tlb ↦ᵣ tlbvec0 -∗
  (* the root cell, PERSISTENT: kvminithart only reads it, and after main's
     boot arm has published the table nobody may write it again -- which is
     what lets the [started] payload carry it to every secondary hart. *)
  (mword_of_int KernelSyms.kernel_pagetable : mword 64) ↦₈□ root_b -∗
  (* the shared table, likewise persistent *)
  kpt_inv root -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr KT0 mr K false p -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    kpt_on cpu_id -∗
    (∃ v : mword 64, stvec ↦ᵣ v) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KVMINITHART.
  Parameter wp_kvminithart_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (mm : regfile) (lvl K : nat)
      (root : mword 44)
      (tlbvec0 : vec (option TLB_Entry) (2 ^ 6)) (p : mword 64),
      wp_kvminithart_sconf_body mm lvl K root tlbvec0 p.
End KVMINITHART.
