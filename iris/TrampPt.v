(* TrampPt.v -- the TRAMPOLINE page's page-table structure, for verifying the
   [userret] trampoline (kernel/trampoline.S) that switches from the kernel
   page table to a user-process page table and sret's to user mode.

   Layout facts (xv6, Sv39):
   - TRAMPOLINE  = MAXVA - PGSIZE = 0x3F_FFFF_F000 (vpn 0x3FFFFFF, hash slot 63)
   - TRAPFRAME   = TRAMPOLINE - PGSIZE            (vpn 0x3FFFFFE, hash slot 62)
   - the trampoline page's PHYSICAL home is kernel text: KernelSyms.trampoline
     = 0x80006000 (ppn 0x80006); [userret] sits at +0x9c.
   - BOTH the kernel page table and every user page table map TRAMPOLINE to
     that physical page via a full 3-level walk (root[255] -> l1[511] ->
     l0[511]); a user table additionally maps TRAPFRAME (l0[510]) to the
     process's trapframe page.

   This file provides the PURE / exec-twin layer:
   - [mk_pte] (a PTE with ppn field + low flags) and its field-extraction
     lemmas usable with a SYMBOLIC ppn;
   - the three-level Sv39 page WALK reading the three owned PTEs (stated per
     level over a GENERIC Acc argument, since the nested [_rec_pt_walk]
     call's [_limit_reduces_bool] is opaque);
   - TLB lemmas for the resulting 4K entries: miss / non-matching-entry miss,
     [add_to_TLB] at level 0, hit, and [tlb_get_ppn];
   - [translateAddr] compositions for InstructionFetch and Load Data through
     a 4K mapping where the OUTPUT physical page differs from the va's page;
   - the [SFENCE_VMA] execute reduction (flush_TLB clears every slot) and the
     S-mode [csrw satp] execute reduction (TVM=0).

   As with [pte_super] (SmodeCore), the leaf PTEs are pinned with the A (and,
   for the writable trapframe, D) bits already SET, so the walk never writes
   the PTE back ([update_PTE_Bits] = None): we verify the steady state after
   the hardware's first-use A/D update. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import WpGprCsrwCommon WpGprCsrwB.
Require Import SmodeCore.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* 1. Constants: the two top-of-VA pages and their vpn/slot geometry.     *)
(* ===================================================================== *)

Definition TRAMPOLINE : Z := 0x3FFFFFF000.
Definition TRAPFRAME  : Z := 0x3FFFFFE000.

Definition tramp_vpn : mword 27 := mword_of_int 0x3FFFFFF.
Definition tf_vpn    : mword 27 := mword_of_int 0x3FFFFFE.

(* the trampoline page's physical page number (KernelSyms.trampoline >> 12). *)
Definition tramp_ppn : mword 44 := mword_of_int 0x80006.


(* The generic 4KB PTE layer ([mk_pte]/[pte_addr_at]), the 3-level walk
   ([exec_pt_walk_tramp3]), [tlb4k_entry] and [exec_add_to_TLB_4k] MOVED to
   Pt4kWalk.v (re-exported here) so the kernel 4KB page table (KptPt.v /
   SmodeCore.v) can use them below this file. *)
Require Export Pt4kWalk.

