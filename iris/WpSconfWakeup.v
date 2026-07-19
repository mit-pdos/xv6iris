(* WpSconfWakeup.v -- wakeup over the SIE-agnostic sconf world (kalloc cone,
   stage 8).  Foundation for the sconf mirror of [wp_wakeup] (WpWakeup.v): a
   loop over the proc[] table that, per proc, acquires the proc lock, wakes it
   if SLEEPING on the given chan, and releases -- threading the counting token
   [intr_count] net-zero across each acquire/release pair.

   THIS FILE currently provides only [wp_myproc_sconf], the sconf-flavoured
   myproc axiom wakeup relies on (the loop skips the current proc).  The full
   loop/prologue/epilogue port is the remaining work (see CLAUDE.md). *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SRegime SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpGpr.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved StackOwn.
Require Import KptTree.
Require Import IntrDefs WpIntrInv WpSmodeIntr.
Require Import WpWakeup.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ======================================================================= *)
(* myproc(), sconf-flavoured.  Like the smode [wp_myproc] (WpWakeup.v), the  *)
(* only fact wakeup needs is that a0 comes back a genuine proc[] entry and   *)
(* the callee-saved registers are preserved.  myproc internally push_off/    *)
(* pop_offs (net-zero) and manages its own stack frame from the lent deep    *)
(* custody, so it threads [sconf] + hart_state + [sie_cap] + [intr_count n]  *)
(* (unchanged) + [tlb_inv_pt] + a deep-K stack slice, exactly the resources  *)
(* the sconf acquire/release thread.                                         *)
(* ======================================================================= *)
Axiom wp_myproc_sconf :
  forall {Σ : gFunctors} {HR : riscvGS Σ} {HL : lockG Σ} {HS : sieG Σ} {CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (m : gmap regidx (mword 64)) (n K : nat),
    let sp0 := m !!! Regidx csp_rs1 in
    let ret_tgt :=
      update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                        (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (10 <= K)%nat ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    sconf γ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sie_cap γ root_ppn m -∗
    intr_count γ root_ppn n -∗
    tlb_inv_pt root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.myproc) -∗ gpr_file m -∗
    stack_own (pa_stk sp0 kv_frame_slots) K -∗
    (∀ (j : nat) (mret : gmap regidx (mword 64)),
       ⌜(j < NPROC)%nat⌝ -∗
       ⌜mret !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j⌝ -∗
       ⌜callee_saved m mret⌝ -∗
       sconf γ -∗
       hart_state ↦ᵣ HART_ACTIVE tt -∗
       sie_cap γ root_ppn mret -∗
       intr_count γ root_ppn n -∗
       tlb_inv_pt root_ppn -∗
       pc_is ret_tgt -∗ gpr_file mret -∗
       stack_own (pa_stk sp0 kv_frame_slots) K -∗
       WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
