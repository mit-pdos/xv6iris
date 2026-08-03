(* SpecTrapinithart.v -- the public interface of trapinithart (kernel/trap.c):
   the per-hart installation of the kernel trap vector.

     trapinithart() { w_stvec((uint64)kernelvec); }

   compiled into the standard 16-byte frame.  The [stvec] cell is threaded
   through EXPLICITLY: after kvminithart flips the translation slot to the
   kernel page table, the slot no longer owns [stvec] (only the Bare arm
   does), so between those two calls the cell rides client-side -- Sv39 with
   no handler installed and SIE = 0 is a legal state.  trapinithart is what
   ends it: its postcondition pins the cell at [kernelvec], which is the
   resource [intr_inv_alloc] needs to build the interrupt invariant and hence
   to fold the SIE = 1 arm of the capability.

   Straight-line, no callees -> unconditional success, no panic_wp.  Follows
   SpecKvminithart.v's file conventions. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import CalleeSaved.
Require Import IntrDefs.
From Kernel Require KernelSyms.

Notation TIH := KernelSyms.trapinithart.

(* trapinithart(): install kernelvec as the S-mode trap vector.  See the
   header.  [tv0] is the arbitrary word the cell held on entry.

   BOOT-ONLY: trapinithart runs strictly before interrupts are ever enabled
   (main()'s boot sequence, on every hart, always before scheduler()'s
   [intr_on()]) -- see claude-notes/projects/explicit-cpuid-porting-guide.md,
   "A function that READS tp mid-body must be stated at b = false" for the
   general shape this follows (worked example: SpecCpuid.v).  So the
   contract is stated at the literal index [false] rather than a generic
   [b], with no [wp_next] wrapper at all (it would collapse via
   [wp_next_off] anyway, since the hart cannot move). *)
Definition wp_trapinithart_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (mm : regfile) (K : nat)
    (tv0 : mword 64) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.trapinithart in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (2 <= K)%nat ->
  sie_cap_gpr mm K false p -∗
  kernel_text -∗
  pc_is pcE -∗
  stvec ↦ᵣ tv0 -∗
  ( ∀ (mr : regfile),
    sie_cap_gpr mr K false p -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    stvec ↦ᵣ (mword_of_int KernelSyms.kernelvec : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type TRAPINITHART.
  Parameter wp_trapinithart_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile) (K : nat)
      (tv0 : mword 64) (p : mword 64),
      wp_trapinithart_sconf_body Φ mm K tv0 p.
End TRAPINITHART.
