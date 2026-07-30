(* SpecPlicinithart.v -- the public interface of plicinithart, stated
   independently of its proof.  [plicinithart] (xv6-riscv/kernel/plic.c) enables
   the UART + VIRTIO interrupts for THIS hart's S-mode context and drops its
   priority threshold to 0:

     0x80005498 <plicinithart>:
       ...prologue...
       jal    cpuid            a0 = hart id
       slliw  a4,a0,0x8
       lui    a5,0xc002
       add    a5,a5,a4         a5 = PLIC + 0x2000 + hart*0x100
       li     a4,1026
       sw     a4,128(a5)       *PLIC_SENABLE(hart)   = (1<<10)|(1<<1) = 1026
       slliw  a0,a0,0xd
       lui    a5,0xc201
       add    a5,a5,a0         a5 = PLIC + 0x201000 + hart*0x2000
       sw     zero,0(a5)       *PLIC_SPRIORITY(hart) = 0
       ...epilogue...

   The two stores are S-mode 32-bit MMIO writes through the kernel page table's
   PLIC identity mapping.

   WHY THIS SPEC OWNS NO PLIC STATE.  plicinithart runs CONCURRENTLY on every
   hart: no hart can own the PLIC state across its two writes, because the
   others are writing their own contexts at the same time.  So the shared
   [plic_frag] half stays in the device invariant [dev_inv] (WpUart.v) and this
   spec takes that invariant -- persistent, hence shareable -- instead.  Each
   store opens it, writes, and closes it.  (This is the same reason [plicinit],
   which hart 0 does run alone at boot, still cannot hold the fragment raw: the
   PLIC gateway latches whenever an irq line is up.)

   What the caller gets back is therefore not this hart's PLIC context but the
   invariant itself: the kernel's PLIC plan [plic_ok] (PlicPlan.v) still holds.
   That plan is deliberately weak -- per-hart thresholds are unconstrained and a
   hart's enable word may only name sources the machine has -- precisely so that
   a hart can re-establish it from its own two writes, knowing nothing about
   what the other harts wrote.  Even so the spec is not vacuous: the proof must
   show both addresses decode to real PLIC context registers for this hart
   ([plic_write] returns [Some]), which is what pins the precondition
   [bv_unsigned tp < dev_ncpu].

   Requires only the definitional layer + SpecCpuid (for [cpuid_ret]) -- never a
   whole-function proof file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes HartTp WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import DevModel PlicPlan DiskPtsto WpUart.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation PLICINITHART := KernelSyms.plicinithart.

(* the S-context enable word xv6 writes: (1 << UART0_IRQ) | (1 << VIRTIO0_IRQ)
   = (1 << 10) | (1 << 1) = 1026 -- exactly the kernel's permitted set. *)
Definition plic_senable_word : bv 32 := Z_to_bv 32 plic_dev_irq_mask.

Definition wp_plicinithart_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γd : uart_names) (γv : disk_names)
    (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (b : bool) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let pcE := mword_of_int KernelSyms.plicinithart in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  bv_unsigned (rget m0 tp_idx) < Z.of_nat dev_ncpu ->
  (* plicinithart's own max depth: its 16-byte frame (2 slots) plus the two
     slots cpuid's frame needs below it. *)
  (4 <= n)%nat ->
  sie_cap_gpr m0 n b -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ m' : regfile,
    sie_cap_gpr m' n b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PLICINITHART.
  Parameter wp_plicinithart_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (b : bool),
      wp_plicinithart_sconf_body γd γv Φ m0 n b.
End PLICINITHART.
