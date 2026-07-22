(* SpecPlicinit.v -- the public interface of plicinit, stated independently of
   its proof.  [plicinit] (xv6-riscv/kernel/plic.c) sets the PLIC source
   priorities of the UART and VIRTIO interrupts to 1 (non-zero = enabled):

     0x8000547e <plicinit>:
       ...prologue...
       lui  a4,0xc000       a4 = PLIC base (0x0c000000)
       li   a5,1
       sw   a5,40(a4)       *(PLIC + UART0_IRQ*4)   = 1   (source 10 priority)
       sw   a5,4(a4)        *(PLIC + VIRTIO0_IRQ*4) = 1   (source 1  priority)
       ...epilogue...

   The two stores are S-mode 32-bit MMIO writes through the kernel page table's
   PLIC identity mapping.  This is a BOOT-time function that runs before the
   device thread / [dev_inv] is live, so it is stated over the RAW [plic_frag]
   half (there is no monotonicity constraint on the PLIC ghost): [plic_frag p]
   in, [plic_frag (plicinit_plic p)] out.

   Requires only the definitional layer -- never a whole-function proof file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import DevModel.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.

Notation PLICINIT := KernelSyms.plicinit.

(* the two PLIC interrupt-source ids xv6 raises to priority 1,
   [uart_irq_id] (= 10) and [virtio_irq_id] (= 1), both come from DevModel. *)

(* plicinit's effect on the PLIC state: sources [uart_irq_id] and
   [virtio_irq_id] get priority 1; all other fields untouched.  This is
   exactly [plic_write (.. off 40 ..) 1] then [plic_write (.. off 4 ..) 1]. *)
Definition plicinit_plic (p : plic_state) : plic_state :=
  PlicState (nupd (nupd (p_prio p) uart_irq_id (Z_to_bv 32 1)) virtio_irq_id (Z_to_bv 32 1))
            (p_pending p) (p_claimed p) (p_enable p) (p_thresh p).

Definition wp_plicinit_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : plic_state) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.plicinit in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m0 n -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  plic_frag p -∗
  ( ∀ m' : regfile,
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    sconf γ -∗
    sie_cap_gpr γ root_ppn m' n -∗
    tlb_inv_pt root_ppn -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 ⌝ -∗
    plic_frag (plicinit_plic p) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PLICINIT.
  Parameter wp_plicinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : plic_state),
      wp_plicinit_sconf_body γ root_ppn Φ m0 n p.
End PLICINIT.
