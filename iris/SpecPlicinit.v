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
   PLIC identity mapping.

   STATED OVER THE TIME-0 DEVICE INVARIANT (2026-07-29).  This contract used to
   own the RAW [plic_frag] half, on the premise that boot-time device init runs
   before the device threads are live.  That premise is false -- the PLIC
   gateway latches whenever an irq line is up, so [plic_frag] can never sit raw
   in a CPU's precondition while the system runs -- so plicinit is stated over
   [WpUart.plic_inv] and borrows the fragment around each of its two writes.

   NOTHING comes back on the device side.  The old [plic_frag (plicinit_plic p)]
   postcondition is dropped: no consumer needs the priorities recorded (a
   device-interrupt proof reads the invariant's [plic_ok], and priority writes
   preserve it), and there is no monotonicity constraint on the PLIC ghost that
   would make a recorded value useful later.  [plicinit_plic] stays as pure
   vocabulary for the proof.

   THE PROOF IS TEMPORARILY ASSUMED (an [Axiom] in LinkPlicinit.v): the
   raw-frag proof (ProofPlicinit.v, deleted here, recoverable from git history)
   is being re-worked over the invariant-opening ACCESSOR-form PLIC store leaf.
   See claude-notes/projects/main-boot.md, G1.

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
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import DevModel.
Require Import WpUart.
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
    (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.plicinit in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  sie_cap_gpr γ m0 n -∗
  kernel_text -∗ pc_is pcE -∗
  (* the PLIC fabric, borrowed from the invariant around each priority write;
     both writes preserve [plic_ok], so nothing is owed back to the caller *)
  plic_inv -∗
  ( ∀ m' : regfile,
    sie_cap_gpr γ m' n -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PLICINIT.
  Parameter wp_plicinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat),
      wp_plicinit_sconf_body γ Φ m0 n.
End PLICINIT.
