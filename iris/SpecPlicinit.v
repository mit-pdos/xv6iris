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

   STATED OVER THE TIME-0 DEVICE INVARIANT.  Boot-time device init does NOT run
   before the device threads are live -- the PLIC gateway latches whenever an
   irq line is up, so [plic_frag] can never sit raw in a CPU's precondition
   while the system runs.  plicinit is therefore stated over [WpUart.plic_inv]
   and borrows the fragment around each of its two writes.

   NOTHING comes back on the device side, and the contract does not name the
   resulting PLIC state at all: no consumer needs the priorities recorded (a
   device-interrupt proof reads the invariant's [plic_ok], and priority writes
   preserve it), and there is no monotonicity constraint on the PLIC ghost that
   would make a recorded value useful later.

   ProofPlicinit.v proves it over the invariant-opening ACCESSOR-form PLIC
   store leaf [WpPlic.wp_sw_plic_pinv_s_sconf], whose per-write obligation --
   "the write is DEFINED and preserves [plic_ok] at EVERY state the plan
   admits", since a hart cannot know what the others have written -- is
   [PlicPlan.plic_write_prio_ok] for a source-priority write.

   Requires only the definitional layer -- never a whole-function proof file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpUart.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Import Defs.


(* the two PLIC interrupt-source ids xv6 raises to priority 1,
   [uart_irq_id] (= 10) and [virtio_irq_id] (= 1), both come from DevModel. *)

Definition wp_plicinit_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (m0 : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.plicinit in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  sie_cap_gpr KT1 m0 n false p -∗
  kernel_text -∗ pc_is pcE -∗
  (* the PLIC fabric, borrowed from the invariant around each priority write;
     both writes preserve [plic_ok], so nothing is owed back to the caller *)
  plic_inv -∗
  wp_next false p (fun (CID : CpuId) =>
    ∀ m' : regfile,
    sie_cap_gpr KT1 m' n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PLICINIT.
  Parameter wp_plicinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (m0 : regfile) (n : nat) (p : mword 64),
      wp_plicinit_sconf_body m0 n p.
End PLICINIT.
