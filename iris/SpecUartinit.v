(* SpecUartinit.v -- the public interface of Uartinit, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   [uartinit] is the 16550 device-init routine (kernel/uart.c).  It runs in
   S-mode during boot, before [dev_inv] is allocated, so it owns the raw
   [uart_frag] half directly (NOT [dev_inv] + a transmitter token like
   [uartputc_sync]) -- indeed it performs the two writes the invariant forbids:
   a FIFO-clearing FCR write and a DLAB set (to program the divisor latch).

   The seven MMIO byte writes are, in order (all to UART0 = [uart_pa off]):
     off 1 = 0x00   disable interrupts (IER)
     off 3 = 0x80   set DLAB (LCR_BAUD_LATCH)
     off 0 = 0x03   LSB divisor       (DLL, DLAB set)
     off 1 = 0x00   MSB divisor       (DLM, DLAB set)
     off 3 = 0x03   8N1, clear DLAB   (LCR_EIGHT_BITS)
     off 2 = 0x07   enable + clear both FIFOs (FCR)
     off 1 = 0x03   enable tx/rx interrupts (IER)
   then [initlock(&tx_lock, "uart")].

   Composing the seven [uart_write]s, the resulting UART state is DETERMINED
   independently of the entry state's DLAB (the 2nd write overwrites LCR), and
   its only dependence on the entry state is the observable output trace
   [u_out], which is preserved.  We name it [uartinit_post], and it has DLAB
   off -- exactly the [uart_dlab u = false] premise [uart_ghosts_alloc] needs
   to allocate [dev_inv] afterward. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import WpLock.
Require Import DevModel.
Require Import IntrDefs.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation UART_INIT := KernelSyms.uartinit.

(* The UART state after the seven device-init writes.  Independent of the
   entry state save for the preserved output trace [u_out u0]:
     rx = [], tx = [] (FCR cleared both FIFOs); ier = 0x03; lcr = 0x03 (DLAB
     off); fcr = 0x07; dll = 0x03; dlm = 0x00. *)
Definition uartinit_post (u0 : uart_state) : uart_state :=
  UartState [] [] (u_out u0)
            (Z_to_bv 8 0x03) (Z_to_bv 8 0x03) (Z_to_bv 8 0x07)
            (Z_to_bv 8 0x03) (Z_to_bv 8 0x00).

(* The payoff the caller relies on: the device leaves init with DLAB off, so
   [dev_inv] can be allocated over [uartinit_post u0]. *)
Lemma uartinit_post_dlab_off (u0 : uart_state) : uart_dlab (uartinit_post u0) = false.
Proof. reflexivity. Qed.

Definition wp_uartinit_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat) (u0 : uart_state) (vlock : bv 32) (vname vcpu : bv 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let lk : mword 64 := mword_of_int KernelSyms.tx_lock in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (4 <= K)%nat ->
  sie_cap_gpr γ m K -∗
  (* [kernel_data] supplies the "uart" string literal uartinit's [auipc a1 /
     addi a1] points at -- the name it hands to initlock. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  uart_frag u0 -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ( ∀ mr,
    sie_cap_gpr γ mr K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    uart_frag (uartinit_post u0) -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field is written once and then DISCARDED: what comes back is
       the persistent [lock_name], ready to be sealed into [is_lock]. *)
    lock_name lk "uart"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UARTINIT.
  Parameter wp_uartinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (K : nat) (u0 : uart_state) (vlock : bv 32) (vname vcpu : bv 64),
      wp_uartinit_sconf_body γ Φ m K u0 vlock vname vcpu.
End UARTINIT.
