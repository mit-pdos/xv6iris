(* SpecUartinit.v -- the public interface of Uartinit, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   [uartinit] is the 16550 device-init routine (kernel/uart.c).  It runs in
   S-mode during boot.  The seven MMIO byte writes are, in order (all to
   UART0 = [uart_pa off]):
     off 1 = 0x00   disable interrupts (IER)
     off 3 = 0x80   set DLAB (LCR_BAUD_LATCH)
     off 0 = 0x03   LSB divisor       (DLL, DLAB set)
     off 1 = 0x00   MSB divisor       (DLM, DLAB set)
     off 3 = 0x03   8N1, clear DLAB   (LCR_EIGHT_BITS)
     off 2 = 0x07   enable + clear both FIFOs (FCR)
     off 1 = 0x03   enable tx/rx interrupts (IER)
   then [initlock(&tx_lock, "uart")].

   STATED OVER THE TIME-0 DEVICE INVARIANT.  Device init does NOT run before
   [dev_inv] is allocated: the UART thread is a top-level thread from step 0 and
   every one of its steps needs the fragment, so [uart_frag] can never sit raw
   in a CPU's precondition while the system runs.  The contract is therefore
   stated over [WpUart.uart_inv], and the two writes that look incompatible with
   an invariant are both discharged by ghost arithmetic rather than by running
   early:

     - the FCR FIFO-CLEAR (off 2, bit 2) discards queued bytes, which a
       [mono_list] over [uart_acc] cannot do -- unless the FIFO is provably
       empty.  It is: the caller's [uart_tx_own γ l] pins [uart_acc u = l] and
       [uart_out_lb γ l] says the transmitted prefix has already reached [l],
       so [DevModel.uart_tx_empty_of_out] leaves nothing in [u_tx] and the
       clear shrinks nothing.  This is the same pair [uartputc_sync]'s poll
       hands forward ([WpUart.uart_tx_ready_persists]).
     - the DLAB SET (off 3 = 0x80) is why the caller threads the UNFROZEN
       half [uart_dlab_is γ (DfracOwn (1/2)) b0] at an ARBITRARY [b0] rather
       than the persistent [uart_dlab_off]: the freeze moved out of
       [uart_ghosts_alloc] into this function's tail, where the final LCR write
       has just cleared DLAB.  So [uart_dlab_off] is uartinit's OUTPUT.

   uartinit writes no THR, so the accepted trace is unchanged and the token and
   receipt come back at the same [l].

   ProofUartinit.v proves it by running each of the seven writes through the
   invariant-opening ACCESSOR-form UART store leaf
   [SpecUart.wp_sb_uart_uinv_s_sconf] and doing one ghost step per write, out
   of the per-offset [uart_write] readings in DevModel.v
   ([uart_write_1_stable] / [_0_dlab_stable] / [_3_stable] / [_2_stable]). *)
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
Require Import WpUart.
Require Import IntrDefs.
Require Import RegFile HartTp WpNext.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation UART_INIT := KernelSyms.uartinit.

(* NOTE: there is deliberately no [uartinit_post] naming the concrete UART state
   the seven writes produce.  The state lives inside [uart_inv], the contract
   talks only about the four ghosts, and the proof goes write-by-write through
   the accessor leaf rather than composing a closed-form successor, so nothing
   would consume it. *)

(* BOOT-ONLY: uartinit runs strictly before interrupts are ever enabled
   (main()'s [consoleinit()], on hart 0, always before scheduler()'s
   [intr_on()]) -- see claude-notes/projects/explicit-cpuid-porting-guide.md,
   "A function that READS tp mid-body must be stated at b = false" for the
   general shape this follows (worked example: SpecCpuid.v).  So the
   contract is stated at the literal index [false] rather than a generic
   [b], with no [wp_next] wrapper at all (it would collapse via
   [wp_next_off] anyway, since the hart cannot move). *)
Definition wp_uartinit_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ}
    `{CID : CpuId}
    (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (l : list (bv 8)) (b0 : bool) (vlock : bv 32) (vname vcpu : bv 64) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let lk : mword 64 := mword_of_int KernelSyms.tx_lock in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (4 <= K)%nat ->
  sie_cap_gpr m K false p -∗
  (* [kernel_data] supplies the "uart" string literal uartinit's [auipc a1 /
     addi a1] points at -- the name it hands to initlock. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the UART fabric, borrowed from the invariant around each write *)
  uart_inv γd -∗
  (* "everything accepted has been transmitted, and the transmitter is mine":
     the pair that makes the FCR FIFO-clear shrink nothing *)
  uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_sent γd l -∗
  (* the UNFROZEN DLAB half, at an arbitrary power-on value *)
  uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  ( ∀ mr,
    sie_cap_gpr mr K false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* no THR write, so the accepted trace is untouched *)
    uart_tx_own γd l -∗ uart_sent γd l -∗
    (* the final LCR write cleared DLAB, so the half is frozen for good *)
    uart_dlab_off γd -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field is written once and then DISCARDED: what comes back is
       the persistent [lock_name], ready to be sealed into [is_lock]. *)
    lock_name lk "uart"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type UARTINIT.
  Parameter wp_uartinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ} `{CID : CpuId}
      (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (vlock : bv 32) (vname vcpu : bv 64) (p : mword 64),
      wp_uartinit_sconf_body γd Φ m K l b0 vlock vname vcpu p.
End UARTINIT.
