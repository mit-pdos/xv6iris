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

   STATED OVER THE TIME-0 DEVICE INVARIANT (2026-07-29).  This contract used to
   own the RAW [uart_frag] half, on the premise that device init runs before
   [dev_inv] is allocated.  That premise is false: the UART thread is a
   top-level thread from step 0 and every one of its steps needs the fragment,
   so [uart_frag] can never sit raw in a CPU's precondition while the system
   runs.  The contract is therefore stated over [WpUart.uart_inv], and the two
   writes the invariant was thought to forbid are both discharged by ghost
   arithmetic rather than by running early:

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

   THE PROOF IS TEMPORARILY ASSUMED (an [Axiom] in LinkUartinit.v).  The old
   raw-frag proof (ProofUartinit.v, deleted here, recoverable from git history)
   is being re-worked over the invariant-opening ACCESSOR-form UART store leaf;
   until it lands this interface is axiom-backed and the coverage report reads
   uartinit as assumed.  See claude-notes/projects/main-boot.md, G1. *)
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
Require Import WpUart.
Require Import IntrDefs.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation UART_INIT := KernelSyms.uartinit.

(* The UART state after the seven device-init writes.  Independent of the
   entry state save for the preserved output trace [u_out u0]:
     rx = [], tx = [] (FCR cleared both FIFOs); ier = 0x03; lcr = 0x03 (DLAB
     off); fcr = 0x07; dll = 0x03; dlm = 0x00.
   No longer part of the contract (the state lives inside [uart_inv] now), but
   kept as the pure vocabulary the re-worked proof composes its seven writes
   into. *)
Definition uartinit_post (u0 : uart_state) : uart_state :=
  UartState [] [] (u_out u0)
            (Z_to_bv 8 0x03) (Z_to_bv 8 0x03) (Z_to_bv 8 0x07)
            (Z_to_bv 8 0x03) (Z_to_bv 8 0x00).

(* the device leaves init with DLAB off -- which is what licenses the freeze
   that mints [uart_dlab_off] at the tail. *)
Lemma uartinit_post_dlab_off (u0 : uart_state) : uart_dlab (uartinit_post u0) = false.
Proof. reflexivity. Qed.

(* and it accepts nothing: the accepted trace is exactly what came in, so the
   transmitter token and the receipt come back at the same list. *)
Lemma uartinit_post_acc (u0 : uart_state) :
  u_tx (uartinit_post u0) = [] /\ uart_acc (uartinit_post u0) = u_out u0.
Proof. split; [reflexivity|]. unfold uart_acc. by rewrite app_nil_r. Qed.

Definition wp_uartinit_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{!uartGhostG Σ}
    `{CID : CpuId}
    (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
    (l : list (bv 8)) (b0 : bool) (vlock : bv 32) (vname vcpu : bv 64) :=
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
    sie_cap_gpr γ mr K -∗
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
      (γ : gname) (γd : uart_names) (Φ : mval -> iProp Σ) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (vlock : bv 32) (vname vcpu : bv 64),
      wp_uartinit_sconf_body γ γd Φ m K l b0 vlock vname vcpu.
End UARTINIT.
