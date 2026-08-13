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
   then [initsleeplock(&tx_lock, "uart")].

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

   AND IT INITIALIZES THE TRANSMIT SLEEPLOCK.  Upstream b7c25cf restored the
   trailing lock init that ae96fd0 had dropped (kernel-defects.md D2), as
   [initsleeplock(&tx_lock, "uart")] -- tx_lock is a [struct sleeplock] now,
   not a spinlock, so it is six fields rather than three.  The contract
   therefore takes the raw storage of that one lock and hands back the
   initialized cells plus the two persistent names, in exactly
   [SpecInitsleeplock.v]'s vocabulary: [SleepLock.sl_raw] in,
   [SleepLock.sl_fresh] out (the same shape SpecBinit/SpecIinit use for the
   sleeplocks THEY init, and precisely [SleepLock.sl_fresh_new]'s premises
   minus the resource).  So the caller's ghost step
   [sl_fresh a_tx_lock "uart" ∗ tx_res γd ==∗ is_sleeplock … a_tx_lock "uart"
   (tx_res γd)] plus the [uart_dlab_off] below is [UartTxInv.is_txlock] --
   the thing [LinkTxLockInit.v]'s axiom currently assumes.

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
Require Import SleepLock.
Require Import WpUart.
Require Import UartTxInv.
Require Import IntrDefs.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.


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
Definition wp_uartinit_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{!lockG Σ} `{!uartGhostG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γd : uart_names) (m : regfile) (K : nat)
    (l : list (bv 8)) (b0 : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (* THE FRAME PLUS THE CALLEE.  uartinit's own frame is [addi sp,sp,-16] = 2
     slots, and [initsleeplock] demands [(6 <= av)] of what is left, so the
     budget is 2 + 6. *)
  (8 <= K)%nat ->
  sie_cap_gpr m K false p -∗
  (* [kernel_data] is load-bearing again: it is where the "uart" string
     literal that the [auipc a1 / addi a1] pair points at comes from -- the
     name uartinit hands [initsleeplock] -- alongside the device-register
     writes, which are stated over the same image resources. *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the UART fabric, borrowed from the invariant around each write *)
  uart_inv γd -∗
  (* "everything accepted has been transmitted, and the transmitter is mine":
     the pair that makes the FCR FIFO-clear shrink nothing *)
  uart_tx_own γd l -∗ uart_out_lb γd l -∗ uart_sent γd l -∗
  (* the UNFROZEN DLAB half, at an arbitrary power-on value *)
  uart_dlab_is γd (DfracOwn (1/2)) b0 -∗
  (* the transmit sleeplock's storage, uninitialized: all six fields of
     [struct sleeplock tx_lock], contents arbitrary. *)
  sl_raw a_tx_lock -∗
  ( ∀ mr,
    sie_cap_gpr mr K false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    (* no THR write, so the accepted trace is untouched *)
    uart_tx_own γd l -∗ uart_sent γd l -∗
    (* the final LCR write cleared DLAB, so the half is frozen for good *)
    uart_dlab_off γd -∗
    (* THE TRANSMIT LOCK COMES BACK OUT, INITIALIZED -- the "newlock" ghost
       step's raw material, restored.  b7c25cf's [initsleeplock(&tx_lock,
       "uart")] zeroes [locked]/[lk.locked]/[lk.cpu]/[pid] and writes the two
       name fields, which are then DISCARDED in favour of the persistent
       [lock_name (sl_lk a_tx_lock) "sleep lock"] / [sl_name a_tx_lock
       "uart"].  [SleepLock.sl_fresh_new] seals the bundle into
       [is_sleeplock … a_tx_lock "uart" R] for the caller's choice of R
       ([UartTxInv.tx_res γd] is the one the driver wants). *)
    sl_fresh a_tx_lock "uart"%string -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTINIT.
  Parameter wp_uartinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{!lockG Σ} `{!uartGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (m : regfile) (K : nat)
      (l : list (bv 8)) (b0 : bool) (p : mword 64),
      wp_uartinit_sconf_body γd m K l b0 p.
End UARTINIT.
