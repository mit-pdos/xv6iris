(* SpecUartintr.v -- the public interface of uartintr, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void uartintr(void);

   The UART's interrupt handler, called from devintr().  It acknowledges the
   interrupt (an ISR read), then does two independent things:

     TX: under tx_lock, if LSR says the transmitter is idle, clear [tx_busy]
         and wake the writers blocked in uartwrite;
     RX: drain the receive FIFO into consoleintr(), one byte at a time, via
         uartgetc() -- which gcc INLINES, so it has no symbol of its own; its
         body is uartintr +0x44..+0x54.

   @ KernelSyms.uartintr = 0x800009ce, 39 instructions, a 32-byte frame.

   THIS IS THE OTHER HALF OF [UartTxInv.tx_res].  uartwrite READS the lock
   invariant's implication "tx_busy == 0 ⟹ everything accepted has been
   transmitted" to license a THR store with no poll; uartintr is what WRITES
   it: the [uart_out_lb] it needs comes from [uart_tx_poll_thre] applied to
   the very LSR read whose THRE bit gates the [tx_busy = 0] store one
   instruction later.  Neither function makes sense without the other, and
   the invariant is the entire interface between them -- see
   claude-notes/projects/uartwrite.md.

   The RX half needs nothing from the device ghosts at all: no read moves the
   accepted trace, the transmitted prefix or DLAB ([DevModel.uart_read_stable]),
   so the rx-ready poll and the RHR pop are plain observations that a hart
   holding no token may perform.  That is also why the rx loop can run AFTER
   the release, exactly as the C does.

   WHAT THE CONTRACT SAYS: nothing about the output.  An interrupt handler's
   job is to leave the caller's state alone, and that is what is promised --
   every callee-saved register, the interrupt-nesting level, and the register
   file's totality.  The rx loop is UNBOUNDED (the device may keep supplying
   bytes), so the WP is, as always, partial correctness.

   Callees: acquire, release, wakeup, and consoleintr -- the last ASSUMED
   (SpecConsoleintr.v / LinkConsoleintr.v). *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import SmodeCore.
Require Import FdSlots.
Require Import ProcGeom.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import SpecPanic.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
From Kernel Require KernelSyms.


(* uartintr's own frame is 4 slots; the deepest callee is consoleintr at 32
   (wakeup wants 18, acquire and release 10). *)
Definition uartintr_stack : nat := 36%nat.

Definition wp_uartintr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γu : uart_names) (γv : disk_names) (γl : gname)
     (γs : list gname)
    (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartintr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  length γs = NPROC ->
  (* the transient noff increments (tx_lock, and wakeup's per-proc lock) stay
     in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (uartintr_stack <= av)%nat ->
  sie_cap_gpr m av b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the device, and the transmitter's lock -- the whole credential *)
  dev_inv γu γv -∗
  is_txlock γl γu -∗
  (* the running-thread bundle (wakeup / consoleintr) *)
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf)) ⌝ -∗
      sie_cap_gpr mf av b pme -∗
      cpu_own lvl eb pme C b -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTINTR.
  Parameter wp_uartintr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γu : uart_names) (γv : disk_names) (γl : gname)
      (γs : list gname)
      (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (C : iProp Σ) (b : bool),
      wp_uartintr_sconf_body γu γv γl γs m av lvl eb pme C b.
End UARTINTR.
