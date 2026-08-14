(* SpecConsputc.v -- the public interface of Consputc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void consputc(int c) {
       if (c == BACKSPACE) {
         uartputc_sync('\b'); uartputc_sync(' '); uartputc_sync('\b');
       } else {
         uartputc_sync(c);
       }
     }

   consputc is the console's one-character output path, and the only thing the
   printk cone does to the UART.  Its contract is uartputc_sync's, LOOSENED on
   one axis: the number of bytes.  The two arms push a different number (three
   for a BACKSPACE, one otherwise), so a post naming a single byte would have to
   case-split on [c] -- and every caller above (printint, printk) would then have
   to carry that split all the way up through a format-string recursion, for no
   gain: nothing in the kernel depends on WHICH bytes reach the UART.  So the
   post says only that SOME byte list [cs] was appended to what this caller has
   provably sent, which is what "the character was printed" means at this
   altitude.

   THERE IS NO LONGER A SECOND PATH TO CHOOSE BETWEEN.  printk.c's two
   [volatile int] globals ([panicking], [panicked]) are deleted, so
   uartputc_sync has exactly one behaviour: it takes [tx_lock] around its
   poll/store pair.  Consequently this contract carries no flag cells and no
   [eq_vec]/[neq_vec] refutation premises, and it DOES carry what any spinlock
   caller carries -- [cpu_own] threaded net-zero (the acquire/release pair
   inside each uartputc_sync leaves the interrupt level as it found it), the
   transient-increment bound on [noff], and [panic_wp_any] for acquire's
   "already holding" arm.

   THE TRANSMITTER IS NOT THREADED.  It is [tx_lock]'s resource
   ([UartTxInv.tx_res]), taken and given back inside each callee, so
   [uart_tx_own] appears nowhere; the caller brings only the persistent
   [UartTxInv.is_txlock γl γd] (which carries [uart_dlab_off] with it).  And
   because the lock is re-acquired PER BYTE -- three times on the BACKSPACE arm,
   with other harts free to interleave in between -- the trace claim is the
   sublist form [UartTxInv.uart_sent_sub], threaded [bs] in / [bs ++ cs] out. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import PanicStub.
From Kernel Require KernelSyms.


(* consputc's own frame is 2 slots ([c.addi16sp sp,-16] at 0x8000028a), over
   uartputc_sync's 14. *)
Definition consputc_stack : nat := 16%nat.

Definition wp_consputc_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
    (bs : list (bv 8)) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.consputc in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (consputc_stack <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "uart" ->
  sie_cap_gpr m0 K b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  panic_wp_any -∗
  dev_inv γd γv -∗
  is_txlock γl γd -∗
  uart_sent_sub γd bs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf cs,
    sie_cap_gpr mf K b p -∗
    cpu_own n eb p C b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    uart_sent_sub γd (bs ++ cs) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSPUTC.
  Parameter wp_consputc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (p : mword 64) (lks : gset string),
      wp_consputc_sconf_body γl γd γv m0 K bs n eb C b p lks.
End CONSPUTC.
