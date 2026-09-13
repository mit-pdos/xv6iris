(* SpecConsputc.v -- the public interface of Consputc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void consputc(int c) {
       if (c == BACKSPACE) {
         uartputc_sync(0, '\b'); uartputc_sync(0, ' '); uartputc_sync(0, '\b');
       } else {
         uartputc_sync(0, c);
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
   transient-increment bound on [noff].  Acquire's "already holding" arm is
   refuted, so nothing panic-related is threaded.

   THE PORT IS THE CALLEE'S BUSINESS, NOT THIS CONTRACT'S.  XV6_REV 163d39b
   gives uartputc_sync a port index and consputc passes 0 at each of its four
   call sites, but the console IS port 0 and always was, so nothing a caller of
   consputc can observe moved: no binder, no premise and no postcondition
   conjunct here mentions a port.  What the bump does add is ONE premise --
   [SpecUartPutc.uart_base_word Uart0], the persistent .data word the callee
   LOADS its MMIO address out of.  It is not derivable from anything already
   here (the old driver spelled the address as a constant), so it has to be
   relayed; being persistent, a caller hands it over for free.

   THE TRANSMITTER IS NOT THREADED.  It is [tx_lock]'s resource
   ([UartTxInv.tx_res]), taken and given back inside each callee, so
   [uart_tx_own] appears nowhere; the caller brings only the persistent
   [UartTxInv.is_txlock γl γd] (which carries [uart_dlab_off] with it).  And
   because the lock is re-acquired PER BYTE -- three times on the BACKSPACE arm,
   with other harts free to interleave in between -- the trace claim is the
   sublist form [UartTxInv.uart_sent_sub], threaded [bs] in / [bs ++ cs] out,
   with [cs] PINNED to the arm's own bytes (below). *)
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
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import DevModel.   (* [Uart0] *)
Require Import DiskPtsto WpUart.
Require Import IntrDefs WpNext.
Require Import LockRank.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import SpecUartPutc.   (* [cp_byte], [cp_byte_sb]: the byte
     uartputc_sync stores for an argument, which is what each arm pushes *)
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* consputc's own frame is 2 slots ([c.addi16sp sp,-16] at +0x00), over
   uartputc_sync's 18.  IT WAS 16: at 163d39b uartputc_sync keeps the port
   pointer, the lock pointer and the loaded base in callee-saved registers, so
   its own frame doubled (32 -> 64 bytes, 4 -> 8 slots) and every caller's
   budget rises by four.  Above this, printint's [printint_stack] and every
   budget over it move with it. *)
Notation consputc_stack := (20%nat) (only parsing).

(* ===================================================================== *)
(*  WHICH BYTES (app-echo.md, E5/O4, lane ECHO-RECEIPT).                  *)
(*                                                                       *)
(*  The post used to say only that SOME list [cs] was appended.  It says  *)
(*  WHICH now, because the console's echo has to be matched to the byte   *)
(*  it echoes and consputc is the only thing between the two: the arms    *)
(*  are a two-way test on [c] and each knows its own bytes, so pinning    *)
(*  them costs this contract one pure conjunct and its caller one         *)
(*  intro.  Nothing above printk reads it -- printk's own post keeps its  *)
(*  [cs] existential ([SpecPrintk.v]), which is where the format          *)
(*  recursion would otherwise have to carry a rendering.                  *)
(*                                                                       *)
(*  [consputc_bs] is the BACKSPACE arm's three bytes -- backspace, space, *)
(*  backspace, i.e. erase one glyph -- and [cp_byte] is the low byte      *)
(*  uartputc_sync stores for an argument, which is what the other arm     *)
(*  pushes.  BACKSPACE is 0x100 (console.c), so it is NOT a byte value    *)
(*  and the two arms never overlap.                                       *)
(* ===================================================================== *)
Definition consputc_bs : list (bv 8) :=
  [(mword_of_int 8 : mword 8); (mword_of_int 32 : mword 8);
   (mword_of_int 8 : mword 8)].

(* BACKSPACE is 0x100 (console.c), so it is not a byte value and the two
   arms cannot both fire. *)
Definition cp_backspace : mword 64 := mword_of_int 256.

(* the three bytes of the BACKSPACE arm, at [cp_byte]'s spelling: what the
   three [c.li a0,_ ; jal uartputc_sync] pairs store. *)
Lemma cp_byte_bs1 : cp_byte (mword_of_int 8) = (mword_of_int 8 : mword 8).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma cp_byte_bs2 : cp_byte (mword_of_int 32) = (mword_of_int 32 : mword 8).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Definition wp_consputc_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
    (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.consputc in
  let ra0 := m0 !!! Regidx ra_idx in
  let a00 := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  (consputc_stack <= K)%nat ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* the order premise, at the LOWEST rank this cone touches; every
     higher one follows by [locks_below_mono]. *)
  locks_below lks "uart" ->
  sie_cap_gpr kt m0 K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  (* the .data word the callee LOADS its MMIO base from (SpecUartPutc.v) *)
  uart_base_word Uart0 -∗
  is_txlock γl γd -∗
  uart_sent_sub γd bs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf cs,
    sie_cap_gpr kt mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    (* WHICH BYTES: the BACKSPACE arm's triple, or the argument's low byte *)
    ⌜ if eq_vec a00 cp_backspace then cs = consputc_bs else cs = [cp_byte a00] ⌝ -∗
    uart_sent_sub γd (bs ++ cs) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSPUTC.
  Parameter wp_consputc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_consputc_sconf_body kt γl γd γv m0 K bs n eb b p lks.
End CONSPUTC.
