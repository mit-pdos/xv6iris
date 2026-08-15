(* SpecPrintint.v -- the public interface of Printint, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static void printint(long long xx, int base, int sign) {
       char buf[20]; int i; unsigned long long x;
       if (sign && (sign = (xx < 0))) x = -xx; else x = xx;
       i = 0;
       do { buf[i++] = digits[x % base]; } while ((x /= base) != 0);
       if (sign) buf[i++] = '-';
       while (--i >= 0) consputc(buf[i]);
     }

   Like consputc's, the post says only that SOME byte list was appended to what
   this caller has provably sent -- the caller (printk) never depends on which
   digits came out.  That is the whole reason this spec is short: a
   digit-accurate post would have to name the base-[base] representation of [xx]
   and thread it up through printk's format recursion.

   THE ONE PRECONDITION THAT IS NOT BOILERPLATE is the range of [base]:

       10 <= uint base <= 16

   and both ends are load-bearing, not defensive:

   - the UPPER bound is what makes [digits[x % base]] a legal read.  [digits] is
     a 16-byte table, and the code indexes it by [x % base] with no check; a
     [base] above 16 would index off the end.
   - the LOWER bound is what makes [buf] big enough.  The do-while writes one
     byte per base-[base] digit of [x] and [buf] holds 20; a 64-bit [x] has at
     most 20 digits once [base >= 10], and in the negative case at most 19 plus
     the '-'.  With [base = 2] the same code would write 64 bytes and run off
     the frame, so this is a genuine caller obligation, and printk (which calls
     only with 10 and 16) discharges it.

   [kernel_data] supplies the [digits] table itself.

   THE PANIC PATH IS GONE, and with it everything this contract used to carry
   because of it: printk.c's [panicking]/[panicked] globals are deleted, so
   there are no flag cells and no [eq_vec]/[neq_vec] refutation premises.  What
   arrives in their place is what every consputc byte now costs -- a [tx_lock]
   acquire/release round trip per byte -- so printint threads the ordinary
   spinlock-caller accounting ([cpu_own] net-zero, the [noff] transient bound,
   [panic_wp_any]) and brings the persistent [UartTxInv.is_txlock] rather than
   the transmitter token, which lives under that lock.  The digit loop takes the
   lock once per digit, so the trace claim is the sublist form
   [UartTxInv.uart_sent_sub] -- see SpecConsputc.v. *)
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
Require Import KernelText KernelDataInv.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
From Kernel Require KernelSyms.


(* printint's own frame is 8 slots ([c.addi16sp sp,-64] at 0x80000474), over
   consputc's 16. *)
Definition printint_stack : nat := 24%nat.

Definition wp_printint_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
    (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let pcE := mword_of_int KernelSyms.printint in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (printint_stack <= K)%nat ->
  (10 <= uint (m0 !!! Regidx a1_idx) <= 16)%Z ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* printint -> consputc -> uartputc_sync *)
  locks_below lks "uart" ->
  sie_cap_gpr m0 K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  is_txlock γl γd -∗
  uart_sent_sub γd bs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf cs,
    sie_cap_gpr mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    uart_sent_sub γd (bs ++ cs) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PRINTINT.
  Parameter wp_printint_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_printint_sconf_body γl γd γv m0 K bs n eb b p lks.
End PRINTINT.
