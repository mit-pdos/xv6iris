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
   two axes:

   - the number of bytes.  The two arms push a different number of bytes (three
     for a BACKSPACE, one otherwise), so a post naming a single byte would have
     to case-split on [c] -- and every caller above (printint, printk) would
     then have to carry that split all the way up through a format-string
     recursion, for no gain: nothing in the kernel depends on WHICH bytes reach
     the UART.  So the post says only that SOME byte list [bs] was appended to
     the accepted trace, which is what "the character was printed" means at this
     altitude.  The exclusive-transmitter token still comes back, now standing
     for [l ++ bs], so the caller can print again -- and the persistent
     [uart_sent] receipt records that the bytes provably reached the FIFO.

   - which path of uartputc_sync runs.  Like uartputc_sync's own spec this is
     the PANIC path ([panicking <> 0], [panicked = 0]): the callee then does no
     push_off/pop_off and takes no lock, so consputc threads no [intr_count]
     and no lock resource either.  It is the path panic() -> printk() runs on.

   The two [volatile int] globals are threaded as fractional cells, exactly as
   uartputc_sync takes them: they are read (never written) on this path, and
   handed straight back. *)
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
From Kernel Require KernelSyms.


Definition wp_consputc_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
    (l : list (bv 8)) (pv pkv : mword 32) (dqm dqm2 : dfrac) (b : bool) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.consputc in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (* consputc's own 2-slot frame, over uartputc_sync's 4 *)
  (6 <= K)%nat ->
  eq_vec (sign_extend' 64 pv) zero_reg = false ->
  neq_vec (sign_extend' 64 pkv) zero_reg = false ->
  sie_cap_gpr m0 K b p -∗
  kernel_text -∗ pc_is pcE -∗
  (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
  (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
  dev_inv γd γv -∗ uart_tx_own γd l -∗ uart_dlab_off γd -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf bs,
    sie_cap_gpr mf K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    (mword_of_int KernelSyms.panicking : mword 64) ↦₄{ dqm } pv -∗
    (mword_of_int KernelSyms.panicked : mword 64) ↦₄{ dqm2 } pkv -∗
    uart_tx_own γd (l ++ bs) -∗ uart_sent γd (l ++ bs) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSPUTC.
  Parameter wp_consputc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ) (m0 : regfile) (K : nat)
      (l : list (bv 8)) (pv pkv : mword 32) {dqm dqm2 : dfrac} (b : bool) (p : mword 64),
      wp_consputc_sconf_body γd γv Φ m0 K l pv pkv dqm dqm2 b p.
End CONSPUTC.
