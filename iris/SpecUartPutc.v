(* SpecUartPutc.v -- the public interface of UartPutc, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     void uartputc_sync(int c) {
       acquire(&tx_lock);
       while ((ReadReg(LSR) & LSR_TX_IDLE) == 0) ;
       WriteReg(THR, c);
       release(&tx_lock);
     }

   THERE IS NO LONGER A PANIC PATH.  Both [volatile int panicking] and
   [volatile int panicked] are DELETED from printk.c, and with them the two
   guarded [push_off]/[pop_off] calls and the [if (panicked) for(;;)] spin that
   used to make this function's behaviour depend on which of the two paths the
   caller was on.  What replaces them is a plain critical section: uartputc_sync
   now takes [tx_lock] -- a SPINLOCK again -- around its poll/store pair, which
   is what makes it agree with uartwrite (the other transmit path) instead of
   racing it.  So the contract carries no flag cells, no [eq_vec]/[neq_vec]
   refutation premises, and, being a spinlock caller, the ordinary [cpu_own]
   accounting of any function that acquires and releases.

   WHAT THE CALLER NO LONGER OWNS.  [UartTxInv.tx_res γd = ∃ l, uart_tx_own γd l]
   is the LOCK's resource now, so the exclusive transmitter token comes out of
   the acquire and goes back on the release: it is neither a premise nor a
   postcondition here.  All the caller brings is the persistent credential
   [UartTxInv.is_txlock γl γd], which bundles the lock with the frozen-DLAB fact
   [uart_dlab_off] the THR store needs -- hence no separate [uart_dlab_off]
   premise either.

   WHAT THE CALLER GETS INSTEAD, and it is WEAKER than before: a SUBLIST claim.
   The old post handed back [uart_sent γd (l ++ [sb])], a CONTIGUOUS accepted
   prefix, which was sound only because the caller held the transmitter across
   its whole output.  The lock is re-acquired per byte now, so another hart may
   have bytes accepted between two of ours and a contiguous claim is simply
   false.  [UartTxInv.uart_sent_sub γd bs] -- "[bs] is a sublist of the accepted
   trace", persistent -- is the honest statement, and this function's step on it
   is exactly [UartTxInv.uart_sent_sub_snoc]: [bs] in, [bs ++ [sb]] out. *)
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
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.


(* uartputc_sync's own frame is 4 slots ([c.addi16sp sp,-32] at 0x8000094c),
   and its only callees are acquire and release, which want 10 below it. *)
Notation uartputc_stack := (14%nat) (only parsing).
Definition wp_uartputc_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
    (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.uartputc_sync in
  let ra0 := m0 !!! Regidx ra_idx in
  let a00 := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  let sb : mword 8 := autocast (T := mword)
     (subrange_vec_dec (and_vec (add_vec zero_reg a00)
        (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
  (uartputc_stack <= K)%nat ->
  (* acquire's transient [noff] increment must not overflow the [int] *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "uart"'s -- uartputc_sync acquires and releases [tx_lock] in the same
     call, so this contract is BALANCED: [lks] is unchanged end to end. *)
  locks_below lks "uart" ->
  sie_cap_gpr kt m0 K b p -∗
  (* the interrupt level is left exactly as found: an acquire/release pair *)
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  is_txlock γl γd -∗
  uart_sent_sub γd bs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf,
    sie_cap_gpr kt mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    uart_sent_sub γd (bs ++ [sb]) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTPUTC.
  Parameter wp_uartputc_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γl : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_uartputc_sconf_body kt γl γd γv m0 K bs n eb b p lks.
End UARTPUTC.
