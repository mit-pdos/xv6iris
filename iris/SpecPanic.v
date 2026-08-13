(* SpecPanic.v -- panic()'s contract.

     void panic(char *s) {
       printk("panic: ");
       printk("%s\n", s);
       for (;;) ;
     }

   NO POSTCONDITION.  panic never returns -- its last instruction is a
   self-jump -- so the contract is a bare [WP Loop] with no continuation at
   all, and a caller that reaches panic has thereby discharged its own goal.
   That is what makes a panic arm cheap to close, and it is the one thing
   [PanicStub.panic_wp] (the placeholder this replaces) already got right.

   THE PRECONDITION IS FORCED BY THE TWO printk CALLS, which are ordinary
   calls with an ordinary contract ([SpecPrintk.PRINTK]).  Four parts:

   1. THE MESSAGE.  [a0] is the vararg of a "%s" directive, so it is described
      exactly as printk describes one: a [pk_arg_desc] of kind [PkStr] -- a
      [char *] to a string the caller owns ([PkAStr dq s], handed over and
      never returned, there being nothing to return it to) or a null pointer
      ([PkANull], which printk prints as "(null)").  Every panic site in xv6
      passes a .rodata literal, so the obligation is discharged by
      [KernelDataInv.kernel_data_string] out of [kernel_data], which the
      caller already holds.

   2. THE STACK.  panic pushes a 32-byte frame (4 slots) and then calls
      printk, whose own budget is [SpecPrintk.printk_stack] = 48; hence
      [panic_stack] = 52.

   3. THE INTERRUPT/LOCK ACCOUNTING.  printk takes pr.lock, and tx_lock under
      it, so the caller's [cpu_own n eb p C b] is required -- and consumed --
      together with the [n + 2] headroom printk asks for.  Unlike printk's own
      [n], panic's is arbitrary: a panic arm is normally reached with locks
      already held.

   4. [panic_env], the persistent credentials printk needs, bundled so a call
      site threads one hypothesis and not four: pr.lock's [is_lock] (whose
      resource is [emp] -- see [SpecPrintkGen.pr_res]), the device invariant
      and the tx_lock credential.  A [uart_sent_sub] rides beside it, indexed
      by the trace prefix, because printk threads that claim in as well as
      out.

   THE ONE PREMISE THAT IS NOT ABOUT panic: [PanicStub.panic_wp_any].  printk's
   own precondition asks for it (acquire's "already holding" arm), so panic has
   to hand printk one -- the C-level panic -> printk -> acquire -> panic cycle
   showing through.  It is an assumption of THIS contract rather than of
   panic's proof so that the shape of the eventual fix is visible: when the
   call sites are spliced over to this contract, that premise becomes this
   contract itself and closes by Löb (panic pushes its frame before it calls
   printk, so there is a step to strip the later on).  See PanicStub.v. *)
From Stdlib Require Import ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile.
Require Import SmodeCore.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import PrintkArgs.
Require Import PanicStub.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* panic's own 4-slot frame, over printk's 48 ([SpecPrintk.printk_stack]; not
   named here, because that file sits above this one). *)
Definition panic_stack : nat := 52%nat.

Section PanicEnv.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId}.

  (* the three persistent credentials the printk cone needs, as one
     hypothesis.  All hart-free, so this crosses a migration untouched. *)
  Definition panic_env (γpr γl : gname) (γd : uart_names) (γv : disk_names)
    : iProp Σ :=
    (is_lock γpr pk_pr_lock "pr"%string (emp : iProp Σ) ∗
     dev_inv γd γv ∗
     is_txlock γl γd)%I.

  Global Instance panic_env_persistent γpr γl γd γv :
    Persistent (panic_env γpr γl γd γv).
  Proof. apply _. Qed.

End PanicEnv.

Definition wp_panic_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr γl : gname) (γd : uart_names) (γv : disk_names)
    (m : regfile) (K : nat) (bs : list (bv 8))
    (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (p : mword 64)
    (dm : pk_arg_desc) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let msg := m !!! Regidx a0_idx in
  (panic_stack <= K)%nat ->
  (* the message is a "%s" argument: a string the caller owns, or null *)
  pk_desc_kind dm = PkStr ->
  (* printk holds pr.lock while the cone below takes tx_lock: [+2], not [+1] *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* NOT about panic -- printk's precondition for acquire's panic arm.  See
     the header and PanicStub.v. *)
  panic_wp_any -∗
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ kernel_data -∗
  pc_is (mword_of_int KernelSyms.panic) -∗
  panic_env γpr γl γd γv -∗
  uart_sent_sub γd bs -∗
  pk_desc_res msg dm -∗
  WP (Loop : expr riscv_lang).

Module Type PANIC.
  Parameter wp_panic_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr γl : gname) (γd : uart_names) (γv : disk_names)
      (m : regfile) (K : nat) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) (b : bool) (p : mword 64)
      (dm : pk_arg_desc),
      wp_panic_sconf_body γpr γl γd γv m K bs n eb C b p dm.
End PANIC.
