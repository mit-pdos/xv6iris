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
      resource is [emp] -- see [SpecPrintk.pr_res]), the device invariant
      and the tx_lock credential.

      AND NOT A [uart_sent_sub].  printk threads that claim IN as well as out
      ([SpecPrintk.v]: [uart_sent_sub γd bs] in, [uart_sent_sub γd (bs ++ cs)]
      out, [bs] universally quantified), but the precondition slot is an
      ACCUMULATOR FOR THE POSTCONDITION, not a gate: [bs] is never inspected,
      it is only re-emitted with printk's own bytes appended, so a caller who
      does not want the ordering claim instantiates it at [[]] and pays
      nothing.  panic has NO POSTCONDITION -- its last instruction is a
      self-jump and the contract is a bare [WP Loop] -- so a premise whose
      only purpose is to feed a postcondition has no purpose here at all.
      [ProofPanic] mints its own [uart_sent_sub γd []] with
      [UartTxInv.uart_sent_sub_nil_free], which needs nothing whatsoever
      ([◯ML []] is the unit of the mono-list RA), and the [bs] parameter is
      gone from this file.

   AND THERE IS NO LONGER A PREMISE THAT IS NOT ABOUT panic.  This contract
   used to ask for [PanicStub.panic_wp_any] as well, because printk's own
   precondition asked for it (acquire's "already holding" arm) and panic had
   to hand printk one -- the C-level panic -> printk -> acquire -> panic cycle
   showing through.  The plan of record was to close that cycle by Löb once
   the call sites were spliced over.  IT DID NOT NEED TO BE CLOSED: acquire's
   arm is refuted now (SpecAcquire.v), so the whole printk cone -- printk,
   printint, consputc, uartputc_sync -- asks for no panic credential at all,
   and panic's contract is self-contained.  What is left of the splice is the
   NINE functions that reach a [jal panic] of their own on a LIVE arm (bread,
   ilock, iget, dirlookup, dirlink, fileread, filewriteParts, kexit (two arms),
   kexecB2) -- kvmmap left the list when SpecKvmmap went counted-only. *)
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
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* panic's own 4-slot frame, over printk's 48 ([SpecPrintk.printk_stack]; not
   named here, because that file sits above this one). *)
Notation panic_stack := (52%nat) (only parsing).
Section PanicEnv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.

  (* the three persistent credentials the printk cone needs, as one
     hypothesis.  All hart-free, so this crosses a migration untouched. *)
  Definition panic_env_at (γpr γl : gname) (γd : uart_names) (γv : disk_names)
    : iProp Σ :=
    (is_lock γpr pk_pr_lock "pr"%string (emp : iProp Σ) ∗
     dev_inv γd γv ∗
     is_txlock γl γd)%I.

  Global Instance panic_env_at_persistent γpr γl γd γv :
    Persistent (panic_env_at γpr γl γd γv).
  Proof. apply _. Qed.

  (* ---- THE GHOST NAMES ARE EXISTENTIAL, AND NOTHING IS LOST BY IT --------
     A call site threads ONE nameless persistent token; no spec below panic
     gains a parameter.  Two independent reasons this is not a weakening.

     LOGICALLY it is an equivalence, not an approximation.  With the
     [uart_sent_sub] premise gone (see the header), all four names occur
     EXACTLY ONCE in [wp_panic_sconf_body] -- inside this one conjunct -- and
     none occurs in the conclusion, which is the bare [WP Loop].  So
     [(∀ γ⃗, panic_env_at γ⃗ -∗ WP Loop)] and [((∃ γ⃗, panic_env_at γ⃗) -∗ WP Loop)]
     are interderivable by ∃-elimination.  Contrast [SpecConsoleintr.console_caps],
     which binds its two LOCK names but keeps [γu] a parameter for precisely
     the missing reason: its [γu] occurs again, in the contract proper.

     PHYSICALLY a caller cannot supply a bogus console, even though the logic
     cannot state uniqueness.  Every name here is pinned by an exclusive
     physical resource: [lock_inv γ lk s R] contains [lock_word lk v], the
     lock word itself, so γpr and γl are determined by the addresses
     [pk_pr_lock] / [a_tx_lock] that this very definition names; and
     [dev_inv]'s body holds [uart_frag u], the ghost half of the PHYSICAL
     device state paired with [uart_auth] inside [state_interp], so at most
     one (γd, γv) can have a live [dev_inv] at all.

     What each name is: γpr and γl key nothing but their own lock's
     held-state ghost (pr.lock's resource is [emp]; tx_lock's is [tx_res γd],
     keyed by γd, NOT by γl).  γd is the only one indexing real resources
     ([uart_tx_own], [uart_sent], [uart_dlab_off]).  γv is baggage: panic
     touches nothing disk, and it is here only because [dev_inv] bundles all
     four devices. *)
  Definition panic_env : iProp Σ :=
    (∃ (γpr γl : gname) (γd : uart_names) (γv : disk_names),
       panic_env_at γpr γl γd γv)%I.

  Global Instance panic_env_persistent : Persistent panic_env.
  Proof. apply _. Qed.

  Lemma panic_env_intro γpr γl γd γv :
    panic_env_at γpr γl γd γv -∗ panic_env.
  Proof. iIntros "#H". iExists γpr, γl, γd, γv. iExact "H". Qed.

  (* the shape a site actually has in hand: the three credentials loose. *)
  Lemma panic_env_of γpr γl γd γv :
    is_lock γpr pk_pr_lock "pr"%string (emp : iProp Σ) -∗
    dev_inv γd γv -∗ is_txlock γl γd -∗ panic_env.
  Proof.
    iIntros "#Hl #Hd #Ht". iExists γpr, γl, γd, γv.
    rewrite /panic_env_at. by iFrame "Hl Hd Ht".
  Qed.

End PanicEnv.

Definition wp_panic_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (m : regfile) (K : nat)
    (n : nat) (eb : bool) (b : bool) (p : mword 64)
    (dm : pk_arg_desc) (lks : gset string) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let msg := m !!! Regidx a0_idx in
  (panic_stack <= K)%nat ->
  (* the message is a "%s" argument: a string the caller owns, or null *)
  pk_desc_kind dm = PkStr ->
  (* printk holds pr.lock while the cone below takes tx_lock: [+2], not [+1] *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (* panic is printk + printk + self-jump; printk's bound is "pr" (14),
     and it reaches "uart" (15) under it via consputc. *)
  locks_below lks "pr" ->
  sie_cap_gpr kt m K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗
  pc_is (mword_of_int KernelSyms.panic) -∗
  panic_env -∗
  pk_desc_res msg dm -∗
  WP (Loop : expr riscv_lang).

Module Type PANIC.
  Parameter wp_panic_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (m : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (dm : pk_arg_desc) (lks : gset string),
      wp_panic_sconf_body kt m K n eb b p dm lks.
End PANIC.
