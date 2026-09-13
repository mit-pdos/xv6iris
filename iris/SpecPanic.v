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

   06ea57f COMMENTED THE TWO CALLS OUT and 163d39b PUT THEM BACK.  The
   stopgap ("no console output on panic, for now") existed only to get the
   UART out of panic's cone; upstream replaced it with a SECOND UART, so
   panic prints again.  Nothing in this contract's SHAPE moved across either
   bump -- parts 1-3 were left standing when the calls went (a premise that
   is merely unused is still provable, a stack bound that is not tight is
   still a bound), so they are already exactly what the restored calls want.
   Only part 4 ever changed, and it changes back.

   1. THE MESSAGE.  [a0] is the vararg of a "%s" directive, so it is described
      exactly as printk describes one: a [pk_arg_desc] of kind [PkStr] -- a
      [char *] to a string the caller owns ([PkAStr dq s], handed over and
      never returned, there being nothing to return it to) or a null pointer
      ([PkANull], which printk prints as "(null)").  Every panic site in xv6
      passes a .rodata literal, so the obligation is discharged by
      [KernelDataInv.kernel_data_string] out of [kernel_data], which the
      caller already holds.

   2. THE STACK.  panic pushes a 32-byte frame (4 slots) and then calls
      printk, whose own budget is [SpecPrintk.printk_stack] = 52; hence
      [panic_stack] = 56.  Both numbers rose by four at this bump -- see the
      note at [panic_stack] below.

   3. THE INTERRUPT/LOCK ACCOUNTING.  printk takes pr.lock, and UART1's
      tx_lock under it, so the caller's [cpu_own n eb p C b] is required --
      and consumed -- together with the [n + 2] headroom printk asks for.  Unlike printk's own
      [n], panic's is arbitrary: a panic arm is normally reached with locks
      already held.

   4. [panic_env], the persistent credentials printk needs, bundled so a call
      site threads one hypothesis and not four: pr.lock's [is_lock] (whose
      resource is [emp] -- see [SpecPrintk.pr_res]) and
      [SpecPrputc.prputc_env], the SECOND PORT's credential.  06ea57f emptied
      this to [emp]; 163d39b REFILLS it, because printk's precondition asks
      for both again and neither is mintable -- an [is_lock] and a
      [uart_inv] can only be handed down from the boot chain that created
      them.  Refilling costs no call site anything for the same reason
      emptying did not: the premise never left [wp_panic_sconf_body], and the
      ninety specs that name it were never swept, so every one of them still
      threads a real [panic_env] through to here.

      AND IT IS THE SECOND PORT'S, NOT THE CONSOLE'S.  What sat here before
      06ea57f was the console triple ([dev_inv], the console's [is_txlock],
      its DLAB).  panic prints through [prputc] now, so the credential names
      [uart_inv Uart1], `&uarts[1].tx_lock` and `uarts[1].base` -- and
      [WpUart.dev_inv] could not be reused even in principle, being the
      CONSOLE BUNDLE by definition ([uart_inv Uart0] + PLIC + disk).

      AND NOT A [uart_sent_sub], nor any other claim about what came out.
      Nothing tracks the second port's wire (claude-notes/projects/
      xv6-bump-163d39b.md, "THE OWNER'S RULING: UART1's output is
      unconstrained"), so printk's contract no longer threads a trace claim
      at all and there is nothing for panic to supply or to report.  This
      file used to explain why the [bs] accumulator was pointless HERE (no
      postcondition to feed); it is now pointless everywhere in the cone, and
      the [UartTxInv.uart_sent_sub_nil_free] mint [ProofPanic] used to run
      is gone with it.

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
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import PrintkArgs.
Require Import SpecPrputc.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* panic's own 4-slot frame, over printk's 52 ([SpecPrintk.printk_stack]; not
   named here, because that file sits above this one).

   IT WENT 52 -> 56 AT 163d39b, and this is the one number in the file that
   the bump forced.  Nothing about panic's own frame moved; uartputc_sync's
   did (32 -> 64 bytes, the port index costing three more callee-saved
   registers), and the +4 arrives here through prputc -> printint -> printk.
   Every caller that derives [panic_stack <= K - <own frame>] from its own
   budget owes four more slots. *)
Notation panic_stack := (56%nat) (only parsing).
Section PanicEnv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.
  Context `{XI : CurCtx}.

  (* the persistent credentials the printk cone needs, as one hypothesis.
     All hart-free, so this crosses a migration untouched.  Two conjuncts
     now: pr.lock, and the second port ([SpecPrputc.prputc_env], which is
     itself the UART1 triple with its ghost names bound). *)
  Definition panic_env_at (γpr : gname) : iProp Σ :=
    (is_lock γpr pk_pr_lock "pr"%string <{ emp : iProp Σ }> ∗
     prputc_env)%I.

  Global Instance panic_env_at_persistent γpr :
    Persistent (panic_env_at γpr).
  Proof. apply _. Qed.

  (* ---- THE GHOST NAMES ARE EXISTENTIAL, AND NOTHING IS LOST BY IT --------
     A call site threads ONE nameless persistent token; no spec below panic
     gains a parameter.  Two independent reasons this is not a weakening.

     LOGICALLY it is an equivalence, not an approximation.  With the
     [uart_sent_sub] premise gone (see the header), every name occurs EXACTLY
     ONCE in [wp_panic_sconf_body] -- inside this one conjunct (γpr here, the
     UART1 pair inside [prputc_env]) -- and none occurs in the conclusion,
     which is the bare [WP Loop].  So [(∀ γ⃗, panic_env_at γ⃗ -∗ WP Loop)] and
     [((∃ γ⃗, panic_env_at γ⃗) -∗ WP Loop)] are interderivable by
     ∃-elimination.  Contrast [SpecConsoleintr.console_caps], which binds its
     two LOCK names but keeps [γu] a parameter for precisely the missing
     reason: its [γu] occurs again, in the contract proper.

     PHYSICALLY a caller cannot supply a bogus port, even though the logic
     cannot state uniqueness.  Every name is pinned by an exclusive physical
     resource: [lock_inv γ lk s R] contains [lock_word lk v], the lock word
     itself, so γpr is determined by the address [pk_pr_lock] that this very
     definition names and UART1's lock name by [UartsFields.uart_f_lock
     Uart1]; and [uart_inv Uart1]'s body holds [uart_frag Uart1 u], the ghost
     half of the PHYSICAL device state paired with [uarts_auth] inside
     [state_interp], so at most one bundle can have a live [uart_inv Uart1]
     at all.

     What each name is: γpr keys nothing but pr.lock's held-state ghost (its
     resource is [emp]); the UART1 lock name keys its own, whose resource is
     [tx_res γ1] -- keyed by the UART bundle, not by the lock name; and γ1 is
     the only one indexing real resources ([uart_tx_own], [uart_sent],
     [uart_dlab_off]) -- all of them at a port nothing above reads. *)
  (* ---- 06ea57f EMPTIED THIS TO [emp]; 163d39b REFILLS IT --------------
     The stopgap bump had panic print nothing, so it needed no UART
     credential and this was [emp] -- the cheap way to shed a resource
     without moving a call site.  163d39b restores the two printk calls, so
     the credential is REAL again.

     THAT COSTS NO CALL SITE ANYTHING EITHER, for exactly the reason
     emptying did not: the premise never left [wp_panic_sconf_body], and
     the ninety specs that name it were never swept, so every site still
     threads a genuine token down to here.  Refilling the definition is a
     one-file change with no fan-out; what a bump must never do is DELETE
     the definition or DROP the premise.

     AND IT HAD TO BE REFILLED, not merely re-attached: [ProofPanic] cannot
     mint either conjunct.  An [is_lock] and a [uart_inv] are handed down
     from the boot chain that created them and nothing below can conjure one.
     The credential is where they come from.  (What [ProofPanic] COULD mint
     -- the empty [uart_sent_sub] -- is exactly what the cone stopped
     wanting, so that mint is gone rather than kept.)

     A SITE THAT CARRIES [panic_env] IS EVIDENCE AGAIN.  Between the two
     bumps it was not -- the token was weightless and a site holding one
     proved nothing about its cone -- so read a pre-163d39b judgement about
     what "needs the console" with that in mind; and read the word "console"
     with care, because what a panic site now proves it can reach is the
     SECOND port. *)
  Definition panic_env : iProp Σ :=
    (∃ (γpr : gname), panic_env_at γpr)%I.

  Global Instance panic_env_persistent : Persistent panic_env.
  Proof. apply _. Qed.

  Lemma panic_env_intro γpr :
    panic_env_at γpr -∗ panic_env.
  Proof. iIntros "#H". iExists γpr. iExact "H". Qed.

  (* the shape a site actually has in hand: the two credentials loose. *)
  Lemma panic_env_of γpr :
    is_lock γpr pk_pr_lock "pr"%string <{ emp : iProp Σ }> -∗
    prputc_env -∗ panic_env.
  Proof.
    iIntros "#Hl #Hp". iExists γpr.
    rewrite /panic_env_at. by iFrame "Hl Hp".
  Qed.

End PanicEnv.

Definition wp_panic_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
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
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (m : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64)
      (dm : pk_arg_desc) (lks : gset string),
      wp_panic_sconf_body kt m K n eb b p dm lks.
End PANIC.
