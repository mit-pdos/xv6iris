(* SpecPrputc.v -- the public interface of Prputc, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     static void prputc(int c) { uartputc_sync(1, c); }

   NEW AT XV6_REV 163d39b, and it is the whole reason printk's cone changed.
   xv6 drives two 16550s: the console on UART0 and the diagnostic printer on
   UART1, and [prputc] is the one-line adapter that sends printk/printint/
   printptr's bytes to the SECOND port.  It replaces [consputc] as printk's
   character sink -- consputc is still the console's own path (console.c), and
   [SpecConsputc.v] is still its contract; nothing here supersedes that file.

   Twelve bytes of code: the standard 16-byte / 2-slot frame, [c.mv a1,a0]
   (the byte moves to uartputc_sync's second argument), [c.li a0,1] (the PORT
   INDEX -- [UartsFields.uart_index Uart1]) and one [jal].  It is exactly
   consputc's non-BACKSPACE arm with the port pinned to 1, so [ProofConsputc.v]
   is the shape to read.

   *** THE SECOND PORT'S WIRE IS DELIBERATELY UNCONSTRAINED. ***
   THE OWNER'S RULING (claude-notes/projects/xv6-bump-163d39b.md, "THE OWNER'S
   RULING: UART1's output is unconstrained"): nothing in the system tracks what
   printk or panic put on that wire, so this contract owes NO [uart_sent], no
   ledger, no trace obligation -- only that its store goes through.  Three
   consequences, and they are what make this file short:

     - NO [bs] PARAMETER and NO TRACE POSTCONDITION.  consputc's contract
       threads [UartTxInv.uart_sent_sub γd bs] in and [bs ++ cs] out, and
       [SpecConsputc.v] even pins WHICH bytes, because the console's echo has
       to be matched to the byte it echoes.  There is no such consumer at the
       second port.  The [uart_sent_sub] uartputc_sync still asks for is minted
       inside the proof out of nothing at all
       ([UartTxInv.uart_sent_sub_nil_free]: [◯ML []] is the unit of the
       mono-list RA) and the one it returns is dropped.

     - NO [dev_inv].  [WpUart.dev_inv] is the CONSOLE BUNDLE -- it names
       [uart_inv Uart0], the PLIC and the disk -- so it cannot even be STATED
       about this port, and widening it would put a resource nobody uses into
       the ~140 specs that name it.  What this cone needs is the second port's
       own ordinary invariant, [uart_inv Uart1].

     - THE GHOST NAMES ARE EXISTENTIAL ([prputc_env] below).  They occur
       nowhere else in the contract -- there being no postcondition about the
       port -- so binding them costs nothing and keeps every caller above
       (printint, printk, panic, and the ninety specs that thread
       [SpecPanic.panic_env]) free of a UART1 parameter.  Same argument, and
       the same physical pinning, as [SpecPanic.v]'s note on its own
       existentials. *)
From Stdlib Require Import ZArith Bool Lia List String.
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
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import DevModel.
Require Import UartsFields.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import SpecUartPutc.   (* [uart_base_word]: the .data word the MMIO
     address is LOADED from, and [uartputc_stack] *)
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* prputc's own frame is 2 slots ([c.addi sp,sp,-16] at +0x00), over
   uartputc_sync's [uartputc_stack] = 18 -- which itself GREW at this bump
   (its frame went 32 -> 64 bytes when the port index took three more
   callee-saved registers), so this number is 4 higher than the [consputc]
   it replaces and that +4 propagates all the way up to [panic_stack]. *)
Notation prputc_stack := (20%nat) (only parsing).

Section PrputcEnv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.

  (* THE SECOND PORT, AS ONE PERSISTENT CREDENTIAL.  Three conjuncts, all of
     them the ordinary port-indexed forms, and all of them hart-free:

       [uart_inv Uart1 γ1]        -- the port's own device invariant.  NOT
                                     [dev_inv], which is the console bundle
                                     (see the header).
       [is_txlock_at Uart1 γl1 γ1] -- `&uarts[1].tx_lock` under the name
                                     `uartinit` gave it ([UartTxInv]), and it
                                     carries the frozen [uart_dlab_off γ1]
                                     the THR store needs.
       [uart_base_word Uart1]     -- what `uarts[1].base` HOLDS.  The MMIO
                                     address is a LOADED value now
                                     ([UartsFields.v]), so a store proof needs
                                     the .data word's persistent snapshot.

     NOTHING ABOUT THE BYTES.  That is the owner's ruling, and this is the
     credential where its absence shows: a holder of [prputc_env] can print,
     and can say nothing whatever about what came out.

     The names are EXISTENTIAL because they occur nowhere else in any contract
     above this one; see the header. *)
  Definition prputc_env : iProp Σ :=
    (∃ (γl1 : gname) (γ1 : uart_names),
       uart_inv Uart1 γ1 ∗ is_txlock_at Uart1 γl1 γ1 ∗ uart_base_word Uart1)%I.

  Global Instance prputc_env_persistent : Persistent prputc_env.
  Proof. rewrite /prputc_env. apply _. Qed.

  (* the shape the boot chain actually has in hand: the three loose. *)
  Lemma prputc_env_of (γl1 : gname) (γ1 : uart_names) :
    uart_inv Uart1 γ1 -∗ is_txlock_at Uart1 γl1 γ1 -∗ uart_base_word Uart1 -∗
    prputc_env.
  Proof.
    iIntros "#Hi #Ht #Hb". iExists γl1, γ1. by iFrame "Hi Ht Hb".
  Qed.

End PrputcEnv.

Definition wp_prputc_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (m0 : regfile) (K : nat)
    (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE := mword_of_int KernelSyms.prputc in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (prputc_stack <= K)%nat ->
  (* uartputc_sync's acquire has a transient [noff] increment *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* the order premise, at the LOWEST rank this cone touches -- the SECOND
     port's lock.  [LockRank.v] was re-keyed at this bump: the single "uart"
     is gone and the two ports' locks are "uart0"/"uart1", at the SAME rank
     17, so a hart holding one may not take the other. *)
  locks_below lks "uart1" ->
  sie_cap_gpr kt m0 K b p -∗
  (* the interrupt level is left exactly as found: uartputc_sync's
     acquire/release pair *)
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  prputc_env -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf,
    sie_cap_gpr kt mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    (* AND NOTHING ELSE.  No byte claim: see the header. *)
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PRPUTC.
  Parameter wp_prputc_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (m0 : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_prputc_sconf_body kt m0 K n eb b p lks.
End PRPUTC.
