(* SpecUartPutc.v -- the public interface of UartPutc, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     void uartputc_sync(int uid, int c) {
       struct uart *u = &uarts[uid];
       acquire(&u->tx_lock);
       while ((ReadReg(u, LSR) & LSR_TX_IDLE) == 0) ;
       WriteReg(u, THR, c);
       release(&u->tx_lock);
     }

   THE FUNCTION TAKES A PORT NOW (XV6_REV 163d39b), AND SO DOES THIS CONTRACT.
   xv6 drives two 16550s and this is the transmit path BOTH of them use:
   [consputc] calls it at uid 0 and [prputc] -- printk's and panic's one
   output primitive -- at uid 1.  So there is ONE contract, parametric in
   [i : uart_id], and everything the function touches is that port's:

     - the ARGUMENTS.  a0 is the index and a1 the byte (pre-bump the byte was
       a0).  The premise [m0 !!! a0 = mword_of_int (uart_index i)] is what
       ties the register to the port; the prologue turns it into
       `&uarts[uid].tx_lock` by `((uid*4 + uid) << 3) + 16 + uarts`, which is
       [UartsFields.uart_f_lock i] exactly when a0 is [uart_index i].

     - the LOCK is [UartTxInv.is_txlock_at i] -- the field
       `&uarts[uid].tx_lock`, under the name [uart_lock_name i] that
       `uartinit` initialised it with ("uart0"/"uart1"; the old single "uart"
       left `.rodata` with the old single lock).

     - the DEVICE premise is the BARE [uart_inv i] , not the [dev_inv]
       bundle: this function opens one port's invariant and nothing else, and
       at the second port the console bundle does not exist.  A console
       caller projects it with [WpUart.dev_inv_uart].

     - the MMIO ADDRESS IS LOADED, NOT COMPUTED.  `ld a3,0(s4)` reads
       `uarts[uid].base` out of `.data` and both the LSR poll and the THR
       store address off that register, so the proof has to know what the
       word HOLDS.  [base] is written by the loader and by nobody else, so
       the resource is a PERSISTENT word snapshot: [uart_base_word i] below.

   WHY [uart_base_word] AND NOT [UartsFields.uarts_pinned].  They are the
   same fact at different TIERS.  [uart_base_pinned] is the RAW PHYSICAL word
   the boot carve produces; an S-mode load leaf consumes the tier
   [uart_base_word] is spelled in, and the crossing between them is BOOT's,
   not a driver's -- see the note on [uart_base_word] below for what the boot
   chain still owes.

   THERE IS NO PANIC PATH.  printk.c's [panicking]/[panicked] globals are
   deleted, and with them the guarded [push_off]/[pop_off] pair and the
   [if (panicked) for(;;)] spin.  What replaces them is a plain critical
   section: uartputc_sync takes the port's [tx_lock] -- a SPINLOCK -- around
   its poll/store pair, which is what makes it agree with uartwrite (the other
   transmit path) instead of racing it.  So the contract carries no flag
   cells, no [eq_vec]/[neq_vec] refutation premises, and, being a spinlock
   caller, the ordinary [cpu_own] accounting of any function that acquires and
   releases.

   WHAT THE CALLER NO LONGER OWNS.  [UartTxInv.tx_res] is the LOCK's resource,
   so the exclusive transmitter token comes out of the acquire and goes back
   on the release: it is neither a premise nor a postcondition here.  All the
   caller brings is the persistent credential [UartTxInv.is_txlock_at i],
   which bundles the lock with the frozen-DLAB fact [uart_dlab_off] the THR
   store needs -- hence no separate [uart_dlab_off] premise either.

   WHAT THE CALLER GETS, AT EITHER PORT.  A SUBLIST claim, not a contiguous
   prefix: the lock is re-acquired per byte, so another hart may have bytes
   accepted between two of ours.  [UartTxInv.uart_sent_sub] -- persistent --
   is the honest statement, and this function's step on it is
   [UartTxInv.uart_sent_sub_snoc]: [bs] in, [bs ++ [sb]] out.  THE OWNER'S
   RULING that UART1's output is unconstrained does NOT mean the claim stops
   being TRUE at port 1: [uart_sent_sub] is keyed on the ghost bundle, not on
   the port, so producing it costs this contract nothing and a caller that
   owes nothing about the wire simply drops it. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list finite bitvector.definitions.
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
Require Import RiscvModelBytes DevModel PowerBoot.
Require Import KptPt KMap Ktier.
Require Import UartsFields.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import UartTxInv.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* uartputc_sync's own frame is EIGHT slots ([c.addi16sp sp,-64] at +0x00),
   and its only callees are acquire and release, which want 10 below it.

   IT WAS 14, OVER A FOUR-SLOT FRAME.  The port index costs three more
   callee-saved registers (s3 = uid, s4 = &uarts[uid], s5 = the byte, on top
   of s1 = &u->tx_lock and s2 = uid*4), so the frame doubled -- 32 to 64
   bytes -- and this bound grew with it.  There is no slack in it: it is the
   frame plus the deeper of the two callees. *)
Notation uartputc_stack := (18%nat) (only parsing).

(* ===================================================================== *)
(*  THE BYTE THIS FUNCTION STORES, as a function of its argument.         *)
(*                                                                       *)
(*  The code reaches the THR store through [c.mv s5,a1] / [andi a5,s5,    *)
(*  255], and the store itself truncates to eight bits -- so what lands   *)
(*  on the wire is exactly the argument's LOW BYTE, and the [andi]        *)
(*  cannot change it.  [cp_byte] is that byte, spelled the way [trunc8]   *)
(*  (WpSconfMem.v) spells a truncation so the console's own bridges       *)
(*  ([ProofConsoleintr.ct_arg_trunc8]) apply to it by conversion.  It is  *)
(*  a function of a VALUE, so the bump's move of the byte from a0 to a1   *)
(*  does not touch it -- only which register it is applied to.            *)
(*                                                                       *)
(*  The contract below still names the raw [sb] expression, because that  *)
(*  is what the store leaf produces; [cp_byte_sb] is the one rewrite that *)
(*  turns it into the byte, and consputc's post is stated on the byte.    *)
(* ===================================================================== *)
Definition cp_byte (a0 : mword 64) : mword 8 :=
  autocast (T := mword) (subrange_vec_dec a0 (Z.sub (Z.mul 1 8) 1) 0).

Lemma cp_byte_sb (a0 : mword 64) :
  (autocast (T := mword)
     (subrange_vec_dec (and_vec (add_vec zero_reg a0)
        (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) : mword 8)
  = cp_byte a0.
Proof.
  apply bv_eq. unfold cp_byte.
  rewrite !autocast_id.
  rewrite (subrange_dec_unsigned_lo0
             (and_vec (add_vec zero_reg a0)
                (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 256
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (subrange_dec_unsigned_lo0 a0 7 256
             ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite and_vec64_unsigned add_vec_unsigned.
  assert (H255 : bv_unsigned (sign_extend' 64 (mword_of_int 255 : mword 12) : mword 64)
                 = 255%Z) by (vm_compute; reflexivity).
  assert (Hz : bv_unsigned (zero_reg : mword 64) = 0%Z)
    by (vm_compute; reflexivity).
  rewrite H255 Hz Z.add_0_l.
  rewrite bv_wrap_small; [| apply bv_unsigned_in_range].
  assert (Ho : (255 = Z.ones 8)%Z) by (vm_compute; reflexivity).
  rewrite Ho (Z.land_ones (bv_unsigned a0) 8 ltac:(lia)).
  assert (E8 : (2 ^ 8 = 256)%Z) by (vm_compute; reflexivity).
  rewrite E8. apply Zmod_mod.
Qed.

(* ===================================================================== *)
(*  THE LOADED MMIO BASE, AT THE TIER A DRIVER CAN USE.                   *)
(* ===================================================================== *)

Section UartBaseWord.
  Context `{!riscvGS Σ}.
  Context `{XI : CurCtx}.

  (* what `ld a3,0(s4)` reads, as an S-mode load leaf wants it: the VA-tier
     persistent doubleword at `&uarts[i].base`.  Pinned at KT0 because the
     `.data` page is identity-mapped, which makes the tier free at any caller
     ([Ktier.ktier_le_bot]). *)
  Definition uart_base_word (i : uart_id) : iProp Σ :=
    ((pa_of_z (uart_f_base i)) ↦₈[KT0]□ (Z_to_bv 64 (uart_base i)))%I.

  Global Instance uart_base_word_persistent i : Persistent (uart_base_word i).
  Proof. rewrite /uart_base_word /word_pointsto. apply _. Qed.

  (* WHERE IT COMES FROM, AND THE ONE GAP THIS LANE CANNOT CLOSE.
     [UartsFields.uart_base_pinned i] is the same fact at the RAW PHYSICAL
     tier ([↦ₚ₈□]) -- what the boot carve naturally produces
     ([BootCarve.boot_ran_phys_word]).  A DRIVER cannot consume that: an
     S-mode load leaf ([WpSconfMem.wp_ld_s_sconf]) wants the tier spelled
     here, and the physical-to-VA direction is not a law
     ([DiskInv.phys_win_to_mem] lands at the RAW VA byte and DROPS the
     ledger, which is the half a context-tier re-entry needs).  The boot
     chain already has the right idiom for a word nobody ever writes -- the
     `_entry` GOT slot, where [BootShared] mints [TsoCtx.pristine_win]
     BESIDE [boot_ran_phys_word] -- so `uarts[i].base` wants the same pair,
     or a persistent [↦₈□] sibling of [BootCarve.boot_ran_ran_word] minted
     directly.  Either way it is one lemma in the boot lane's files, and
     until it exists this premise is what a UART driver must be handed. *)
  (* ------------------------------------------------------------------ *)
  (*  BOTH ELEMENTS' BOTH IMMUTABLE FIELDS, AS ONE ROW.                   *)
  (* ------------------------------------------------------------------ *)
  (* The VA-tier twin of [UartsFields.uarts_pinned], and it travels as ONE
     row for two reasons.  `uarts[]` is one static array: the boot chain
     crosses all four words in one place and no client ever learns one
     without the others.  And these are the only CONTEXT-RELATIVE facts the
     interrupt path needs about the array -- everything else it carries
     about a port (that port's invariant, its PLIC slot's one-shot, its
     frozen DLAB) is a ghost and rides any context for free -- so keeping
     the four together puts the whole context-relative half in ONE bundle,
     the one that already crosses ([SpecConsoleintr.console_caps], which
     [UsertrapRes.park_globals] carries to the resumer's context).  Splitting
     them per port would put a ξ-relative row into the SECOND port's
     otherwise ξ-free credential ([SpecDevintr.uart1_caps]), which is
     rebuilt at a foreign context by a proof that holds no domination and so
     can transport nothing.

     Indexed off [enum uart_id] exactly as [uarts_pinned] is, so a third
     port stays a constructor and nothing else. *)
  Definition uarts_words : iProp Σ :=
    ([∗ list] i ∈ enum uart_id, uart_base_word i ∗ uart_rx_word i)%I.

  Global Instance uarts_words_persistent : Persistent uarts_words.
  Proof. rewrite /uarts_words. apply _. Qed.

  (* focus one port out of the four, the only way a driver reaches one *)
  Lemma uarts_words_at (i : uart_id) :
    uarts_words -∗ uart_base_word i ∗ uart_rx_word i.
  Proof.
    rewrite /uarts_words /enum /uart_id_finite /=.
    iIntros "#(H0 & H1 & _)". by destruct i.
  Qed.

  Lemma uarts_words_base (i : uart_id) : uarts_words -∗ uart_base_word i.
  Proof. iIntros "#H". by iDestruct (uarts_words_at i with "H") as "[$ _]". Qed.

  Lemma uarts_words_rx (i : uart_id) : uarts_words -∗ uart_rx_word i.
  Proof. iIntros "#H". by iDestruct (uarts_words_at i with "H") as "[_ $]". Qed.

  (* ...and the assembly, which only the boot chain runs *)
  Lemma uarts_words_intro :
    uart_base_word Uart0 -∗ uart_rx_word Uart0 -∗
    uart_base_word Uart1 -∗ uart_rx_word Uart1 -∗ uarts_words.
  Proof.
    iIntros "#Hb0 #Hr0 #Hb1 #Hr1".
    rewrite /uarts_words /enum /uart_id_finite /=.
    iFrame "Hb0 Hr0 Hb1 Hr1".
  Qed.
End UartBaseWord.

Definition wp_uartputc_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (i : uart_id) (γl : gname) (γd : uart_names) (m0 : regfile) (K : nat)
    (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let pcE := mword_of_int KernelSyms.uartputc_sync in
  let ra0 := m0 !!! Regidx ra_idx in
  let a10 := m0 !!! Regidx a1_idx in
  let ret_tgt := ret_pc ra0 in
  let sb : mword 8 := autocast (T := mword)
     (subrange_vec_dec (and_vec (add_vec zero_reg a10)
        (sign_extend' 64 (mword_of_int 255 : mword 12))) 7 0) in
  (uartputc_stack <= K)%nat ->
  (* THE PORT, AS THE ARGUMENT REGISTER HOLDS IT *)
  m0 !!! Regidx a0_idx = (mword_of_int (uart_index i) : mword 64) ->
  (* acquire's transient [noff] increment must not overflow the [int] *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* acquire's order premise: every lock this hart already holds ranks below
     port [i]'s -- uartputc_sync acquires and releases it in the same call, so
     this contract is BALANCED: [lks] is unchanged end to end. *)
  locks_below lks (uart_lock_name i) ->
  sie_cap_gpr kt m0 K b p -∗
  (* the interrupt level is left exactly as found: an acquire/release pair *)
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  uart_inv i γd -∗
  (* the .data word the MMIO address is LOADED from *)
  uart_base_word i -∗
  is_txlock_at i γl γd -∗
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
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (i : uart_id) (γl : gname) (γd : uart_names) (m0 : regfile) (K : nat)
      (bs : list (bv 8)) (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_uartputc_sconf_body kt i γl γd m0 K bs n eb b p lks.
End UARTPUTC.
