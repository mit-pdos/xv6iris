(* UartTxInv.v -- the UART transmitter's software side: what serializes the
   writers, and the two trace lemmas a driver needs to read the accepted-byte
   history out of [dev_inv].

   Geometry (uart.c's two remaining file-static objects):

     a_tx_lock   -- &tx_lock   (a struct sleeplock; it serializes uartwrite
                                callers and nothing else)
     a_tx_chan   -- &tx_chan   (int: its ADDRESS is the sleep channel; the
                                cell itself is never read or written, so
                                nothing here owns it)

   WHAT THE LOCK PROTECTS ([tx_res]) IS NOW ONE THING: the EXCLUSIVE
   TRANSMITTER TOKEN [uart_tx_own γu l] (WpUart.v) -- the right to push a byte
   into THR, and the statement that the accepted trace is exactly [l].

   THE CERTIFICATE THAT USED TO LIVE HERE IS GONE, and that is the whole
   change.  The old uart.c drove the transmitter by BEING TOLD it was idle:
   uartintr checked LSR.THRE and cleared a [tx_busy] flag, and uartwrite's THR
   store was licensed by the lock invariant's implication "tx_busy == 0 ⟹
   everything accepted has been transmitted" -- the software's record of
   somebody else's THRE observation.  That is what forced the token into a
   lock shared with the interrupt handler, and it is what this file existed to
   state.

   The new uart.c POLLS THRE ITSELF, immediately before every byte:

       sleep_prepare(&tx_chan);
       if (ReadReg(LSR) & LSR_TX_IDLE) { WriteReg(THR, buf[i]); i += 1; }
       else                            { sleep(); }

   so the store is licensed by [uart_tx_poll_thre] applied to the writer's own
   LSR read -- uartputc_sync's route -- and needs no invariant at all.  With
   the certificate goes the flag ([tx_busy] no longer exists), and with the
   flag goes the reason uartintr had to reach the token: the handler now only
   observes LSR and calls wakeup(&tx_chan), which moves no device ghost.  The
   two functions no longer meet in a shared resource; they meet in the sleep
   channel.

   *** OWED: [is_txlock] IS NOT CONSTRUCTIBLE AT BOOT AS THE SOURCE STANDS. ***
   uart.c declares [static struct sleeplock tx_lock] and NEVER CALLS
   [initsleeplock] on it -- uartinit's [initlock(&tx_lock, "uart")] went away
   with the spinlock and nothing replaced it.  The C works (a zero-initialized
   sleeplock reads as unlocked), but the zeroed [name] fields are NULL
   POINTERS, and both [WpLock.lock_name] and [SleepLock.sl_name] say the field
   points at a real NUL-terminated string -- which no address in this model's
   memory map can satisfy.  So [is_txlock] below is a premise no caller can
   discharge, exactly like [SpecIlock]'s [i_ref] (design/fs-icache.md).  See
   claude-notes/kernel-defects.md D2 for the two ways out (fix the C, or make
   a lock's NAME optional so an anonymous lock can be minted from zeroed
   bytes).  Everything else in the cone is stated and proved against
   [is_txlock] as if it were available, so closing D2 closes the cone. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import DevModel DiskPtsto WpUart.
Require Import WpLock.
Require Import SleepLock.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section UartTxInv.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  (* [WpUart.dev_inv] carries the era-local permit channel at the ambient
     generation (PermInv.v), so the two lemmas below that OPEN it are
     [GenId]-indexed too.  Implicit, so no caller changes: every holder of
     [dev_inv] has an instance in scope. *)
  Context `{GEN : RiscvLang.GenId}.

  (* ---- geometry.  The sleeplock's own words belong to [SleepLock.sl_res] /
     the inner spinlock's [lock_inv]; nothing here names them. *)
  Definition a_tx_lock : mword 64 := mword_of_int KernelSyms.tx_lock.
  Definition a_tx_chan : mword 64 := mword_of_int KernelSyms.tx_chan.

  (* ---- the protected resource: the transmitter, at whatever trace it is at.
     The trace is EXISTENTIAL here because no reader of the lock predicts it --
     a writer learns the current value when it takes the lock, and every claim
     it then makes about its own bytes is a [uart_sent_sub] (below), which is
     persistent and survives the release. *)
  Definition tx_res (γu : uart_names) : iProp Σ :=
    (∃ l : list (bv 8), uart_tx_own γu l)%I.

  Lemma tx_res_intro (γu : uart_names) (l : list (bv 8)) :
    uart_tx_own γu l -∗ tx_res γu.
  Proof. iIntros "H". by iExists l. Qed.

  (* ---- the lock.  [uart_dlab_off] rides along because it is persistent and
     every THR write needs it: offset 0 is the divisor latch, not THR, while
     DLAB is set, so "the byte was transmitted" is false without it.  A client
     that holds the lock therefore holds everything the store leaf wants.

     A SLEEPLOCK, not a spinlock: uartwrite parks between bytes, and it must
     keep the transmitter across the park -- which a spinlock cannot do
     (sched() demands noff = 1).  [γl] is the inner spinlock's ghost, [γsl] the
     sleeplock's own. *)
  Definition is_txlock (γl γsl : gname) (γu : uart_names) : iProp Σ :=
    (is_sleeplock γl γsl a_tx_lock "uart"%string (tx_res γu) ∗
     uart_dlab_off γu)%I.

  Global Instance is_txlock_persistent γl γsl γu : Persistent (is_txlock γl γsl γu).
  Proof. apply _. Qed.

  Lemma is_txlock_lock γl γsl γu :
    is_txlock γl γsl γu -∗ is_sleeplock γl γsl a_tx_lock "uart"%string (tx_res γu).
  Proof. iIntros "[$ _]". Qed.

  Lemma is_txlock_dlab γl γsl γu : is_txlock γl γsl γu -∗ uart_dlab_off γu.
  Proof. iIntros "[_ $]". Qed.

  Lemma is_txlock_intro γl γsl γu :
    is_sleeplock γl γsl a_tx_lock "uart"%string (tx_res γu) -∗
    uart_dlab_off γu -∗ is_txlock γl γsl γu.
  Proof. iIntros "#Hl #Ho". by iFrame "Hl Ho". Qed.

  (* ===================================================================== *)
  (*  Reading the accepted trace out of [dev_inv].                          *)
  (* ===================================================================== *)

  (* WHAT A DRIVER THAT SLEEPS BETWEEN BYTES CAN CLAIM.  [uart_sent] records a
     CONTIGUOUS accepted prefix, which is the right shape for a driver that
     holds the transmitter across its whole output (uartputc_sync) and the
     wrong one for a driver that parks in the middle of it: while uartwrite
     sleeps, another hart's bytes may be accepted between two of its own.  So
     the claim is SUBLIST -- the bytes went out, in order, possibly
     interleaved.  Persistent, like [uart_sent] itself. *)
  Definition uart_sent_sub (γu : uart_names) (bs : list (bv 8)) : iProp Σ :=
    (∃ tr : list (bv 8), uart_sent γu tr ∗ ⌜ bs `sublist_of` tr ⌝)%I.

  Global Instance uart_sent_sub_persistent γu bs : Persistent (uart_sent_sub γu bs).
  Proof. apply _. Qed.

  Lemma uart_sent_sub_nil γu (tr : list (bv 8)) :
    uart_sent γu tr -∗ uart_sent_sub γu [].
  Proof.
    iIntros "H". iExists tr. iFrame "H". iPureIntro. apply stdpp.list_relations.sublist_nil_l.
  Qed.

  (* the step: one more byte accepted at the END of a trace that already
     contains the previous ones. *)
  Lemma uart_sent_sub_snoc γu (bs l : list (bv 8)) (c : bv 8) :
    bs `sublist_of` l ->
    uart_sent γu (l ++ [c]) -∗ uart_sent_sub γu (bs ++ [c]).
  Proof.
    iIntros (Hsub) "H". iExists ((l ++ [c])%list). iFrame "H". iPureIntro.
    apply stdpp.list_relations.sublist_app; [exact Hsub | reflexivity].
  Qed.

  (* the [un_acc] twin of [uart_out_prefix]: a persistent record is a prefix
     of the authoritative accepted trace. *)
  Lemma uart_sent_prefix (γu : uart_names) (u : uart_state) (l : list (bv 8)) :
    uart_sent_auth γu u -∗ uart_sent γu l -∗ ⌜ l `prefix_of` uart_acc u ⌝.
  Proof.
    iIntros "Ha Hl". rewrite /uart_sent_auth /uart_sent.
    by iDestruct (own_valid_2 with "Ha Hl") as %?%mono_list_both_valid_L.
  Qed.

  (* THE TOKEN KNOWS THE TRACE.  [uart_tx_own γu l] says the accepted trace is
     exactly [l]; opening [dev_inv] turns that into the permanent record
     [uart_sent γu l].  No physical step happens, so this is a plain fupd a
     caller runs under [fupd_wp]. *)
  Lemma uart_tx_own_snapshot (γu : uart_names) (γd : disk_names)
      (l : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l ={E}=∗
      uart_tx_own γu l ∗ uart_sent γu l.
  Proof.
    iIntros (HE) "#Hinv Hown".
    (* only the UART half is needed, and [↑uartN ⊆ ↑devN ⊆ E] *)
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hlb]".
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl]") as "_".
    { iNext. iExists u. rewrite /uart_ghosts. iFrame. }
    iModIntro. iFrame "Hown". rewrite -Hacc. iExact "Hlb".
  Qed.

  Lemma uart_tx_own_sent_prefix (γu : uart_names) (γd : disk_names)
      (l L : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent γu L ={E}=∗
      uart_tx_own γu l ∗ ⌜ L `prefix_of` l ⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #HL".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_prefix with "Hs HL") as %Hpre.
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl]") as "_".
    { iNext. iExists u. rewrite /uart_ghosts. iFrame. }
    iModIntro. iFrame "Hown". iPureIntro. by rewrite -Hacc.
  Qed.

  (* and the version that re-links an EARLIER record to the current trace:
     what a driver holding the token learns about the [uart_sent] it kept
     across a sleep.  Everything it saw accepted is still a prefix of what has
     been accepted now, so its sublist claim carries over to the trace it is
     about to extend. *)
  Lemma uart_tx_own_sent_sub (γu : uart_names) (γd : disk_names)
      (l : list (bv 8)) (bs : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent_sub γu bs ={E}=∗
      uart_tx_own γu l ∗ ⌜ bs `sublist_of` l ⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #Hsub".
    iDestruct "Hsub" as (L) "[#HL %Hbs]".
    iMod (uart_tx_own_sent_prefix γu γd l L E HE with "Hinv Hown HL")
      as "[Hown %Hpre]".
    iModIntro. iFrame "Hown". iPureIntro.
    destruct Hpre as [k ->].
    apply (transitivity Hbs). apply stdpp.list_relations.sublist_inserts_r. reflexivity.
  Qed.


End UartTxInv.
