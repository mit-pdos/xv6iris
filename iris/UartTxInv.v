(* UartTxInv.v -- the UART transmitter's software side: what serializes the
   writers, and the two trace lemmas a driver needs to read the accepted-byte
   history out of [dev_inv].

   Geometry (uart.c's two remaining file-static objects):

     a_tx_lock   -- &tx_lock   (a struct SPINLOCK; it serializes every THR
                                write -- uartwrite's and uartputc_sync's)
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

   *** THE D2 OBSTRUCTION IS GONE. ***  This paragraph used to say [is_txlock]
   was not constructible at boot: `ae96fd0` made tx_lock a sleeplock and
   deleted uartinit's [initlock(&tx_lock,"uart")] without replacing it, so the
   zeroed [name] fields were NULL POINTERS and no address in this model's
   memory map could satisfy [lock_name] (kernel-defects.md D2, which we
   reported).  Upstream fixed it -- `b7c25cf` added [initsleeplock], and
   `d80e61c5` settled on [initlock(&tx_lock, "uart")] with tx_lock back to a
   spinlock -- so the name is written and [lock_name] is satisfiable.

   The boot chain now carries the storage end to end: [main_locks_raw] hands
   [lk_raw a_tx_lock] down through consoleinit into uartinit, which returns
   [lk_fresh a_tx_lock "uart"], and [newlock] turns that into the [is_lock]
   half of [is_txlock] below.  What is still owed is only the boot ASSEMBLY
   that runs that step -- a [WpLock.newlock] -- and the resource it
   must supply, [tx_res], which is the printk cone's business now that
   [SpecPrintk.pr_res] no longer holds the transmitter. *)
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
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* [◯ML []] is the UNIT of the mono-list resource algebra
   ([mono_listUR A := authUR (max_prefix_listUR A)], and [to_max_prefix_list []]
   is the empty map).  Stated outside the section because it is pure algebra --
   no ghost state, no [Σ]. *)
Lemma mono_list_lb_nil_is_unit (A : ofe) :
  (◯ML ([] : list A)) ≡ (ε : mono_listUR A).
Proof. done. Qed.

Section UartTxInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
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

     A SPINLOCK AGAIN, and the reason the sleeplock existed is gone.  It was a
     sleeplock because the old uartwrite parked BETWEEN bytes while holding the
     transmitter, which a spinlock cannot do (sched() demands noff = 1).  The
     `verified` branch's uartwrite takes and releases the lock AROUND EACH
     LSR-check/THR-write pair and parks outside it:

         sleep_prepare(&tx_chan);
         acquire(&tx_lock);
         if (LSR & TX_IDLE) { WriteReg(THR, buf[i]); release(...); i++; }
         else               { release(...); sleep(); }

     so nothing is held across the park and one ghost suffices.  uartputc_sync
     takes the same lock, which is what makes the two transmit paths agree --
     and is why [SpecPrintk.pr_res] no longer needs the transmitter at all.

     THE COST IS BORNE BY THE CALLERS' TRACE CLAIM, not by this predicate:
     a driver that re-acquires per byte cannot claim a CONTIGUOUS
     [uart_sent], because another hart may interleave between two of its
     bytes.  That is what [uart_sent_sub] below is for. *)
  Definition is_txlock (γl : gname) (γu : uart_names) : iProp Σ :=
    (is_lock γl a_tx_lock "uart"%string (tx_res γu) ∗
     uart_dlab_off γu)%I.

  Global Instance is_txlock_persistent γl γu : Persistent (is_txlock γl γu).
  Proof. apply _. Qed.

  Lemma is_txlock_lock γl γu :
    is_txlock γl γu -∗ is_lock γl a_tx_lock "uart"%string (tx_res γu).
  Proof. iIntros "[$ _]". Qed.

  Lemma is_txlock_dlab γl γu : is_txlock γl γu -∗ uart_dlab_off γu.
  Proof. iIntros "[_ $]". Qed.

  Lemma is_txlock_intro γl γu :
    is_lock γl a_tx_lock "uart"%string (tx_res γu) -∗
    uart_dlab_off γu -∗ is_txlock γl γu.
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

  (* THE EMPTY CLAIM IS FREE, AND FROM NOTHING AT ALL -- no [dev_inv], no
     invariant to open, no mask side condition, not even an allocated
     authority.  [uart_sent γ l] is [own γ.(un_acc) (◯ML l)] and [◯ML []] is
     the UNIT of [mono_listUR], so [own_unit] hands it over under a plain
     [|==>].  ([uart_sent_sub_nil] above is the route for a holder who already
     has a trace in hand; this is the route for one who has nothing.)

     This is what lets a spec whose only use of the trace claim is to feed a
     POSTCONDITION drop it from its precondition outright -- see SpecPanic.v,
     which has no postcondition and therefore no use for [bs]. *)
  Lemma uart_sent_sub_nil_free (γu : uart_names) :
    ⊢ |==> uart_sent_sub γu [].
  Proof.
    iMod (own_unit (mono_listUR (leibnizO (bv 8))) γu.(un_acc)) as "H".
    iModIntro. rewrite /uart_sent_sub. iExists []. iSplitL "H"; last first.
    { iPureIntro. apply stdpp.list_relations.sublist_nil_l. }
    rewrite /uart_sent -(mono_list_lb_nil_is_unit (leibnizO (bv 8))). done.
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
