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
Require Import TsoCtx.   (* the lock payload's context axis; [<{ }>] *)
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

(* A SUBLIST SURVIVES A MAP.  stdpp has [sublist_app]/[sublist_inserts_r] but
   no fmap congruence for [sublist]; this is it, by induction on the
   relation.  Used to read the BYTES of a tagged claim off the tagged
   trace. *)
Lemma sublist_fmap_gen {A B : Type} (f : A -> B) (l1 l2 : list A) :
  l1 `sublist_of` l2 -> (f <$> l1) `sublist_of` (f <$> l2).
Proof.
  induction 1 as [| x l1' l2' _ IH | x l1' l2' _ IH]; cbn.
  - constructor.
  - by constructor.
  - by constructor.
Qed.

(* tagging a byte list and then forgetting the tags is the identity *)
Lemma fmap_snd_pair {A B : Type} (a : A) (l : list B) :
  (snd <$> ((pair a) <$> l)) = l.
Proof. induction l as [| b l IH]; cbn; [done | by rewrite IH]. Qed.

Section UartTxInv.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{XI : CurCtx}.
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
    (is_lock γl a_tx_lock "uart"%string <{ tx_res γu }> ∗
     uart_dlab_off γu)%I.

  Global Instance is_txlock_persistent γl γu : Persistent (is_txlock γl γu).
  Proof. apply _. Qed.

  Lemma is_txlock_lock γl γu :
    is_txlock γl γu -∗ is_lock γl a_tx_lock "uart"%string <{ tx_res γu }>.
  Proof. iIntros "[$ _]". Qed.

  Lemma is_txlock_dlab γl γu : is_txlock γl γu -∗ uart_dlab_off γu.
  Proof. iIntros "[_ $]". Qed.

  Lemma is_txlock_intro γl γu :
    is_lock γl a_tx_lock "uart"%string <{ tx_res γu }> -∗
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

  (* ===================================================================== *)
  (*  THE TAG-AWARE CLAIM.                                                  *)
  (*                                                                        *)
  (*  [uart_sent_sub_at γu src bs] is [uart_sent_sub] refined by the WRITER: *)
  (*  the bytes [bs], EACH TAGGED [src], are a sublist of the accepted       *)
  (*  TAGGED trace ([WpUart.uart_sent_tagged]).  Persistent, for the same    *)
  (*  reason [uart_sent_sub] is: it is a mono-list lower bound plus a pure   *)
  (*  fact.                                                                 *)
  (*                                                                        *)
  (*  SUBLIST AND NOT CONTIGUOUS, exactly as in the untagged form: tx_lock   *)
  (*  is re-acquired per byte, so another hart's bytes -- under any tag,     *)
  (*  INCLUDING THE SAME ONE -- may be accepted in between.  What the tag    *)
  (*  buys is the ability to say WHICH writer a byte came from at all, and   *)
  (*  hence to project the accepted trace onto one source; it does not by    *)
  (*  itself make a source's own run exact (UartSentLoc.v's header).         *)
  (*                                                                        *)
  (*  THE UNTAGGED CLAIM IS NOT BUNDLED IN.  The two ghosts are kept in      *)
  (*  lockstep by [WpUart.uart_tagsE], a conjunct of [uart_ghosts], so       *)
  (*  [uart_sent_sub_of_at] recovers [uart_sent_sub] through [dev_inv] for   *)
  (*  any consumer that wants it -- and no producer pays for a claim its     *)
  (*  caller does not read.                                                  *)
  Definition uart_sent_sub_at (γu : uart_names) (src : txsrc)
      (bs : list (bv 8)) : iProp Σ :=
    (∃ tg : list (txsrc * bv 8),
       uart_sent_tagged γu tg ∗ ⌜((pair src) <$> bs) `sublist_of` tg⌝)%I.

  Global Instance uart_sent_sub_at_persistent γu src bs :
    Persistent (uart_sent_sub_at γu src bs).
  Proof. apply _. Qed.
  Global Instance uart_sent_sub_at_timeless γu src bs :
    Timeless (uart_sent_sub_at γu src bs).
  Proof. apply _. Qed.

  (* THE EMPTY CLAIM IS FREE, AND FROM NOTHING AT ALL -- [◯ML []] is the
     unit of [mono_listUR], so [own_unit] hands it over under a plain
     [|==>].  [UartTxInv.uart_sent_sub_nil_free]'s tagged twin. *)
  Lemma uart_sent_sub_at_nil_free (γu : uart_names) (src : txsrc) :
    ⊢ |==> uart_sent_sub_at γu src [].
  Proof.
    iMod (own_unit (mono_listUR (leibnizO (txsrc * bv 8))) γu.(un_tag)) as "H".
    iModIntro. rewrite /uart_sent_sub_at. iExists []. iSplitL "H"; last first.
    { iPureIntro. apply stdpp.list_relations.sublist_nil_l. }
    rewrite /uart_sent_tagged -(mono_list_lb_nil_is_unit (leibnizO (txsrc * bv 8))).
    done.
  Qed.

  (* ...and the empty claim at one tag IS the empty claim at any other: its
     body does not mention [src] once [bs] is empty.  What lets a bundle
     carry ONE baseline for a caller that picks its tag later
     ([SpecConsoleintr.console_caps]). *)
  Lemma uart_sent_sub_at_nil_any (γu : uart_names) (src src' : txsrc) :
    uart_sent_sub_at γu src [] -∗ uart_sent_sub_at γu src' [].
  Proof.
    iIntros "H". iDestruct "H" as (tg) "[Htg _]". iExists tg. iFrame "Htg".
    iPureIntro. apply stdpp.list_relations.sublist_nil_l.
  Qed.

  (* the step: one more byte, tagged [src], at the END of a tagged trace
     that already contains the previous ones.  [uart_sent_sub_snoc]'s tagged
     twin, and the shape the THR store leaf's postcondition is built for. *)
  Lemma uart_sent_sub_at_snoc γu (src : txsrc) (bs : list (bv 8))
      (tg0 : list (txsrc * bv 8)) (c : bv 8) :
    ((pair src) <$> bs) `sublist_of` tg0 ->
    uart_sent_tagged γu (tg0 ++ [(src, c)]) -∗
    uart_sent_sub_at γu src (bs ++ [c]).
  Proof.
    iIntros (Hsub) "H". iExists ((tg0 ++ [(src, c)])%list). iFrame "H".
    iPureIntro. rewrite fmap_app /=.
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
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htg)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hlb]".
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl Htg Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts. iFrame. }
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
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htg)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_prefix with "Hs HL") as %Hpre.
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl Htg Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts. iFrame. }
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


  (* THE TAGGED TRACE, READ OUT UNDER THE TOKEN.  A writer holding the
     transmitter at trace [l] opens the device invariant and takes the
     CURRENT tagged trace [tg] out of it: its bytes are [l] (the lockstep
     [WpUart.uart_tagsE], agreed against the token), and the claim the
     writer carried in still sits inside it.  These are exactly the two
     things [uart_sent_sub_at_snoc] and the THR store leaf want, and it is
     [uart_tx_own_sent_sub]'s tagged twin. *)
  Lemma uart_tx_own_sent_sub_at (γu : uart_names) (γd : disk_names)
      (l : list (bv 8)) (src : txsrc) (bs : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent_sub_at γu src bs ={E}=∗
      uart_tx_own γu l ∗
      ∃ tg : list (txsrc * bv 8),
        uart_sent_tagged γu tg ∗ ⌜(snd <$> tg) = l⌝ ∗
        ⌜((pair src) <$> bs) `sublist_of` tg⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #Hsub".
    iDestruct "Hsub" as (tg0) "[#Htg0 %Hb]".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htg)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct "Htg" as (tgA) "[HtgA %HtgA]".
    iDestruct (uart_tags_get with "HtgA") as "[HtgA #HlbA]".
    iDestruct (uart_tags_prefix with "HtgA Htg0") as %Hpre0.
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl HtgA Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts.
      iFrame "Hu Hs Hout Htx Hdl Hcol". iExists tgA. by iFrame "HtgA". }
    iModIntro. iFrame "Hown". iExists tgA. iFrame "HlbA". iPureIntro.
    split; [by rewrite HtgA Hacc |].
    destruct Hpre0 as [k ->].
    apply (transitivity Hb).
    apply stdpp.list_relations.sublist_inserts_r. reflexivity.
  Qed.

  (* THE PROJECTION back to the untagged vocabulary, through the lockstep.
     Not free (it opens [dev_inv]) and not needed by any producer: it is
     here for a consumer that holds only the tagged claim and wants the
     landed [uart_sent_sub]. *)
  Lemma uart_sent_sub_of_at (γu : uart_names) (γd : disk_names)
      (src : txsrc) (bs : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_sent_sub_at γu src bs ={E}=∗ uart_sent_sub γu bs.
  Proof.
    iIntros (HE) "#Hinv #Hsub".
    iDestruct "Hsub" as (tg0) "[#Htg0 %Hb]".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htg)".
    iDestruct "Htg" as (tgA) "[HtgA %HtgA]".
    iDestruct (uart_tags_prefix with "HtgA Htg0") as %Hpre0.
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hlb]".
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl HtgA Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts.
      iFrame "Hu Hs Hout Htx Hdl Hcol". iExists tgA. by iFrame "HtgA". }
    iModIntro. iExists (uart_acc u). iFrame "Hlb". iPureIntro.
    rewrite -HtgA.
    (* the bytes of a tagged sublist are a sublist of the tagged trace's
       bytes, and [tg0] sits inside the authoritative [tgA] *)
    assert (Hsub : ((pair src) <$> bs) `sublist_of` tgA).
    { destruct Hpre0 as [k ->]. apply (transitivity Hb).
      apply stdpp.list_relations.sublist_inserts_r. reflexivity. }
    apply (sublist_fmap_gen snd) in Hsub.
    by rewrite fmap_snd_pair in Hsub.
  Qed.

End UartTxInv.
