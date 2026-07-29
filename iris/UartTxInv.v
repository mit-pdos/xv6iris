(* UartTxInv.v -- the UART transmitter's software side: the [tx_lock] spinlock
   and what it protects, plus the two trace lemmas a driver needs to read the
   accepted-byte history out of [dev_inv].

   Geometry (uart.c's three file-static objects):

     a_tx_lock   -- &tx_lock   (the spinlock, "uart")
     a_tx_busy   -- &tx_busy   (int: "the UART is still sending")
     a_tx_chan   -- &tx_chan   (int: its ADDRESS is the sleep channel; the
                                cell itself is never read or written, so
                                nothing here owns it)

   WHAT THE LOCK PROTECTS ([tx_res]).  Two things, and the second is the whole
   point of the file:

     - the [tx_busy] cell, at an arbitrary value;
     - the EXCLUSIVE TRANSMITTER TOKEN [uart_tx_own] (WpUart.v) -- the right
       to push a byte into THR, and the statement that the accepted trace is
       exactly [l];
     - and, hanging off [tx_busy] being zero, the certificate
       [uart_out_lb γu l]: everything accepted has already been transmitted.

   That last implication is what makes uartwrite's THR store provable at all.
   The device leaf ([wp_uart_thr_write_s_sconf]) will not let a byte be pushed
   unless the FIFO provably has room, and the only way to know that is to have
   SEEN it empty -- either by polling THRE (uartputc_sync's route) or by being
   told, and the interrupt-driven driver is told: uartintr checks LSR.THRE and
   only then clears [tx_busy].  So "tx_busy == 0" is not merely a hint that the
   UART is idle, it is the software's record of a THRE observation, and the
   invariant is where that record is cashed.

   Consequently the token CANNOT live with a caller: uartintr needs it (to
   read the trace out at the THRE check) and uartwrite needs it (to push), and
   they meet only under this lock.

   The two [dev_inv] lemmas at the end ([uart_tx_own_snapshot],
   [uart_tx_own_sent_prefix]) are what turn the token's "the trace is exactly
   [l]" into statements about the PERSISTENT record [uart_sent]: a snapshot at
   the current value, and the fact that any earlier record is a prefix of it.
   A driver that pushes bytes across a sleep needs the second one -- it is
   what re-links the trace it saw before parking to the one it finds after. *)
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
Local Open Scope Z_scope.

Section UartTxInv.
  Context `{!riscvGS Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.

  (* ---- geometry.  The lock's own two words ([locked] at +0, [cpu] at +16)
     belong to [lock_inv] (WpLock.v); nothing here names them. *)
  Definition a_tx_lock : mword 64 := mword_of_int KernelSyms.tx_lock.
  Definition a_tx_busy : mword 64 := mword_of_int KernelSyms.tx_busy.
  Definition a_tx_chan : mword 64 := mword_of_int KernelSyms.tx_chan.

  (* ---- the protected resource. *)
  Definition tx_res (γu : uart_names) : iProp Σ :=
    (∃ (b : mword 32) (l : list (bv 8)),
       a_tx_busy ↦₄ b ∗
       uart_tx_own γu l ∗
       (⌜ b = (mword_of_int 0 : mword 32) ⌝ -∗ uart_out_lb γu l))%I.

  (* the two shapes a client re-closes with: "still sending" (any trace) and
     "idle" (the trace it has just seen fully transmitted). *)
  Lemma tx_res_busy (γu : uart_names) (b : mword 32) (l : list (bv 8)) :
    b <> (mword_of_int 0 : mword 32) ->
    a_tx_busy ↦₄ b -∗ uart_tx_own γu l -∗ tx_res γu.
  Proof.
    iIntros (Hb) "Hcell Hown". iExists b, l. iFrame "Hcell Hown".
    iIntros (Heq). exfalso. exact (Hb Heq).
  Qed.

  Lemma tx_res_idle (γu : uart_names) (b : mword 32) (l : list (bv 8)) :
    a_tx_busy ↦₄ b -∗ uart_tx_own γu l -∗ uart_out_lb γu l -∗ tx_res γu.
  Proof.
    iIntros "Hcell Hown #Hlb". iExists b, l. iFrame "Hcell Hown".
    iIntros (_). iExact "Hlb".
  Qed.

  (* ---- the lock.  [uart_dlab_off] rides along because it is persistent and
     every THR write needs it: offset 0 is the divisor latch, not THR, while
     DLAB is set, so "the byte was transmitted" is false without it.  A client
     that holds the lock therefore holds everything the store leaf wants. *)
  Definition is_txlock (γl : gname) (γu : uart_names) : iProp Σ :=
    (is_lock γl a_tx_lock "uart"%string (tx_res γu) ∗ uart_dlab_off γu)%I.

  Global Instance is_txlock_persistent γl γu : Persistent (is_txlock γl γu).
  Proof. apply _. Qed.

  Lemma is_txlock_lock γl γu :
    is_txlock γl γu -∗ is_lock γl a_tx_lock "uart"%string (tx_res γu).
  Proof. iIntros "[$ _]". Qed.

  Lemma is_txlock_dlab γl γu : is_txlock γl γu -∗ uart_dlab_off γu.
  Proof. iIntros "[_ $]". Qed.

  (* ---- construction (the "newlock" ghost step), the shape uartinit's
     postcondition leaves behind: the freshly zeroed lock word and its
     persistent name, the [tx_busy] cell, and the transmitter token. *)
  Lemma new_txlock E (γu : uart_names) (b : mword 32) (l : list (bv 8)) :
    lock_name a_tx_lock "uart"%string -∗
    a_tx_lock ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu a_tx_lock ↦₈ (zero_reg : mword 64) -∗
    a_tx_busy ↦₄ b -∗
    uart_tx_own γu l -∗
    (⌜ b = (mword_of_int 0 : mword 32) ⌝ -∗ uart_out_lb γu l) -∗
    uart_dlab_off γu ={E}=∗ ∃ γl : gname, is_txlock γl γu.
  Proof.
    iIntros "#Hnm Hlkw Hcpu Hbusy Hown Hlb #Hoff".
    iMod (newlock E a_tx_lock "uart"%string (tx_res γu)
            with "Hnm Hlkw Hcpu [Hbusy Hown Hlb]") as (γl) "#Hlk".
    { iExists b, l. iFrame "Hbusy Hown Hlb". }
    iModIntro. iExists γl. iFrame "Hlk Hoff".
  Qed.

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
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u p v) "(Hu & Hp & Hv & Hg & Hrest)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hlb]".
    iMod ("Hclose" with "[Hu Hp Hv Hs Hout Htx Hdl Hrest]") as "_".
    { iNext. iExists u, p, v. rewrite /uart_ghosts. iFrame. }
    iModIntro. iFrame "Hown". rewrite -Hacc. iExact "Hlb".
  Qed.

  Lemma uart_tx_own_sent_prefix (γu : uart_names) (γd : disk_names)
      (l L : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent γu L ={E}=∗
      uart_tx_own γu l ∗ ⌜ L `prefix_of` l ⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #HL".
    iInv "Hinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u p v) "(Hu & Hp & Hv & Hg & Hrest)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_prefix with "Hs HL") as %Hpre.
    iMod ("Hclose" with "[Hu Hp Hv Hs Hout Htx Hdl Hrest]") as "_".
    { iNext. iExists u, p, v. rewrite /uart_ghosts. iFrame. }
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
