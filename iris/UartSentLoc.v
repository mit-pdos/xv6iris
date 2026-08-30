(* UartSentLoc.v -- THE LOCATED ACCEPTED-TRACE RECEIPT, at the altitude of
   the transmitter invariant it is about ([UartTxInv.v]).

   [SpecSysWriteConsAU.v] states this same receipt at SYSCALL altitude,
   where its consumer reads it; this file is the same definition where its
   PRODUCERS live -- the uartwrite and consolewrite walks, which sit far
   below the syscall cone and must not require it (SpecSysWriteConsAU pulls
   in SpecFilewrite / SpecSysWrite / the whole fs configuration; a device
   driver's proof requiring the write syscall's statement file would invert
   the layering for no gain).  The two definitions are literally the same
   term at the same context, and [ProofSysWriteConsAU.v] -- the one file
   that sees both -- carries the one-line identification.  R10 forbids
   editing SpecSysWriteConsAU.v, so the duplication is the ruled shape, not
   an accident; when that seal's consumer set settles, the campaign's
   retirement step points it at this file and the copy comes out.

   WHAT IT SAYS.  [uart_sent_from γu tr0 bs]: the bytes [bs] were accepted
   by the UART, IN ORDER, at positions STRICTLY AFTER a trace that had
   [tr0] as a prefix -- [UartTxInv.uart_sent_sub] refined by a LOCATION.
   Persistent (it is a mono_list lower bound plus two pure facts), so it
   survives everything; and LOCATED, which is what makes successive calls'
   receipts CONCATENATE ([uart_sent_from_chain]) where two bare
   [uart_sent_sub]s cannot -- nothing orders one call's trace witness
   against another's.

   THE TWO LEMMAS THIS FILE ADDS BEYOND THE SPEC FILE'S ALGEBRA are exactly
   what a walk that pushes bytes under the transmitter token needs:

   * [uart_tx_own_sent_from] -- the token re-links a receipt it kept across
     a park to the CURRENT accepted trace, delivering BOTH pure facts about
     [l] (this is [UartTxInv.uart_tx_own_sent_sub] plus the location, and
     the located form of [uart_tx_own_sent_prefix] the campaign's plan
     named);
   * [uart_sent_from_snoc] -- one more byte at the end of that trace
     extends the receipt ([UartTxInv.uart_sent_sub_snoc]'s located twin).

   Design of record: SpecSysWriteConsAU.v's header (THE OBSERVABLE, and WHY
   THERE IS NO COMMIT BUNDLE) -- nothing is restated here. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* THE COMPOSITION FACT (SpecSysWriteConsAU.sublist_drop_chain, under a
   lane-local name so a file that imports both keeps two unambiguous
   spellings): a sublist of one trace extension followed by a sublist of
   the next IS a sublist of the joint extension. *)
Lemma usl_sublist_drop_chain {A : Type} (tr0 tr1 tr2 bs1 bs2 : list A) :
  tr0 `prefix_of` tr1 -> tr1 `prefix_of` tr2 ->
  bs1 `sublist_of` drop (length tr0) tr1 ->
  bs2 `sublist_of` drop (length tr1) tr2 ->
  ((bs1 ++ bs2)%list) `sublist_of` drop (length tr0) tr2.
Proof.
  intros H01 H12 Hb1 Hb2.
  destruct H12 as [ext ->].
  rewrite drop_app_le; last by apply stdpp.list_relations.prefix_length.
  rewrite drop_app_length in Hb2.
  by apply stdpp.list_relations.sublist_app.
Qed.

Section UartSentLoc.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The receipt (SpecSysWriteConsAU.v section 2, verbatim).             *)
  (* ------------------------------------------------------------------ *)

  Definition uart_sent_from (γu : uart_names) (tr0 bs : list (bv 8))
      : iProp Σ :=
    (∃ tr : list (bv 8),
       uart_sent γu tr ∗ ⌜tr0 `prefix_of` tr⌝ ∗
       ⌜bs `sublist_of` drop (length tr0) tr⌝)%I.

  Global Instance uart_sent_from_persistent γu tr0 bs :
    Persistent (uart_sent_from γu tr0 bs).
  Proof. apply _. Qed.

  (* the reflexive receipt: nothing was accepted after a seed one holds --
     the [n = 0] arm of every walk below, and free *)
  Lemma uart_sent_from_refl (γu : uart_names) (tr0 : list (bv 8)) :
    uart_sent γu tr0 -∗ uart_sent_from γu tr0 [].
  Proof.
    iIntros "H". iExists tr0. iFrame "H". iPureIntro. split.
    - by exists []; rewrite app_nil_r.
    - apply stdpp.list_relations.sublist_nil_l.
  Qed.

  (* the projection to the landed vocabulary: located implies sublist *)
  Lemma uart_sent_from_sub (γu : uart_names) (tr0 bs : list (bv 8)) :
    uart_sent_from γu tr0 bs -∗ uart_sent_sub γu bs.
  Proof.
    iIntros "H". iDestruct "H" as (tr) "(Htr & %Hp & %Hs)".
    iExists tr. iFrame "Htr". iPureIntro.
    apply (transitivity Hs). apply stdpp.list_relations.sublist_drop.
  Qed.

  (* THE CHAIN: a caller who destructed call k's receipt -- learning its
     trace witness [tr1] (kept: [uart_sent] is persistent) and the two pure
     facts -- and seeded call k+1 with [tr1], concatenates. *)
  Lemma uart_sent_from_chain (γu : uart_names)
      (tr0 tr1 bs1 bs2 : list (bv 8)) :
    tr0 `prefix_of` tr1 ->
    bs1 `sublist_of` drop (length tr0) tr1 ->
    uart_sent_from γu tr1 bs2 -∗
    uart_sent_from γu tr0 ((bs1 ++ bs2)%list).
  Proof.
    iIntros (Hp Hb) "H". iDestruct "H" as (tr2) "(Htr & %Hp2 & %Hs2)".
    iExists tr2. iFrame "Htr". iPureIntro. split.
    - by etrans.
    - by eapply usl_sublist_drop_chain.
  Qed.

  (* the seed a caller with no trace bound in hand mints from nothing
     ([◯ML []] is the unit of the mono-list algebra) *)
  Lemma uart_sent_nil (γu : uart_names) : ⊢ |==> uart_sent γu [].
  Proof.
    iMod (own_unit (mono_listUR (leibnizO (bv 8))) γu.(un_acc)) as "H".
    iModIntro.
    rewrite /uart_sent -(mono_list_lb_nil_is_unit (leibnizO (bv 8))).
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  What the PRODUCER of a receipt needs, and the spec file does not.   *)
  (* ------------------------------------------------------------------ *)

  (* ONE MORE BYTE, at the end of the trace the token pins.
     [UartTxInv.uart_sent_sub_snoc]'s located twin. *)
  Lemma uart_sent_from_snoc (γu : uart_names) (tr0 bs l : list (bv 8))
      (c : bv 8) :
    tr0 `prefix_of` l ->
    bs `sublist_of` drop (length tr0) l ->
    uart_sent γu ((l ++ [c])%list) -∗ uart_sent_from γu tr0 ((bs ++ [c])%list).
  Proof.
    iIntros (Hp Hb) "H". iExists ((l ++ [c])%list). iFrame "H". iPureIntro.
    split.
    - etrans; [exact Hp|]. by exists [c].
    - rewrite drop_app_le; last by apply stdpp.list_relations.prefix_length.
      apply stdpp.list_relations.sublist_app; [exact Hb | reflexivity].
  Qed.

  (* the device fabric's own binders, exactly UartTxInv.v's ([dev_inv] is
     stated at a [GenId]) *)
  Context `{GEN : RiscvLang.GenId}.

  (* THE TOKEN RE-LINKS THE RECEIPT.  A driver that kept
     [uart_sent_from γu tr0 bs] across a park and has just re-acquired the
     transmitter at trace [l] learns BOTH of the pure facts about [l] that
     the next push needs: its seed is still a prefix, and its own bytes are
     still located after it.  [UartTxInv.uart_tx_own_sent_sub] with the
     location kept -- same proof, one transitivity longer. *)
  Lemma uart_tx_own_sent_from (γu : uart_names) (γd : disk_names)
      (l tr0 bs : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent_from γu tr0 bs ={E}=∗
      uart_tx_own γu l ∗ ⌜ tr0 `prefix_of` l ⌝ ∗
      ⌜ bs `sublist_of` drop (length tr0) l ⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #Hfrom".
    iDestruct "Hfrom" as (tr) "(#HL & %Hp & %Hs)".
    iMod (uart_tx_own_sent_prefix γu γd l tr E HE with "Hinv Hown HL")
      as "[Hown %Hpre]".
    iModIntro. iFrame "Hown". iPureIntro.
    pose proof Hpre as Hpre'. destruct Hpre' as [k ->].
    split.
    - by etrans.
    - rewrite drop_app_le; last by apply stdpp.list_relations.prefix_length.
      apply (transitivity Hs).
      apply stdpp.list_relations.sublist_inserts_r. reflexivity.
  Qed.

End UartSentLoc.
