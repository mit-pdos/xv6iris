(* UartSentResidue.v -- THE IRIS-TO-PURE STEP of the console trace
   connection: what a LOCATED RECEIPT says about the DEVICE, and from there
   about what the host saw.

   The campaign's console receipt is [UartSentLoc.uart_sent_from γu tr0 bs]
   -- the bytes [bs] were accepted by the UART, in order, at positions
   strictly after an accepted trace that had [tr0] as a prefix.  It is a
   mono-list LOWER BOUND plus two pure facts, so on its own it says nothing
   about any particular device state.  Agreed against the AUTHORITY
   [WpUart.uart_sent_auth γu u] -- which is [own _ (●ML (uart_acc u))], and
   which the UART thread's arms hold as part of [WpUart.uart_ghosts γ u] --
   it becomes two PURE facts about [uart_acc u], and those two facts are
   exactly the hypotheses [UartAccepted.run_out_accepted_from] and
   [SystemUartAccepted.xv6_out_accepted_from_xv6Σ] take.

   [uart_sent_from_obs] is the whole composition in one line: the receipt,
   the authority, the WIRE TIE (which [WpUart.wp_uart_step] hands its
   callback and [uart_obs_permit] passes to a client's wands) and the
   device invariant [UartAccepted.out_wire_ok] give the located reading of
   the observable trace -- the cycle's output splits at the receipt's seed,
   and everything after the split was accepted after the seed, in the
   accepted order.

   THIS IS THE MEETING POINT the lane's brief names -- one instruction, two
   facts: the THR-store's byte reaches the wire, and the acceptance ghost
   already records it.  What is NOT here is the delivery of its premises at
   an event: the trace ledger's wands ([WpUart.uart_obs_permit_ledger])
   receive an ARBITRARY [γ : uart_names] and no device invariant, so a
   client's [R] can neither know the [γ] it is handed is the era's nor that
   [out_wire_ok] holds of the state it is looking at.  Both gaps are stated
   in [SystemUartAccepted.v]'s header and in this lane's report; the pure
   route ([UartAccepted.run_out_accepted]) needs neither and is what the
   landed export uses. *)

From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import DevModel WpUart.
Require Import UartTxInv UartSentLoc.
Require Import ObsTrace UartAccepted.
Require Import Xv6G.
Local Open Scope Z_scope.

Section UartSentResidue.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE RESIDUE.  Both pure facts at once, against the accepted trace of
     the state the authority is about.  [UartSentLoc.uart_tx_own_sent_from]
     is the same step routed through the transmitter token and [dev_inv];
     this is the form for a holder of the AUTHORITY itself -- the UART
     thread's arms, which are where the trace events happen. *)
  Lemma uart_sent_from_acc (γu : uart_names) (u : uart_state)
      (tr0 bs : list (bv 8)) :
    uart_sent_auth γu u -∗ uart_sent_from γu tr0 bs -∗
      ⌜tr0 `prefix_of` uart_acc u
       /\ bs `sublist_of` drop (length tr0) (uart_acc u)⌝.
  Proof.
    iIntros "Ha #Hfrom". iDestruct "Hfrom" as (tr) "(#HL & %Hp & %Hs)".
    iDestruct (uart_sent_prefix with "Ha HL") as %Hpre.
    iPureIntro. pose proof Hpre as Hpre'. destruct Hpre' as [k Hk].
    split.
    - etrans; [exact Hp | exact Hpre].
    - rewrite Hk drop_app_le;
        last by apply stdpp.list_relations.prefix_length.
      apply (transitivity Hs).
      apply stdpp.list_relations.sublist_inserts_r. reflexivity.
  Qed.

  (* ...AND WHAT IT BUYS ON THE TRACE.  [Hwire] is the wire tie the machine
     layer knows at every UART arm ([ObsTrace.obs_wf]'s third conjunct, as
     [WpUart.wp_uart_step] hands it over); [Hok] is the device invariant
     [UartAccepted.out_wire_ok], a step invariant of the language proved
     there.  Given both, a receipt LOCATES the observable output. *)
  Lemma uart_sent_from_obs (γu : uart_names) (u : uart_state)
      (h : list RiscvLang.mobs) (tr0 bs : list (bv 8)) :
    obs_wire (open_seg h) = u_wire u ->
    out_wire_ok u ->
    uart_sent_auth γu u -∗ uart_sent_from γu tr0 bs -∗
      ⌜exists w1 w2 : list (bv 8),
         obs_wire (open_seg h) = (w1 ++ w2)%list
         /\ w1 `sublist_of` tr0
         /\ w2 `sublist_of` drop (length tr0) (uart_acc u)
         /\ bs `sublist_of` drop (length tr0) (uart_acc u)⌝.
  Proof.
    iIntros (Hwire Hok) "Ha #Hfrom".
    iDestruct (uart_sent_from_acc with "Ha Hfrom") as %[Hpre Hbs].
    iPureIntro.
    assert (Hsub : obs_wire (open_seg h) `sublist_of` uart_acc u).
    { rewrite Hwire. exact (out_wire_ok_acc _ Hok). }
    destruct (out_accepted_locate _ _ _ Hsub Hpre) as (w1 & w2 & Hw & Hw1 & Hw2).
    exists w1, w2. done.
  Qed.

End UartSentResidue.
