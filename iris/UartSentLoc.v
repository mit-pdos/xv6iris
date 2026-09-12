(* UartSentLoc.v -- THE LOCATED ACCEPTED-TRACE RECEIPT, at the altitude of
   the transmitter invariant it is about ([UartTxInv.v]).

   THIS IS THE ONLY COPY, and it lives here because its PRODUCERS do -- the
   uartwrite and consolewrite walks, which sit far below the syscall cone
   and must not require its statement files (SpecFilewrite / SpecSysWrite
   pull in the whole fs configuration; a device driver's proof requiring
   them would invert the layering for no gain).  [SpecFilewrite]'s console
   arms are stated on the definition below.

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

   WHY THERE IS NO COMMIT BUNDLE HERE: the UART's accepted trace is an
   OBSERVABLE, not a piece of the abstract file-system state, so a console
   write has nothing to fire and its receipt is history a caller keeps.

   ---- THE TAGGED FORMS (app-echo.md, E5/O4, lane TX-TAG) ---------------

   [uart_sent_from_at γu n0 src bs] is the same receipt on the TAGGED
   trace ([WpUart.uart_sent_tagged]): the bytes [bs], each tagged [src],
   appear in order at positions at or after [n0].  The seed is a LENGTH
   and not a trace, because the tagged and untagged traces are kept the
   same length and [length tr0] is all a located claim ever used of the
   seed.  It is what a user write's receipt is stated on, at
   [src = TxW pid].

   IT IS A SUBLIST CLAIM, NOT AN EXACT ONE, AND THAT IS A GAP, NOT A
   CHOICE.  The receipt one wants for a process's own writes is "the bytes
   tagged [TxW pid] accepted since the seed are EXACTLY [bs]" --
   [uart_sent_exact_at] below, which is stated here because the next lane
   (TX-RECEIPT) is where it is needed.  Nothing in the tree proves it
   today, and the reason is structural: the THR store leaf
   ([WpSconfUartAccess.wp_uart_thr_write_s_sconf]) takes its [txsrc] from
   the caller and checks it against nothing, so two harts can push under
   the SAME [TxW pid] and no resource refutes it.  Making it exact needs
   ONE of:

   * an EXCLUSIVE PER-PID TRANSMIT TOKEN, minted where a pid is (allocproc,
     beside the pid register [SlotGen.pid_reg_auth]), demanded by the store
     leaf whenever [src] is a [TxW], and held by the writing process across
     its call.  Then "no other writer used my tag while I ran" is ghost
     arithmetic, exactly as [uart_tx_own] is for the transmitter; or
   * pid UNIQUENESS plus a store-leaf premise tying [TxW pid] to the
     caller's own [proc_priv] -- weaker, because the leaf would then have
     to be given a piece of the process's private bundle, which the device
     layer does not otherwise see.

   Neither exists, so the SUBLIST form is what this lane lands, and
   [uart_sent_exact_at] is a statement with no producer. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import DevModel.   (* [uart_acc]: the accepted trace the tag column
     is kept in lockstep with; named in [uart_sent_from_tag_entry] *)
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* THE COMPOSITION FACT: a sublist of one trace extension followed by a
   sublist of the next IS a sublist of the joint extension. *)
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

(* THE PROJECTION OF A TAGGED TRACE ONTO ONE WRITER: [tag_proj src tg bs]
   says [bs] is EXACTLY the byte sequence of the [src]-tagged entries of
   [tg], in order.  Inductive rather than a [filter], so no decidable
   equality on [txsrc] (hence on [list mobs]) is needed. *)
Inductive tag_proj (src : txsrc) : list (txsrc * bv 8) -> list (bv 8) -> Prop :=
| tag_proj_nil : tag_proj src [] []
| tag_proj_yes tg bs b :
    tag_proj src tg bs -> tag_proj src ((src, b) :: tg) (b :: bs)
| tag_proj_no tg bs s b :
    s <> src -> tag_proj src tg bs -> tag_proj src ((s, b) :: tg) bs.

Section UartSentLoc.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* ------------------------------------------------------------------ *)
  (*  The receipt.                                                        *)
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
  (*  THE TAGGED RECEIPT.                                                 *)
  (* ------------------------------------------------------------------ *)

  (* INDEXED BY A LENGTH, not by a seed trace.  The tagged and untagged
     traces are kept the same length ([WpUart.uart_tagsE]), so the only
     thing a seed [tr0] contributes to a located claim is [length tr0] --
     and carrying the number makes the chain lemma below an ordinary
     [sublist_app] instead of a translation between two vocabularies.  A
     caller holding [uart_sent γu tr0] passes [length tr0]. *)
  Definition uart_sent_from_at (γu : uart_names) (n0 : nat)
      (src : txsrc) (bs : list (bv 8)) : iProp Σ :=
    (∃ tg : list (txsrc * bv 8),
       uart_sent_tagged γu tg ∗ ⌜(n0 <= length tg)%nat⌝ ∗
       ⌜((pair src) <$> bs) `sublist_of` drop n0 tg⌝)%I.

  Global Instance uart_sent_from_at_persistent γu n0 src bs :
    Persistent (uart_sent_from_at γu n0 src bs).
  Proof. apply _. Qed.
  Global Instance uart_sent_from_at_timeless γu n0 src bs :
    Timeless (uart_sent_from_at γu n0 src bs).
  Proof. apply _. Qed.

  (* THE EXACT FORM, STATED AND UNPRODUCED (see the header): the bytes
     tagged [src] accepted after position [n0] are EXACTLY [bs].  This is
     what the TX-RECEIPT lane needs of a user write, and what a per-pid
     transmit token would buy.  Nothing in this lane proves it. *)
  Definition uart_sent_exact_at (γu : uart_names) (n0 : nat)
      (src : txsrc) (bs : list (bv 8)) : iProp Σ :=
    (∃ tg : list (txsrc * bv 8),
       uart_sent_tagged γu tg ∗ ⌜(n0 <= length tg)%nat⌝ ∗
       ⌜tag_proj src (drop n0 tg) bs⌝)%I.

  Global Instance uart_sent_exact_at_persistent γu n0 src bs :
    Persistent (uart_sent_exact_at γu n0 src bs).
  Proof. apply _. Qed.

  (* the reflexive tagged receipt: nothing tagged [src] has been accepted
     after the trace one is holding.  The [n = 0] arm of every walk. *)
  Lemma uart_sent_from_at_refl (γu : uart_names)
      (tg : list (txsrc * bv 8)) (src : txsrc) :
    uart_sent_tagged γu tg -∗ uart_sent_from_at γu (length tg) src [].
  Proof.
    iIntros "H". iExists tg. iFrame "H". iPureIntro. split; [lia|].
    apply stdpp.list_relations.sublist_nil_l.
  Qed.

  (* the projection to the unlocated tagged vocabulary *)
  Lemma uart_sent_from_at_sub (γu : uart_names) (n0 : nat)
      (src : txsrc) (bs : list (bv 8)) :
    uart_sent_from_at γu n0 src bs -∗ uart_sent_sub_at γu src bs.
  Proof.
    iIntros "H". iDestruct "H" as (tg) "(Htg & %Hlen & %Hs)".
    iExists tg. iFrame "Htg". iPureIntro.
    apply (transitivity Hs). apply stdpp.list_relations.sublist_drop.
  Qed.

  (* THE CHAIN, [uart_sent_from_chain]'s tagged twin: a caller that
     destructed call k's tagged receipt -- learning its witness [tg1] and
     the pure fact -- and seeded call k+1 at [length tg1], concatenates. *)
  Lemma uart_sent_from_at_chain (γu : uart_names) (n0 : nat)
      (src : txsrc) (bs1 bs2 : list (bv 8)) (tg1 : list (txsrc * bv 8)) :
    (n0 <= length tg1)%nat ->
    ((pair src) <$> bs1) `sublist_of` drop n0 tg1 ->
    uart_sent_tagged γu tg1 -∗
    uart_sent_from_at γu (length tg1) src bs2 -∗
    uart_sent_from_at γu n0 src ((bs1 ++ bs2)%list).
  Proof.
    iIntros (H0 Hb1) "#Htg1 H".
    iDestruct "H" as (tg2) "(#Htg2 & %Hlen2 & %Hs2)".
    iDestruct (uart_sent_tagged_prefix γu tg1 tg2 Hlen2 with "Htg1 Htg2")
      as %[k ->].
    iExists ((tg1 ++ k)%list). iFrame "Htg2". iPureIntro.
    split; [rewrite length_app; lia |].
    rewrite drop_app_le; [| lia].
    rewrite drop_app_length in Hs2.
    rewrite fmap_app.
    apply stdpp.list_relations.sublist_app; [exact Hb1 | exact Hs2].
  Qed.

  (* ONE MORE TAGGED BYTE at the end of the trace the token pins:
     [uart_sent_from_snoc]'s tagged twin. *)
  Lemma uart_sent_from_at_snoc (γu : uart_names) (n0 : nat)
      (src : txsrc) (bs : list (bv 8)) (tg0 : list (txsrc * bv 8))
      (c : bv 8) :
    (n0 <= length tg0)%nat ->
    ((pair src) <$> bs) `sublist_of` drop n0 tg0 ->
    uart_sent_tagged γu (tg0 ++ [(src, c)]) -∗
    uart_sent_from_at γu n0 src ((bs ++ [c])%list).
  Proof.
    iIntros (Hlen Hb) "H". iExists ((tg0 ++ [(src, c)])%list). iFrame "H".
    iPureIntro. split; [rewrite length_app; cbn [length]; lia |].
    rewrite drop_app_le; [| lia]. rewrite fmap_app /=.
    apply stdpp.list_relations.sublist_app; [exact Hb | reflexivity].
  Qed.

  (* THE JOINT RECEIPT, which is what a writer's contract actually hands
     out: the located run on the untagged trace -- what [SpecFilewrite]'s
     console arms are stated on -- AND the same run on the tagged one, at
     the writer's own tag.

     ONE SHARED PAIR OF WITNESSES, TIED BY THE LOCKSTEP EQUATION, and that
     is what makes successive calls CHAIN.  Two independent receipts would
     name two unrelated trace bounds, and the next call's seed (a BYTE
     trace) could not be placed against this call's TAGGED bound at all.
     With [snd <$> tg = tr] the two have the same length, so seeding the
     next call at [tr] locates it after everything this one claimed on
     BOTH lists. *)
  Definition uart_sent_from_tag (γu : uart_names) (tr0 : list (bv 8))
      (src : txsrc) (bs : list (bv 8)) : iProp Σ :=
    (∃ (tr : list (bv 8)) (tg : list (txsrc * bv 8)),
       uart_sent γu tr ∗ uart_sent_tagged γu tg ∗ ⌜(snd <$> tg) = tr⌝ ∗
       ⌜tr0 `prefix_of` tr⌝ ∗
       ⌜bs `sublist_of` drop (length tr0) tr⌝ ∗
       ⌜((pair src) <$> bs) `sublist_of` drop (length tr0) tg⌝)%I.

  Global Instance uart_sent_from_tag_persistent γu tr0 src bs :
    Persistent (uart_sent_from_tag γu tr0 src bs).
  Proof. apply _. Qed.

  Lemma uart_sent_from_tag_plain (γu : uart_names) (tr0 : list (bv 8))
      (src : txsrc) (bs : list (bv 8)) :
    uart_sent_from_tag γu tr0 src bs -∗ uart_sent_from γu tr0 bs.
  Proof.
    iIntros "H". iDestruct "H" as (tr tg) "(Htr & _ & _ & %Hp & %Hs & _)".
    iExists tr. by iFrame "Htr".
  Qed.

  Lemma uart_sent_from_tag_tagged (γu : uart_names) (tr0 : list (bv 8))
      (src : txsrc) (bs : list (bv 8)) :
    uart_sent_from_tag γu tr0 src bs -∗
    uart_sent_from_at γu (length tr0) src bs.
  Proof.
    iIntros "H". iDestruct "H" as (tr tg) "(_ & Htg & %Heq & %Hp & _ & %Hst)".
    iExists tg. iFrame "Htg". iPureIntro. split; [| exact Hst].
    rewrite -(length_fmap snd tg) Heq. by apply prefix_length.
  Qed.

  (* THE SEED FOR THE NEXT CALL, read off the receipt one holds.  Every
     field is persistent or pure, so this does NOT consume the receipt. *)
  Lemma uart_sent_from_tag_seed (γu : uart_names) (tr0 : list (bv 8))
      (src : txsrc) (bs : list (bv 8)) :
    uart_sent_from_tag γu tr0 src bs -∗
    ∃ (tr : list (bv 8)) (tg : list (txsrc * bv 8)),
      uart_sent γu tr ∗ uart_sent_tagged γu tg ∗ ⌜(snd <$> tg) = tr⌝ ∗
      ⌜tr0 `prefix_of` tr⌝ ∗
      ⌜bs `sublist_of` drop (length tr0) tr⌝ ∗
      ⌜((pair src) <$> bs) `sublist_of` drop (length tr0) tg⌝.
  Proof. iIntros "H". iExact "H". Qed.

  (* THE CHAIN: call k's receipt, destructed to its witness pair, followed
     by call k+1's receipt seeded at that pair's BYTE trace. *)
  Lemma uart_sent_from_tag_chain (γu : uart_names)
      (tr0 tr1 : list (bv 8)) (tg1 : list (txsrc * bv 8))
      (src : txsrc) (bs1 bs2 : list (bv 8)) :
    (snd <$> tg1) = tr1 ->
    tr0 `prefix_of` tr1 ->
    bs1 `sublist_of` drop (length tr0) tr1 ->
    ((pair src) <$> bs1) `sublist_of` drop (length tr0) tg1 ->
    uart_sent_tagged γu tg1 -∗
    uart_sent_from_tag γu tr1 src bs2 -∗
    uart_sent_from_tag γu tr0 src ((bs1 ++ bs2)%list).
  Proof.
    iIntros (Heq1 Hp01 Hb1 Ht1) "#Htg1 H".
    iDestruct "H" as (tr2 tg2) "(#Htr2 & #Htg2 & %Heq2 & %Hp12 & %Hb2 & %Ht2)".
    assert (Hlen1 : length tg1 = length tr1)
      by (rewrite -(length_fmap snd tg1) Heq1; reflexivity).
    assert (Hlen2 : length tg2 = length tr2)
      by (rewrite -(length_fmap snd tg2) Heq2; reflexivity).
    assert (Hle : (length tg1 <= length tg2)%nat)
      by (rewrite Hlen1 Hlen2; by apply prefix_length).
    iDestruct (uart_sent_tagged_prefix γu tg1 tg2 Hle with "Htg1 Htg2")
      as %[k ->].
    assert (Hn0 : (length tr0 <= length tg1)%nat)
      by (rewrite Hlen1; by apply prefix_length).
    iExists tr2, ((tg1 ++ k)%list). iFrame "Htr2 Htg2". iPureIntro.
    split; [exact Heq2 |].
    split; [by etrans |].
    split; [by eapply usl_sublist_drop_chain |].
    (* the tagged halves: [length tr1] IS [length tg1] by the lockstep
       equation, so the second run starts exactly where the first ends *)
    rewrite fmap_app drop_app_le; [| lia].
    rewrite -Hlen1 drop_app_length in Ht2.
    apply stdpp.list_relations.sublist_app; [exact Ht1 | exact Ht2].
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

  (* THE ENTRY RECEIPT, and the one place the tagged half cannot be minted
     from nothing: an empty run located at [tr0] still has to name a tagged
     trace that reaches [tr0], and only the invariant has one.  One fupd at
     the walk's entry buys it. *)
  Lemma uart_sent_from_tag_entry (γu : uart_names) (γd : disk_names)
      (tr0 : list (bv 8)) (src : txsrc) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_sent γu tr0 ={E}=∗ uart_sent_from_tag γu tr0 src [].
  Proof.
    iIntros (HE) "#Hinv #Hseed".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htg)".
    iDestruct (uart_sent_prefix with "Hs Hseed") as %Hpre.
    iDestruct (uart_sent_get with "Hs") as "[Hs #Hacc]".
    iDestruct "Htg" as (tgA) "[HtgA %HtgA]".
    iDestruct (uart_tags_get with "HtgA") as "[HtgA #HlbA]".
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl HtgA Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts.
      iFrame "Hu Hs Hout Htx Hdl Hcol". iExists tgA. by iFrame "HtgA". }
    iModIntro. iExists (uart_acc u), tgA. iFrame "Hacc HlbA". iPureIntro.
    split_and!; [exact HtgA | exact Hpre |
                 apply stdpp.list_relations.sublist_nil_l |
                 apply stdpp.list_relations.sublist_nil_l].
  Qed.

  (* THE RE-LINK UNDER THE TOKEN: a walk that kept the joint receipt across
     a park and has re-acquired the transmitter at trace [l] learns the
     three pure facts the next push needs, on BOTH lists.
     [uart_tx_own_sent_from]'s joint twin. *)
  Lemma uart_tx_own_sent_from_tag (γu : uart_names) (γd : disk_names)
      (l tr0 : list (bv 8)) (src : txsrc) (bs : list (bv 8)) (E : coPset) :
    ↑devN ⊆ E ->
    dev_inv γu γd -∗ uart_tx_own γu l -∗ uart_sent_from_tag γu tr0 src bs ={E}=∗
      uart_tx_own γu l ∗ ⌜tr0 `prefix_of` l⌝ ∗
      ⌜bs `sublist_of` drop (length tr0) l⌝ ∗
      ∃ tg : list (txsrc * bv 8),
        uart_sent_tagged γu tg ∗ ⌜(snd <$> tg) = l⌝ ∗
        ⌜((pair src) <$> bs) `sublist_of` drop (length tr0) tg⌝.
  Proof.
    iIntros (HE) "#Hinv Hown #Hrcpt".
    iDestruct "Hrcpt" as (tr tg) "(#Htr & #Htg & %Heq & %Hp0 & %Hb & %Ht)".
    iDestruct (dev_inv_uart with "Hinv") as "#Huinv".
    iInv "Huinv" as ">Hbody" "Hclose".
    iDestruct "Hbody" as (u) "(Hu & Hg & Hcol)".
    iEval (rewrite /uart_ghosts) in "Hg".
    iDestruct "Hg" as "(Hs & Hout & Htx & Hdl & Htgs)".
    iDestruct (uart_tx_own_agree with "Htx Hown") as %Hacc.
    iDestruct (uart_sent_prefix with "Hs Htr") as %Hprl.
    iDestruct "Htgs" as (tgA) "[HtgA %HtgA]".
    iDestruct (uart_tags_get with "HtgA") as "[HtgA #HlbA]".
    iDestruct (uart_tags_prefix with "HtgA Htg") as %Hptg.
    iMod ("Hclose" with "[Hu Hs Hout Htx Hdl HtgA Hcol]") as "_".
    { iApply bi.later_intro. iExists u. rewrite /uart_ghosts.
      iFrame "Hu Hs Hout Htx Hdl Hcol". iExists tgA. by iFrame "HtgA". }
    rewrite Hacc in Hprl. rewrite Hacc in HtgA.
    iModIntro. iFrame "Hown". iSplitR; [iPureIntro; by etrans |].
    iSplitR.
    { iPureIntro. destruct Hprl as [k ->].
      rewrite drop_app_le; last by apply prefix_length.
      apply (transitivity Hb).
      apply stdpp.list_relations.sublist_inserts_r. reflexivity. }
    iExists tgA. iFrame "HlbA". iPureIntro. split; [exact HtgA |].
    destruct Hptg as [k ->].
    rewrite drop_app_le; last first.
    { rewrite -(length_fmap snd tg) Heq. by apply prefix_length. }
    apply (transitivity Ht).
    apply stdpp.list_relations.sublist_inserts_r. reflexivity.
  Qed.

  (* ONE MORE BYTE at the end of the trace the token pins, on both lists.
     [uart_sent_from_snoc]'s joint twin. *)
  Lemma uart_sent_from_tag_snoc (γu : uart_names)
      (tr0 bs l : list (bv 8)) (src : txsrc)
      (tg0 : list (txsrc * bv 8)) (c : bv 8) :
    tr0 `prefix_of` l ->
    bs `sublist_of` drop (length tr0) l ->
    (snd <$> tg0) = l ->
    ((pair src) <$> bs) `sublist_of` drop (length tr0) tg0 ->
    uart_sent γu ((l ++ [c])%list) -∗
    uart_sent_tagged γu ((tg0 ++ [(src, c)])%list) -∗
    uart_sent_from_tag γu tr0 src ((bs ++ [c])%list).
  Proof.
    iIntros (Hp Hb Heq Hbt) "#Hsent #Htg".
    assert (Hlen : (length tr0 <= length tg0)%nat).
    { rewrite -(length_fmap snd tg0) Heq. by apply prefix_length. }
    iExists ((l ++ [c])%list), ((tg0 ++ [(src, c)])%list).
    iFrame "Hsent Htg". iPureIntro. split_and!.
    - by rewrite fmap_app /= Heq.
    - etrans; [exact Hp |]. by exists [c].
    - rewrite drop_app_le; last by apply prefix_length.
      apply stdpp.list_relations.sublist_app; [exact Hb | reflexivity].
    - rewrite fmap_app /= drop_app_le; [| lia].
      apply stdpp.list_relations.sublist_app; [exact Hbt | reflexivity].
  Qed.

End UartSentLoc.
