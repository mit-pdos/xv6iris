(* ===================================================================== *)
(*  EchoLinksBan.v -- THE SHELL'S PROMPT FROM THE BANNER-OWED CREDENTIAL, *)
(*  AND THE DISCIPLINE LEMMA AT THE WIDENED BOUNDARY (app-echo.md, E5 --  *)
(*  THE CONSOLE I/O CLAIM; lane PROLOGUE-ALTS-3, after the ruling that    *)
(*  init's banner is OPTIONAL in the transcript).                         *)
(*                                                                       *)
(*  /init's console open can fail while the shell's own opens succeed.   *)
(*  /init then prints nothing and lends the shell the era's write         *)
(*  credential in its BANNER-OWED shape ([EchoLinks.ewc_ban] at [0]):    *)
(*  the round's next letter is still to come, and the shell's prompt is  *)
(*  that letter -- the bare prompt, [EchoDisc.pro_alts !!! 0] with no    *)
(*  banner before it.  [EchoLinks.echo_prompt_dollar_ban] pays it at the  *)
(*  loose shapes; this file pays it at the TIGHT shapes of               *)
(*  [EchoLinksLine], which is what the shell's credential family is       *)
(*  instantiated at, and states the discipline lemma at that family's    *)
(*  boundary shape ([ewc_line]): an untainted read at a boundary whose   *)
(*  prompt is not out is the taint.                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
Require Import EchoLinksLine.
(* as in EchoDisc / EchoOutPure / EchoOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  THE PURE HALF: the block written up to its prompt is an unwritten     *)
(*  prompt too ([EchoLinksLine.ewc_post]), so the reader's echoes refute  *)
(*  it exactly as they refute [wr_blk] ([EchoLinks.wr_blk_read_refute]).  *)
(*                                                                       *)
(*  ONE ARITHMETIC CASE SPLIT, not three: the bytes already out are       *)
(*  [length (line_alts_of (last_ws I) !!! a) - 2] whatever [a] is, and    *)
(*  the only thing the three alternatives decide is whether that number   *)
(*  is ZERO.  At [a = 2] it is (the child recorded no choice, so the      *)
(*  block's own first byte is still owed); at [a = 0] it is the length    *)
(*  of what echo printed back, which is at least one byte because a line  *)
(*  always carries its newline ([LineWords.wl_line_pos]); at [a = 1] it   *)
(*  is the exec diagnostic's seventeen.                                   *)
(* ===================================================================== *)
Lemma wr_post_read_refute (ps cs ps0 cs0 : list nat) (I I0 : list (bv 8))
      (P a : nat) :
  (a < 3)%nat ->
  wr_blk ps cs I P ->
  (blkcs cs a (length (line_alts_of (last_ws I) !!! a) - 2) `prefix_of` cs0
   \/ cs0 `prefix_of`
      blkcs cs a (length (line_alts_of (last_ws I) !!! a) - 2)) ->
  I `prefix_of` I0 -> I <> I0 -> rd_stage ps0 cs0 I0 ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (length (proc_before ps0 cs0 I0)
   <= P + (length (line_alts_of (last_ws I) !!! a) - 2))%nat ->
  False.
Proof.
  intros Ha Hw Hcs HI Hne Hrs Hps Hle.
  pose proof Hrs as (HFps0 & HFcs0 & Hpin0 & Hbnd0).
  pose proof Hw as (Hpin & Hr & Hn & HP).
  pose proof (line_alts_len_ge2 (last_ws I) a Ha) as Hge2.
  (* the reader's line list reaches past the block's own entry *)
  assert (Hlen0 : (S (length cs) <= length cs0)%nat).
  { rewrite -Hn. etrans; [| exact Hbnd0].
    apply nlines_prefix, (epu_prefix_of_removelast I I0 HI Hne). }
  (* one lemma for the two filed alternatives *)
  assert (Hfiled : forall d, (0 < d)%nat ->
            (d < length (line_alts_of (last_ws I) !!! a))%nat ->
            (blkcs cs a d `prefix_of` cs0 \/ cs0 `prefix_of` blkcs cs a d) ->
            (length (proc_before ps0 cs0 I0) <= P + d)%nat -> False).
  { intros d Hd0 Hd Hc Hl.
    destruct d as [| d]; [lia |]. cbn [blkcs] in Hc.
    assert (Hpre : (cs ++ [a]) `prefix_of` cs0).
    { destruct Hc as [Hc | Hc]; [exact Hc |].
      pose proof (prefix_length _ _ Hc) as Hlc.
      rewrite (length_app cs [a]) in Hlc. cbn [length] in Hlc.
      rewrite (prefix_length_eq _ _ Hc
                 ltac:(rewrite (length_app cs [a]); cbn [length]; lia)).
      reflexivity. }
    assert (Hcs' : cs `prefix_of` cs0).
    { etrans; [| exact Hpre]. by eexists. }
    assert (Hat : cs0 !!! length cs = a).
    { rewrite -(snoc_lookup_total cs a).
      apply (lookup_total_prefix (cs ++ [a]) cs0); [exact Hpre |].
      rewrite (length_app cs [a]). cbn [length]. lia. }
    assert (Hd' : (S d < length (line_alts_of (last_ws I)
                                   !!! (cs0 !!! length cs)))%nat)
      by (rewrite Hat; exact Hd).
    exact (wr_blk_read_refute ps cs ps0 cs0 I I0 P (S d) Hw Hcs' Hd' HI Hne
             Hrs Hps Hl). }
  destruct (decide (a = 2%nat)) as [Ha2 | Ha2].
  - (* nothing filed: the block's first byte is the prompt itself *)
    rewrite Ha2 (line_alts_len2_ (last_ws I)) in Hcs Hle.
    cbn [Nat.sub blkcs] in Hcs.
    assert (Hcs' : cs `prefix_of` cs0).
    { destruct Hcs as [Hc | Hc]; [exact Hc |].
      apply prefix_length in Hc. exfalso. lia. }
    assert (Hd0 : (0 < length (line_alts_of (last_ws I)
                                 !!! (cs0 !!! length cs)))%nat).
    { destruct (line_alts_of (last_ws I) !!! (cs0 !!! length cs))
        as [| y ys] eqn:Hy; [| cbn [length]; lia].
      exfalso.
      exact (line_alts_of_nonnil _ _ (cs_ok_of_Forall _ HFcs0 _) Hy). }
    exact (wr_blk_read_refute ps cs ps0 cs0 I I0 P 0 Hw Hcs' Hd0 HI Hne Hrs Hps
             ltac:(lia)).
  - (* echo's output ([a = 0]) or the exec diagnostic ([a = 1]): at least
       one byte of the block is out *)
    apply (Hfiled (length (line_alts_of (last_ws I) !!! a) - 2)%nat);
      [| lia | exact Hcs | exact Hle].
    destruct a as [| [| [| a]]]; [| | done | lia].
    + rewrite (line_alts_of_0_length (last_ws I)).
      pose proof (wl_line_pos (drop 1 (last_ws I))). lia.
    + rewrite (line_alts_len1 (last_ws I)). lia.
Qed.

Section echo_links_ban.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* THE BANNER-OWED CREDENTIAL IS THE WIDENED BOUNDARY'S OPEN-PROLOGUE
     ARM: what /init lends when it printed nothing lands exactly where the
     shell's loop expects its credential. *)
  Lemma ewc_ban_line (v : era_pins) (I : list (bv 8)) :
    EchoLinks.ewc_ban T v I 0%nat -∗ EchoLinksLine.ewc_line T v I.
  Proof using Persistent0.
    iIntros "Hc". iApply EchoLinksLine.ewc_line_of_pro.
    rewrite /EchoLinksLine.ewc_pro. iApply (EchoLinks.ewc_ban_pro with "Hc").
  Qed.

  (* THE '$' FROM THE BANNER-OWED SHAPE, at the tight after-'$' shape: the
     round's letter is the bare prompt. *)
  Lemma echo_prompt_dollar_ban (k : nat) (v : era_pins) (I : list (bv 8))
      (b : bv 8) (Φ : iProp Σ) :
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ echo_links T γ -∗ EchoLinks.ewc_ban T v I 0%nat -∗
    (EchoLinksLine.ewc_sp_t T v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Persistent0.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iApply (EchoLinksLine.echo_prompt_dollar_line T γ k v I b Φ Hb
              with "Hpin Hlk [Hc] HΦ").
    by iApply ewc_ban_line.
  Qed.

  (* =================================================================== *)
  (*  THE DISCIPLINE LEMMA AT THE WIDENED BOUNDARY: every arm of          *)
  (*  [ewc_line] says the boundary's prompt is not out, so a read that    *)
  (*  delivered a byte there is the taint.                                *)
  (*                                                                     *)
  (*  [length I = n] is what ties the credential's boundary to the read's *)
  (*  (see [EchoLinks.ewc_owed_read_refute]): the two lower bounds of one *)
  (*  era's input then settle that the reader's input STRICTLY EXTENDS    *)
  (*  the writer's boundary, which is what used to be [n < m].            *)
  (* =================================================================== *)
  Lemma ewc_post_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (a : nat) (ws : list (list mobs * bv 8)) :
    (a < 3)%nat -> length I = n -> (0 < length ws)%nat ->
    EchoLinksLine.ewc_post T v I a -∗ read_ret T k v n ws -∗ T.
  Proof using Persistent0.
    intros Ha HIn Hws. iIntros "Hc Hr".
    rewrite /EchoLinksLine.ewc_post /EchoLinksLine.ewc_blk.
    iDestruct "Hc" as "[Hl | #HT]"; [| done].
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct Hw as [Hw _].
    rewrite /read_ret. iDestruct "Hr" as "[[#HT Hdl] | [Hdlr Hfacts]]"; [done |].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsc & #Hinp & %Hdi & Hrest)".
    iDestruct "Hrest" as "[%Hws0 | Hbb]".
    { exfalso. rewrite Hws0 in Hws. cbn in Hws. lia. }
    iDestruct "Hbb" as (cs0 ps0) "(#Hcs0 & #Hps0 & %Hbd & #Htlb & %Hrs)".
    iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcsc.
    iDestruct (turn_lb_le with "Htn Htlb") as %Hle.
    iDestruct (inp_lb_cmp with "HE Hinp") as %Hic.
    iExFalso. iPureIntro.
    assert (Hlen : length (snd <$> (dl ++ ws)) = (n + length ws)%nat).
    { by rewrite length_fmap length_app Hdl. }
    assert (HI : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hic as [Hc | Hc]; [exact Hc |].
      exfalso. apply prefix_length in Hc. lia. }
    assert (Hne : I <> (snd <$> (dl ++ ws)))
      by (intros Hq; rewrite Hq Hlen in HIn; lia).
    exact (wr_post_read_refute ps cs ps0 cs0 I (snd <$> (dl ++ ws)) P a Ha Hw
             Hcsc HI Hne Hrs Hpsc Hle).
  Qed.

  Lemma ewc_line_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    EchoLinksLine.ewc_line T v I -∗ read_ret T k v n ws -∗ T.
  Proof using Persistent0.
    intros HIn Hws. iIntros "Hc Hr".
    rewrite /EchoLinksLine.ewc_line. iDestruct "Hc" as "[Hc | Hc]".
    - iDestruct (EchoLinksLine.ewc_pro_owed with "Hc") as "Hc".
      iApply (EchoLinks.ewc_owed_read_taint T k v n I ws HIn Hws with "Hc Hr").
    - iDestruct "Hc" as (a) "[%Ha Hc]".
      iApply (ewc_post_read_taint k v n I a ws Ha HIn Hws with "Hc Hr").
  Qed.

  (* ...and at the banner-owed shape itself *)
  Lemma ewc_ban_read_taint (k : nat) (v : era_pins) (n : nat)
      (I : list (bv 8)) (ws : list (list mobs * bv 8)) :
    length I = n -> (0 < length ws)%nat ->
    EchoLinks.ewc_ban T v I 0%nat -∗ read_ret T k v n ws -∗ T.
  Proof using Persistent0.
    intros HIn Hws. iIntros "Hc Hr".
    iDestruct (EchoLinks.ewc_ban_owed with "Hc") as "Hc".
    iApply (EchoLinks.ewc_owed_read_taint T k v n I ws HIn Hws with "Hc Hr").
  Qed.

End echo_links_ban.
