(* ===================================================================== *)
(*  PipeOutNEv.v -- THE OPEN ROUND'S OTHER EVENTS (design:               *)
(*  claude-notes/design/pipes-general.md SS2.2, cut C5b).                *)
(*                                                                       *)
(*  [PipeOutN.pecl'] -- the generic claim between rounds, [popenN] while *)
(*  a round of any number of writers is open -- answers every console    *)
(*  event, as the landed [PipeOut.pecl] does: the log's close and open,  *)
(*  the arm read back, the read, the echo, the byte and the drain.  The  *)
(*  claim-side steps are [GenOut]'s; the open reading's are proved here  *)
(*  ONCE, over any line model ([gcl_pure_o_close] .. [_no_echo],          *)
(*  [lm_good_out_of_stage_open]), and read at [pipes_lm].                 *)
(*                                                                       *)
(*  1. The open reading's pure steps, over any model.                    *)
(*  2. The events at [popenN] and at [pecl'], and the filing of an EMPTY *)
(*     block (no writer wrote: the prompt is the block's first byte,     *)
(*     filed by [GenOut.gcl_step_write_blk]).                             *)
(*  3. THE N = 2 CHECK, continued: the open reading at the landed model  *)
(*     [pipe_lm] IS the landed [PipeOut.pcl_pure_o], and the landed      *)
(*     events' pure cores (the close, the read, the echo's refutation)   *)
(*     are re-derived from section 1's.                                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeHooks.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipesDiscDec.
Require Import PipeOutN.
(* stdpp's list names over the ones the Stdlib import above re-exports *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE OPEN READING'S PURE STEPS, OVER ANY LINE MODEL                *)
(* ===================================================================== *)

Section open_events_pure.
  Context (M : lmodel) (sd : lm_st M).
  Local Notation st so := (gs_state M sd so).

  Lemma gcl_pure_o_E k ho so r pre H :
    gcl_pure_o M sd k ho so r pre H -> gs_E M so = ch_E H.
  Proof using. by intros (_ & _ & _ & _ & _ & HE & _). Qed.

  Lemma gcl_pure_o_arm k ho so r pre H :
    gcl_pure_o M sd k ho so r pre H -> garm_era M k ho H.
  Proof using. by intros (_ & _ & _ & _ & Hera & _). Qed.

  (* the open round's own length law *)
  Lemma lm_blk_open_cs so r pre :
    lm_blk_open M sd so r pre ->
    length (gs_cs M so) = (nlines (snd <$> gs_E M so) - 1)%nat
    /\ rest_of (snd <$> gs_E M so) = [] /\ (snd <$> gs_E M so) <> [].
  Proof using. intros (_ & _ & _ & a & (Hne & Hr & Hq & _) & _). by split_and!. Qed.

  Lemma gcl_pure_o_rd_stage k ho so r pre H :
    gcl_pure_o M sd k ho so r pre H ->
    lm_rd_stage M (gs_ps M so) (gs_cs M so) (st so) (snd <$> gs_E M so).
  Proof using.
    intros (Hout & Hop & _).
    destruct Hout as (_ & _ & _ & Hpsb & Hpin & Hcsb & _).
    destruct (lm_blk_open_cs so r pre Hop) as (Hq & Hr & _).
    rewrite /lm_rd_stage. split_and!; [exact Hpsb | exact Hcsb | exact Hpin |].
    rewrite (ll_nlines_removelast _ Hr) Hq. lia.
  Qed.

  (* ---- the log's CLOSE ---- *)
  Lemma gcl_pure_o_close k ho so r pre H :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    gcl_pure_o M sd k ho so r pre H ->
    gcl_pure_o M sd k ho so r pre (ConsLog.cons_step H ConsLog.EvClose).
  Proof using.
    intros Hok Hev Hecl.
    pose proof (ch_E_close H) as Hclose.
    pose proof (ch_E_close_len H) as Hlen.
    pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
    unfold ConsLog.cons_hist_ok in Hok'. destruct Hok' as [Hlog' _].
    destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; cycle 1.
    { rewrite /ConsLog.cons_step Ha. exact Hecl. }
    destruct Hecl as (Hout & Hop & Hps & Hin & Hera & HE & Hdlok).
    destruct Hin as (_ & Hdsc & Hbts & Hdl & _ & _ & _ & Hall).
    rewrite /garm_era Ha in Hera.
    destruct Hera as (Hdseg & Hboots & _ & _ & _ & Hcsa & _).
    destruct Hev as (a & Ha2 & _ & HK3). rewrite Ha in Ha2.
    injection Ha2 as <-.
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_byte LogEntryDefs.ca_sent
         le_echo le_byte fst snd] in HK3.
    assert (Hj : j = 1%nat) by (apply HK3; exact Hcsa).
    assert (Hech : log_echoed (h, c, take j cs)).
    { rewrite Hcsa Hj. cbn [take]. exact (log_echoed_echo h c). }
    destruct (lm_blk_open_cs so r pre Hop) as (Hqq & Hrr & Hnn).
    rewrite /ConsLog.cons_step Ha in Hlog', Hlen |- *.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm] in Hlog', Hlen |- *.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H ++ [(h, c, take j cs)]))
                   = gs_E M so).
    { rewrite HE -Hclose /ch_E /ConsLog.cons_step Ha.
      cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
      by rewrite app_nil_r. }
    rewrite /gcl_pure_o.
    split_and!.
    - exact Hout.
    - exact Hop.
    - exact Hps.
    - split_and!.
      + exact Hlog'.
      + intros e He. apply elem_of_app in He as [He | He]; [exact (Hdsc e He) |].
        apply elem_of_list_singleton in He as ->. cbn [le_hist fst snd]. exact Hdseg.
      + intros e He. apply elem_of_app in He as [He | He]; [exact (Hbts e He) |].
        apply elem_of_list_singleton in He as ->. cbn [le_hist fst snd]. exact Hboots.
      + rewrite (echoed_snoc_yes _ _ Hech).
        by apply (prefix_app_r _ _ [(le_hist (h, c, take j cs),
                                     le_byte (h, c, take j cs))]).
      + rewrite Hseg. by destruct Hout as (_ & HEi & _).
      + rewrite Hseg. by destruct Hout as (_ & _ & HEb & _).
      + rewrite -(seg_of_snd (echoed _)) Hseg Hqq. lia.
      + apply Forall_app. split; [exact Hall | by rewrite Forall_singleton].
    - exact I.
    - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
      rewrite app_nil_r. by rewrite Hseg.
    - exact Hdlok.
  Qed.

  (* ---- the READ ---- *)
  Lemma gcl_pure_o_read k ho so r pre H (ws : list (list mobs * bv 8)) :
    (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
    gcl_pure_o M sd k ho so r pre H ->
    gcl_pure_o M sd k ho so r pre (ConsLog.cons_step H (ConsLog.EvRead ws)).
  Proof using.
    intros Hpre (Hout & Hop & Hp & Hin & Hera & HE & Hdlok).
    destruct Hin as (Hlog & Hdsc & Hbts & _ & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera
                | by rewrite HE /ch_E |].
    - by split_and!.
    - apply (lm_dl_ok_mono M so (LogEntryDefs.ch_dl H)); [| exact Hdlok].
      rewrite length_app. lia.
  Qed.

  (* ---- the OPEN ---- *)
  Lemma lm_out_pure_o_move (k : nat) (ho h : list mobs) (so : gstage M)
      (acc : list (bv 8)) (L : list log_entry) (dl : list (list mobs * bv 8)) :
    trace_shape h true ->
    obs_boots h = k ->
    (forall e, e ∈ L -> hist_ext (le_hist e) h) ->
    gin_pure M k L dl (gs_cs M so) ->
    seg_of (echoed L) = gs_E M so ->
    (length (gs_E M so) <= length (ins (open_seg h)))%nat ->
    lm_out_pure_o M sd k ho so acc -> lm_out_pure_o M sd k h so acc.
  Proof using.
    intros Hsh Hk Hord Hin Hseg Hle
      (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc & _ & _ & _ & Hnofk & Hf0 & Hfok).
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & _).
    split_and!; [exact Hacc | exact Hidx | exact Hbyte | exact Hpsb | exact Hpin
                | exact Hcsb | exact Hdsc | | exact Hle | | exact Hnofk | exact Hf0
                | exact Hfok].
    - rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed L !! j) as [y |] eqn:Hy; [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
      assert (Hyin : y ∈ echoed L) by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv L y Hyin) as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      + rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
      + rewrite -Hye. cbn [fst]. rewrite (Hstamp e He). by rewrite Hk.
      + exact Hsh.
    - right. exact Hk.
  Qed.

  Lemma gcl_pure_o_open (B : lm_byte_laws M) k ho so r pre H
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input M (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc M h -> trace_shape h true ->
    gcl_pure_o M sd k ho so r pre H ->
    gcl_pure_o M sd k h so r pre (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using.
    intros Hok Hev Hd Hb Hdh Hsh (Hout & Hop & Hp & Hin & _ & HE & Hdlok).
    pose proof Hev as (Hn & Hends & Hecho & Hord & Hwire & HK1f & HK2).
    pose proof (ch_E_open H h c cs Hn) as Hopen.
    assert (HK1 : (length (LogEntryDefs.ch_log H) + 1)%nat = length (ins (open_seg h))).
    { destruct HK1f as (f & Hfl & Hcnt).
      rewrite (lm_flush_lost_zero M h f Hsh Hdh Hfl) Nat.add_0_r in Hcnt.
      by rewrite -ins_obs_ins in Hcnt. }
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = gs_E M so).
    { rewrite HE /ch_E Hn. cbn [ch_arm_E]. by rewrite app_nil_r. }
    assert (Hall : Forall log_echoed (LogEntryDefs.ch_log H))
      by (by destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hq)).
    assert (Hcnt : length (gs_E M so) = (length (ins (open_seg h)) - 1)%nat).
    { rewrite -Hseg seg_of_length (echoed_all_len _ Hall). lia. }
    assert (Hle : (length (gs_E M so) <= length (ins (open_seg h)))%nat) by lia.
    pose proof (lm_out_pure_o_move k ho h so (LogEntryDefs.ch_acc H)
                  (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
                  Hsh Hb Hord Hin Hseg Hle Hout) as Hout'.
    assert (Hpl : forall j x, gs_E M so !! j = Some x -> x.1 `prefix_of` open_seg h).
    { destruct Hout' as (_ & _ & _ & _ & _ & _ & _ & Hpre1 & _).
      intros j x Hx. exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx). }
    assert (Hidx : E_index (gs_E M so)) by (by destruct Hout as (_ & Hq & _)).
    assert (Hbytes : (snd <$> gs_E M so)
                     = take (length (LogEntryDefs.ch_log H)) (ins (open_seg h))).
    { rewrite (E_bytes_of_hist (gs_E M so) (open_seg h) Hidx Hpl Hle).
      by replace (length (gs_E M so)) with (length (LogEntryDefs.ch_log H)) by lia. }
    assert (Hcin : c ∈ ins (open_seg h)).
    { destruct Hends' as [h0 Hh0]. rewrite Hh0 ins_app ins_in.
      apply elem_of_app. right. apply elem_of_list_here. }
    pose proof (lm_disc_drop_byte M B _ c Hd Hcin) as (_ & _ & Hner).
    assert (Hcs : cs = [echo_of c]).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]]; [| exact Hech |]; last first.
      { exfalso. rewrite Hner in Herase. discriminate. }
      exfalso.
      exact (lm_cons_drop_refuted M B h c (LogEntryDefs.ch_log H)
               (LogEntryDefs.ch_dl H) (snd <$> gs_E M so) (gs_w M so)
               HK1 Hall Hdlok Hbytes Hd Hcin (HK2 Hnil)). }
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout' | exact Hop | exact Hp | exact Hin | | | exact Hdlok].
    - rewrite /garm_era. cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
      split_and!; [exact Hd | exact Hb | exact Hdh | exact Hsh | reflexivity
                  | exact Hcs | exact HK1].
    - rewrite HE -Hopen /ConsLog.cons_step /ch_E.
      by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
  Qed.

  (* ---- the block the round owes once its code is filed ---- *)
  Lemma lm_pending_filed ps cs s I a :
    I <> [] -> rest_of I = [] -> length cs = (nlines I - 1)%nat ->
    lm_panic M (lm_dec M a) = false ->
    lm_pending_at M ps (cs ++ [a]) s I
    = lm_cont M (lm_upto M cs s (bodies_of I) (nlines I - 1))
        (lm_of M (bodies_of I !!! (nlines I - 1)%nat)) (lm_dec M a).
  Proof using.
    intros Hne Hr Hq Hnp. pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    assert (Hn : nlines I = S (length cs)) by lia.
    rewrite /lm_pending_at decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
    rewrite /lm_cont_at (lm_blk_snoc_at M cs I a Hn) (lm_blk_snoc_upto M cs s I a Hn)
      Hnp app_nil_r.
    reflexivity.
  Qed.

  (* ---- the DRAIN: F4 at a block whose code is not filed -- the witness
          the existential wants is the round's own code, appended ---- *)
  Lemma lm_good_out_of_stage_open (K : lm_hooks M) (B : lm_byte_laws M)
      (ps cs : list nat) (s : lm_st M) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (a : nat) (seg : list mobs) :
    Forall (fun x => (x < length pro_alts)%nat) ps ->
    lm_alts_pre M s (ins seg) cs ->
    lm_E_disc M E ->
    lm_pro_pin M ps cs (snd <$> E) ->
    lm_blk_at M cs (snd <$> E) s w a ->
    obs_wire Uart0 seg `prefix_of` (lm_D M ps cs s E ++ w) ->
    (snd <$> E) `prefix_of` ins seg ->
    lm_good_out M s seg.
  Proof using.
    intros Hps Hao HE Hpin Hblk Hwire Hinp.
    pose proof Hblk as (Hne & Hr & Hq & Hok0 & Hpan & Hpre).
    pose proof (nlines_pos_of_rest_nil _ Hne Hr) as Hpos.
    assert (Hnl : (nlines (snd <$> E) <= nlines (ins seg))%nat) by (by apply nlines_prefix).
    assert (Hbod : bodies_of (ins seg) !!! (nlines (snd <$> E) - 1)%nat
                   = bodies_of (snd <$> E) !!! (nlines (snd <$> E) - 1)%nat).
    { destruct (bodies_of_prefix (snd <$> E) (ins seg) Hinp) as [z Hz].
      rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hpos |- *; lia]. }
    assert (Hbodj : forall j, (j < nlines (snd <$> E))%nat ->
              bodies_of (ins seg) !!! j = bodies_of (snd <$> E) !!! j).
    { destruct (bodies_of_prefix (snd <$> E) (ins seg) Hinp) as [z Hz].
      intros j Hj. rewrite Hz !list_lookup_total_alt lookup_app_l;
        [reflexivity | rewrite /nlines in Hj; lia]. }
    assert (Hao' : lm_alts_pre M s (ins seg) (cs ++ [a])).
    { apply (lm_alts_pre_snoc M s (ins seg) cs a Hao); [rewrite Hq; lia |].
      rewrite Hq Hbod.
      rewrite (lm_upto_ext M cs cs s (bodies_of (ins seg)) (bodies_of (snd <$> E))
                 (nlines (snd <$> E) - 1) ltac:(intros j _; reflexivity)
                 ltac:(intros j Hj; apply Hbodj; lia)).
      exact Hok0. }
    assert (Hpin' : lm_pro_pin M ps (cs ++ [a]) (snd <$> E)).
    { intros q Hq'. rewrite (lm_pro_idx_app_le M); [by apply Hpin |].
      rewrite (ll_nstarted_rest_nil _ Hr) in Hq'. rewrite Hq. lia. }
    assert (HD : lm_D M ps (cs ++ [a]) s E = lm_D M ps cs s E).
    { symmetry. apply (lm_D_cs_prefix M); [reflexivity | by eexists | exact Hpin |].
      rewrite (ll_nlines_removelast _ Hr) Hq. lia. }
    apply (lm_good_out_of_stage M K B ps (cs ++ [a]) s E w seg Hps Hao').
    - rewrite (ll_nlines_removelast _ Hr) length_app Hq /=. lia.
    - left. rewrite length_app Hq /=. lia.
    - exact HE.
    - exact Hpin'.
    - rewrite /lm_pending (lm_pending_filed ps cs s (snd <$> E) a Hne Hr Hq Hpan).
      exact Hpre.
    - by rewrite HD.
    - exact Hinp.
  Qed.

  (* ---- THE ECHO CANNOT HAPPEN WHILE A ROUND'S BLOCK IS OPEN.  The claim's
          resolution completed with the round's own code is compared with
          the discipline's (the model's determinacy), F2 says the block
          would have to be WHOLE; a non-terminal alternative's whole block
          carries the prompt, and the open block is '$'-free; a terminal
          one's is a mergeable output, which D4 refutes below the input's
          last byte.  The landed [PipeOut.pcl_pure_o_no_echo], once. ---- *)
  Lemma gcl_pure_o_no_echo (L : lm_laws M) (K : lm_hooks M) (B : lm_byte_laws M)
      (h : list mobs) (c : bv 8) (ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (so : gstage M) (r : nat) (pre : list (bv 8)) :
    lm_disc M h ->
    trace_shape h true ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    gcl_pure_o M sd (obs_boots h) ho so r pre CH -> False.
  Proof using.
    intros Hdisc Hsh Hends Hwire Hord HK1 Harm Hopen.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & _).
    destruct Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                      & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & Halle).
    pose proof Hop as (Hreq & Hwp' & Hne' & ao & Hb2 & Hoarm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposn.
    assert (HnS : nlines (snd <$> gs_E M so) = S (length (gs_cs M so))) by lia.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log CH)) = gs_E M so).
    { rewrite HEtie /ch_E Harm ch_arm_E_open app_nil_r. reflexivity. }
    destruct (lm_disc_open_seg M h Hsh Hdisc) as (sdd & Hsdok & Hd').
    pose proof (proj1 Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (lm_disc_seg'_pt_last M sdd (open_seg h) c Hd' Hends')
      as (ps' & cs' & Hok' & Hao' & Hnm' & Hlow').
    assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (gs_E M so)).
    { rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed (LogEntryDefs.ch_log CH) !! j) as [y |] eqn:Hy;
        [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
      assert (Hyin : y ∈ echoed (LogEntryDefs.ch_log CH))
        by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) y Hyin)
        as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      - rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
      - rewrite -Hye. cbn [fst]. exact (Hstamp e He).
      - exact Hsh. }
    assert (Hpl : forall j x, gs_E M so !! j = Some x -> x.1 `prefix_of` open_seg h)
      by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hprefixes Hx)).
    assert (Hoi : length (gs_E M so) = length (echoed (LogEntryDefs.ch_log CH)))
      by (by rewrite -Hseg seg_of_length).
    assert (Hcnt : length (gs_E M so) = (length (ins (open_seg h)) - 1)%nat)
      by (rewrite Hoi (echoed_all_len _ Halle); lia).
    assert (Hbytes : (snd <$> gs_E M so) = take (length (gs_E M so)) (ins (open_seg h)))
      by (apply (E_bytes_of_hist (gs_E M so) (open_seg h) Hidx Hpl); lia).
    assert (HI : removelast (ins (open_seg h)) = (snd <$> gs_E M so)).
    { rewrite Hbytes epu_removelast_take.
      replace (length (ins (open_seg h)) - 1)%nat with (length (gs_E M so)) by lia.
      reflexivity. }
    assert (Hnew' : forall x, x ∈ gs_E M so -> hist_ext x.1 (open_seg h)).
    { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
      destruct (Hidx jj x Hj) as [Hxe Hxlen].
      pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
      apply lookup_lt_Some in Hj.
      split; [exact Hpx |].
      destruct Hpx as [z Hz]. destruct z as [| aa z'].
      - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
      - rewrite Hz length_app /=. lia. }
    assert (Hup : obs_wire Uart0 (open_seg h)
                  `prefix_of` (lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so)
                               ++ gs_w M so))
      by (rewrite -Hacc; exact Hwire).
    (* THE CLAIM'S RESOLUTION, COMPLETED WITH THE ROUND'S OWN CODE *)
    assert (HlenA : length (gs_cs M so ++ [ao]) = nlines (snd <$> gs_E M so))
      by (rewrite length_app /=; lia).
    assert (HaoA : lm_alts_pre M (st so) (snd <$> gs_E M so) (gs_cs M so ++ [ao])).
    { apply (lm_alts_pre_snoc M _ _ (gs_cs M so) ao Hcsb'); [lia |].
      rewrite Hqq. exact Hokao. }
    assert (HpinA : lm_pro_pin M (gs_ps M so) (gs_cs M so ++ [ao]) (snd <$> gs_E M so)).
    { intros q Hq. rewrite (lm_pro_idx_app_le M); [by apply Hpinf |].
      rewrite (ll_nstarted_rest_nil _ Hrr) in Hq. lia. }
    assert (HpendA : lm_pending M (gs_ps M so) (gs_cs M so ++ [ao]) (st so) (gs_E M so)
                     = lm_cont M (lm_upto M (gs_cs M so) (st so) (bodies_of (snd <$> gs_E M so))
                                    (nlines (snd <$> gs_E M so) - 1))
                         (lm_of M (bodies_of (snd <$> gs_E M so)
                                     !!! (nlines (snd <$> gs_E M so) - 1)%nat))
                         (lm_dec M ao)).
    { rewrite /lm_pending. exact (lm_pending_filed _ _ _ _ ao Hnn Hrr Hqq Hpanao). }
    assert (HwpreA : gs_w M so `prefix_of`
                       lm_pending M (gs_ps M so) (gs_cs M so ++ [ao]) (st so) (gs_E M so)).
    { rewrite HpendA Hwp'. exact Hprefao. }
    assert (HrlA : (nlines (removelast (snd <$> gs_E M so)) <= length (gs_cs M so ++ [ao]))%nat).
    { rewrite (ll_nlines_removelast _ Hrr) HlenA. lia. }
    destruct (lm_stage_sess_pad M K B (gs_ps M so) (gs_cs M so ++ [ao]) (st so) (gs_E M so)
                (gs_w M so) HaoA HrlA ltac:(left; lia) Hbyte HpinA HwpreA)
      as (HokP & HpinP & HDP & HwP & HstP).
    assert (HpadA : lm_alts_pad M K (snd <$> gs_E M so) (gs_cs M so ++ [ao])
                    = gs_cs M so ++ [ao]).
    { rewrite /lm_alts_pad drop_ge; [by rewrite fmap_nil app_nil_r |].
      rewrite HlenA /nlines. lia. }
    rewrite HpadA in HokP HpinP HDP HwP HstP.
    assert (HDA : lm_D M (gs_ps M so) (gs_cs M so ++ [ao]) (st so) (gs_E M so)
                  = lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so)).
    { symmetry. apply (lm_D_cs_prefix M); [reflexivity | by eexists | exact Hpinf |].
      rewrite (ll_nlines_removelast _ Hrr) Hqq. lia. }
    assert (Hdi1 : lm_disc_input M (done_of (removelast (ins (open_seg h))))).
    { apply (lm_disc_input_prefix M B _ (ins (open_seg h))); [| exact Hdseg].
      etrans; [apply done_of_prefix | apply gop_removelast_prefix]. }
    assert (Hbelow : lm_sess M ps' cs' sdd (done_of (removelast (ins (open_seg h))))
                     `prefix_of` lm_sess M (gs_ps M so) (gs_cs M so ++ [ao]) (st so)
                                   (snd <$> gs_E M so)).
    { etrans; [exact Hlow' |]. etrans; [exact Hup |]. rewrite -HDA. exact HstP. }
    assert (HnI' : nlines (done_of (removelast (ins (open_seg h)))) = nlines (snd <$> gs_E M so))
      by (rewrite nlines_done HI; reflexivity).
    (* D4's claim side: the filed rounds are never terminal, the open one
       is the input's last line *)
    assert (Hd4c : forall i, (i < nlines (done_of (removelast (ins (open_seg h)))))%nat ->
              lm_term M (lm_at M (gs_cs M so ++ [ao]) i) = true ->
              S i = nlines (snd <$> gs_E M so) /\ rest_of (snd <$> gs_E M so) = []).
    { intros i Hi Ht. rewrite HnI' in Hi. split; [| exact Hrr].
      destruct (decide (i < length (gs_cs M so))%nat) as [Hlt | Hge]; [exfalso | lia].
      revert Ht. rewrite /lm_at list_lookup_total_alt lookup_app_l; [| lia].
      rewrite -list_lookup_total_alt.
      destruct (lookup_lt_is_Some_2 (gs_cs M so) i Hlt) as [a Ha].
      rewrite (list_lookup_total_correct _ _ _ Ha).
      by rewrite (Forall_lookup_1 _ _ _ _ Hnofk Ha). }
    destruct (lm_sess_prefix_det M L (gs_ps M so) ps' (gs_cs M so ++ [ao]) cs' (st so) sdd
                (done_of (removelast (ins (open_seg h)))) (snd <$> gs_E M so)
                Hpsb Hok' HokP Hao' HpinP Hbyte Hdi1 Hfok0 Hsdok Hd4c Hnm' Hbelow)
      as (_ & _ & Heq & Hconts).
    assert (Hlow : lm_sess M (gs_ps M so) (gs_cs M so ++ [ao]) (st so)
                     (done_of (removelast (ins (open_seg h))))
                   `prefix_of` obs_wire Uart0 (open_seg h))
      by (rewrite -Heq; exact Hlow').
    assert (HupP : obs_wire Uart0 (open_seg h)
                   `prefix_of` (lm_D M (gs_ps M so) (gs_cs M so ++ [ao]) (st so) (gs_E M so)
                                ++ gs_w M so))
      by (rewrite HDA; exact Hup).
    pose proof (lm_next_input_of_complete M B (gs_ps M so) (gs_cs M so ++ [ao]) (st so)
                  (gs_E M so) (gs_w M so) (obs_wire Uart0 (open_seg h)) (open_seg h) c
                  (length (ins (open_seg h)))
                  Hbyte Hidx Hnew' Hends' eq_refl ltac:(lia) HwP
                  ltac:(rewrite -ll_removelast_take; exact Hlow) HupP) as HweqP.
    (* ...so the block would have to be WHOLE *)
    rewrite HpendA in HweqP.
    destruct Hoarm as [[Hfk Hnd] | Hfk].
    - (* NON-TERMINAL: the whole block carries the prompt *)
      destruct (lmh_cont_prompt K
                  (lm_upto M (gs_cs M so) (st so) (bodies_of (snd <$> gs_E M so))
                     (nlines (snd <$> gs_E M so) - 1)) _ _ Hokao Hpanao Hfk) as [u Hu].
      rewrite Hu Hwp' in HweqP. rewrite HweqP in Hnd.
      pose proof (lb_dollar_at u []) as Hd. rewrite app_nil_r in Hd.
      apply (nodollar_prompt_head (Forall_lookup_1 _ _ _ _ Hnd Hd)).
    - (* TERMINAL: the discipline read the round's bytes too, and a
         mergeable output below the input's last byte is D4's *)
      assert (Hi0 : (nlines (snd <$> gs_E M so) - 1
                     < nlines (done_of (removelast (ins (open_seg h)))))%nat)
        by (rewrite HnI'; lia).
      apply (Hnm' _ Hi0).
      + rewrite bodies_of_done HI. exact (lml_term_st L _ _ _ Hokao Hfk _).
      + pose proof (Hconts _ Hi0) as Hc0.
        rewrite (lmN_cont_at_nopanic M (gs_ps M so) (gs_cs M so ++ [ao]) (st so)) in Hc0;
          last first.
        { rewrite (lm_blk_snoc_at M (gs_cs M so) (snd <$> gs_E M so) ao HnS). exact Hpanao. }
        rewrite (lm_blk_snoc_at M (gs_cs M so) (snd <$> gs_E M so) ao HnS)
          (lm_blk_snoc_upto M (gs_cs M so) (st so) (snd <$> gs_E M so) ao HnS) in Hc0.
        rewrite /lm_cont_at in Hc0.
        apply (lml_merge_prefix L _
                 (lm_cont M (lm_upto M (gs_cs M so) (st so) (bodies_of (snd <$> gs_E M so))
                               (nlines (snd <$> gs_E M so) - 1))
                    (lm_of M (bodies_of (snd <$> gs_E M so)
                                !!! (nlines (snd <$> gs_E M so) - 1)%nat))
                    (lm_dec M ao))).
        * rewrite -Hc0. by apply prefix_app_r.
        * assert (Hstn : lm_st_ok M (lm_upto M (gs_cs M so) (st so)
                                       (bodies_of (snd <$> gs_E M so))
                                       (nlines (snd <$> gs_E M so) - 1))).
          { apply (lm_upto_st_ok M L); [exact Hfok0 | |].
            - intros i Hi. apply (lml_body_line L), (lm_disc_input_at M _ i Hbyte). lia.
            - intros i Hi. apply (lm_alts_pre_at M _ _ _ i Hcsb'). lia. }
          exact (lml_term_merge L _ _ _ Hstn Hokao Hfk).
  Qed.
End open_events_pure.

(* ===================================================================== *)
(*  2.  THE EVENTS AT [popenN] AND AT [pecl']                             *)
(* ===================================================================== *)

Section pipes_events.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Notation T := (echo_taint γ).
  Context (fc : bytes -> option bytes) (adm : pline' -> bool).
  Context (Lw : lm_laws (pipes_lm fc adm)).
  Local Notation PM := (pipes_lm fc adm).
  Local Notation PB := (pipes_lm_byte_laws fc adm).
  Local Notation K := (pipes_hooks fc adm).
  Local Notation PO := (popenN g fc adm).
  Local Notation PC := (pecl' g fc adm Lw).
  Local Notation GC := (gcl PM (pipesN_cparams g fc adm Lw) tt (pipesN_wa g fc adm Lw)).

  Lemma pecl'_gen (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    PC k ho H ⊣⊢ GC k ho H ∨ PO k ho H.
  Proof using . done. Qed.

  Lemma cs_lb_weakenN (v : era_pins) (l l' : list nat) :
    l' `prefix_of` l -> cs_lb v l -∗ cs_lb v l'.
  Proof using .
    intros Hp. rewrite /cs_lb. iIntros "H".
    iApply (own_mono with "H"). by apply mono_list_lb_mono.
  Qed.

  (* ---- FILING THE LOG ENTRY, AND OPENING ONE, TAKE NOTHING ---- *)
  Lemma popenN_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    PO k ho H -∗ PO k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. iIntros "Hp".
    iDestruct "Hp" as (v w so r gb pre tm)
      "(Hpin & Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE".
    rewrite ch_dl_close. iFrame "Hdl Hdll". iPureIntro.
    exact (gcl_pure_o_close PM tt k ho so r pre H Hok Hev Hpure).
  Qed.

  Lemma popenN_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input PM (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc PM h -> trace_shape h true ->
    PO k ho H -∗ PO k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh. iIntros "Hp".
    iDestruct "Hp" as (v w so r gb pre tm)
      "(Hpin & Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, w, so, r, gb, pre, tm. iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. iFrame "Hdl Hdll".
    iPureIntro. exact (gcl_pure_o_open PM tt PB k ho so r pre H h c cs Hok Hev Hd Hb Hdh Hsh Hpure).
  Qed.

  Lemma popenN_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    PO k ho CH -∗ PO k ho CH ∗ ⌜garm_era PM k ho CH⌝.
  Proof using .
    iIntros "Hp".
    iDestruct "Hp" as (v w so r gb pre tm)
      "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iSplitL.
    - iExists v, w, so, r, gb, pre, tm.
      iFrame "Hpin Hpera Hblk Hcur Hrb Htn Hcs Hps HE Hdl Hdll". by iPureIntro.
    - iPureIntro. exact (gcl_pure_o_arm PM tt k ho so r pre CH Hall).
  Qed.

  Lemma pecl'_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    PC k ho H -∗ PC k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite !pecl'_gen. iIntros "[Hc | Hc]".
    - iLeft. by iApply (gcl_close with "Hc").
    - iRight. by iApply (popenN_close with "Hc").
  Qed.

  Lemma pecl'_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input PM (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc PM h -> trace_shape h true ->
    PC k ho H -∗ PC k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hok Hev Hd Hb Hdh Hsh. rewrite !pecl'_gen. iIntros "[Hc | Hc]".
    - iLeft. iApply (gcl_open with "Hc"); first [exact PB | done].
    - iRight. by iApply (popenN_open with "Hc").
  Qed.

  (* THE SUPPLY'S LAW: a tainted era answers any event out of its taint *)
  Lemma pecl'_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ PC k ho H ==∗ PC k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. by iApply (pecl'_taint with "HT"). Qed.

  Lemma pecl'_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    PC k ho CH -∗ PC k ho CH ∗ (T ∨ ⌜garm_era PM k ho CH⌝).
  Proof using .
    rewrite !pecl'_gen. iIntros "[Hc | Hc]".
    - iDestruct (gcl_arm with "Hc") as "[Hc Ha]". iSplitL "Hc"; [by iLeft | done].
    - iDestruct (popenN_arm with "Hc") as "[Hc Ha]". iSplitL "Hc"; [by iRight |].
      by iRight.
  Qed.

  (* ---- THE READ ---- *)

  (* the reader's receipt: [GenOut.gcl_step_read]'s, at the pipeline *)
  Definition rd_retN (k : nat) (v : era_pins) (n : nat) (CH : LogEntryDefs.cons_hist)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((T ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
       ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
       ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
       ∗ ⌜lm_E_disc PM (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
       ∗ ⌜forall x : list mobs * bv 8,
            x ∈ LogEntryDefs.ch_dl CH ++ ws -> obs_boots x.1 = k⌝
       ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
       ∗ ⌜lm_disc_input PM (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
       ∗ (⌜ws = []⌝
          ∨ ∃ (cs0 ps0 : list nat) (s0 : lm_st PM),
              cs_lb v cs0 ∗ ps_lb v ps0 ∗ gcW (pipesN_cparams g fc adm Lw) k s0
              ∗ ⌜(nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws)) <= S (length cs0))%nat⌝
              ∗ turn_lb v (length (lm_proc_before PM ps0 cs0 s0
                             (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
              ∗ ⌜lm_rd_stage PM ps0 cs0 s0 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝))%I.

  Lemma popenN_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ PO k ho CH ==∗
      PO k ho (ConsLog.cons_step CH (ConsLog.EvRead ws)) ∗ rd_retN k v n CH ws.
  Proof using .
    intros Hread. iIntros "#Hpinr Hdlr Hp".
    iDestruct "Hp" as (v2 w so r gb pre tm)
      "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
    iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hin as Hin2.
    destruct Hin2 as (_ & _ & Hbt & _ & Hidx & Hbyte & Hbnd0 & _).
    destruct (gin_read_pure PM PB k (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH)
                ws (gs_cs PM so) Hread Hin) as (Hpref & Hp' & Hbnd').
    assert (Hst : gs_state PM tt so = tt) by (by destruct (gs_state PM tt so)).
    assert (Hboots : forall x : list mobs * bv 8,
              x ∈ LogEntryDefs.ch_dl CH ++ ws -> obs_boots x.1 = k).
    { intros x Hx.
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) x
                  (elem_of_prefix _ _ _ Hx Hpref)) as (e & He & _ & <-).
      exact (Hbt e He). }
    assert (HEpre : (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                    `prefix_of` (snd <$> gs_E PM so)).
    { rewrite (gcl_pure_o_E PM tt k ho so r pre CH Hall0) /ch_E.
      etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
      rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log CH))).
      apply epu_fmap_prefix. by apply prefix_app_r. }
    assert (Hdi : lm_disc_input PM (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    { apply (lm_disc_input_prefix PM PB _ (snd <$> gs_E PM so) HEpre).
      by destruct Hpure as (_ & _ & Hd & _). }
    pose proof (gcl_pure_o_rd_stage PM tt k ho so r pre CH Hall0) as Hrd.
    pose proof Hrd as (Hpsb & Hcsb' & Hpinf & Hbd).
    (* the reader's own list: the claim's, cut to its own line count *)
    set (Iw := (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    set (q := nlines Iw).
    set (csq := take q (gs_cs PM so)).
    assert (Hqle : (nlines (removelast Iw) <= length csq)%nat).
    { rewrite /csq length_take.
      assert (H1 : (nlines (removelast Iw) <= q)%nat)
        by (apply nlines_prefix, gop_removelast_prefix).
      assert (H2 : (nlines (removelast Iw) <= length (gs_cs PM so))%nat).
      { etrans; [| exact Hbd].
        apply nlines_prefix, pop_prefix_removelast, HEpre. }
      lia. }
    assert (Hagree : forall j, (j < q)%nat -> csq !!! j = gs_cs PM so !!! j).
    { intros j Hj. rewrite /csq !list_lookup_total_alt.
      destruct (decide (j < length (gs_cs PM so))%nat) as [Hl | Hl].
      - rewrite lookup_take; [done | lia].
      - rewrite (lookup_ge_None_2 (gs_cs PM so) j ltac:(lia)).
        rewrite (lookup_ge_None_2 (take q (gs_cs PM so)) j);
          [done | rewrite length_take; lia]. }
    assert (Hqbnd : (q <= S (length csq))%nat).
    { rewrite /csq length_take.
      destruct (decide (q <= length (gs_cs PM so))%nat) as [Hl | Hl]; [lia |].
      rewrite /q /Iw. lia. }
    assert (Hpbq : lm_proc_before PM (gs_ps PM so) csq tt Iw
                   = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt Iw).
    { apply (lm_proc_before_ext PM). intros J HJ Hne.
      apply (lm_pending_at_cs_ext PM (gs_ps PM so) csq (gs_cs PM so) tt J).
      - rewrite /csq. apply prefix_take.
      - etrans; [| exact Hqle].
        apply nlines_prefix, (pop_prefix_of_removelast J Iw HJ Hne). }
    assert (Hrdq : lm_rd_stage PM (gs_ps PM so) csq tt Iw).
    { rewrite /lm_rd_stage. split_and!; [exact Hpsb | | | exact Hqle].
      - intros i c Hc.
        assert (Hci : gs_cs PM so !! i = Some c)
          by (rewrite /csq in Hc; by apply lookup_take_Some in Hc as [? _]).
        assert (Hiq : (i < q)%nat).
        { apply lookup_lt_Some in Hc. rewrite /csq length_take in Hc. lia. }
        destruct (Hcsb' i c Hci) as [_ Hok].
        split; [exact Hiq |].
        destruct (bodies_of_prefix Iw (snd <$> gs_E PM so) HEpre) as [z Hz].
        rewrite Hz !list_lookup_total_alt lookup_app_l in Hok;
          [| rewrite /q /nlines in Hiq; lia].
        rewrite -!list_lookup_total_alt in Hok. exact Hok.
      - intros q' Hq'.
        assert (Hq'q : (q' <= q)%nat).
        { pose proof (nstarted_le_S Iw). rewrite /q. lia. }
        rewrite (lm_pro_idx_ext PM csq (gs_cs PM so) q
                   ltac:(intros j Hj; apply Hagree; lia) q' Hq'q).
        apply Hpinf. pose proof (nstarted_prefix Iw (snd <$> gs_E PM so) HEpre).
        lia. }
    iDestruct (pcs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (cs_lb_weakenN v (gs_cs PM so) csq
                 ltac:(rewrite /csq; apply prefix_take) with "Hcslb") as "#Hcslbq".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iDestruct (turn_lb_get with "Hta") as "#Htlb".
    iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n
            (n + length ws)%nat with "Hdl Hdlr") as "[Hdl Hdlr]".
    iMod (dl_list_auth_grow v (LogEntryDefs.ch_dl CH) ws with "Hdll")
      as "[Hdll #Hdllb]".
    iModIntro. iSplitL "Hta Hcs Hps HE Hdl Hdll Hblk Hcur Hrb".
    { iExists v, w, so, r, gb, pre, tm.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite length_app Hdleq.
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro. exact (gcl_pure_o_read PM tt k ho so r pre CH ws Hpref Hall0). }
    rewrite /rd_retN. iRight. iFrame "Hdlr".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; exact Hboots |].
    iSplitR.
    { iApply (inp_lb_of_dl_lb v (LogEntryDefs.ch_dl CH ++ ws) _ (reflexivity _)).
      iExact "Hdllb". }
    iSplitR; [by iPureIntro |].
    destruct (decide (ws = [])) as [-> | Hne]; [by iLeft |].
    iRight. iExists csq, (gs_ps PM so), tt. iFrame "Hcslbq Hpslb".
    iSplitR; [done |].
    iSplitR; [iPureIntro; exact Hqbnd |].
    iSplitR.
    { assert (Hle2 : (length (lm_proc_before PM (gs_ps PM so) csq tt Iw)
                      <= lm_pcount PM (gs_ps PM so) (gs_cs PM so) (gs_state PM tt so)
                           (gs_E PM so) (gs_w PM so))%nat).
      { rewrite /lm_pcount Hst Hpbq.
        pose proof (prefix_length _ _
                      (lm_proc_before_prefix PM (gs_ps PM so) (gs_cs PM so)
                         tt Iw (snd <$> gs_E PM so) HEpre)) as Hlp.
        lia. }
      iApply (turn_lb_weaken with "Htlb"). exact Hle2. }
    iPureIntro. exact Hrdq.
  Qed.

  Lemma pecl'_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ PC k ho CH ==∗
      PC k ho (ConsLog.cons_step CH (ConsLog.EvRead ws)) ∗ rd_retN k v n CH ws.
  Proof using .
    intros Hread. iIntros "#Hpin Hdl Hcl". rewrite !pecl'_gen.
    iDestruct "Hcl" as "[Hc | Hc]".
    - iMod (gcl_step_read PM (pipesN_cparams g fc adm Lw) PB tt (pipesN_wa g fc adm Lw)
              with "Hpin Hdl Hc") as "[Hc Hr]"; [exact Hread |].
      iModIntro. iSplitL "Hc"; [by iLeft |]. rewrite /rd_retN. iExact "Hr".
    - iMod (popenN_step_read with "Hpin Hdl Hc") as "[Hc Hr]"; [exact Hread |].
      iModIntro. iFrame "Hr". by iRight.
  Qed.

  (* ---- THE ECHO: refuted while a round is open ---- *)
  Lemma pecl'_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    lm_disc PM h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    PC k ho CH ==∗ PC k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using .
    intros Hdisc Hsh Hk Hends Hwire Hord HK1 Harm. rewrite !pecl'_gen.
    iIntros "[Hc | Hp]".
    - iMod (gcl_step_echo PM (pipesN_cparams g fc adm Lw) PB tt (pipesN_wa g fc adm Lw)
              with "Hc") as "Hc"; try done.
      iModIntro. by iLeft.
    - iDestruct "Hp" as (v w so r gb pre tm)
        "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hopen)".
      subst k. by destruct (gcl_pure_o_no_echo PM tt Lw K PB h c ho CH so r pre
                              Hdisc Hsh Hends Hwire Hord HK1 Harm Hopen).
  Qed.

  (* ...AND THE BYTE, which takes NOTHING *)
  Lemma pecl'_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    PC k ho CH ==∗ PC k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using .
    intros Hok Hev. iIntros "Hcl".
    iDestruct (pecl'_arm with "Hcl") as "[Hcl [#HT | %Hera]]".
    { iModIntro. by iApply (pecl'_taint with "HT"). }
    pose proof Hev as Hev0.
    destruct Hev0 as (a & Ha & Hlk). destruct a as [[[ha ca] csa] ja].
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Hlk.
    rewrite /garm_era Ha in Hera.
    destruct Hera as (Hdseg & Hbts & Hdisc & Hsh & Hw & _ & HK1).
    subst ha.
    destruct Hok as [_ Harm]. rewrite Ha in Harm.
    cbn [from_option LogEntryDefs.ca_hist LogEntryDefs.ca_byte
         LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Harm.
    destruct Harm as (Hends & Hecho & _ & Hord & Hwire).
    assert (Hshape : csa = [echo_of ca] /\ ja = 0%nat /\ b = echo_of ca).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]].
      - exfalso. rewrite Hnil in Hlk. by rewrite lookup_nil in Hlk.
      - rewrite Hech in Hlk.
        destruct ja as [| j']; cbn in Hlk; [| by rewrite lookup_nil in Hlk].
        injection Hlk as <-. by split_and!.
      - exfalso.
        assert (Hcin : ca ∈ ins (open_seg ho)).
        { destruct (open_seg_ends_in ho ca Hends) as [h0 Hh0].
          rewrite Hh0 ins_app ins_in.
          apply elem_of_app. right. apply elem_of_list_here. }
        destruct (lm_disc_drop_byte PM PB _ ca Hdseg Hcin) as (_ & _ & Hno).
        rewrite Hno in Herase. discriminate. }
    destruct Hshape as (Hcsa & Hja & Hb).
    subst b. rewrite Hcsa Hja in Ha.
    iApply (pecl'_step_echo k ho ca ho CH Hdisc Hsh Hbts Hends Hwire Hord HK1 Ha
              with "Hcl").
  Qed.

  (* ---- THE DRAIN: F4 at an unfiled block, its witness the round's own
          code ---- *)
  Lemma popenN_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    PO k ho CH -∗ PO k ho CH ∗ ⌜lm_good_out PM tt seg⌝.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire. subst k.
    iIntros "Hp".
    iDestruct "Hp" as (v w so r gb pre tm)
      "(#Hpin & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hpo)".
    pose proof (proj1 Hpo)
      as (Hacc & Hidx & Hbyte & Hpsb & Hpinf & Hcs' & Hdsc & Hpre1 & Hpre2 & Hpre3
          & Hnofk & Hf0n & Hfok0).
    iSplitL "Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
    { iExists v, w, so, r, gb, pre, tm.
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll". by iPureIntro. }
    iPureIntro.
    assert (Hbytes : (snd <$> gs_E PM so) `prefix_of` ins seg).
    { destruct Hpre3 as [HEnil | Hbo].
      - rewrite HEnil fmap_nil. apply prefix_nil.
      - assert (Hpl : forall j x, gs_E PM so !! j = Some x ->
                        x.1 `prefix_of` open_seg ho)
          by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
        rewrite (E_bytes_of_hist (gs_E PM so) (open_seg ho) Hidx Hpl Hpre2).
        etrans; [apply prefix_take |].
        rewrite Hins. apply ins_prefix_of, open_seg_prefix_boots;
          [exact Hpre | by rewrite Hbo | exact Hsh]. }
    destruct Hpo as (_ & Hop & _).
    pose proof Hop as (_ & Hwp' & _ & ao & Hb2 & _).
    assert (Hst : gs_state PM tt so = tt) by (by destruct (gs_state PM tt so)).
    rewrite -{1}Hst.
    apply (lm_good_out_of_stage_open PM K PB (gs_ps PM so) (gs_cs PM so)
             (gs_state PM tt so) (gs_E PM so) (gs_w PM so) ao seg Hpsb).
    - apply (lm_alts_pre_mono PM _ (snd <$> gs_E PM so)); [exact Hbytes | exact Hcs'].
    - exact Hbyte.
    - exact Hpinf.
    - rewrite Hwp'. exact Hb2.
    - rewrite -Hacc. exact Hwire.
    - exact Hbytes.
  Qed.

  Lemma pecl'_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    PC k ho CH -∗ PC k ho CH ∗ (T ∨ ⌜lm_good_out PM tt seg⌝).
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. rewrite !pecl'_gen. iIntros "[Hc | Hc]".
    - iDestruct (gcl_drain PM (pipesN_cparams g fc adm Lw) PB tt (pipesN_wa g fc adm Lw)
                   k h ho CH seg Hsh Hk Hpre Hins Hwire Hne with "Hc") as "[Hc Hd]".
      iSplitL "Hc"; [by iLeft |].
      iDestruct "Hd" as "[#HT | (%s0 & %Hgo & _)]"; [by iLeft |].
      iRight. iPureIntro. by destruct s0.
    - iDestruct (popenN_drain with "Hc") as "[Hc %Hgo]"; try done.
      iSplitL "Hc"; [by iRight |]. by iRight.
  Qed.

  (* ---- FILING AN EMPTY BLOCK: no writer wrote, so the prompt is the
          block's first byte, and the claim -- between rounds -- files the
          round at [PLRun []] by [GenOut.gcl_step_write_blk] (an open
          round would have written a byte, and the turn refutes it) ---- *)
  Lemma pwc_blkN_file_empty (v : era_pins) (I : list (bv 8)) (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) (b : bv 8) :
    adm (lineN fc adm I) = true -> line_blocks fc (lineN fc adm I) [] ->
    b = u_prompt !!! 0%nat ->
    pwc_blkN g fc adm v I k [] false -∗ PC k ho H ==∗
      PC k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (P : nat),
            ⌜wr_blkN fc adm ps cs I P⌝ ∗ turn v (S P)
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [plalt_code (PLRun [])]) ∗ inp_lb v I) ∨ T).
  Proof using .
    intros Ha Hbl Hbv. iIntros "Hpw Hcl".
    iDestruct "Hpw" as "[Hx | #HT]"; last first.
    { iModIntro. iSplitR; [by iApply (pecl'_taint with "HT") | by iRight]. }
    iDestruct "Hx" as (ps cs P) "(%Hw & #Hpin & Htn & #Hps & #Hcs & _ & #HE)".
    pose proof Hw as ((Hpp & Hr & Hn & HP) & _).
    assert (HneI : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    replace (P + length (@nil (bv 8)))%nat with P by (cbn [length]; lia).
    rewrite pecl'_gen. iDestruct "Hcl" as "[Hc | Hp]"; last first.
    { (* AN OPEN ROUND has already written a byte: the turn refutes it *)
      iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs2 & Hps2 & HE2 & Hdl & Hdll & %Hopen)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Htn Hta") as %HP2.
      iDestruct (pcs_lb_prefix with "Hcs2 Hcs") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps2 Hps") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll HE") as %HI0dl.
      assert (HI0 : I `prefix_of` (snd <$> gs_E PM so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E PM tt _ _ _ _ _ _ Hopen)]. }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _).
      assert (Hst : gs_state PM tt so = tt) by (by destruct (gs_state PM tt so)).
      rewrite Hst in HP2.
      assert (Hs2 : lm_proc_before PM ps cs tt I
                    = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt I).
      { apply (lm_proc_before_cs_prefix PM ps (gs_ps PM so) cs (gs_cs PM so) tt I
                 Hpsp Hcsp Hpp).
        rewrite (ll_nlines_removelast I Hr). lia. }
      pose proof (prefix_length _ _
        (lm_proc_before_prefix PM (gs_ps PM so) (gs_cs PM so) tt I
           (snd <$> gs_E PM so) HI0)) as Hle2.
      assert (Hwne : (1 <= length (gs_w PM so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP2. rewrite HP Hs2 in HP2.
      exfalso. lia. }
    assert (Hok : lm_ok PM tt (lm_of PM (bodies_of I !!! (nlines I - 1)%nat))
                    (lm_dec PM (plalt_code (PLRun [])))).
    { cbn [pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. right.
      split; [exact Ha | exact Hbl]. }
    assert (Hterm : lm_term PM (lm_dec PM (plalt_code (PLRun []))) = false).
    { cbn [pipes_lm lm_term lm_dec]. by rewrite plalt_of_code. }
    assert (Hhead : lm_cont PM (lm_upto PM cs tt (bodies_of I) (nlines I - 1))
                      (lm_of PM (bodies_of I !!! (nlines I - 1)%nat))
                      (lm_dec PM (plalt_code (PLRun []))) !! 0%nat = Some b).
    { rewrite Hbv. cbn [pipes_lm lm_cont lm_dec]. rewrite plalt_of_code.
      vm_compute. reflexivity. }
    iAssert (gcW (pipesN_cparams g fc adm Lw) k tt) as "HW"; [done |].
    iMod (gcl_step_write_blk PM (pipesN_cparams g fc adm Lw) PB tt (pipesN_wa g fc adm Lw)
            k v P (plalt_code (PLRun [])) b ps cs tt I ho H HneI Hr ltac:(lia) Hpp HP
            Hok Hterm Hhead
            with "Hpin Htn Hps Hcs HE HW Hc") as "[Hc Hret]".
    iModIntro. iSplitL "Hc"; [by iLeft |].
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _ & _) | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs' HE". by iPureIntro.
  Qed.
End pipes_events.

(* ===================================================================== *)
(*  2b.  AT THE PIPELINE APPLICATION'S MODEL                              *)
(*                                                                       *)
(*  [PipesDisc.pipes_lmE] (every echo pipeline, no [cat f]; owner ruling *)
(*  2026-09-24) with its laws [pipes_lm_echo_laws] and hooks             *)
(*  [PipesDiscDec.pipes_hooksE]: the claim every lemma above is stated   *)
(*  over, at the application's parameters.                               *)
(* ===================================================================== *)
Definition peclE {Σ : gFunctors} `{!echoOutG Σ, !pipeOutG Σ} (g : pipe_gn)
    : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ :=
  pecl' g (fun _ => None) adm_echo pipes_lm_echo_laws.

(* ===================================================================== *)
(*  3.  THE N = 2 CHECK, CONTINUED                                        *)
(*                                                                       *)
(*  The open reading at the landed model [pipe_lm] IS the landed         *)
(*  [PipeOut.pcl_pure_o] ([pcl_pure_o_lm]), and the landed events' pure  *)
(*  cores -- the close, the read, the open, the echo's refutation and    *)
(*  the drain's F4 -- are re-derived, statement for statement, from      *)
(*  section 1's generic ones.  The landed [popen] ITSELF is not           *)
(*  re-derivable at [pipes_lm .. adm1]: its choice-list ghost [pcs]       *)
(*  holds [PipeDisc.palt_code]s and [popenN]'s holds                      *)
(*  [PipesDisc.plalt_code]s, related only by [PipesDisc.corr]/[cs_to],    *)
(*  and a mono-list authority cannot be renamed under the writers' lower *)
(*  bounds.  So the C8 bridge is at the PURE level, at the model the     *)
(*  application is born at: the discipline in ([disc_p_disc_ps]), the    *)
(*  cycle conclusion out ([good_out_ps_good_out_p], with the lines'       *)
(*  admission from [lm_disc_input]), and no ghost translation.           *)
(* ===================================================================== *)

Lemma pout_pure_o_lm (k : nat) (ho : list mobs) (so : postage) (acc : list (bv 8)) :
  pout_pure_o k ho so acc <-> lm_out_pure_o pipe_lm tt k ho (pstage_g so) acc.
Proof using.
  rewrite /pout_pure_o /lm_out_pure_o /pstage_g /cs_nofork /=.
  set (st := gs_state pipe_lm tt _).
  rewrite (D_p_lm _ _ st).
  split.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    split_and!; try done; try (by apply pro_pin_p_lm); by case_decide.
  - intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _ & _).
    split_and!; try done; by apply pro_pin_p_lm.
Qed.

Lemma pblk_open_lm (so : postage) (r : nat) (pre : list (bv 8)) :
  pblk_open so r pre <-> lm_blk_open pipe_lm tt (pstage_g so) r pre.
Proof using. split; intros H; exact H. Qed.

(* THE OPEN READING AT THE LANDED MODEL IS THE LANDED ONE *)
Lemma pcl_pure_o_lm (k : nat) (ho : list mobs) (so : postage) (r : nat)
    (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  pcl_pure_o k ho so r pre H <-> gcl_pure_o pipe_lm tt k ho (pstage_g so) r pre H.
Proof using.
  rewrite /pcl_pure_o /gcl_pure_o.
  rewrite pout_pure_o_lm pblk_open_lm ps_len_ok_p_lm pein_pure_lm ch_arm_era_p_lm dl_ok_lm.
  done.
Qed.

Theorem pcl_pure_o_close_N (k : nat) (ho : list mobs) (so : postage) (r : nat)
    (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H ConsLog.EvClose ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k ho so r pre (ConsLog.cons_step H ConsLog.EvClose).
Proof using.
  rewrite !pcl_pure_o_lm. exact (gcl_pure_o_close pipe_lm tt k ho (pstage_g so) r pre H).
Qed.

Theorem pcl_pure_o_read_N (k : nat) (ho : list mobs) (so : postage) (r : nat)
    (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
  (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k ho so r pre (ConsLog.cons_step H (ConsLog.EvRead ws)).
Proof using.
  rewrite !pcl_pure_o_lm. exact (gcl_pure_o_read pipe_lm tt k ho (pstage_g so) r pre H ws).
Qed.

Theorem pcl_pure_o_open_N (k : nat) (ho : list mobs) (so : postage) (r : nat)
    (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) (h : list mobs) (c : bv 8)
    (cs : list (bv 8)) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
  disc_seg_p (open_seg h) -> obs_boots h = k ->
  disc_p h -> trace_shape h true ->
  pcl_pure_o k ho so r pre H ->
  pcl_pure_o k h so r pre (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
Proof using.
  intros Hok Hev Hd Hb Hdh Hsh. rewrite !pcl_pure_o_lm.
  apply (gcl_pure_o_open pipe_lm tt pipe_lm_byte_laws k ho (pstage_g so) r pre H h c cs
           Hok Hev); [| exact Hb | by apply disc_p_lm | exact Hsh].
  by rewrite /disc_seg_p disc_input_p_lm in Hd.
Qed.

(* THE ECHO'S REFUTATION, the landed 200-line proof's statement, from the
   generic one at the landed model's laws and hooks *)
Theorem pcl_pure_o_no_echo_N (h : list mobs) (c : bv 8) (ho : list mobs)
    (CH : LogEntryDefs.cons_hist) (so : postage) (r : nat) (pre : list (bv 8)) :
  disc_p h ->
  trace_shape h true ->
  obs_ends_in Uart0 h c ->
  obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
  (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
  (length (LogEntryDefs.ch_log CH) + 1)%nat = length (ins (open_seg h)) ->
  LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
  pcl_pure_o (obs_boots h) ho so r pre CH -> False.
Proof using.
  intros Hdisc Hsh Hends Hwire Hord HK1 Harm Hopen. apply pcl_pure_o_lm in Hopen.
  exact (gcl_pure_o_no_echo pipe_lm tt pipe_lm_laws pipe_hooks pipe_lm_byte_laws
           h c ho CH (pstage_g so) r pre (proj1 (disc_p_lm h) Hdisc) Hsh Hends Hwire Hord
           HK1 Harm Hopen).
Qed.

(* THE DRAIN'S F4 at an unfiled block ([PipeBothPure.good_out_p_of_stage_blk2]) *)
Theorem good_out_p_of_stage_blk2_N (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) (a : nat) (seg : list mobs) :
  Forall (fun x => (x < length pro_alts)%nat) ps ->
  alts_pre_p (ins seg) cs ->
  E_disc_p E ->
  pro_pin_p ps cs (snd <$> E) ->
  pblk2_at cs (snd <$> E) w a ->
  obs_wire Uart0 seg `prefix_of` (D_p ps cs E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out_p seg.
Proof using.
  intros Hps Hao HE Hpin Hblk Hwire Hinp. apply good_out_p_lm.
  apply (lm_good_out_of_stage_open pipe_lm pipe_hooks pipe_lm_byte_laws ps cs tt E w a seg
           Hps Hao HE); [by apply pro_pin_p_lm | exact Hblk | | exact Hinp].
  by rewrite -(D_p_lm _ _ tt).
Qed.
