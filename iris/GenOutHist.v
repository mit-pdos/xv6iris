(* ===================================================================== *)
(*  GenOutHist.v -- THE CONSOLE CLAIM'S PURE HISTORY LAYER, ONCE OVER A  *)
(*  LINE MODEL (app-both M3b, first cut).                                *)
(*                                                                       *)
(*  [EchoOut] section 1, [FileOut] section 1 and [PipeOut] section 1     *)
(*  state three times what the per-cycle claim knows of the CONSOLE LOG: *)
(*  the input side's account ([ein_pure]: the log is well-formed, every  *)
(*  entry's segment is disciplined and in this era, the delivered list   *)
(*  is a prefix of the echoed one, and (A1) every entry is echoed), what *)
(*  the claim remembers of an open arm ((K1) the byte's input number and *)
(*  the arm's echo), (A2) the delivered list reaches the lines below the *)
(*  writer's, and the whole pure claim ([ecl_pure]) with its event       *)
(*  steps.  Every clause reads the application only through the line     *)
(*  model ([GenOutPure.lm_out_pure], [LineModel.lm_disc_input],          *)
(*  [lm_disc]), so it is stated here once; the drop arm's refutation and *)
(*  the receive flush's are at the model's byte laws.                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import EchoOut.          (* [ch_E], [seg_of], [echoed]'s snoc laws *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

Local Lemma ghist_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

Section gen_out_hist.
  Context (M : lmodel) (K : lm_hooks M) (B : lm_byte_laws M) (sd : lm_st M).

  (* ================================================================== *)
  (*  1.  WHAT THE DISCIPLINE REFUTES OF THE KERNEL'S DROPS              *)
  (* ================================================================== *)

  (* a disciplined byte is none of the bytes a [consoleintr] arm drops
     or treats as an edit *)
  Lemma lm_disc_drop_byte (I : list (bv 8)) (c : bv 8) :
    lm_disc_input M I -> c ∈ I ->
    bv_unsigned c <> 0%Z /\ bv_unsigned c <> 16%Z /\ cons_erase c = false.
  Proof using B.
    intros Hd Hc. pose proof (lm_disc_input_byte_val M B I c Hd Hc) as Hv.
    split; [lia |]. split; [lia |].
    rewrite /cons_erase.
    rewrite (ghist_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (ghist_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (ghist_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  Qed.

  Lemma lm_disc_input_rest_short I :
    lm_disc_input M I -> S (length (rest_of I)) < line_max.
  Proof using. by intros (_ & _ & H). Qed.

  (* THE RING BOUND: under D3 an input is its complete lines plus at most
     one line's worth of bytes *)
  Lemma lm_lines_bytes_disc_bound (I : list (bv 8)) (n : nat) :
    lm_disc_input M I ->
    (n = nlines I \/ (rest_of I = [] /\ n = nlines I - 1)) ->
    length I <= lines_bytes I n + line_max.
  Proof using B.
    intros Hd Hn.
    pose proof (lines_bytes_rest I) as Hsum.
    destruct Hn as [-> | [Hr ->]].
    - pose proof (lm_disc_input_rest_short I Hd). lia.
    - destruct (decide (0 < nlines I)) as [Hpos | Hz].
      + rewrite (lines_bytes_last I Hpos) in Hsum.
        assert (Hk : nlines I - 1 < length (bodies_of I))
          by (rewrite /nlines in Hpos |- *; lia).
        destruct (lookup_lt_is_Some_2 (bodies_of I) (nlines I - 1) Hk)
          as [l Hl].
        rewrite (list_lookup_total_correct _ _ _ Hl) in Hsum.
        pose proof (lmb_body_short B l (lm_disc_input_body M I _ l Hd Hl)).
        rewrite Hr in Hsum. cbn [length] in Hsum. lia.
      + assert (Hnl : nlines I = 0) by lia.
        rewrite Hnl lines_bytes_0 Hr in Hsum. cbn [length] in Hsum. lia.
  Qed.

  Lemma lm_drop_refuted (h : list mobs) (L : list log_entry)
        (dl : list (list mobs * bv 8)) (Eb w : list (bv 8)) :
    length L + 1 = length (ins (open_seg h)) ->
    Forall log_echoed L ->
    128 + length dl <= length (filter log_echoed L) ->
    lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                    then nlines Eb - 1 else nlines Eb) <= length dl ->
    Eb = take (length L) (ins (open_seg h)) ->
    lm_disc_input M (ins (open_seg h)) ->
    False.
  Proof using B.
    intros HK1 HA1 Hring HA2 HEb Hdisc.
    rewrite (epu_filter_all log_echoed L HA1) in Hring.
    assert (HlenEb : length Eb = length L)
      by (rewrite HEb length_take; lia).
    assert (HdEb : lm_disc_input M Eb)
      by (rewrite HEb; exact (lm_disc_input_prefix M B _ _ (prefix_take _ _) Hdisc)).
    assert (Hb : length Eb
                 <= lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                                    then nlines Eb - 1 else nlines Eb)
                    + line_max).
    { apply (lm_lines_bytes_disc_bound Eb _ HdEb). case_decide as Hc.
      - right. split; [exact (proj1 Hc) | reflexivity].
      - by left. }
    rewrite /line_max in Hb. lia.
  Qed.

  Lemma lm_cons_drop_refuted (h : list mobs) (c : bv 8) (L : list log_entry)
        (dl : list (list mobs * bv 8)) (Eb w : list (bv 8)) :
    length L + 1 = length (ins (open_seg h)) ->
    Forall log_echoed L ->
    lines_bytes Eb (if decide (rest_of Eb = [] /\ w = [])
                    then nlines Eb - 1 else nlines Eb) <= length dl ->
    Eb = take (length L) (ins (open_seg h)) ->
    lm_disc_input M (ins (open_seg h)) ->
    c ∈ ins (open_seg h) ->
    cons_drop_ok c L dl -> False.
  Proof using B.
    intros HK1 HA1 HA2 HEb Hdisc Hc Hdrop.
    destruct (lm_disc_drop_byte _ c Hdisc Hc) as (H0 & H16 & Her).
    destruct Hdrop as [Hz | [Hp | [He | Hring]]].
    - exact (H0 Hz).
    - exact (H16 Hp).
    - rewrite Her in He. discriminate.
    - exact (lm_drop_refuted h L dl Eb w HK1 HA1 Hring HA2 HEb Hdisc).
  Qed.

  (* the session is never empty once round 0 has settled *)
  Lemma lm_sess_nonnil (ps cs : list nat) (s : lm_st M) (I : list (bv 8)) :
    Forall (fun a => a < length pro_alts) ps -> pro_done ps ->
    lm_sess M ps cs s I <> [].
  Proof using.
    intros HF Hd H. rewrite /lm_sess in H.
    apply app_eq_nil in H as [H _].
    assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
    pose proof (pro_of_pos ps HF Hne) as Hpos. rewrite H in Hpos.
    cbn [length] in Hpos. lia.
  Qed.

  Lemma lm_disc_open_seg (h : list mobs) :
    trace_shape h true -> lm_disc M h ->
    exists s : lm_st M, lm_st_ok M s /\ lm_disc_seg' M s (open_seg h).
  Proof using.
    intros Hsh Hd.
    destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
    assert (Hin : open_seg h ∈ cycles_of h)
      by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
    apply elem_of_list_lookup in Hin as [i Hi].
    exact (Forall_lookup_1 _ _ _ _ Hd Hi).
  Qed.

  (* THE RECEIVE FLUSH LOSES NOTHING: D1 at the empty input asks for the
     prologue, and there is no room for it on an output-free wire *)
  Lemma lm_flush_lost_disc (s : lm_st M) (seg sf : list mobs) (f : nat) :
    lm_disc_seg' M s seg -> sf `prefix_of` seg ->
    obs_wire Uart0 sf = [] -> length (obs_ins Uart0 sf) = f -> f = 0.
  Proof using.
    intros Hd Hpre Hw Hlen.
    destruct (decide (f = 0)) as [Hz | Hne]; [exact Hz | exfalso].
    assert (Hlp : 0 < length (in_pres sf))
      by (rewrite in_pres_length /ins; lia).
    destruct (lookup_lt_is_Some_2 (in_pres sf) 0 Hlp) as [p0 Hp0].
    assert (Hins0 : ins p0 = [])
      by (apply nil_length_inv; exact (in_pres_lookup_ins sf 0 p0 Hp0)).
    assert (Hp0seg : p0 ∈ in_pres seg).
    { apply elem_of_list_lookup_2 with 0.
      destruct (in_pres_mono sf seg Hpre) as [z Hz].
      rewrite Hz lookup_app_l; [exact Hp0 | lia]. }
    assert (Hw0 : obs_wire Uart0 p0 = []).
    { destruct (in_pres_prefix sf 0 p0 Hp0) as [z Hz].
      rewrite Hz obs_wire_app in Hw. by apply app_eq_nil in Hw as [Hw _]. }
    destruct Hd as [_ (ps & cs & _ & _ & Hall)].
    destruct (Hall p0 Hp0seg) as [Hok Hpt].
    destruct Hok as [HF Hlt].
    apply (lm_sess_nonnil ps cs s [] HF (proj2 (pro_done_rounds ps) ltac:(lia))).
    apply prefix_nil_inv.
    rewrite /lm_disc_pt Hins0 done_of_nil Hw0 in Hpt. exact Hpt.
  Qed.

  Lemma lm_flush_lost_zero (h : list mobs) (f : nat) :
    trace_shape h true -> lm_disc M h -> ConsLog.flush_lost h f -> f = 0.
  Proof using.
    intros Hsh Hdisc [Hz | (sf & Hpre & Hw & Hlen)]; [exact Hz |].
    destruct (lm_disc_open_seg h Hsh Hdisc) as (s & _ & Hd).
    exact (lm_flush_lost_disc s (open_seg h) sf f Hd Hpre Hw Hlen).
  Qed.

  (* ================================================================== *)
  (*  2.  THE INPUT SIDE'S ACCOUNT, AND (A2)                             *)
  (* ================================================================== *)

  Definition gin_pure (k : nat) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) (cs0 : list nat) : Prop :=
    log_ok pops
    /\ (forall e, e ∈ pops -> lm_disc_input M (ins (open_seg (le_hist e))))
    /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
    /\ dl `prefix_of` echoed pops
    /\ E_index (seg_of (echoed pops))
    /\ lm_E_disc M (seg_of (echoed pops))
    /\ nlines (snd <$> echoed pops) <= S (length cs0)
    (* (A1) EVERY LOG ENTRY IS ECHOED: the drop arm is refuted at the open
       ([gcl_pure_open]) and the store arm sends its byte before it files
       ([ConsLog.cons_ev_ok]'s [EvClose] clause) *)
    /\ Forall log_echoed pops.

  Lemma gin_pure_0 k : gin_pure k [] [] [].
  Proof using.
    rewrite /gin_pure. split_and!.
    - exact log_ok_nil.
    - intros e He. by apply elem_of_nil in He.
    - intros e He. by apply elem_of_nil in He.
    - apply prefix_nil.
    - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
      by rewrite lookup_nil in Hx.
    - rewrite /lm_E_disc /seg_of echoed_nil !fmap_nil.
      split_and!; [constructor | constructor |].
      rewrite rest_of_nil. cbn [length]. rewrite /line_max. lia.
    - rewrite echoed_nil fmap_nil nlines_nil. cbn [length]. lia.
    - constructor.
  Qed.

  (* (A2) THE DELIVERED LIST REACHES THE LINES BELOW THE WRITER'S: at a
     drop the kernel says 128 echoed entries are undelivered, and this
     says those bytes lie inside ONE line *)
  Definition lm_dl_ok (so : gstage M) (dl : list (list mobs * bv 8)) : Prop :=
    lines_bytes (snd <$> gs_E M so)
      (if decide (rest_of (snd <$> gs_E M so) = [] /\ gs_w M so = [])
       then nlines (snd <$> gs_E M so) - 1
       else nlines (snd <$> gs_E M so))
    <= length dl.

  Lemma lm_dl_ok_0 : lm_dl_ok (gstage0 M) [].
  Proof using.
    rewrite /lm_dl_ok /gstage0. cbn [gs_E gs_w]. rewrite fmap_nil.
    rewrite lines_bytes_nil. lia.
  Qed.

  Lemma lm_dl_ok_mono (so : gstage M) (dl dl' : list (list mobs * bv 8)) :
    length dl <= length dl' -> lm_dl_ok so dl -> lm_dl_ok so dl'.
  Proof using. rewrite /lm_dl_ok. lia. Qed.

  (* A PROCESS BYTE puts the writer inside a block *)
  Lemma lm_dl_ok_out (so so' : gstage M) (dl : list (list mobs * bv 8)) :
    gs_E M so' = gs_E M so -> gs_w M so' <> [] ->
    (gs_w M so <> [] \/ rest_of (snd <$> gs_E M so) <> []
     \/ (snd <$> gs_E M so) = []) ->
    lm_dl_ok so dl -> lm_dl_ok so' dl.
  Proof using.
    intros HE Hw Hcase Hdl. rewrite /lm_dl_ok in Hdl |- *. rewrite HE.
    rewrite decide_False; last first.
    { intros [_ Hq]. by apply Hw. }
    destruct Hcase as [Hc | [Hc | Hc]].
    - rewrite decide_False in Hdl; [exact Hdl | by intros [_ Hq]].
    - rewrite decide_False in Hdl; [exact Hdl | by intros [Hq _]].
    - rewrite Hc lines_bytes_nil. lia.
  Qed.

  (* ...AND AT A BLOCK'S FIRST BYTE the clause is paid by the writer's own
     bound on the delivered input *)
  Lemma lm_dl_ok_out_full (so so' : gstage M) (dl : list (list mobs * bv 8)) :
    gs_E M so' = gs_E M so -> gs_w M so' <> [] ->
    rest_of (snd <$> gs_E M so) = [] ->
    length (snd <$> gs_E M so) <= length dl ->
    lm_dl_ok so' dl.
  Proof using.
    intros HE Hw Hr Hlen. rewrite /lm_dl_ok HE.
    rewrite decide_False; last first.
    { intros [_ Hq]. by apply Hw. }
    pose proof (lines_bytes_rest (snd <$> gs_E M so)) as Hsum.
    rewrite Hr in Hsum. cbn [length] in Hsum. lia.
  Qed.

  (* THE ECHO leaves the writer owing a whole block *)
  Lemma lm_dl_ok_echo (so : gstage M) (x : list mobs * bv 8)
      (dl : list (list mobs * bv 8)) :
    lm_alts_pre M (gs_state M sd so) (snd <$> gs_E M so) (gs_cs M so) ->
    gs_w M so = lm_pending M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                  (gs_E M so) ->
    lm_dl_ok so dl ->
    lm_dl_ok (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so ++ [x]) []
                (gs_st M so)) dl.
  Proof using K.
    intros Hcsb Hweq Hdl. rewrite /lm_dl_ok in Hdl |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite (fmap_snd_snoc (gs_E M so) x).
    destruct (decide (rest_of (snd <$> gs_E M so) = [] /\ gs_w M so = []))
      as [[Hr0 Hw0] | Hne].
    - assert (HEnil : (snd <$> gs_E M so) = []).
      { destruct (decide ((snd <$> gs_E M so) = [])) as [? | Hq];
          [done | exfalso].
        apply (lm_pending_nonnil M K (gs_ps M so) (gs_cs M so)
                 (gs_state M sd so) (gs_E M so) Hcsb Hq Hr0).
        rewrite -Hweq. exact Hw0. }
      rewrite HEnil. case_decide as Hc2.
      + destruct Hc2 as [Hr2 _].
        assert (Hn2 : nlines ([] ++ [x.2]) = 1).
        { destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
          - by rewrite Hx nlines_snoc_nl nlines_nil.
          - exfalso. rewrite (rest_of_snoc_other [] x.2 Hx) rest_of_nil in Hr2.
            discriminate Hr2. }
        rewrite Hn2. replace (1 - 1) with 0 by lia.
        rewrite lines_bytes_0. lia.
      + assert (Hn2 : nlines ([] ++ [x.2]) = 0).
        { destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
          - exfalso. apply Hc2. split; [| reflexivity].
            rewrite Hx. apply rest_of_snoc_nl.
          - by rewrite (nlines_snoc_other [] x.2 Hx) nlines_nil. }
        rewrite Hn2 lines_bytes_0. lia.
    - destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
      + rewrite Hx. case_decide as Hc2; last first.
        { exfalso. apply Hc2. split; [apply rest_of_snoc_nl | reflexivity]. }
        rewrite nlines_snoc_nl.
        replace (S (nlines (snd <$> gs_E M so)) - 1)
          with (nlines (snd <$> gs_E M so)) by lia.
        by rewrite (lines_bytes_snoc_nl _ _ (Nat.le_refl _)).
      + case_decide as Hc2.
        { exfalso. destruct Hc2 as [Hq _].
          rewrite (rest_of_snoc_other _ x.2 Hx) in Hq.
          destruct (app_eq_nil _ _ Hq) as [_ Hq2]. discriminate Hq2. }
        rewrite (nlines_snoc_other _ x.2 Hx).
        by rewrite (lines_bytes_snoc_other _ x.2 _ Hx).
  Qed.

  (* ================================================================== *)
  (*  3.  THE OPEN ARM, AND THE WHOLE PURE CLAIM                         *)
  (* ================================================================== *)

  (* WHAT THE CLAIM REMEMBERS ABOUT AN OPEN ARM: the era facts, the arm's
     echo ([cs = [echo_of c]], the drop and erase arms refuted at the
     open) and the byte's INPUT NUMBER (K1) -- the log is complete below
     this input *)
  Definition garm_era (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : Prop :=
    match LogEntryDefs.ch_arm H with
    | Some (h, c, cs, j) =>
        lm_disc_input M (ins (open_seg h)) /\ obs_boots h = k
        /\ lm_disc M h /\ trace_shape h true
        /\ h = ho
        /\ cs = [echo_of c]
        /\ length (LogEntryDefs.ch_log H) + 1 = length (ins (open_seg h))
    | None => True
    end.

  Definition gcl_pure (k : nat) (ho : list mobs) (so : gstage M)
      (H : LogEntryDefs.cons_hist) : Prop :=
    lm_out_pure M sd k ho so (LogEntryDefs.ch_acc H)
    /\ lm_cs_len_ok M so
    /\ lm_ps_len_ok M sd so
    /\ gin_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (gs_cs M so)
    /\ garm_era k ho H
    /\ gs_E M so = ch_E H
    /\ lm_dl_ok so (LogEntryDefs.ch_dl H).

  Lemma gcl_pure_arm k ho so H : gcl_pure k ho so H -> garm_era k ho H.
  Proof using. by intros (_ & _ & _ & _ & Hera & _). Qed.

  Lemma gcl_pure_E k ho so H : gcl_pure k ho so H -> gs_E M so = ch_E H.
  Proof using. by intros (_ & _ & _ & _ & _ & HE & _). Qed.

  (* THE DELIVERED BYTES ARE INSIDE THE ERA'S INPUT *)
  Lemma gcl_pure_dl_E k ho so H :
    gcl_pure k ho so H ->
    (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> gs_E M so).
  Proof using.
    intros (_ & _ & _ & Hin & _ & HE & _).
    destruct Hin as (_ & _ & _ & Hdlp & _).
    rewrite HE /ch_E.
    etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
    rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
    apply epu_fmap_prefix. by apply prefix_app_r.
  Qed.

  Lemma gcl_pure_rd_stage k ho so H :
    gcl_pure k ho so H ->
    lm_rd_stage M (gs_ps M so) (gs_cs M so) (gs_state M sd so) (snd <$> gs_E M so).
  Proof using.
    intros (Hout & Hcsl & _ & _ & _ & _).
    destruct Hout as (_ & _ & _ & _ & Hpsb & Hpin & Hcsb & _).
    rewrite /lm_rd_stage. split_and!;
      [exact Hpsb | exact Hcsb | exact Hpin |].
    rewrite /lm_cs_len_ok in Hcsl. rewrite Hcsl. case_decide as Hd.
    - destruct Hd as [_ Hr]. rewrite (ll_nlines_removelast _ Hr). lia.
    - apply nlines_prefix, gop_removelast_prefix.
  Qed.

  (* ---- the five event steps of the pure part ---- *)

  Lemma gcl_pure_close k ho so H :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    gcl_pure k ho so H ->
    gcl_pure k ho so (ConsLog.cons_step H ConsLog.EvClose).
  Proof using.
    intros Hok Hev Hecl.
    pose proof (ch_E_close H) as Hclose.
    pose proof (ch_E_close_len H) as Hlen.
    pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
    unfold ConsLog.cons_hist_ok in Hok'. destruct Hok' as [Hlog' _].
    destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; cycle 1.
    { rewrite /ConsLog.cons_step Ha. exact Hecl. }
    destruct Hecl as (Hout & Hcs & Hps & Hin & Hera & HE & Hdlok).
    destruct Hin as (_ & Hdsc & Hbts & Hdl & _ & _ & _ & Hall).
    rewrite /garm_era Ha in Hera.
    destruct Hera as (Hdseg & Hboots & _ & _ & _ & Hcsa & _).
    (* (A1) AT THE CLOSE: the arm's echo IS the byte, and the kernel says a
       store arm sends its byte before it closes (K3) *)
    destruct Hev as (a & Ha2 & _ & HK3). rewrite Ha in Ha2.
    injection Ha2 as <-.
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_byte LogEntryDefs.ca_sent
         le_echo le_byte fst snd] in HK3.
    assert (Hj : j = 1) by (apply HK3; exact Hcsa).
    assert (Hech : log_echoed (h, c, take j cs)).
    { rewrite Hcsa Hj. cbn [take]. exact (log_echoed_echo h c). }
    destruct Hout as (Hacc & Hw & HEi & HEb & Hpsf & Hpin & Hcsf & Hdse & Hpre
                      & Hle & Hbo & Hnofk & Hf0 & Hfok).
    rewrite /ConsLog.cons_step Ha in Hlog', Hlen |- *.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm] in Hlog', Hlen |- *.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H ++ [(h, c, take j cs)]))
                   = gs_E M so).
    { rewrite HE -Hclose /ch_E /ConsLog.cons_step Ha.
      cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
      by rewrite app_nil_r. }
    split_and!.
    - by split_and!.
    - exact Hcs.
    - exact Hps.
    - split_and!.
      + exact Hlog'.
      + intros e He. apply elem_of_app in He as [He | He].
        * exact (Hdsc e He).
        * apply elem_of_list_singleton in He as ->.
          cbn [le_hist fst snd]. exact Hdseg.
      + intros e He. apply elem_of_app in He as [He | He].
        * exact (Hbts e He).
        * apply elem_of_list_singleton in He as ->.
          cbn [le_hist fst snd]. exact Hboots.
      + rewrite (echoed_snoc_yes _ _ Hech).
        by apply (prefix_app_r _ _ [(le_hist (h, c, take j cs),
                                     le_byte (h, c, take j cs))]).
      + by rewrite Hseg.
      + by rewrite Hseg.
      + rewrite -(seg_of_snd (echoed _)) Hseg.
        rewrite /lm_cs_len_ok in Hcs.
        destruct (decide (gs_w M so = [] /\ rest_of (snd <$> gs_E M so) = []));
          lia.
      + apply Forall_app. split; [exact Hall | by rewrite Forall_singleton].
    - exact I.
    - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
      rewrite app_nil_r. by rewrite Hseg.
    - exact Hdlok.
  Qed.

  Lemma gcl_pure_out k ho (so so' : gstage M) H (b : bv 8) :
    length (gs_cs M so) <= length (gs_cs M so') -> gs_E M so' = gs_E M so ->
    lm_out_pure M sd k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_cs_len_ok M so' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok so' (LogEntryDefs.ch_dl H) ->
    gcl_pure k ho so H ->
    gcl_pure k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall].
    - by rewrite HE' HE /ch_E.
  Qed.

  Lemma gcl_pure_read k ho so H (ws : list (list mobs * bv 8)) :
    (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
    gcl_pure k ho so H ->
    gcl_pure k ho so (ConsLog.cons_step H (ConsLog.EvRead ws)).
  Proof using.
    intros Hpre (Hout & Hc & Hp & Hin & Hera & HE & Hdlok).
    destruct Hin as (Hlog & Hdsc & Hbts & _ & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera
                | by rewrite HE /ch_E |].
    - by split_and!.
    - apply (lm_dl_ok_mono so (LogEntryDefs.ch_dl H)); [| exact Hdlok].
      rewrite length_app. lia.
  Qed.

  (* MOVING THE WITNESS: the claim's [ho]-dependent clauses transfer to a
     LATER history by the log's own order fact *)
  Lemma lm_out_pure_move (k : nat) (ho h : list mobs) (so : gstage M)
      (acc : list (bv 8)) (L : list log_entry)
      (dl : list (list mobs * bv 8)) :
    trace_shape h true ->
    obs_boots h = k ->
    (forall e, e ∈ L -> hist_ext (le_hist e) h) ->
    gin_pure k L dl (gs_cs M so) ->
    seg_of (echoed L) = gs_E M so ->
    length (gs_E M so) <= length (ins (open_seg h)) ->
    lm_out_pure M sd k ho so acc -> lm_out_pure M sd k h so acc.
  Proof using.
    intros Hsh Hk Hord Hin Hseg Hle
      (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc & _ & _ & _
       & Hnofk & Hf0 & Hfok).
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi & _).
    split_and!; [exact Hacc | exact Hwpre | exact Hidx | exact Hbyte
                | exact Hpsb | exact Hpin | exact Hcsb | exact Hdsc
                | | exact Hle | | exact Hnofk | exact Hf0 | exact Hfok].
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

  (* THE OPEN: (K1) and the arm's echo are recorded, the drop arm and the
     receive flush refuted by the discipline *)
  Lemma gcl_pure_open k ho so H (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input M (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc M h -> trace_shape h true ->
    gcl_pure k ho so H ->
    gcl_pure k h so (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using B.
    intros Hok Hev Hd Hb Hdh Hsh (Hout & Hc & Hp & Hin & _ & HE & Hdlok).
    pose proof Hev as (Hn & Hends & Hecho & Hord & Hwire & HK1f & HK2).
    pose proof (ch_E_open H h c cs Hn) as Hopen.
    assert (HK1 : length (LogEntryDefs.ch_log H) + 1 = length (ins (open_seg h))).
    { destruct HK1f as (f & Hfl & Hcnt).
      rewrite (lm_flush_lost_zero h f Hsh Hdh Hfl) Nat.add_0_r in Hcnt.
      by rewrite -ins_obs_ins in Hcnt. }
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = gs_E M so).
    { rewrite HE /ch_E Hn. cbn [ch_arm_E]. by rewrite app_nil_r. }
    assert (Hall : Forall log_echoed (LogEntryDefs.ch_log H))
      by (by destruct Hin as (_ & _ & _ & _ & _ & _ & _ & Hq)).
    assert (Hcnt : length (gs_E M so) = length (ins (open_seg h)) - 1).
    { rewrite -Hseg seg_of_length (echoed_all_len _ Hall). lia. }
    assert (Hle : length (gs_E M so) <= length (ins (open_seg h))) by lia.
    pose proof (lm_out_pure_move k ho h so (LogEntryDefs.ch_acc H)
                  (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
                  Hsh Hb Hord Hin Hseg Hle Hout) as Hout'.
    assert (Hpl : forall j x, gs_E M so !! j = Some x ->
                    x.1 `prefix_of` open_seg h).
    { destruct Hout' as (_ & _ & _ & _ & _ & _ & _ & _ & Hpre1 & _).
      intros j x Hx. exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx). }
    assert (Hidx : E_index (gs_E M so)) by (by destruct Hout as (_ & _ & Hq & _)).
    assert (Hbytes : (snd <$> gs_E M so)
                     = take (length (LogEntryDefs.ch_log H)) (ins (open_seg h))).
    { rewrite (E_bytes_of_hist (gs_E M so) (open_seg h) Hidx Hpl Hle).
      by replace (length (gs_E M so)) with (length (LogEntryDefs.ch_log H))
        by lia. }
    assert (Hcin : c ∈ ins (open_seg h)).
    { destruct Hends' as [h0 Hh0]. rewrite Hh0 ins_app ins_in.
      apply elem_of_app. right. apply elem_of_list_here. }
    pose proof (lm_disc_drop_byte _ c Hd Hcin) as (_ & _ & Hner).
    assert (Hcs : cs = [echo_of c]).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]]; [| exact Hech |];
        last first.
      { exfalso. rewrite Hner in Herase. discriminate. }
      exfalso.
      exact (lm_cons_drop_refuted h c (LogEntryDefs.ch_log H)
               (LogEntryDefs.ch_dl H) (snd <$> gs_E M so) (gs_w M so)
               HK1 Hall Hdlok Hbytes Hd Hcin (HK2 Hnil)). }
    rewrite /gcl_pure /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout' | exact Hc | exact Hp | exact Hin | | | exact Hdlok].
    - rewrite /garm_era. cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
      split_and!; [exact Hd | exact Hb | exact Hdh | exact Hsh | reflexivity
                  | exact Hcs | exact HK1].
    - rewrite HE -Hopen /ConsLog.cons_step /ch_E.
      by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
  Qed.

  Lemma gcl_pure_byte k (ho ho' : list mobs) (so so' : gstage M) H (b : bv 8)
      (h : list mobs) (c : bv 8) :
    LogEntryDefs.ch_arm H = Some (h, c, [echo_of c], 0) ->
    ho' = h ->
    length (gs_cs M so) <= length (gs_cs M so') ->
    gs_E M so' = gs_E M so ++ [(open_seg h, c)] ->
    lm_out_pure M sd k ho' so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_cs_len_ok M so' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok so' (LogEntryDefs.ch_dl H) ->
    gcl_pure k ho so H ->
    gcl_pure k ho' so' (ConsLog.cons_step H (ConsLog.EvByte b)).
  Proof using.
    intros Ha Hw Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
    pose proof (ch_E_byte_echo H b h c Ha) as Hgrow.
    rewrite /gcl_pure /ConsLog.cons_step Ha.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hc | exact Hp
                | split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                              | exact HEi | exact HEb | lia | exact Hall]
                | | | exact Hdlok'].
    - rewrite /garm_era Ha in Hera. rewrite /garm_era.
      cbn [LogEntryDefs.ch_arm LogEntryDefs.ch_log].
      destruct Hera as (Hds & Hb & Hd & Hshh & _ & Hcsa & Hk1). by split_and!.
    - rewrite HE' HE -Hgrow /ConsLog.cons_step Ha.
      by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
  Qed.

  (* AN OUTPUT CLAIM AT [acc = []] STANDS AT THE START OF ITS ERA *)
  Lemma lm_out_pure_nil_stage (k : nat) (ho : list mobs) (so : gstage M) :
    lm_out_pure M sd k ho so [] ->
    lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so) (gs_E M so)
      (gs_w M so) = 0.
  Proof using.
    intros (Hacc & _).
    assert (Hlen : length (lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                             (gs_E M so)) + length (gs_w M so) = 0)
      by (rewrite -length_app -Hacc; reflexivity).
    destruct (gs_E M so) as [| y E1] eqn:HE.
    - rewrite /lm_pcount fmap_nil lm_proc_before_nil. cbn [length]. lia.
    - exfalso.
      assert (Hup : 0 < length (lm_D M (gs_ps M so) (gs_cs M so)
                                  (gs_state M sd so) (y :: E1))).
      { change (lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so) (y :: E1))
          with (lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) []
                ++ [echo_of y.2]
                ++ lm_D_from M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                     ([] ++ [y.2]) E1).
        rewrite !length_app. cbn [length]. lia. }
      lia.
  Qed.
End gen_out_hist.
