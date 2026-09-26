(* ===================================================================== *)
(*  GenOutWild.v -- THE PURE LAYER OF THE CLAIM'S TERMINAL ARM (seccomp   *)
(*  lane S2; design: claude-notes/design/seccomp.md section 10).          *)
(*                                                                       *)
(*  A WILD LINE is one after which the discipline reads nothing more of  *)
(*  the era and whose continuation is ANY nonempty byte string: every    *)
(*  state admits a coverage-ending alternative with that continuation,  *)
(*  and the line's merge set is everything ([lm_wild]).  At the union it *)
(*  is the [seccomp x] line.  What the claim's third arm reads off it:   *)
(*                                                                       *)
(*  1. D4 AT A WILD LINE ([lm_disc_wild_last]): a disciplined history    *)
(*     has no input byte after a complete wild line.                     *)
(*  2. THE PRESENTER PINS ([lm_blk_stage_inp], [lm_pro_stage_inp],       *)
(*     [lm_proc_before_pos]): a writer at the stage's cursor whose input *)
(*     bound is a prefix of the stage's echoed input stands AT that      *)
(*     input -- the process stream grows by at least the prompt per      *)
(*     complete line ([LineModelLinks.lm_pending_at_nonnil_at]).         *)
(*  3. THE TRANSITION'S FACTS ([lm_rd_wild_stage]): a read whose window  *)
(*     completes a wild line finds the log fully delivered, no arm open, *)
(*     nothing of the line's block written, and the choice list one      *)
(*     short.                                                            *)
(*  4. THE DRAIN AT THE ARM ([lm_good_out_wild]): the stage's transcript *)
(*     followed by ANY tail is good, the line's terminal alternative at  *)
(*     that tail (made nonempty) filed after the frozen list.            *)
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
Require Import EchoOut.          (* [ch_E], [seg_of], [echoed] *)
Require Import GenOutHist.
Require Import ConsoleInv.       (* [cons_chain], [cons_placed]: the ring's facts *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* two inputs ending at a newline, one a prefix of the other, with the same
   number of lines, are the same input *)
Lemma wild_prefix_lines_eq (I J : list (bv 8)) :
  I `prefix_of` J -> rest_of I = [] -> rest_of J = [] -> nlines I = nlines J ->
  I = J.
Proof.
  intros Hp HrI HrJ Hn.
  pose proof (bodies_of_prefix I J Hp) as Hb.
  assert (Hbe : bodies_of I = bodies_of J).
  { apply prefix_length_eq; [exact Hb | rewrite /nlines in Hn; lia]. }
  rewrite (wl_cut_join I) (wl_cut_join J) HrI HrJ Hbe. reflexivity.
Qed.

Lemma wild_prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

(* a strict prefix extends by the next element *)
Lemma wild_prefix_strict_snoc {A} (w l : list A) :
  w `prefix_of` l -> length w < length l -> exists b, (w ++ [b]) `prefix_of` l.
Proof.
  intros Hp Hlt. destruct (lookup_lt_is_Some_2 l (length w) Hlt) as [b Hb].
  exists b. exact (wild_prefix_snoc_lookup w l b Hp Hb).
Qed.

Section gen_out_wild.
  Context (M : lmodel).

  (* ================================================================== *)
  (*  1.  THE WILD LINE AND D4                                           *)
  (* ================================================================== *)
  Definition lm_wild (l : lm_line M) : Prop :=
    (forall (s : lm_st M) (u : list (bv 8)), u <> [] ->
       exists c : nat, lm_ok M s l (lm_dec M c) /\ lm_term M (lm_dec M c) = true
                       /\ lm_cont M s l (lm_dec M c) = u)
    /\ (forall u, lm_merge M l u).

  Lemma lm_d4_wild (cs : list nat) (s : lm_st M) (I : list (bv 8)) (i : nat) :
    lm_d4 M cs s I -> i < nlines I -> lm_wild (lm_of M (bodies_of I !!! i)) ->
    nlines I = S i /\ rest_of I = [].
  Proof using.
    intros Hd4 Hi [Hc Hm]. apply (Hd4 i Hi); [| apply Hm].
    destruct (Hc (lm_upto M cs s (bodies_of I) i) [wl_nl] ltac:(done))
      as (c & Hok & Ht & _).
    by exists (lm_dec M c).
  Qed.

  (* D4 AT A WILD LINE: a disciplined history has no input byte after a
     complete wild line *)
  Lemma lm_disc_wild_last (h : list mobs) (I : list (bv 8)) (c : bv 8) :
    lm_disc M h -> trace_shape h true -> I <> [] -> rest_of I = [] ->
    lm_wild (lm_line_at M I) -> (I ++ [c]) `prefix_of` ins (open_seg h) -> False.
  Proof using.
    intros Hd Hsh Hne Hr Hw Hp.
    destruct (lm_disc_open_seg M h Hsh Hd) as (s & _ & (_ & ps & cs & _ & Hd4 & _)).
    assert (HIJ : I `prefix_of` ins (open_seg h)) by (etrans; [| exact Hp]; by eexists).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (nlines_prefix I _ HIJ) as Hle.
    assert (Hbod : bodies_of (ins (open_seg h)) !!! (nlines I - 1)
                   = bodies_of I !!! (nlines I - 1)).
    { destruct (bodies_of_prefix I _ HIJ) as [z Hz].
      rewrite Hz !list_lookup_total_alt lookup_app_l; [done | rewrite /nlines in Hpos |- *; lia]. }
    rewrite /lm_line_at -Hbod in Hw.
    destruct (lm_d4_wild cs s (ins (open_seg h)) (nlines I - 1) Hd4 ltac:(lia) Hw)
      as [HnJ HrJ].
    pose proof (wild_prefix_lines_eq I _ HIJ Hr HrJ ltac:(lia)) as HeqIJ.
    apply prefix_length in Hp. rewrite -HeqIJ length_app in Hp. cbn [length] in Hp. lia.
  Qed.

  (* ================================================================== *)
  (*  2.  THE PRESENTER PINS                                             *)
  (* ================================================================== *)

  (* the era's head write stands at cursor zero, and a stage that has
     echoed a byte is past it: the settled prologue is due first *)
  Lemma lm_proc_before_pos (ps cs : list nat) (s : lm_st M) (I : list (bv 8)) :
    Forall (fun a => a < length pro_alts) ps -> lm_pro_pin M ps cs I -> I <> [] ->
    0 < length (lm_proc_before M ps cs s I).
  Proof using.
    intros HF Hpin Hne. destruct I as [| b I]; [done |].
    rewrite /lm_proc_before. cbn [lm_proc_before_from]. rewrite length_app.
    assert (Hpa : lm_pending_at M ps cs s [] = pro_of ps)
      by (rewrite /lm_pending_at; case_decide as Hq; [done | by destruct (Hq eq_refl)]).
    rewrite Hpa.
    assert (Hne' : ps <> []).
    { intros ->. pose proof (Hpin 0 (nstarted_pos (b :: I) ltac:(done))) as H0.
      cbn in H0. lia. }
    pose proof (pro_of_pos ps HF Hne'). lia.
  Qed.

  (* A BLOCK WRITER AT THE STAGE'S CURSOR stands at the stage's input:
     every further complete line of the stage's input puts at least its
     continuation (which is nonempty) before the cursor *)
  Lemma lm_blk_stage_inp (K : lm_hooks M) (ps0 ps cs0 cs : list nat) (s : lm_st M)
      (I E : list (bv 8)) :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> lm_pro_pin M ps0 cs0 I ->
    I <> [] -> rest_of I = [] -> nlines I <= S (length cs0) ->
    I `prefix_of` E -> lm_alts_pre M s E cs ->
    length (lm_proc_before M ps0 cs0 s I) = length (lm_proc_before M ps cs s E) ->
    I = E.
  Proof using.
    intros Hps Hcs Hpin Hne Hr Hn HIE Hao Hlen.
    rewrite (lm_proc_before_cs_prefix M ps0 ps cs0 cs s I Hps Hcs Hpin) in Hlen;
      [| rewrite (ll_nlines_removelast I Hr); lia].
    destruct (decide (I = E)) as [? | HIne]; [done | exfalso].
    pose proof (prefix_length _ _ (lm_proc_stream_before M ps cs s I E HIE HIne)) as Hle.
    rewrite /lm_proc_stream length_app in Hle.
    apply (lm_pending_at_nonnil_at M K ps cs s I E HIE Hao Hne Hr).
    apply nil_length_inv. lia.
  Qed.

  (* A PROLOGUE WRITER AT THE STAGE'S CURSOR stands at the stage's input:
     past its input the stage's round is settled, the writer's is not
     ([GenOut.gcl_step_write_pro]'s argument, once) *)
  Lemma lm_pro_stage_inp (L : lm_laws M) (ps0 ps cs0 cs : list nat) (s : lm_st M)
      (I E : list (bv 8)) (m : nat) :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
    Forall (fun x => x < length pro_alts) ps ->
    lm_pro_pin M ps0 cs0 I -> rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs0 (nlines I - 1)) = true) ->
    nlines I <= length cs0 ->
    ~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I)) ps0) ->
    I `prefix_of` E -> lm_pro_pin M ps cs E ->
    length (lm_proc_stream M ps0 cs0 s I) = length (lm_proc_before M ps cs s E) + m ->
    I = E.
  Proof using.
    intros Hpsp Hcsp Hpsb Hpin0 Hr0 Hopen Hdiv Hnd HI0 Hpinf Hm.
    pose proof (ll_nlines_removelast I Hr0) as Hrl0.
    assert (Hpsb0 : Forall (fun x => x < length pro_alts) ps0).
    { destruct Hpsp as [z Hz]. rewrite Hz in Hpsb. by apply Forall_app in Hpsb as [? _]. }
    assert (Hlk : forall j, j < nlines I -> cs !!! j = cs0 !!! j).
    { intros j Hj. destruct Hcsp as [z ->].
      rewrite !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (Hidxeq : lm_pro_idx M cs (nlines I) = lm_pro_idx M cs0 (nlines I))
      by exact (lm_pro_idx_ext M cs cs0 (nlines I) Hlk (nlines I) ltac:(lia)).
    rewrite -Hidxeq in Hnd.
    assert (HopenC : I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true).
    { destruct (decide (I = [])) as [Hz | Hne0]; [by left | right].
      pose proof (nlines_pos_of_rest_nil I Hne0 Hr0) as Hpos0.
      destruct Hopen as [Hz | H3]; [by destruct (Hne0 Hz) |].
      rewrite /lm_at (Hlk (nlines I - 1) ltac:(lia)). exact H3. }
    assert (Hstream : lm_proc_before M ps0 cs0 s I = lm_proc_before M ps cs s I).
    { apply (lm_proc_before_cs_prefix M ps0 ps cs0 cs s I Hpsp Hcsp Hpin0). lia. }
    assert (Hpend0 : lm_pending_at M ps0 cs0 s I = lm_pending_at M ps0 cs s I)
      by exact (lm_pending_at_cs_ext M ps0 cs0 cs s I Hcsp Hdiv).
    assert (Hpmono : lm_pending_at M ps0 cs s I `prefix_of` lm_pending_at M ps cs s I)
      by (by apply lm_pending_at_ps_mono).
    destruct (decide (I = E)) as [? | Hne]; [done | exfalso].
    pose proof (lm_proc_stream_before M ps cs s I E HI0 Hne) as Hpre.
    apply prefix_length in Hpre.
    rewrite /lm_proc_stream length_app -Hstream in Hpre.
    rewrite /lm_proc_stream length_app Hpend0 in Hm.
    pose proof (prefix_length _ _ Hpmono) as Hlp.
    assert (Hpe : lm_pending_at M ps0 cs s I = lm_pending_at M ps cs s I).
    { apply prefix_length_eq; [exact Hpmono | lia]. }
    pose proof (lm_pending_at_round_det M L ps0 ps cs s I Hr0 HopenC Hpe) as Hpro.
    assert (Hdone : pro_done (pro_from (lm_pro_idx M cs (nlines I)) ps)).
    { apply pro_from_done. apply Hpinf. exact (nstarted_strict I E HI0 Hne). }
    apply Hnd.
    destruct (pro_of_prefix_free
                (pro_from (lm_pro_idx M cs (nlines I)) ps0)
                (pro_from (lm_pro_idx M cs (nlines I)) ps)
                ltac:(by apply pro_from_Forall) ltac:(by apply pro_from_Forall)
                Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
    exact Hd.
  Qed.

  (* the reader's range condition grows by the alternative a block files
     ([GenOut.lm_alts_pre_snoc], which lives in an Iris file) *)
  Lemma lm_alts_pre_snoc_w (s0 : lm_st M) (I : list (bv 8)) (cs : list nat) (a : nat) :
    lm_alts_pre M s0 I cs -> length cs < nlines I ->
    lm_ok M (lm_upto M cs s0 (bodies_of I) (length cs))
      (lm_of M (bodies_of I !!! length cs)) (lm_dec M a) ->
    lm_alts_pre M s0 I (cs ++ [a]).
  Proof using.
    intros H Hlt Hok i c Hc.
    assert (Hup : forall j, j <= length cs ->
              lm_upto M (cs ++ [a]) s0 (bodies_of I) j = lm_upto M cs s0 (bodies_of I) j).
    { intros j Hj. apply (lm_upto_ext M); [| intros j' _; reflexivity].
      intros j' Hj'. rewrite !list_lookup_total_alt lookup_app_l; [done | lia]. }
    destruct (decide (i < length cs)) as [Hi | Hi].
    - rewrite lookup_app_l in Hc; [| lia]. rewrite (Hup i ltac:(lia)). exact (H i c Hc).
    - rewrite lookup_app_r in Hc; [| lia].
      assert (Hie : i = length cs).
      { apply lookup_lt_Some in Hc. cbn [length] in Hc. lia. }
      subst i. rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-.
      rewrite (Hup (length cs) ltac:(lia)). by split.
  Qed.

  (* ================================================================== *)
  (*  3.  THE DRAIN AT THE ARM                                           *)
  (* ================================================================== *)
  Lemma lm_good_out_wild (L : lm_laws M) (K : lm_hooks M) (B : lm_byte_laws M)
      (ps cs : list nat) (s : lm_st M) (E : list (list mobs * bv 8))
      (u : list (bv 8)) (seg : list mobs) :
    Forall (fun a => a < length pro_alts) ps ->
    lm_alts_pre M s (snd <$> E) cs ->
    lm_pro_pin M ps cs (snd <$> E) ->
    lm_E_disc M E ->
    (snd <$> E) <> [] -> rest_of (snd <$> E) = [] ->
    length cs = nlines (snd <$> E) - 1 ->
    lm_wild (lm_line_at M (snd <$> E)) ->
    obs_wire Uart0 seg `prefix_of` (lm_D M ps cs s E ++ u) ->
    (snd <$> E) `prefix_of` ins seg ->
    lm_good_out M s seg.
  Proof using.
    intros Hpsb Hao Hpin HE Hne Hr Hlen [Hwc _] Hwire Hinp.
    set (I := snd <$> E) in *.
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    set (u' := if decide (u = []) then [wl_nl] else u).
    assert (Hu' : u' <> []) by (rewrite /u'; case_decide; done).
    assert (Huu : u `prefix_of` u').
    { rewrite /u'. case_decide as Hq; [rewrite Hq; apply prefix_nil | reflexivity]. }
    destruct (Hwc (lm_upto M cs s (bodies_of I) (nlines I - 1)) u' Hu')
      as (c & Hok & Hterm & Hcont).
    set (cs1 := cs ++ [c]).
    assert (Hcs1 : cs `prefix_of` cs1) by (rewrite /cs1; by eexists).
    assert (Hag : forall j, j < nlines I - 1 -> cs1 !!! j = cs !!! j).
    { intros j Hj. rewrite /cs1 !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (Hat : lm_at M cs1 (nlines I - 1) = lm_dec M c).
    { rewrite /lm_at /cs1 list_lookup_total_alt lookup_app_r; [| lia].
      rewrite (_ : nlines I - 1 - length cs = 0); [reflexivity | lia]. }
    assert (Hup : lm_upto M cs1 s (bodies_of I) (nlines I - 1)
                  = lm_upto M cs s (bodies_of I) (nlines I - 1))
      by (apply (lm_upto_ext M); [exact Hag | intros; reflexivity]).
    assert (Hpin1 : lm_pro_pin M ps cs1 I).
    { intros q Hq. rewrite (nstarted_rest_nil I Hr) in Hq.
      rewrite (lm_pro_idx_ext M cs1 cs q ltac:(intros j Hj; apply Hag; lia) q
                 ltac:(lia)).
      apply Hpin. rewrite (nstarted_rest_nil I Hr). exact Hq. }
    assert (Hrl : nlines (removelast I) <= length cs)
      by (rewrite (ll_nlines_removelast I Hr); lia).
    apply (lm_good_out_of_stage M K B ps cs1 s E u' seg Hpsb).
    - apply (lm_alts_pre_mono M s I (ins seg)); [exact Hinp |].
      apply lm_alts_pre_snoc_w; [exact Hao | lia |].
      rewrite Hlen. exact Hok.
    - rewrite /cs1 length_app. cbn [length].
      change (nlines (removelast I) <= length cs + 1). lia.
    - left. rewrite /cs1 length_app. cbn [length].
      change (nlines I <= length cs + 1). lia.
    - exact HE.
    - exact Hpin1.
    - rewrite /lm_pending /lm_pending_at decide_False; [| exact Hne].
      rewrite decide_True; [| exact Hr].
      rewrite /lm_cont_at Hat Hup /lm_line_at in Hcont |- *.
      rewrite (lml_term_nopanic L _ Hterm) app_nil_r Hcont. reflexivity.
    - rewrite -(lm_D_cs_prefix M ps ps cs cs1 s E ltac:(reflexivity) Hcs1 Hpin Hrl).
      etrans; [exact Hwire |]. by apply prefix_app.
    - exact Hinp.
  Qed.

  (* ================================================================== *)
  (*  4.  THE TRANSITION'S FACTS                                         *)
  (* ================================================================== *)
  Context (sd : lm_st M).
  Local Notation st so := (gs_state M sd so).

  (* A READ WHOSE WINDOW COMPLETES A WILD LINE finds: no arm open (the
     arm's byte would follow the line), every echoed entry delivered (an
     undelivered one would, and its history is disciplined), nothing of
     the line's block written ((A2): the block's first byte needs the
     line delivered), and the choice list one short *)
  Lemma lm_rd_wild_stage (k : nat) (ho : list mobs) (so : gstage M)
      (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    gcl_pure M sd k ho so H ->
    (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
    ws <> [] ->
    (snd <$> (LogEntryDefs.ch_dl H ++ ws)) <> [] ->
    rest_of (snd <$> (LogEntryDefs.ch_dl H ++ ws)) = [] ->
    lm_wild (lm_line_at M (snd <$> (LogEntryDefs.ch_dl H ++ ws))) ->
    LogEntryDefs.ch_arm H = None
    /\ LogEntryDefs.ch_dl H ++ ws = echoed (LogEntryDefs.ch_log H)
    /\ (snd <$> gs_E M so) = (snd <$> (LogEntryDefs.ch_dl H ++ ws))
    /\ gs_w M so = []
    /\ length (gs_cs M so) = nlines (snd <$> gs_E M so) - 1.
  Proof using.
    intros (Hout & Hcsl & _ & Hin & Hera & HEt & Hdlok) Hpref Hws Hne Hr Hwild.
    destruct Hout as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc
                      & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok).
    destruct Hin as (Hlog & _ & _ & _ & _ & _ & _ & _ & Hdh).
    set (I := snd <$> (LogEntryDefs.ch_dl H ++ ws)) in *.
    set (EL := echoed (LogEntryDefs.ch_log H)) in *.
    assert (Hpl : forall j x, gs_E M so !! j = Some x -> x.1 `prefix_of` open_seg ho)
      by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
    pose proof (E_bytes_of_hist (gs_E M so) (open_seg ho) Hidx Hpl Hpre2) as HEB.
    assert (HELE : seg_of EL `prefix_of` gs_E M so)
      by (rewrite HEt /ch_E; by eexists).
    assert (HIEL : I `prefix_of` (snd <$> EL))
      by (exact (epu_fmap_prefix snd _ _ Hpref)).
    assert (HIE : I `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HIEL |]. rewrite -(seg_of_snd EL). by apply epu_fmap_prefix. }
    assert (HEBo : (snd <$> gs_E M so) `prefix_of` ins (open_seg ho))
      by (rewrite HEB; apply prefix_take).
    assert (HlenEL : length EL <= length (LogEntryDefs.ch_log H)).
    { rewrite /EL /echoed length_fmap. apply length_filter. }
    (* (A) no arm is open *)
    assert (Harm : LogEntryDefs.ch_arm H = None).
    { destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; [exfalso | done].
      rewrite /garm_era Ha in Hera.
      destruct Hera as (_ & _ & Hdh' & Hsh' & -> & _ & HK1).
      assert (HIo : I `prefix_of` ins (open_seg ho)) by (etrans; [exact HIE | exact HEBo]).
      assert (HlI : length I <= length EL)
        by (rewrite /I; apply prefix_length in HIEL; rewrite length_fmap in HIEL; exact HIEL).
      destruct (wild_prefix_strict_snoc I _ HIo ltac:(lia)) as [x Hx].
      exact (lm_disc_wild_last ho I x Hdh' Hsh' Hne Hr Hwild Hx). }
    assert (HEseg : gs_E M so = seg_of EL)
      by (rewrite HEt /ch_E Harm /ch_arm_E app_nil_r; reflexivity).
    (* (B) every echoed entry is delivered *)
    assert (HlenI : length EL <= length I).
    { destruct (decide (length EL <= length I)) as [? | Hgt]; [done | exfalso].
      destruct (lookup_lt_is_Some_2 (seg_of EL) (length I)
                  ltac:(rewrite /seg_of length_fmap; lia)) as [x Hx].
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (EL !! length I) as [y |] eqn:Hy; [| discriminate].
      cbn in Hx. injection Hx as <-.
      destruct (echoed_lookup _ _ _ Hy) as (e & He & _ & <-). cbn [fst snd].
      assert (HxE : gs_E M so !! length I = Some (open_seg (le_hist e), le_byte e)).
      { rewrite HEseg /seg_of list_lookup_fmap Hy. reflexivity. }
      destruct (Hidx _ _ HxE) as [_ Hlx]. cbn [fst] in Hlx.
      pose proof (ins_prefix_of _ _ (Hpl _ _ HxE)) as Hxo. cbn [fst] in Hxo.
      assert (HlenE : length I < length (snd <$> gs_E M so)).
      { rewrite HEseg length_fmap /seg_of length_fmap. lia. }
      assert (Htake : ins (open_seg (le_hist e))
                      = take (S (length I)) (snd <$> gs_E M so)).
      { rewrite HEB take_take. rewrite (_ : S (length I) `min` length (gs_E M so)
                                         = S (length I)); [| rewrite length_fmap in HlenE; lia].
        destruct Hxo as [z Hz]. rewrite Hz -Hlx take_app_length. reflexivity. }
      destruct (wild_prefix_strict_snoc I _ HIE HlenE) as [b Hb].
      apply (lm_disc_wild_last (le_hist e) I b (proj1 (Hdh e He)) (proj2 (Hdh e He))
               Hne Hr Hwild).
      rewrite Htake. destruct Hb as [z Hz]. rewrite Hz.
      rewrite (_ : S (length I) = length (I ++ [b])); [| rewrite length_app /=; lia].
      rewrite take_app_length. reflexivity. }
    assert (Hdlall : LogEntryDefs.ch_dl H ++ ws = EL).
    { apply prefix_length_eq; [exact Hpref |].
      rewrite /I length_fmap in HlenI. exact HlenI. }
    assert (HEI : (snd <$> gs_E M so) = I).
    { rewrite HEseg seg_of_snd /I Hdlall. reflexivity. }
    (* (C) nothing of the block is written *)
    assert (Hw : gs_w M so = []).
    { destruct (decide (gs_w M so = [])) as [? | Hwne]; [done | exfalso].
      rewrite /lm_dl_ok decide_False in Hdlok; [| by intros [_ ?]].
      pose proof (lines_bytes_rest (snd <$> gs_E M so)) as Hlb.
      rewrite HEI Hr in Hlb. cbn [length] in Hlb.
      rewrite HEI in Hdlok.
      assert (HlI' : length I = length (LogEntryDefs.ch_dl H) + length ws)
        by (rewrite /I length_fmap length_app; reflexivity).
      destruct ws; [done | cbn [length] in HlI'; lia]. }
    split_and!; [exact Harm | exact Hdlall | exact HEI | exact Hw |].
    rewrite /lm_cs_len_ok decide_True in Hcsl; [exact Hcsl |].
    split; [exact Hw | rewrite HEI; exact Hr].
  Qed.
  (* ================================================================== *)
  (*  S5a.  THE SECCOMP NEWLINE'S TRACE, AND WHAT A LATER BYTE'S IS       *)
  (* ================================================================== *)

  (* AT A READ: the delivered list's LAST trace names the whole delivered
     input.  The delivered entries are echoed log entries (their era, their
     shape), consecutive ones extend ([read_ok]'s [hist_chain]), so every
     earlier trace's segment is a prefix of the last one's, and [E_index]
     puts entry [j]'s byte at input position [j]. *)
  Lemma lm_rd_last_hist (k : nat) (pops : list log_entry)
      (D : list (list mobs * bv 8)) :
    D `prefix_of` echoed pops -> E_index (seg_of (echoed pops)) ->
    (forall e, e ∈ pops -> obs_boots (le_hist e) = k) ->
    (forall e, e ∈ pops -> trace_shape (le_hist e) true) ->
    hist_chain D -> D <> [] ->
    exists (h0 : list mobs) (c0 : bv 8),
      list_basics.last D = Some (h0, c0) /\ ins (open_seg h0) = snd <$> D
      /\ obs_boots h0 = k /\ trace_shape h0 true.
  Proof using.
    intros HD Hidx Hbt Hsh Hch Hne.
    destruct (list_basics.last D) as [[h0 c0] |] eqn:Hl; last first.
    { exfalso. apply Hne. by apply last_None. }
    assert (Hlk : D !! (length D - 1)%nat = Some (h0, c0)).
    { rewrite -Hl last_lookup. f_equal. destruct D; cbn; [done | lia]. }
    assert (Hof : forall x, x ∈ D -> obs_boots x.1 = k /\ trace_shape x.1 true).
    { intros x Hx.
      destruct (echoed_elem_inv pops x (elem_of_prefix _ _ _ Hx HD)) as (e & He & _ & <-).
      split; [exact (Hbt e He) | exact (Hsh e He)]. }
    destruct (Hof (h0, c0) (elem_of_list_lookup_2 _ _ _ Hlk)) as [Hb0 Hs0].
    assert (HidxD : E_index (seg_of D)).
    { intros j x Hx. apply Hidx.
      apply (prefix_lookup_Some _ _ _ _ Hx).
      destruct HD as [z ->]. rewrite seg_of_app. by eexists. }
    assert (Hpre : forall j x, seg_of D !! j = Some x -> x.1 `prefix_of` open_seg h0).
    { intros j x Hx. rewrite /seg_of list_lookup_fmap in Hx.
      destruct (D !! j) as [[hj cj] |] eqn:Hj; [| discriminate Hx].
      injection Hx as <-. cbn [fst].
      pose proof (lookup_lt_Some _ _ _ Hj) as Hjl.
      destruct (decide (j = length D - 1)%nat) as [-> | Hjne].
      { rewrite Hlk in Hj. injection Hj as -> ->. done. }
      destruct (hist_chain_lt D j (length D - 1) hj cj h0 c0 Hch ltac:(lia) Hj Hlk)
        as [Hp _].
      destruct (Hof (hj, cj) (elem_of_list_lookup_2 _ _ _ Hj)) as [Hbj _].
      apply (open_seg_prefix_of_boots hj h0 Hp); [cbn [fst] in Hbj; rewrite Hbj Hb0; reflexivity | exact Hs0]. }
    assert (Hlen : length (ins (open_seg h0)) = length D).
    { assert (Hx : seg_of D !! (length D - 1)%nat = Some (open_seg h0, c0))
        by (rewrite /seg_of list_lookup_fmap Hlk; reflexivity).
      destruct (HidxD _ _ Hx) as [_ Hl']. cbn [fst] in Hl'.
      destruct D; cbn in *; [done | lia]. }
    pose proof (E_bytes_of_hist (seg_of D) (open_seg h0) HidxD Hpre
                  ltac:(rewrite seg_of_length; lia)) as Hby.
    rewrite seg_of_snd seg_of_length take_ge in Hby; [| lia].
    exists h0, c0. split_and!; [reflexivity | by rewrite Hby | exact Hb0 | exact Hs0].
  Qed.

  (* THE CHAIN LEMMA (seccomp design 10.12): a byte the ring stored AFTER
     the seccomp newline (position [n0], trace [h0], whose era input [I0]
     ends in a complete wild line) has a push trace that strictly extends
     the newline's; in the newline's own era that trace's input has a byte
     after [I0], so D4 ([lm_disc_wild_last]) says it is not disciplined. *)
  Lemma lm_placed_wild_undisc (sl : list (list mobs * bv 8)) (n0 lo k d : nat)
      (hs : list (list mobs)) (j : nat) (h0 : list mobs) (c0 : bv 8)
      (I0 : list (bv 8)) :
    cons_chain sl -> sl !! n0 = Some (h0, c0) -> (n0 < lo)%nat ->
    cons_placed sl lo k d hs -> (j < d)%nat ->
    I0 `prefix_of` ins (open_seg h0) ->
    I0 <> [] -> rest_of I0 = [] -> lm_wild (lm_line_at M I0) ->
    trace_shape (hs !!! j) true -> obs_boots (hs !!! j) = obs_boots h0 ->
    ~ lm_disc M (hs !!! j).
  Proof using.
    intros Hch Hn0 Hlo [_ Hpl] Hj HI0 Hne Hr Hw Hsh Hbt Hd.
    destruct (Hpl j Hj) as (p & h & b & Hp & Hhs & [g Hg] & Hsl & _).
    rewrite (list_lookup_total_correct _ _ _ Hhs) in Hsh Hbt Hd.
    destruct (Hch n0 p h0 h c0 b Hn0 Hsl ltac:(lia)) as [[z Hz] Hlt].
    subst h.
    assert (Hg0 : h0 `prefix_of` g).
    { destruct z as [| e z _] using rev_ind.
      - rewrite app_nil_r in Hz. subst h0. lia.
      - rewrite app_assoc in Hz. apply app_inj_tail in Hz as [-> _]. by eexists. }
    assert (Hshg : trace_shape g true).
    { revert Hsh. rewrite /trace_shape foldl_app.
      destruct (foldl obs_step (Some false) g) as [[|] |]; cbn; done. }
    assert (Hbg : obs_boots g = obs_boots h0).
    { rewrite obs_boots_app in Hbt. cbn in Hbt. lia. }
    pose proof (open_seg_prefix_of_boots h0 g Hg0 (eq_sym Hbg) Hshg) as Hseg.
    assert (Hins : ins (open_seg (g ++ [ObsUartIn Uart0 b])) = ins (open_seg g) ++ [b]).
    { rewrite open_seg_io; [| by repeat constructor]. by rewrite ins_app ins_in. }
    assert (HIg : I0 `prefix_of` ins (open_seg g)).
    { etrans; [exact HI0 | exact (ins_prefix_of _ _ Hseg)]. }
    destruct HIg as [u Hu].
    set (c := match u with [] => b | x :: _ => x end).
    apply (lm_disc_wild_last (g ++ [ObsUartIn Uart0 b]) I0 c Hd Hsh Hne Hr Hw).
    rewrite Hins Hu. destruct u as [| x u]; cbn [c].
    - rewrite app_nil_r. done.
    - exists (u ++ [b]). by rewrite -!app_assoc.
  Qed.
End gen_out_wild.
