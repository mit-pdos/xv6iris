(* ===================================================================== *)
(*  PipeOutN.v -- THE N-WRITER ROUND'S CLAIM (design:                    *)
(*  claude-notes/design/pipes-general.md SS2.2, cut C5).                 *)
(*                                                                       *)
(*  [PipeOut.pecl] -- the generic claim between rounds, [popen] while a  *)
(*  two-writer round is open -- at the per-stage outcome model           *)
(*  [PipesDisc.pipes_lm], with the open round read off the line MODEL    *)
(*  and not off [PipeDisc]'s alternatives:                               *)
(*                                                                       *)
(*    pecl' := gcl (pipes_lm fc adm) .. ∨ popenN                         *)
(*                                                                       *)
(*  1. The open reading, pure and over ANY line model ([lm_blk_open],    *)
(*     [gcl_pure_o]), with the three out-steps of the pure part.         *)
(*  1b. THE CLAIM OVER ANY LINE MODEL (cut C9c'): [peclV := gcl M G sd   *)
(*     WA ∨ popenV], its three steps at the state the writer's witness   *)
(*     pins, the credential [pwc_blkV] at the ROUND'S STATE, the ONE     *)
(*     obligation ([pblkV_ecl_holds]), and -- through a pipeline view    *)
(*     ([PipesView.pview]) -- the non-terminal witness and the filing.   *)
(*     The union's claim (C9e') instantiates it at [UnionDisc.ulm].     *)
(*  2. The claim at [pipes_lm] -- section 1b's by conversion: its        *)
(*     parameters (the laws are the                                      *)
(*     caller's, the hooks the model's own [PipesDiscDec.pipes_hooks]),  *)
(*     [popenN], [pecl'], and the three claim steps                      *)
(*     [pecl'_blkN_open_gen] / [_byte_gen] / [_file], the twins of the   *)
(*     landed [PipeOut.pecl_blk2_*].                                     *)
(*  3. The family's credential [pwc_blkN] and the ONE obligation         *)
(*     [PipeBothN.eclN] it asks of the claim, PROVED here               *)
(*     ([pblkN_ecl_holds]), and the model's blocks as the claim's        *)
(*     non-terminal witness ([pipesN_HWIT]).                              *)
(*  4a/4b. THE FAMILY at a pipeline round of any model with a view (the  *)
(*     pipeline application's is its instance).                          *)
(*  5. THE N = 2 CHECK: the landed two-writer merge IS the N-form at     *)
(*     [W := bool], and the landed [PipeBoth.pblk2_wit_both] (the        *)
(*     witness the landed byte steps spend at a [PBoth] round) is        *)
(*     re-derived from [PipeBothNPure.pendN_complete] through the n = 1 *)
(*     bridge of C2 ([PipesDisc.palt_of_ok]).                             *)
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
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesPair.
Require Import PipesDisc.
Require Import PipesDiscDec.      (* [pipes_hooks] *)
Require Import PipesView.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeOutPure.         (* [pline_at] *)
Require Import RiscvPtsto.
Require Import WpUart.
(* stdpp's list names over the ones the Stdlib import above re-exports *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE OPEN READING, OVER ANY LINE MODEL                             *)
(* ===================================================================== *)

Lemma lmN_prefix_head {A} (l : list A) (b : A) : l !! 0%nat = Some b -> [b] `prefix_of` l.
Proof using. destruct l as [| x l]; [discriminate | cbn; intros [= ->]; by exists l]. Qed.

Section open_pure.
  Context (M : lmodel) (sd : lm_st M).
  Local Notation st so := (gs_state M sd so).

  (* [GenOutPure.lm_out_pure] minus the conjunct that reads the block off
     the choice list: the landed [PipeOut.pout_pure_o], once *)
  Definition lm_out_pure_o (k : nat) (ho : list mobs) (so : gstage M)
      (acc : list (bv 8)) : Prop :=
    acc = lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) ++ gs_w M so
    /\ E_index (gs_E M so)
    /\ lm_E_disc M (gs_E M so)
    /\ Forall (fun a => (a < length pro_alts)%nat) (gs_ps M so)
    /\ lm_pro_pin M (gs_ps M so) (gs_cs M so) (snd <$> gs_E M so)
    /\ lm_alts_pre M (st so) (snd <$> gs_E M so) (gs_cs M so)
    /\ Forall (fun x => lm_disc_input M (ins x.1)) (gs_E M so)
    /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (gs_E M so)
    /\ (length (gs_E M so) <= length (ins (open_seg ho)))%nat
    /\ (gs_E M so = [] \/ obs_boots ho = k)
    /\ Forall (fun c => lm_term M (lm_dec M c) = false) (gs_cs M so)
    /\ (gs_st M so = None <-> (gs_E M so = [] /\ gs_w M so = []))
    /\ lm_st_ok M (st so).

  (* THE ROUND'S LINE AND AN ADMITTED ALTERNATIVE the block so far is a
     prefix of: [PipeOutPure.pblk2_at], at the model *)
  Definition lm_blk_at (cs : list nat) (I : list (bv 8)) (s : lm_st M)
      (pre : list (bv 8)) (a : nat) : Prop :=
    I <> [] /\ rest_of I = [] /\ length cs = (nlines I - 1)%nat
    /\ lm_ok M (lm_upto M cs s (bodies_of I) (nlines I - 1))
         (lm_of M (bodies_of I !!! (nlines I - 1))) (lm_dec M a)
    /\ lm_panic M (lm_dec M a) = false
    /\ pre `prefix_of` lm_cont M (lm_upto M cs s (bodies_of I) (nlines I - 1))
                         (lm_of M (bodies_of I !!! (nlines I - 1))) (lm_dec M a).

  (* THE BLOCK IN PROGRESS: [PipeOut.pblk_open], at the model *)
  Definition lm_blk_open (so : gstage M) (r : nat) (pre : list (bv 8)) : Prop :=
    r = (nlines (snd <$> gs_E M so) - 1)%nat
    /\ gs_w M so = pre
    /\ pre <> []
    /\ exists a : nat,
         lm_blk_at (gs_cs M so) (snd <$> gs_E M so) (st so) pre a
         /\ ((lm_term M (lm_dec M a) = false /\ Forall nodollar pre)
             \/ lm_term M (lm_dec M a) = true).

  (* the claim's pure part WHILE A ROUND IS OPEN: [PipeOut.pcl_pure_o] *)
  Definition gcl_pure_o (k : nat) (ho : list mobs) (so : gstage M)
      (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) : Prop :=
    lm_out_pure_o k ho so (LogEntryDefs.ch_acc H)
    /\ lm_blk_open so r pre
    /\ lm_ps_len_ok M sd so
    /\ gin_pure M k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (gs_cs M so)
    /\ garm_era M k ho H
    /\ gs_E M so = ch_E H
    /\ lm_dl_ok M so (LogEntryDefs.ch_dl H).

  Lemma gcl_pure_o_dl_E k ho so r pre H :
    gcl_pure_o k ho so r pre H ->
    (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> gs_E M so).
  Proof using.
    intros (_ & _ & _ & Hin & _ & HE & _).
    destruct Hin as (_ & _ & _ & Hdlp & _).
    rewrite HE /ch_E.
    etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
    rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
    apply epu_fmap_prefix. by apply prefix_app_r.
  Qed.

  (* THE THREE OUT-STEPS of the pure part: opening, keeping, closing *)
  Lemma gcl_pure_o_out k ho (so so' : gstage M) r pre H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_blk_open so' r pre -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure M sd k ho so H ->
    gcl_pure_o k ho so' r pre (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall & Hdh).
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall | exact Hdh].
    - by rewrite HE' HE /ch_E.
  Qed.

  Lemma gcl_pure_o_out2 k ho (so so' : gstage M) r r' pre pre' H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_blk_open so' r' pre' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure_o k ho so r pre H ->
    gcl_pure_o k ho so' r' pre' (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall & Hdh).
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall | exact Hdh].
    - by rewrite HE' HE /ch_E.
  Qed.

  Lemma gcl_pure_of_o_out k ho (so so' : gstage M) r pre H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure M sd k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_cs_len_ok M so' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure_o k ho so r pre H ->
    gcl_pure M sd k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall & Hdh).
    rewrite /gcl_pure /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall | exact Hdh].
    - by rewrite HE' HE /ch_E.
  Qed.

  (* [GenOutPure.lm_ps_len_ok_blk] at ANY written block: the filing byte
     of a round whose block several writers put out ([PipeOut]'s
     [ps_len_ok_p_blk_w], once) *)
  Lemma lm_ps_len_ok_blk_w (B : lm_byte_laws M) (so : gstage M) (a : nat)
      (w' : list (bv 8)) :
    rest_of (snd <$> gs_E M so) = [] ->
    (snd <$> gs_E M so) <> [] ->
    length (gs_cs M so) = (nlines (snd <$> gs_E M so) - 1)%nat ->
    lm_ps_len_ok M sd so ->
    lm_ps_len_ok M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) w'
                        (gs_st M so)).
  Proof using.
    intros Hr Hne Hq Hok.
    pose proof (nlines_pos_of_rest_nil (snd <$> gs_E M so) Hne Hr) as Hpos.
    pose proof Hok as [HA HB].
    rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB |- *.
    assert (Hold : lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))
                   = lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so) - 1)%nat).
    { replace (nlines (snd <$> gs_E M so))
        with (S (nlines (snd <$> gs_E M so) - 1))%nat at 1 by lia.
      apply lm_pro_idx_Sn. apply (lm_panic_ge M B). lia. }
    assert (Hnew : (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))
                    <= lm_pro_idx M (gs_cs M so ++ [a])
                         (nlines (snd <$> gs_E M so)))%nat).
    { rewrite Hold.
      replace (nlines (snd <$> gs_E M so))
        with (S (nlines (snd <$> gs_E M so) - 1))%nat at 2 by lia.
      rewrite lm_pro_idx_S
        (lm_pro_idx_app_le M (gs_cs M so) [a] (nlines (snd <$> gs_E M so) - 1)%nat
           ltac:(lia)).
      destruct (lm_panic M _); lia. }
    split.
    - apply (lm_ps_len_ok_empty_above M sd so); [exact Hok |].
      rewrite /lm_ps_round. exact Hnew.
    - intros Ho ps' Hp Hne2. exfalso.
      destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
      assert (Ha3 : lm_panic M (lm_dec M a) = true).
      { rewrite /lm_at list_lookup_total_alt lookup_app_r in H3; [| lia].
        rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
      assert (Heq : lm_pro_idx M (gs_cs M so ++ [a]) (nlines (snd <$> gs_E M so))
                    = S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so)))).
      { rewrite Hold
          -(lm_pro_idx_app_le M (gs_cs M so) [a] (nlines (snd <$> gs_E M so) - 1)%nat
              ltac:(lia)).
        replace (nlines (snd <$> gs_E M so))
          with (S (nlines (snd <$> gs_E M so) - 1))%nat at 1 by lia.
        apply lm_pro_idx_Sp.
        rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
        rewrite Hq Nat.sub_diag. by cbn. }
      rewrite Heq in Hne2. apply Hne2.
      assert (Hnil : pro_from
                       (S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))))
                       (gs_ps M so) = []) by exact HA.
      assert (Hnil' : pro_from
                        (S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))))
                        ps' = []).
      { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
      by rewrite Hnil Hnil'.
  Qed.
End open_pure.

(* the continuation of a round whose alternative does not panic is the
   alternative's own, with no prologue after it *)
Lemma lmN_cont_at_nopanic (M : lmodel) ps cs s bs i :
  lm_panic M (lm_at M cs i) = false ->
  lm_cont_at M ps cs s bs i = lm_cont M (lm_upto M cs s bs i) (lm_of M (bs !!! i)) (lm_at M cs i).
Proof using. intros H. rewrite /lm_cont_at H. apply app_nil_r. Qed.

(* ===================================================================== *)
(*  1b.  THE CLAIM OVER ANY LINE MODEL (cut C9c', union.md B4)            *)
(*                                                                       *)
(*  [peclV := gcl M G sd WA ∨ popenV]: the generic claim between rounds, *)
(*  and the open round of any number of writers, at ANY line model [M],  *)
(*  its claim parameters [G], default state [sd] and state witness       *)
(*  [WA] whose stream extension is the pipe's era ledger ([Hext]).  The  *)
(*  open round carries the witness's authority ([gwa WA k (gs_st so)]),  *)
(*  so a writer's [gcW G k s0] pins the state its round is read at.     *)
(*  The pipeline application's [pecl'] (section 2) is this claim at      *)
(*  [pipes_lm] (state [unit], witness [emp]) by conversion; the union's  *)
(*  claim is it at [UnionDisc.ulm].                                      *)
(* ===================================================================== *)

(* THE OPEN ROUND at the model, its pin [PIN] and the witness's authority
   [X] ([gwa] of the state witness; [emp] at the pipeline application) *)
Section pipes_open_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn) (M : lmodel).
  Context (PIN : nat -> era_pins -> iProp Σ) (X : nat -> option (lm_st M) -> iProp Σ).
  Context (sd : lm_st M).

  Definition popenV (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (∃ (v : era_pins) (w : pipe_era) (so : gstage M)
       (r : nat) (gb : gname) (pre : list (bv 8)) (tm : bool),
       PIN k v ∗ pera_pin g k w ∗ X k (gs_st M so) ∗ blk_auth w (lm_stream M sd so)
       ∗ cur_half w (1/2) r gb tm ∗ rblk_auth gb pre
       ∗ turn_auth v (lm_pcount M (gs_ps M so) (gs_cs M so)
                        (gs_state M sd so) (gs_E M so) (gs_w M so))
       ∗ pcs v (gs_cs M so) tm
       ∗ ps_auth v (gs_ps M so)
       ∗ Elist_auth v (gs_E M so)
       ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
       ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
       ∗ ⌜gcl_pure_o M sd k ho so r pre H⌝)%I.
End pipes_open_v.

(* THE FAMILY'S CREDENTIAL AT THE MODEL: the pin [PIN], the writer's
   witness [W] and the taint [T] are the claim's ([gcPIN]/[gcW]/[gcT]);
   [sR] is the ROUND'S STATE -- the writer's boot state read up to the
   round's line -- at which the family's runs and the witnesses are read *)
Section pipes_cred_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn) (M : lmodel).
  Context (PIN : nat -> era_pins -> iProp Σ) (W : nat -> lm_st M -> iProp Σ) (T : iProp Σ).

  (* the round's line *)
  Definition lineV (I : list (bv 8)) : lm_line M :=
    lm_of M (bodies_of I !!! (nlines I - 1)%nat).

  (* the writer's stage at a block ([LineModel.lm_wr_blk_t]) *)
  Definition wr_blkV (ps cs : list nat) (s0 : lm_st M) (I : list (bv 8)) (P : nat) : Prop :=
    lm_wr_blk_t M ps cs s0 I P.

  (* THE ROUND'S LEDGER, as the family holds it *)
  Definition pledV (k : nat) (I pre : list (bv 8)) (tm : bool) : iProp Σ :=
    (⌜pre = []⌝ ∨ ∃ (w : pipe_era) (gb : gname),
        pera_pin g k w ∗ cur_half w (1/2) (nlines I - 1)%nat gb tm ∗ rblk_lb gb pre)%I.

  Definition pwc_blkV (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (k : nat)
      (pre : list (bv 8)) (tm : bool) : iProp Σ :=
    ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
        ⌜wr_blkV ps cs s0 I P /\ lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
        ∗ PIN k v ∗ W k s0 ∗ turn v (P + length pre)%nat
        ∗ ps_lb v ps ∗ cs_lb v cs ∗ pledV k I pre tm ∗ inp_lb v I) ∨ T)%I.

  Lemma pwc_blkV_timeless (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (k : nat)
      (pre : list (bv 8)) (tm : bool) :
    (forall k v, Timeless (PIN k v)) -> (forall k s, Timeless (W k s)) -> Timeless T ->
    Timeless (pwc_blkV v I sR k pre tm).
  Proof using . intros ???. rewrite /pwc_blkV /pledV. apply _. Qed.

  (* what a terminal byte hands its writer *)
  Definition ptkV (v : era_pins) (I : list (bv 8)) (k : nat) : iProp Σ :=
    (cs_frozen_at v (nlines I - 1)%nat ∨ T)%I.

  Lemma ptkV_persistent (v : era_pins) (I : list (bv 8)) (k : nat) :
    Persistent T -> Persistent (ptkV v I k).
  Proof using . intros ?. rewrite /ptkV. apply _. Qed.

  (* WHAT THE CLAIM ASKS OF A BLOCK at the flag [tm], at the round's state *)
  Definition pwitV (I : list (bv 8)) (sR : lm_st M) (tm : bool) (pre : list (bv 8)) : Prop :=
    exists a : nat,
      lm_ok M sR (lineV I) (lm_dec M a)
      /\ lm_panic M (lm_dec M a) = false
      /\ lm_term M (lm_dec M a) = tm
      /\ pre `prefix_of` lm_cont M sR (lineV I) (lm_dec M a)
      /\ (tm = false -> Forall nodollar pre).

  (* THE ENTRY: the lend a round's writer holds before the block's first
     byte is the credential at the empty block, at the round's state *)
  Lemma pwc_blkV_entry (v : era_pins) (I : list (bv 8)) (k : nat)
      (ps cs : list nat) (s0 : lm_st M) (P : nat) :
    wr_blkV ps cs s0 I P ->
    PIN k v -∗ W k s0 -∗ turn v P -∗ ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗
    pwc_blkV v I (lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat) k [] false.
  Proof using .
    intros Hw. iIntros "Hpin HW Ht Hps Hcs HE". rewrite /pwc_blkV. iLeft.
    iExists ps, cs, s0, P. iFrame "Hpin HW Hps Hcs HE".
    iSplitR; [iPureIntro; split; [exact Hw | reflexivity] |].
    cbn [length]. rewrite Nat.add_0_r. iFrame "Ht".
    rewrite /pledV. by iLeft.
  Qed.
End pipes_cred_v.

(* THE MODEL'S BLOCKS ARE THE CLAIM'S NON-TERMINAL WITNESS, through the
   view: at a pipeline line the model's alternative for a block of the
   line's runs is the view's [PLRun] *)
Lemma pipesV_HWIT (M : lmodel) (V : pview M) (I : list (bv 8)) (sR : lm_st M) (lR : pline') :
  pv_line V (lineV M I) = Some lR -> fc_ok (pv_fc V sR) -> pv_adm V lR = true -> pl_ok lR ->
  forall pre bl, blkN (wids (lcats lR)) (runN (pv_fc V sR) lR) bl ->
    pre `prefix_of` bl -> pwitV M I sR false pre.
Proof using.
  intros HlR Hfc Ha Hl pre bl Hb Hp.
  exists (pv_enc V lR (PLRun bl)). split_and!.
  - exact (pv_run_ok V sR _ lR bl HlR Ha (blkN_line_blocks (pv_fc V sR) lR bl Hb)).
  - exact (pv_run_panic V lR bl).
  - exact (pv_run_term V lR bl).
  - rewrite (pv_run_cont V sR _ lR bl HlR). etrans; [exact Hp |]. by eexists.
  - intros _. exact (prefix_forall _ _ _ Hp (pipesN_blk_nodollar (pv_fc V sR) lR bl Hfc Hl Hb)).
Qed.

Section pipes_out_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Context (M : lmodel) (G : gen_cparams M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  (* the stream extension is the pipe's era ledger *)
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT G).
  Local Notation PIN := (gcPIN G).
  Local Notation K := (gcK G).
  Local Notation st so := (gs_state M sd so).
  Local Notation POV := (popenV g M (gcPIN G) (gwa WA) sd).
  Local Notation PWV := (pwc_blkV g M (gcPIN G) (gcW G) (gcT G)).

  (* THE CLAIM *)
  Definition peclV (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (gcl M G sd WA k ho H ∨ POV k ho H)%I.

  Global Instance peclV_timeless k ho H : Timeless (peclV k ho H).
  Proof using . rewrite /peclV /popenV. apply _. Qed.

  Lemma peclV_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    T -∗ peclV k ho H.
  Proof using . iIntros "#HT". rewrite /peclV /gcl. iLeft. by iLeft. Qed.

  (* ---- (W-openN) THE ROUND'S FIRST BYTE, at the state the writer's
          witness pins ---- *)
  Lemma peclV_blkN_open_gen (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec M a) ->
    lm_panic M (lm_dec M a) = false ->
    lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec M a) !! 0%nat = Some b ->
    ((lm_term M (lm_dec M a) = false /\ nodollar b)
     \/ lm_term M (lm_dec M a) = true) ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    peclV k ho H ==∗
      peclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (w : pipe_era) (gb : gname),
            turn v (S P) ∗ pera_pin g k w
            ∗ cur_half w (1/2) (nlines I0 - 1)%nat gb (lm_term M (lm_dec M a))
            ∗ rblk_lb gb [b]
            ∗ (⌜lm_term M (lm_dec M a) = false⌝
               ∨ cs_frozen_at v (nlines I0 - 1)%nat)
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using Hext.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hpan Hhead Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]"; last first.
    { (* AN OPEN ROUND has already written a byte: the turn refutes it *)
      iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
      iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
      assert (Hst' : st so = s0) by exact Hst.
      clear Hst. subst s0.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen)]. }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _).
      assert (Hs2 : lm_proc_before M ps0 cs0 (st so) I0
                    = lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) I0).
      { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so) (st so) I0
                 Hpsp Hcsp Hpin0). lia. }
      pose proof (prefix_length _ _
        (lm_proc_before_prefix M (gs_ps M so) (gs_cs M so) (st so) I0
           (snd <$> gs_E M so) HI0)) as Hle2.
      assert (Hwne : (1 <= length (gs_w M so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP. rewrite HPeq Hs2 in HP.
      exfalso. lia. }
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [by iApply peclV_taint | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hx & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    rewrite Hext.
    iDestruct "Hx" as (w r gb pre tm) "(#Hpera & Hblk & Hcur & Hrb)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
    assert (Hst' : st so = s0) by exact Hst.
    clear Hst. subst s0.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so H Hall0)]. }
    assert (Hstream : lm_proc_before M ps0 cs0 (st so) I0
                      = lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so)
               (st so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (HlenE : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so)
                    (st so) I0 (snd <$> gs_E M so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (lm_pending_at_nonnil_at M K (gs_ps M so) (gs_cs M so)
                    (st so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at M (gs_ps M so) (gs_cs M so)
                                     (st so) I0))%nat).
      { destruct (lm_pending_at M (gs_ps M so) (gs_cs M so) (st so) I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hwnil : gs_w M so = []).
    { assert (Hz : length (gs_w M so) = 0%nat).
      { rewrite /lm_pcount in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = gs_cs M so).
    { apply (prefix_length_eq cs0 (gs_cs M so) Hcsp). rewrite Hq. lia. }
    subst cs0.
    assert (Hpc2 : lm_pcount M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) [b] = S P).
    { rewrite /lm_pcount HlenE -Hstream. cbn [length]. lia. }
    (* the round's OWN ledger, minted here and nowhere else *)
    iMod rblk_alloc as (gb2) "Hrb2".
    iMod (rblk_auth_grow gb2 [] b with "Hrb2") as "[Hrb2 #Hrlb]".
    iMod (cur_retarget w r gb tm (nlines I0 - 1)%nat gb2
            (lm_term M (lm_dec M a)) with "Hcur") as "Hcur".
    iDestruct (cur_split w (nlines I0 - 1)%nat gb2 (lm_term M (lm_dec M a))
                 with "Hcur") as "[Hcur1 Hcur2]".
    iDestruct (pcs_of_auth v (gs_cs M so) false eq_refl with "Hcs") as "Hcs".
    iAssert (|==> pcs v (gs_cs M so) (lm_term M (lm_dec M a))
                  ∗ (⌜lm_term M (lm_dec M a) = false⌝
                     ∨ cs_frozen_at v (nlines I0 - 1)%nat))%I
      with "[Hcs]" as ">[Hcs #Hfz]".
    { destruct (lm_term M (lm_dec M a)) eqn:Hfk2.
      - iMod (pcs_freeze v (gs_cs M so) false with "Hcs") as "[Hcs #Hf]".
        iModIntro. iFrame "Hcs". iRight.
        iApply (cs_frozen_at_of v (gs_cs M so) (nlines I0 - 1)%nat with "Hf").
        exact Hq.
      - iModIntro. iFrame "Hcs". iLeft. by iPureIntro. }
    iMod (turn_update v P _ (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream M sd so) b with "Hblk") as "[Hblk _]".
    iModIntro. iSplitR "Ht Hcur2".
    - rewrite /peclV. iRight.
      iExists v, w, (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) [b] (gs_st M so)),
              (nlines I0 - 1)%nat, gb2, [b], (lm_term M (lm_dec M a)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) [b]
                                    (gs_st M so)) = st so); [| reflexivity].
      rewrite Hpc2.
      rewrite (_ : lm_stream M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      [b] (gs_st M so))
                   = lm_stream M sd so ++ [b]); last first.
      { rewrite /lm_stream. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite Hwnil app_nil_r. reflexivity. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hwa Hblk Hcur1 Hrb2 Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_o_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) [b] (gs_st M so))
               (nlines I0 - 1)%nat [b] H b);
        [cbn [gs_cs]; lia | reflexivity | | | | | exact Hall0].
      + rewrite /lm_out_pure_o. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) [b]
                                      (gs_st M so)) = st so); [| reflexivity].
        split_and!.
        * rewrite Hacc Hwnil app_nil_r. reflexivity.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split; [| intros [_ Hq2]; discriminate Hq2].
          intros Hnone. exfalso. destruct (proj1 Hf0n Hnone) as [HE0 _].
          apply Hne0. by rewrite -HlenE HE0.
        * exact Hfok0.
      + rewrite /lm_blk_open. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        split_and!; [by rewrite HlenE | reflexivity | done |].
        exists a. split.
        { rewrite /lm_blk_at HlenE.
          split_and!; [exact Hne0 | exact Hr0 | exact Hq | exact Halt | exact Hpan |].
          apply lmN_prefix_head. exact Hhead. }
        destruct Hfarm as [[Hfk Hnd] | Hfk];
          [left; split; [exact Hfk | by apply Forall_singleton] | by right].
      + pose proof (lm_ps_len_ok_write M sd so b Hpsl) as Hx.
        rewrite Hwnil in Hx. exact Hx.
      + apply (lm_dl_ok_out_full M so
                 (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) [b] (gs_st M so)));
          [reflexivity | cbn [gs_w]; discriminate | by rewrite HlenE |].
        pose proof (prefix_length _ _ HI0dl) as Hlp.
        rewrite !length_fmap in Hlp. rewrite HlenE. lia.
    - iLeft. iExists w, gb2.
      iFrame "Ht Hpera Hcur2 Hrlb Hfz Hpslb Hcslb Hilb".
  Qed.

  (* ---- (W-byteN) A FURTHER BYTE OF AN OPEN ROUND, by ANY of its
          writers ---- *)
  Lemma peclV_blkN_byte_gen (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (tmi : bool) (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_upto M cs0 s0 (bodies_of I0) r) (lm_of M (bodies_of I0 !!! r)) (lm_dec M a) ->
    lm_panic M (lm_dec M a) = false ->
    (pre0 ++ [b]) `prefix_of`
      lm_cont M (lm_upto M cs0 s0 (bodies_of I0) r) (lm_of M (bodies_of I0 !!! r)) (lm_dec M a) ->
    ((lm_term M (lm_dec M a) = false /\ Forall nodollar pre0 /\ nodollar b)
     \/ lm_term M (lm_dec M a) = true) ->
    PIN k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb tmi -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    peclV k ho H ==∗
      peclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat
          ∗ cur_half w (1/2) r gb (tmi || lm_term M (lm_dec M a))
          ∗ rblk_lb gb (pre0 ++ [b])
          ∗ (⌜lm_term M (lm_dec M a) = false⌝ ∨ cs_frozen_at v r)) ∨ T).
  Proof using Hext.
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hpref Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]".
    { (* BETWEEN ROUNDS the claim holds the whole ghost *)
      iDestruct "Hcl" as "[#HT | Hp]".
      { iModIntro. iSplitR; [by iApply peclV_taint | by iRight]. }
      iDestruct "Hp" as (v2 so) "(_ & _ & Hx & _)".
      rewrite Hext.
      iDestruct "Hx" as (w2 r2 gb2 pre tm) "(#Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm)
      "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
    assert (Hst' : st so = s0) by exact Hst.
    clear Hst. subst s0.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    assert (Hs2 : lm_proc_before M ps0 cs0 (st so) I0
                  = lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so) (st so) I0
               Hpsp Hcsp Hpin0).
      rewrite (ll_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
    assert (HIeq : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done |].
      exfalso.
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so) (st so) I0
                    (snd <$> gs_E M so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
      apply prefix_length in Hp2.
      rewrite /lm_proc_stream length_app -Hs2 in Hp2.
      pose proof (lm_pending_at_nonnil_at M K (gs_ps M so) (gs_cs M so)
                    (st so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at M (gs_ps M so) (gs_cs M so)
                                     (st so) I0))%nat).
      { destruct (lm_pending_at M (gs_ps M so) (gs_cs M so) (st so) I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hlen0 : length pre0 = length (gs_w M so)).
    { rewrite /lm_pcount HIeq -Hs2 -HPeq in HP. lia. }
    assert (Hpre0 : pre0 = gs_w M so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    assert (Hcs0 : cs0 = gs_cs M so).
    { apply (prefix_length_eq cs0 (gs_cs M so) Hcsp). rewrite Hcseq Hqq Hreq2. lia. }
    subst cs0.
    (* THE TERMINAL FIRE: a coverage-ending byte sets the flag and freezes *)
    iAssert (|==> pcs v (gs_cs M so) (tmi || lm_term M (lm_dec M a))
                  ∗ cur_half w (1/2) r gb (tmi || lm_term M (lm_dec M a))
                  ∗ cur_half w (1/2) r gb (tmi || lm_term M (lm_dec M a))
                  ∗ (⌜lm_term M (lm_dec M a) = false⌝ ∨ cs_frozen_at v r))%I
      with "[Hcs Hcur Hcw]" as ">(Hcs & Hcur & Hcw & #Hfz)".
    { destruct (lm_term M (lm_dec M a)) eqn:Hfk2.
      - rewrite (orb_true_r tmi).
        iMod (pcs_freeze v (gs_cs M so) tmi with "Hcs") as "[Hcs #Hf]".
        iMod (cur_half_update w r gb tmi r gb tmi r gb true
                with "Hcur Hcw") as "[Hcur Hcw]".
        iModIntro. iFrame "Hcs Hcur Hcw". iRight.
        iApply (cs_frozen_at_of v (gs_cs M so) r with "Hf").
        by rewrite Hqq Hreq2.
      - rewrite (orb_false_r tmi).
        iModIntro. iFrame "Hcs Hcur Hcw". iLeft. by iPureIntro. }
    iMod (rblk_auth_grow gb pre b with "Hrb") as "[Hrb #Hrlb1]".
    iMod (turn_update v (P + length pre0)%nat _ (S (P + length pre0)) ltac:(lia)
            with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream M sd so) b with "Hblk") as "[Hblk _]".
    assert (Hbod : bodies_of (snd <$> gs_E M so) !!! r = bodies_of I0 !!! r)
      by (by rewrite HIeq).
    assert (Hpc2 : lm_pcount M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so)
                     (gs_w M so ++ [b]) = S (P + length pre0)).
    { rewrite lm_pcount_write -HP. reflexivity. }
    iModIntro. iSplitR "Ht Hcw".
    - rewrite /peclV. iRight.
      iExists v, w, (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                       (gs_w M so ++ [b]) (gs_st M so)),
              r, gb, (pre ++ [b]), (tmi || lm_term M (lm_dec M a)).
      rewrite (lm_stream_write M sd so b).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                    (gs_w M so ++ [b]) (gs_st M so)) = st so);
        [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hwa Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_o_out2 M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                  (gs_w M so ++ [b]) (gs_st M so))
               r r pre (pre ++ [b]) H b);
        [cbn [gs_cs]; lia | reflexivity | | | | | exact Hopen].
      + rewrite /lm_out_pure_o. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so)) = st so);
          [| reflexivity].
        split_and!.
        * rewrite Hacc app_assoc. reflexivity.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split.
          -- intros Hn. exfalso. destruct (proj1 Hf0n Hn) as [_ Hw0].
             rewrite Hwp' in Hw0. exact (Hne' Hw0).
          -- intros [_ Hq2]. exfalso. destruct (app_eq_nil _ _ Hq2) as [_ Hq3].
             discriminate Hq3.
        * exact Hfok0.
      + rewrite /lm_blk_open. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        split_and!; [exact Hreq2 | by rewrite Hwp' |
                     intros Hz; destruct (app_eq_nil _ _ Hz) as [_ Hz2]; discriminate Hz2 |].
        exists a. split.
        { rewrite /lm_blk_at. rewrite -Hreq2 Hbod.
          split_and!; [exact Hnn | exact Hrr | by rewrite Hqq Hreq2 | | exact Hpan |].
          - rewrite HIeq. exact Halt.
          - rewrite HIeq -Hwp' -Hpre0. exact Hpref. }
        destruct Hfarm as [(Hfk & Hnd0 & Hnd) | Hfk]; [| by right].
        left. split; [exact Hfk |].
        apply Forall_app. split; [| by apply Forall_singleton].
        rewrite -Hwp' -Hpre0. exact Hnd0.
      + exact (lm_ps_len_ok_write M sd so b Hpsl).
      + apply (lm_dl_ok_out M so
                 (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                    (gs_w M so ++ [b]) (gs_st M so)));
          [reflexivity | cbn [gs_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite Hpre0 -Hwp'. iFrame "Ht Hcw Hrlb1 Hfz".
  Qed.

  (* ---- (W-fileN) THE FILING, at the prompt's first byte ---- *)
  Lemma peclV_blkN_file (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_upto M cs0 s0 (bodies_of I0) r) (lm_of M (bodies_of I0 !!! r)) (lm_dec M a) ->
    lm_panic M (lm_dec M a) = false ->
    lm_term M (lm_dec M a) = false ->
    lm_cont M (lm_upto M cs0 s0 (bodies_of I0) r) (lm_of M (bodies_of I0 !!! r)) (lm_dec M a)
      = pre0 ++ u_prompt ->
    b = u_prompt !!! 0%nat ->
    PIN k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ gcW G k s0 -∗
    peclV k ho H ==∗
      peclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat ∗ ps_lb v ps0
          ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T).
  Proof using B Hext.
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hcont Hbv.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]".
    { iDestruct "Hcl" as "[#HT | Hp]".
      { iModIntro. iSplitR; [by iApply peclV_taint | by iRight]. }
      iDestruct "Hp" as (v2 so) "(_ & _ & Hx & _)".
      rewrite Hext.
      iDestruct "Hx" as (w2 r2 gb2 pre tm) "(#Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm)
      "(#Hpin2 & #Hpera & Hwa & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (gcPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (gwa_agree WA with "Hwa HW") as %Hst.
    assert (Hst' : st so = s0) by exact Hst.
    clear Hst. subst s0.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E M sd _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    assert (Hs2 : lm_proc_before M ps0 cs0 (st so) I0
                  = lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so) (st so) I0
               Hpsp Hcsp Hpin0).
      rewrite (ll_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
    assert (HIeq : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done |].
      exfalso.
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so) (st so) I0
                    (snd <$> gs_E M so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
      apply prefix_length in Hp2.
      rewrite /lm_proc_stream length_app -Hs2 in Hp2.
      pose proof (lm_pending_at_nonnil_at M K (gs_ps M so) (gs_cs M so)
                    (st so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at M (gs_ps M so) (gs_cs M so)
                                     (st so) I0))%nat).
      { destruct (lm_pending_at M (gs_ps M so) (gs_cs M so) (st so) I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hlen0 : length pre0 = length (gs_w M so)).
    { rewrite /lm_pcount HIeq -Hs2 -HPeq in HP. lia. }
    assert (Hpre0 : pre0 = gs_w M so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    assert (Hcs0 : cs0 = gs_cs M so).
    { apply (prefix_length_eq cs0 (gs_cs M so) Hcsp). rewrite Hcseq Hqq Hreq2. lia. }
    subst cs0.
    iMod (turn_update v (P + length pre0)%nat _ (S (P + length pre0)) ltac:(lia)
            with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream M sd so) b with "Hblk") as "[Hblk _]".
    iDestruct (pcs_auth v (gs_cs M so) false eq_refl with "Hcs") as "Hcs".
    iMod (cs_auth_grow v (gs_cs M so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (cur_join w r gb false with "Hcur Hcw") as "Hcur".
    assert (Hbod : bodies_of (snd <$> gs_E M so) !!! r = bodies_of I0 !!! r)
      by (by rewrite HIeq).
    pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposc.
    assert (Hrlbnd : (nlines (removelast (snd <$> gs_E M so))
                      <= length (gs_cs M so))%nat).
    { rewrite (ll_nlines_removelast _ Hrr) Hqq. lia. }
    assert (Hpinq : lm_pro_pin M (gs_ps M so) (gs_cs M so ++ [a]) (snd <$> gs_E M so)).
    { intros qq Hqq2. rewrite lm_pro_idx_app_le; [by apply Hpin |].
      rewrite (nstarted_rest_nil _ Hrr) in Hqq2. rewrite Hqq. lia. }
    assert (HD : lm_D M (gs_ps M so) (gs_cs M so ++ [a]) (st so) (gs_E M so)
                 = lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so)).
    { symmetry.
      apply (lm_D_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
               (gs_cs M so ++ [a]) (st so) (gs_E M so));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hproc : lm_proc_before M (gs_ps M so) (gs_cs M so ++ [a]) (st so)
                      (snd <$> gs_E M so)
                    = lm_proc_before M (gs_ps M so) (gs_cs M so) (st so) (snd <$> gs_E M so)).
    { symmetry.
      apply (lm_proc_before_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
               (gs_cs M so ++ [a]) (st so) (snd <$> gs_E M so));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hpc2 : lm_pcount M (gs_ps M so) (gs_cs M so ++ [a]) (st so) (gs_E M so)
                     (gs_w M so ++ [b]) = S (P + length pre0)).
    { rewrite /lm_pcount Hproc -/(lm_pcount M (gs_ps M so) (gs_cs M so) (st so)
                                    (gs_E M so) (gs_w M so ++ [b])).
      rewrite lm_pcount_write -HP. reflexivity. }
    assert (Hat : lm_at M (gs_cs M so ++ [a]) (nlines (snd <$> gs_E M so) - 1)
                  = lm_dec M a).
    { rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hqq Nat.sub_diag. reflexivity. }
    (* the round's block starts at the state the writer's witness pins: the
       line's own entry is not read below it *)
    assert (Hfst : lm_upto M (gs_cs M so ++ [a]) (st so) (bodies_of I0) (nlines I0 - 1)
                   = lm_upto M (gs_cs M so) (st so) (bodies_of I0) (nlines I0 - 1)).
    { apply lm_upto_cs_ext. intros j Hj.
      rewrite !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (HpendA : lm_pending M (gs_ps M so) (gs_cs M so ++ [a]) (st so) (gs_E M so)
                     = pre0 ++ u_prompt).
    { rewrite /lm_pending /lm_pending_at decide_False; [| exact Hnn].
      rewrite decide_True; [| exact Hrr].
      rewrite lmN_cont_at_nopanic; [| by rewrite Hat].
      rewrite Hat HIeq Hfst -Hreq. exact Hcont. }
    iModIntro. iSplitR "Ht".
    - rewrite /peclV. iLeft. rewrite /gcl. iRight.
      iExists v, (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                    (gs_w M so ++ [b]) (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                                    (gs_w M so ++ [b]) (gs_st M so)) = st so);
        [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iSplitR; [iExact "Hpin" |]. iSplitL "Hwa"; [iExact "Hwa" |].
      iSplitL "Hblk Hcur Hrb".
      { rewrite Hext /pext.
        iExists w, r, gb, pre, false. iFrame "Hpera Hcur Hrb".
        rewrite (_ : lm_stream M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                        (gs_E M so) (gs_w M so ++ [b]) (gs_st M so))
                     = lm_stream M sd so ++ [b]); [iExact "Hblk" |].
        rewrite /lm_stream. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so)) = st so);
          [| reflexivity].
        rewrite Hproc app_assoc. reflexivity. }
      iFrame "Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_of_o_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                  (gs_w M so ++ [b]) (gs_st M so))
               r pre H b);
        [cbn [gs_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | | | | exact Hopen].
      + rewrite /lm_out_pure. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so)) = st so);
          [| reflexivity].
        split_and!.
        * rewrite Hacc HD app_assoc. reflexivity.
        * rewrite HpendA -Hpre0 Hbv. apply prefix_app.
          exists (drop 1 u_prompt).
          rewrite -{1}(take_drop 1 u_prompt). f_equal.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * apply lm_alts_pre_snoc; [exact Hcsb' | rewrite Hqq; lia |].
          rewrite Hqq -Hreq2 Hbod HIeq. exact Halt.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * apply Forall_app. split; [exact Hnofk | by apply Forall_singleton].
        * split.
          -- intros Hn. exfalso. destruct (proj1 Hf0n Hn) as [_ Hw0].
             rewrite Hwp' in Hw0. exact (Hne' Hw0).
          -- intros [_ Hq2]. exfalso. destruct (app_eq_nil _ _ Hq2) as [_ Hq3].
             discriminate Hq3.
        * exact Hfok0.
      + apply lm_cs_len_ok_intro.
        * intros [Hz _]. exfalso. destruct (app_eq_nil _ _ Hz) as [_ Hz2].
          discriminate Hz2.
        * intros _. rewrite length_app Hqq. cbn [length]. lia.
      + exact (lm_ps_len_ok_blk_w M sd B so a (gs_w M so ++ [b]) Hrr Hnn Hqq Hpsl).
      + apply (lm_dl_ok_out M so
                 (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so)
                    (gs_w M so ++ [b]) (gs_st M so)));
          [reflexivity | cbn [gs_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. iFrame "Ht Hpslb Hcslb2 Hilb".
  Qed.

  (* THE CLAIM PAYS THE FAMILY'S ONE OBLIGATION at the round's state: the
     first byte opens the round, every further byte (any writer's)
     appends to its ledger *)
  Theorem pblkV_ecl_holds (v : era_pins) (I : list (bv 8)) (sR : lm_st M) :
    ⊢ eclN peclV (PWV v I sR) (ptkV T v I) (pwitV M I sR).
  Proof using Hext.
    rewrite /eclN. iModIntro.
    iIntros (k ho H pre b tm tm' Htmt Hwit) "Hpw Hcl".
    destruct Hwit as (a & Hok & Hpan & Hterm & Hpref & Hnd).
    iDestruct "Hpw" as "[Hx | #HT]"; last first.
    { iModIntro. iSplitR; [by iApply peclV_taint |].
      iSplitR; [rewrite /pwc_blkV; by iRight | iRight; rewrite /ptkV; by iRight]. }
    iDestruct "Hx" as (ps cs s0 P) "([%Hw %Htie] & #Hpin & #HW & Htn & #Hps & #Hcs & Hled & #HE)".
    subst sR.
    pose proof Hw as ((Hpp & Hr & Hn & HP) & _).
    assert (Hne : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - (* THE BLOCK'S FIRST BYTE: the round opens *)
      subst pre. cbn [app] in Hpref, Hnd |- *.
      assert (Hb0 : lm_cont M (lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat)
                      (lineV M I) (lm_dec M a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hfarm : (lm_term M (lm_dec M a) = false /\ nodollar b)
                      \/ lm_term M (lm_dec M a) = true).
      { destruct tm'; [by right |]. left. split; [exact Hterm |].
        exact (proj1 (Forall_singleton _ _) (Hnd eq_refl)). }
      iMod (peclV_blkN_open_gen k v P a b ps cs s0 I ho H Hne Hr ltac:(lia) Hpp HP
              Hok Hpan Hb0 Hfarm with "Hpin [Htn] Hps Hcs HE HW Hcl") as "(Hcl & Hret)".
      { cbn [length] in *. rewrite Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; last first.
      { iSplitR; [rewrite /pwc_blkV; by iRight | iRight; rewrite /ptkV; by iRight]. }
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & #Hfz & _ & _ & _)".
      rewrite Hterm.
      iSplitL "Htn Hcur".
      + rewrite /pwc_blkV. iLeft. iExists ps, cs, s0, P. iFrame "Hpin HW Hps Hcs HE".
        iSplitR; [iPureIntro; split; [exact Hw | reflexivity] |].
        rewrite (_ : (P + length [b])%nat = S P); [| cbn [length]; lia]. iFrame "Htn".
        rewrite /pledV. iRight. iExists w, gb. iFrame "Hpera Hcur Hrlb".
      + iDestruct "Hfz" as "[%Hf | #Hf]"; [by iLeft | iRight; rewrite /ptkV; by iLeft].
    - (* A FURTHER BYTE, by any writer *)
      iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      assert (Hfarm : (lm_term M (lm_dec M a) = false /\ Forall nodollar pre
                       /\ nodollar b) \/ lm_term M (lm_dec M a) = true).
      { destruct tm'; [by right |]. left.
        pose proof (Hnd eq_refl) as Hall. apply Forall_app in Hall as [H1 H2].
        split; [exact Hterm | split; [exact H1 |]].
        exact (proj1 (Forall_singleton _ _) H2). }
      iMod (peclV_blkN_byte_gen k v w gb tm P (nlines I - 1)%nat a b pre ps cs s0 I ho H
              Hne Hr eq_refl ltac:(lia) Hpp HP Hok Hpan Hpref Hfarm
              with "Hpin Hpera Htn Hcur Hrlb Hps Hcs HE HW Hcl") as "(Hcl & Hret)".
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb' & #Hfz) | #HT]"; last first.
      { iSplitR; [rewrite /pwc_blkV; by iRight | iRight; rewrite /ptkV; by iRight]. }
      assert (Hor : (tm || lm_term M (lm_dec M a)) = tm').
      { rewrite Hterm. destruct tm, tm'; try reflexivity. discriminate (Htmt eq_refl). }
      rewrite Hor Hterm.
      iSplitL "Htn Hcur".
      + rewrite /pwc_blkV. iLeft. iExists ps, cs, s0, P. iFrame "Hpin HW Hps Hcs HE".
        iSplitR; [iPureIntro; split; [exact Hw | reflexivity] |].
        rewrite (_ : (P + length (pre ++ [b]))%nat = S (P + length pre));
          [| rewrite length_app; cbn [length]; lia].
        iFrame "Htn". rewrite /pledV. iRight. iExists w, gb. iFrame "Hpera Hcur Hrlb'".
      + iDestruct "Hfz" as "[%Hf | #Hf]"; [by iLeft | iRight; rewrite /ptkV; by iLeft].
  Qed.

  (* THE FILING, at the credential, through the view: once the family has
     handed the block back, the prompt's first byte files it as the view's
     [PLRun pre] *)
  Lemma pwc_blkV_file (V : pview M) (v : era_pins) (I : list (bv 8)) (sR : lm_st M)
      (lR : pline') (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (pre : list (bv 8)) (b : bv 8) :
    pv_line V (lineV M I) = Some lR -> pv_adm V lR = true ->
    line_blocks (pv_fc V sR) lR pre -> pre <> [] -> b = u_prompt !!! 0%nat ->
    PWV v I sR k pre false -∗ peclV k ho H ==∗
      peclV k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (s0 : lm_st M) (P : nat),
            ⌜wr_blkV M ps cs s0 I P /\ lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat = sR⌝
            ∗ gcW G k s0 ∗ turn v (S (P + length pre))%nat
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [pv_enc V lR (PLRun pre)]) ∗ inp_lb v I) ∨ T).
  Proof using B Hext.
    intros HlR Ha Hbl Hne Hbv. iIntros "Hpw Hcl".
    iDestruct "Hpw" as "[Hx | #HT]"; last first.
    { iModIntro. iSplitR; [by iApply peclV_taint | by iRight]. }
    iDestruct "Hx" as (ps cs s0 P) "([%Hw %Htie] & #Hpin & #HW & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as ((Hpp & Hr & Hn & HP) & _).
    assert (HneI : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    iDestruct "Hled" as "[%Hnil | Hled]"; [by destruct (Hne Hnil) |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    assert (Hok : lm_ok M (lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat)
                    (lm_of M (bodies_of I !!! (nlines I - 1)%nat))
                    (lm_dec M (pv_enc V lR (PLRun pre)))).
    { rewrite Htie. exact (pv_run_ok V sR _ lR pre HlR Ha Hbl). }
    assert (Hcont : lm_cont M (lm_upto M cs s0 (bodies_of I) (nlines I - 1)%nat)
                      (lm_of M (bodies_of I !!! (nlines I - 1)%nat))
                      (lm_dec M (pv_enc V lR (PLRun pre))) = pre ++ u_prompt).
    { exact (pv_run_cont V _ _ lR pre HlR). }
    iMod (peclV_blkN_file k v w gb P (nlines I - 1)%nat (pv_enc V lR (PLRun pre)) b pre
            ps cs s0 I ho H HneI Hr eq_refl ltac:(lia) Hpp HP Hok
            (pv_run_panic V lR pre) (pv_run_term V lR pre) Hcont Hbv
            with "Hpin Hpera Htn Hcur Hrlb Hps Hcs HE HW Hcl") as "(Hcl & Hret)".
    iModIntro. iFrame "Hcl".
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _) | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, s0, P. iFrame "Htn Hps Hcs' HE HW".
    iPureIntro. split; [exact Hw | exact Htie].
  Qed.
End pipes_out_v.

(* ===================================================================== *)
(*  2.  THE CLAIM AT THE PER-STAGE OUTCOME MODEL                          *)
(*                                                                       *)
(*  Section 1b's claim at [pipes_lm fc adm]: state [unit], the witness   *)
(*  [emp], the pin echo's era pin.  Every definition below IS the        *)
(*  generic one at the model (by conversion), and every step its         *)
(*  instance at the state [tt].                                          *)
(* ===================================================================== *)

Section pipes_out_n.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Notation T := (echo_taint γ).
  (* THE MODEL: the content function, the admitted lines, and the laws
     of [pipes_lm fc adm], which are the caller's (at
     [PipesDisc.pipes_lm_laws]) *)
  Context (fc : bytes -> option bytes) (adm : pline' -> bool).
  Context (Lw : lm_laws (pipes_lm fc adm)).
  Local Notation PM := (pipes_lm fc adm).
  (* THE HOOKS are the model's own ([PipesDiscDec.pipes_hooks]) *)
  Local Notation K := (pipes_hooks fc adm).
  Local Notation PB := (pipes_lm_byte_laws fc adm).

  Definition pipesN_cparams : gen_cparams PM :=
    MkGCP PM Lw K T _ _ (era_pin γ) _ _ (era_pin_agree γ) (fun _ _ => emp%I) _ _.

  Lemma pipesN_wa_agree (k : nat) (st : option (lm_st PM)) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp -∗ ⌜default tt st = s0⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct (default tt st), s0. Qed.

  Lemma pipesN_wa_W (k : nat) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp ∗ emp ∗ emp.
  Proof using . iIntros "_". by iSplit; [| iSplit]. Qed.

  Lemma pipesN_wa_file (k : nat) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp ==∗ emp ∗ emp.
  Proof using . iIntros "_ _". by iModIntro; iSplit. Qed.

  Lemma pipesN_wa_free (k : nat) : (emp : iProp Σ) ==∗ emp.
  Proof using . by iIntros "_". Qed.

  (* the stream extension is the PIPE's: the era's byte ledger and the
     current-round ghost, held whole between rounds ([PipeOut.pext]) *)
  Definition pipesN_wa : gen_wa PM pipesN_cparams tt :=
    @MkGWA Σ _ PM pipesN_cparams tt (fun _ _ => emp%I) _ pipesN_wa_agree
      (fun _ => emp%I) _ pipesN_wa_W (fun _ _ => emp%I) pipesN_wa_file
      False (fun Hf => match Hf with end)
      True (fun _ => pipesN_wa_free)
      (pext g) _ (pext_grow g).

  Local Notation GP := pipesN_cparams.
  Local Notation GA := pipesN_wa.

  (* THE OPEN ROUND: [popenV] at the model, the witness [emp] *)
  Definition popenN (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    popenV g PM (era_pin γ) (fun _ _ => emp%I) tt k ho H.

  (* THE CLAIM: [peclV] at the model *)
  Definition pecl' (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (gcl PM pipesN_cparams tt pipesN_wa k ho H ∨ popenN k ho H)%I.

  Global Instance pecl'_timeless k ho H : Timeless (pecl' k ho H).
  Proof using . rewrite /pecl' /popenN /popenV. apply _. Qed.

  (* ================================================================= *)
  (*  3.  THE FAMILY'S CREDENTIAL, AND THE ONE OBLIGATION               *)
  (* ================================================================= *)

  (* the round's line *)
  Definition lineN (I : list (bv 8)) : pline' := lineV PM I.

  (* THE CREDENTIAL [PipeBothN]'s family is parameterised by: [pwc_blkV]
     at the model, its round's state [tt] *)
  Definition pwc_blkN (v : era_pins) (I : list (bv 8)) (k : nat)
      (pre : list (bv 8)) (tm : bool) : iProp Σ :=
    pwc_blkV g PM (era_pin γ) (fun _ _ => emp%I) T v I tt k pre tm.

  Global Instance pwc_blkN_timeless v I k pre tm : Timeless (pwc_blkN v I k pre tm).
  Proof using . rewrite /pwc_blkN /pwc_blkV /pledV. apply _. Qed.

  (* what a terminal byte hands its writer *)
  Definition ptkN (v : era_pins) (I : list (bv 8)) (k : nat) : iProp Σ :=
    ptkV T v I k.

  Global Instance ptkN_persistent v I k : Persistent (ptkN v I k).
  Proof using . rewrite /ptkN /ptkV. apply _. Qed.
End pipes_out_n.

(* ===================================================================== *)
(*  4.  THE FAMILY AT THE PIPELINE, AT THE REAL CLAIM                      *)
(*                                                                       *)
(*  [PipeBothN]'s laws with every parameter instantiated: the writers of *)
(*  the round's line ([wids]), its complete runs ([runN]), the claim     *)
(*  [pecl'] behind the port's record equation, the credential            *)
(*  [pwc_blkN], and the obligation paid by [pblkN_ecl_holds].  What      *)
(*  stays open is exactly what the round's walk (C6/C7) supplies: the    *)
(*  terminal sources and invariant, the deposits, and the pure premises  *)
(*  of each step.                                                        *)
(* ===================================================================== *)

(* a line has a run: the top node's pipe panic, or a silent echo *)
Lemma wids_from_silent (src : wid -> bytes) (k m : nat) :
  (1 <= k)%nat -> (forall j, (1 <= j)%nat -> src (WSh j) = [] /\ src (WLeft j) = []) ->
  src WLast = [] -> src <$> wids_from k m = replicate (2 * m + 1) [].
Proof using.
  intros Hk Hs Hl. revert k Hk. induction m as [| m IH]; intros k Hk; cbn [wids_from].
  - by rewrite fmap_cons fmap_nil Hl.
  - destruct (Hs k Hk) as [H1 H2]. rewrite !fmap_cons H1 H2 (IH (S k) ltac:(lia)).
    replace (2 * S m + 1)%nat with (S (S (2 * m + 1))) by lia. reflexivity.
Qed.

(* THE SILENT ROUND IS A RUN: every writer silent (the producer's argv[0]
   empty, every cat's too) -- the family's invariant at its birth *)
Lemma sfx_runV_silent (fc : bytes -> option bytes) (L : bytes) (F : filt) (fs : list filt)
    (win : wr_out) (wc : bool) :
  sfx_runV fc L (F :: fs) win wc (replicate (2 * length fs + 1) []).
Proof using.
  revert F win wc. induction fs as [| F' fs IH]; intros F win wc.
  - cbn. apply (srv_last fc L F win wc (MkSO [] (Some RdGone) None) (so_silent fc L (SLast F))).
    cbn. destruct win; exact I.
  - replace (2 * length (F' :: fs) + 1)%nat with (S (S (2 * length fs + 1)))
      by (cbn [length]; lia). cbn [replicate].
    apply (srv_node fc L F F' fs win wc (MkSO [] (Some RdGone) (Some WrNone)) _
             (so_silent fc L (SMid F))); [cbn; destruct win; exact I |].
    exact (IH F' WrNone (filt_is_cat F)).
Qed.

Lemma runN_silent (fc : bytes -> option bytes) (l : pline') :
  pl_ok l -> runS (runN fc l) (fun _ => None).
Proof using.
  intros Hl. exists (fun _ => []). split; [| intros w; reflexivity].
  destruct l as [ws | p fs].
  - rewrite /runN. cbn. apply lrv_echo_silent.
  - destruct Hl as (_ & Hn & _).
    destruct fs as [| F fs]; [exfalso; exact (Hn eq_refl) |].
    rewrite /runN /wids. cbn [lcats length wids_from].
    rewrite !fmap_cons (wids_from_silent (fun _ => []) 1 (length fs) ltac:(lia)
                         (fun _ _ => conj eq_refl eq_refl) eq_refl).
    exact (lrv_node fc p (F :: fs) (MkSO [] None (Some WrNone)) (replicate (2 * length fs + 1) [])
             (so_silent fc (prod_content fc p) (SProd p))
             (sfx_runV_silent fc (prod_content fc p) F fs WrNone (prod_cat p))).
Qed.

(* ===================================================================== *)
(*  4a.  THE FAMILY AT A PIPELINE ROUND OF ANY MODEL (cut C9c')            *)
(*                                                                       *)
(*  [PipeBothN]'s laws at the round of a model with a pipeline view: the  *)
(*  round's line is the pipeline [lR], its runs are read at the ROUND'S  *)
(*  STATE [sR]'s content, the claim is [peclV], the credential           *)
(*  [pwc_blkV] at [sR].  Section 4b is this at the pipeline application. *)
(* ===================================================================== *)
(* THE CONSOLE CLAIM A PIPELINE ROUND WRITES THROUGH: the record's claim
   is SOME claim that pays the N-writer family's one obligation at every
   pipeline line of the view -- [peclV] itself ([cons_claimV_peclV]), or
   the union's three-arm claim, which pays it only at lines that are not
   wild (seccomp design 10.7) *)
Section pipes_claim_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Definition cons_claimV (g : pipe_gn) (M : lmodel) (V : pview M) (G : gen_cparams M)
      (sd : lm_st M) (WA : gen_wa M G sd) : Prop :=
    exists CL : nat -> list mobs -> LogEntryDefs.cons_hist -> iProp Σ,
      @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = CL
      /\ forall (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (lR : pline'),
           pv_line V (lineV M I) = Some lR ->
           ⊢ eclN CL (pwc_blkV g M (gcPIN G) (gcW G) (gcT G) v I sR)
               (ptkV (gcT G) v I) (pwitV M I sR).

  Lemma cons_claimV_peclV (g : pipe_gn) (M : lmodel) (V : pview M) (G : gen_cparams M)
      (sd : lm_st M) (WA : gen_wa M G sd) :
    (forall k l, gext WA k l = pext g k l) ->
    @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g M G sd WA ->
    cons_claimV g M V G sd WA.
  Proof using .
    intros Hext Hc. exists (peclV g M G sd WA). split; [exact Hc |].
    intros v I sR lR _. exact (pblkV_ecl_holds g M G sd WA Hext v I sR).
  Qed.
End pipes_claim_v.

Section pipes_family_v.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context `{HRg : !riscvGS Σ}.
  Context `{!ghost_varG Σ (option (list (bv 8)))}.
  (* THE MODEL, ITS VIEW AND ITS CLAIM *)
  Context (g : pipe_gn) (M : lmodel) (V : pview M) (G : gen_cparams M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Context (Hcons : cons_claimV g M V G sd WA).
  (* THE ROUND: its pins, its input, its STATE [sR] (the writer's boot
     state read to the round's line), and the pipeline [lR] its line is *)
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (lR : pline').
  Hypothesis HlR : pv_line V (lineV M I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc V sR).
  Hypothesis Ha : pv_adm V lR = true.
  Hypothesis Hl : pl_ok lR.

  Local Notation fcR := (pv_fc V sR).
  Local Notation wsN := (wids (lcats lR)).
  Local Notation RUNN := (runN fcR lR).
  Local Notation PWN := (pwc_blkV g M (gcPIN G) (gcW G) (gcT G) v I sR).
  Local Notation TKN := (ptkV (gcT G) v I).
  Local Notation WITN := (pwitV M I sR).

  Lemma PWN_tl k pre tm : Timeless (PWN k pre tm).
  Proof using . apply pwc_blkV_timeless; apply _. Qed.
  Lemma TKN_pers k : Persistent (TKN k).
  Proof using . apply ptkV_persistent. apply _. Qed.
  Lemma HWITV : forall pre bl, blkN wsN RUNN bl -> pre `prefix_of` bl -> WITN false pre.
  Proof using HlR Hfc Ha Hl. exact (pipesV_HWIT M V I sR lR HlR Hfc Ha Hl). Qed.

  (* THE ROUND'S LEND at the pipeline *)
  Lemma pipesV_alloc (E : coPset) (N : namespace) (k : nat)
      (TERM : wid -> list (bv 8) -> bool)
      (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop)
      (dep : wid -> list (bv 8) -> iProp Σ) :
    PWN k [] false ={E}=∗
    ∃ γc γm : wid -> gname,
      blkN_inv wsN RUNN PWN TERM TOK dep N k γc γm
      ∗ [∗ list] w ∈ wsN, wcurN γc w (1/2) 0 ∗ wmodeN γm w (1/2) None.
  Proof using Hl.
    iIntros "HPW".
    iApply (blkN_alloc wsN (wids_NoDup _) RUNN PWN
              TERM TOK dep E N k (runN_silent fcR lR Hl) with "HPW").
  Qed.

  (* A FURTHER BYTE by any writer of the pipeline *)
  Lemma pipesV_cstep (N : namespace) (k : nat) (γc γm : wid -> gname)
      (TERM : wid -> list (bv 8) -> bool)
      (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop)
      (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s))
      (w : wid) (s : list (bv 8)) (c : nat) (b : bv 8) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    w ∈ wsN -> (0 < c)%nat -> s !! c = Some b ->
    cstep_okN wsN RUNN WITN TERM TOK w s c ->
    blkN_inv wsN RUNN PWN TERM TOK dep N k γc γm -∗
    wcurN γc w (1/2) c -∗ wmodeN γm w (1/2) (Some s) -∗
    (wcurN γc w (1/2) (S c) -∗ wmodeN γm w (1/2) (Some s)
     -∗ (⌜TERM w s = false⌝ ∨ TKN k) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hext HlR Hfc Ha Hl.
    intros Hns Hw Hc Hb Hok. iIntros "#Hinv HcW HmW HΦ".
    destruct Hcons as (CL & HcCL & Hecl).
    iApply (blkN_cstep wsN (wids_NoDup _) CL HcCL RUNN PWN
              PWN_tl TKN TKN_pers WITN
              HWITV TERM TOK dep dep_tl
              N k γc γm w s c b Φ Hns Hw Hc Hb Hok
              with "[] Hinv HcW HmW HΦ").
    iApply (Hecl v I sR lR HlR).
  Qed.

  (* A WRITER'S FIRST BYTE, spending the exclusions *)
  Lemma pipesV_fire (N : namespace) (Eex : coPset) (k : nat) (γc γm : wid -> gname)
      (TERM : wid -> list (bv 8) -> bool)
      (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop)
      (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s))
      (w : wid) (s : list (bv 8)) (b : bv 8)
      (EXCL : wid -> list (bv 8) -> Prop) (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    Eex ⊆ (⊤ ∖ ↑uartN Uart0 ∖ ↑N : coPset) ->
    w ∈ wsN -> s !! 0%nat = Some b ->
    fire_okN wsN RUNN WITN TERM TOK w s EXCL ->
    □ (∀ w' s', ⌜EXCL w' s'⌝ -∗ dep w' s' -∗ dep w s ={Eex}=∗ False) -∗
    blkN_inv wsN RUNN PWN TERM TOK dep N k γc γm -∗
    wcurN γc w (1/2) 0 -∗ wmodeN γm w (1/2) None -∗ dep w s -∗
    (wcurN γc w (1/2) 1 -∗ wmodeN γm w (1/2) (Some s)
     -∗ (⌜TERM w s = false⌝ ∨ TKN k) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons Hext HlR Hfc Ha Hl.
    intros Hns HEx Hw Hb Hok. iIntros "#Hex #Hinv HcW HmW Hdep HΦ".
    destruct Hcons as (CL & HcCL & Hecl).
    iApply (blkN_fire wsN (wids_NoDup _) CL HcCL RUNN PWN
              PWN_tl TKN TKN_pers WITN
              HWITV TERM TOK dep dep_tl
              N Eex k γc γm w s b EXCL Φ Hns HEx Hw Hb Hok
              with "Hex [] Hinv HcW HmW Hdep HΦ").
    iApply (Hecl v I sR lR HlR).
  Qed.

  (* AT THE PROMPT, WITH EVERY HALF BACK: the block is one of the line's,
     and the claim's credential comes back at the flag [false] -- which
     [pwc_blkV_file] files at the prompt's first byte (a block nobody
     wrote is filed by the single-writer [GenOut.gcl_step_write_blk]) *)
  Lemma pipesV_file (E : coPset) (N : namespace) (k : nat) (γc γm : wid -> gname)
      (TERM : wid -> list (bv 8) -> bool)
      (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop)
      (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s))
      (sw : wid -> list (bv 8)) :
    (↑N : coPset) ⊆ E ->
    (forall w, w ∈ wsN -> TERM w (sw w) = false) ->
    blkN_inv wsN RUNN PWN TERM TOK dep N k γc γm -∗
    ([∗ list] w ∈ wsN, wcurN γc w (1/2) (length (sw w))
                        ∗ wmodeN γm w (1/2) (Some (sw w))) ={E}=∗
    ∃ pre : list (bv 8), PWN k pre false ∗ ⌜line_blocks fcR lR pre⌝.
  Proof using HlR Hfc Ha Hl.
    intros HN HT. iIntros "#Hinv Hall".
    iMod (blkN_file wsN (wids_NoDup _) RUNN PWN PWN_tl
            WITN HWITV TERM TOK dep dep_tl
            E N k γc γm sw HN ltac:(rewrite /wids; destruct (lcats _); discriminate) HT
            with "Hinv Hall") as (pre) "[HPW %Hb]".
    iModIntro. iExists pre. iFrame "HPW". iPureIntro. exact (blkN_line_blocks fcR lR pre Hb).
  Qed.
  (* ================================================================= *)
  (*  4b.  THE TERMINAL ROUND AT THE PIPELINE (cut C5b)                  *)
  (*                                                                     *)
  (*  [TERM] is [PipeBothNPure.termw] (sh node k's [fork] line and the   *)
  (*  prompt), [TOK] is [PipeBothNPure.tokN] (the committed sources      *)
  (*  extend to a terminal vector, the prompt follows the waited         *)
  (*  stages), and the claim's terminal witness is DERIVED from it       *)
  (*  ([tokV_wit]).  What the round's walk still supplies is what it     *)
  (*  alone knows: at a commit, that the committed sources extend to a   *)
  (*  run (resp. a terminal vector) or that a deposit refutes the pair;  *)
  (*  at the prompt, the waited stages' halves.                          *)
  (* ================================================================= *)
  Local Notation TOKN := (tokN fcR lR).

  (* THE CLAIM'S TERMINAL WITNESS: a prefix of a terminal block *)
  Lemma pwitV_true (pre : list (bv 8)) :
    pre <> [] -> (exists b', line_term_blocks fcR lR b' /\ pre `prefix_of` b') ->
    WITN true pre.
  Proof using HlR Ha.
    intros Hne Hex. exists (pv_enc V lR (PLTerm pre)).
    destruct (pv_term_ok V sR (lineV M I) lR pre HlR Ha (conj Hne Hex))
      as (Hok & Hterm & Hpan & Hcont).
    split_and!; [exact Hok | exact Hpan | exact Hterm | rewrite Hcont; reflexivity |
                 intros Hq; discriminate Hq].
  Qed.

  (* ...READ OFF THE INVARIANT at any family state *)
  Lemma tokV_wit (md : wid -> option (list (bv 8))) (sel : list wid) :
    TOKN md sel -> sel_firedN md sel -> sel_wfN (srcN md) sel -> sel <> [] ->
    WITN true (pendN md sel).
  Proof using HlR Ha.
    intros Htok Hfd Hwf Hne. apply pwitV_true; [| exact (tokN_blocks fcR lR md sel Htok Hfd Hwf)].
    intros Hq. apply (f_equal length) in Hq. rewrite /pendN (mergeN_length _ _ Hwf) in Hq.
    apply Hne. by apply nil_length_inv.
  Qed.

  (* before the terminal byte no sigma has its fork source on the wire *)
  Lemma prompt_okN_nt (md : wid -> option (list (bv 8))) (sel : list wid) :
    tmN termw md sel = false -> prompt_okN md sel.
  Proof using.
    intros Htm s1 s2 k Hsel HmT. exfalso.
    assert (Hin : WSh k ∈ sel) by (rewrite Hsel; apply elem_of_app; right; apply elem_of_list_here).
    revert Htm. apply not_false_iff_true. rewrite /tmN existsb_exists. exists (WSh k).
    split; [by apply elem_of_list_In |]. rewrite /srcN HmT.
    exact (bool_decide_eq_true_2 _ eq_refl).
  Qed.

  (* ---- the steps' premises ---- *)

  (* A BYTE THAT IS NOT A PROMPT BYTE, by any writer *)
  Lemma cstep_okV_tok (w : wid) (s : list (bv 8)) (c : nat) :
    (0 < c)%nat -> (c < length s)%nat ->
    (forall k, w = WSh k -> s = alt_forkc -> (c < length dg_fork_b)%nat) ->
    cstep_okN wsN RUNN WITN termw TOKN w s c.
  Proof using HlR Ha.
    intros Hc Hlt Hnp md sel Hfam Hmw Hcw Htm.
    destruct Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    destruct (proj2 Hinvn Htm) as [Hcp Hpo].
    assert (Hws : w ∈ sel) by (apply cntN_elem; lia).
    assert (Htok : TOKN md (sel ++ [w])).
    { split.
      - apply (runS_ext _ (rmd md sel)); [| exact Hcp].
        intros x. rewrite /rmd (cmtN_step md sel _ x Hws). reflexivity.
      - apply prompt_okN_snoc; [exact Hpo |]. intros k -> HmT.
        rewrite Hmw in HmT. injection HmT as HmT. rewrite Hcw. exact (Hnp k eq_refl HmT). }
    split; [exact Htok |].
    apply tokV_wit; [exact Htok | | | intros Hq; apply app_eq_nil in Hq as [_ Hq]; discriminate Hq].
    - apply sel_firedN_snoc; [exact Hfd | rewrite Hmw; by eexists].
    - apply (sel_wfN_fired_snoc md sel w s Hwf Hmw). lia.
  Qed.

  (* the waited stages' halves at their whole sources, above node [k] *)
  Definition heldN (k : nat) (sw : nat -> list (bv 8)) : list (wid * list (bv 8) * nat) :=
    (fun j => (WLeft j, sw j, length (sw j))) <$> seq 0 k.

  (* THE PROMPT BYTE of sh node k's terminal source, with the waited
     stages' halves in hand *)
  Lemma cstep_okVh_prompt (k : nat) (sw : nat -> list (bv 8)) (c : nat) :
    (0 < c)%nat -> (c < length alt_forkc)%nat ->
    cstep_okNh wsN RUNN WITN termw TOKN (WSh k) alt_forkc c (heldN k sw).
  Proof using HlR Ha.
    intros Hc Hlt md sel Hfam Hmw Hcw Hheld Htm.
    destruct Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    destruct (proj2 Hinvn Htm) as [Hcp Hpo].
    assert (Hws : WSh k ∈ sel) by (apply cntN_elem; lia).
    assert (Htok : TOKN md (sel ++ [WSh k])).
    { split.
      - apply (runS_ext _ (rmd md sel)); [| exact Hcp].
        intros x. rewrite /rmd (cmtN_step md sel _ x Hws). reflexivity.
      - apply prompt_okN_prompt; [exact Hpo |]. intros j Hj.
        destruct (Hheld (WLeft j, sw j, length (sw j))) as [Hm Hcn].
        { rewrite /heldN elem_of_list_fmap. exists j. split; [reflexivity |].
          apply elem_of_seq. lia. }
        exists (sw j). split; [exact Hm | exact Hcn]. }
    split; [exact Htok |].
    apply tokV_wit; [exact Htok | | | intros Hq; apply app_eq_nil in Hq as [_ Hq]; discriminate Hq].
    - apply sel_firedN_snoc; [exact Hfd | rewrite Hmw; by eexists].
    - apply (sel_wfN_fired_snoc md sel (WSh k) alt_forkc Hwf Hmw). lia.
  Qed.

  (* A COMMIT (first byte) BY ANY WRITER: the walk names the run (or the
     terminal vector) the committed sources extend to, or the deposit that
     refutes the pair; the family's terminal invariant and witness follow *)
  Lemma fire_okV_tok (w : wid) (s : list (bv 8)) (EXCL : wid -> list (bv 8) -> Prop) :
    s <> [] ->
    (forall md sel, famN wsN RUNN termw TOKN md sel -> md w = None -> w ∉ sel ->
       tmN termw (mdupd md w s) (sel ++ [w]) = false ->
       runS RUNN (rmd (mdupd md w s) (sel ++ [w]))
       \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s') ->
    (forall md sel, famN wsN RUNN termw TOKN md sel -> md w = None -> w ∉ sel ->
       tmN termw (mdupd md w s) (sel ++ [w]) = true ->
       runS (termsN fcR lR) (rmd (mdupd md w s) (sel ++ [w]))
       \/ exists w' s', cmtN md sel w' = true /\ md w' = Some s' /\ EXCL w' s') ->
    fire_okN wsN RUNN WITN termw TOKN w s EXCL.
  Proof using HlR Ha.
    intros Hs Hnt Ht md sel Hfam Hmw Hws. split; [exact (Hnt md sel Hfam Hmw Hws) |].
    intros Htm'. destruct (Ht md sel Hfam Hmw Hws Htm') as [Hc | Hx]; [left | right; exact Hx].
    pose proof Hfam as (Hin & Hmin & Hfd & Hwf & Hinvn).
    assert (Hpo : prompt_okN md sel).
    { destruct (tmN termw md sel) eqn:Htm.
      - exact (proj2 (proj2 Hinvn Htm)).
      - exact (prompt_okN_nt md sel Htm). }
    assert (Hmw' : mdupd md w s w = Some s) by (rewrite /mdupd decide_True; done).
    assert (Htok : TOKN (mdupd md w s) (sel ++ [w])).
    { split; [exact Hc |].
      apply prompt_okN_snoc; [exact (prompt_okN_mdupd md sel w s Hmw Hws Hpo) |].
      intros k -> _. rewrite (cntN_nil_notin sel _ Hws). rewrite dg_fork_b_len. lia. }
    split; [exact Htok |].
    apply tokV_wit; [exact Htok | | | intros Hq; apply app_eq_nil in Hq as [_ Hq]; discriminate Hq].
    - apply sel_firedN_snoc; [exact (sel_firedN_mdupd md sel w s Hfd) | rewrite Hmw'; by eexists].
    - apply (sel_wfN_fired_snoc (mdupd md w s) sel w s (sel_wfN_mdupd md sel w s Hws Hwf) Hmw').
      rewrite (cntN_nil_notin sel _ Hws).
      destruct s as [| s0 s']; [exfalso; exact (Hs eq_refl) | cbn [length]; lia].
  Qed.

  (* A SILENT EXIT, the same way *)
  (* A SILENT EXIT, BY ANY WRITER, AT ANY STATE (lane PIPES-C7): the family
     reads an uncommitted writer as silent already, so a silent commit
     leaves both its invariants where they were -- no exclusion is spent *)
  Lemma silence_okV_tok (w : wid) (EXCL : wid -> list (bv 8) -> Prop) :
    silence_okN wsN RUNN termw TOKN w EXCL.
  Proof using.
    intros md sel Hfam Hmw Hws.
    pose proof Hfam as (_ & _ & _ & _ & Hinvn).
    split.
    - intros Htm. left. apply (runS_ext _ (rmd md sel)); [| exact (proj1 Hinvn Htm)].
      intros x. exact (rmd_silence_src md sel w x Hws Hmw).
    - intros Htm. left. destruct (proj2 Hinvn Htm) as [Hr Hpo]. split.
      + apply (runS_ext _ (rmd md sel)); [| exact Hr].
        intros x. exact (rmd_silence_src md sel w x Hws Hmw).
      + exact (prompt_okN_mdupd md sel w [] Hmw Hws Hpo).
  Qed.
End pipes_family_v.

(* the sources of [echo .. | cat] whose two children both failed their
   exec (the right one's at [R]); sigma_0 is silent *)
Definition src2 (R : bytes) (w : wid) : bytes :=
  match w with WLeft 0 => dg_execL | WLast => R | _ => [] end.

Definition md2 (R : bytes) : wid -> option bytes := fun w => Some (src2 R w).
