(* ===================================================================== *)
(*  GenOutPure.v -- THE CONSOLE CLAIM'S STAGE, ONCE OVER A LINE MODEL     *)
(*  (app-both M3a).                                                      *)
(*                                                                       *)
(*  [EchoOutPure]/[EchoOut] section 1, [FileOutPure] sections 2-10 and   *)
(*  [PipeOutPure] state the per-cycle console claim's PURE side three     *)
(*  times: the stage (the era's prologue choices [ps], the line choices   *)
(*  [cs], the echoed input [E] with its histories, the bytes [w] of the   *)
(*  block in progress, and -- at the file -- the boot state), the         *)
(*  transcript it owes ([D], structural on [E]), the block pending after  *)
(*  the last echo, the cursor count, the two length laws of the choice    *)
(*  lists, and the stage's whole pure account.  Every one of them reads   *)
(*  the application's session only through the line model's functions    *)
(*  ([LineModel.lm_pending_at], [lm_proc_before], [lm_sess], [lm_pro_pin], *)
(*  [lm_disc_input]), so this file states and proves them once over an   *)
(*  [lmodel] with its byte laws; the three tiers are its instances.       *)
(*                                                                       *)
(*  THE STATE IS A PARAMETER of every stage function, as it is of the     *)
(*  model's session; the stage record carries it as an OPTION (the file's *)
(*  [fo_f0]: [None] until the era's first process byte files it), read   *)
(*  through a default the instance supplies ([gs_state]).                 *)
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
Require Import LineModel.
Require Import LineModelLinks.
Require Import EchoOutPure.      (* [E_index], [lines_bytes], the [epu_] list facts *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ---- the list facts every tier restated ([EchoOut.epu_*], [fop_*],
        [pop_*]), once ---- *)
Lemma gop_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof.
  destruct l as [| a l] using rev_ind; [done |].
  rewrite removelast_last. by eexists.
Qed.

Lemma gop_nlines_removelast (I : list (bv 8)) :
  (nlines (removelast I) <= nlines I)%nat.
Proof. apply nlines_prefix, gop_removelast_prefix. Qed.

Section gen_out_pure.
  Context (M : lmodel).
  Context (L : lm_laws M) (K : lm_hooks M) (B : lm_byte_laws M).

  (* ================================================================== *)
  (*  1.  THE STAGE                                                      *)
  (* ================================================================== *)
  Record gstage := MkGS {
    gs_ps : list nat;
    gs_cs : list nat;
    gs_E  : list (list mobs * bv 8);
    gs_w  : list (bv 8);
    gs_st : option (lm_st M);
  }.

  Definition gstage0 : gstage := MkGS [] [] [] [] None.

  (* the state the stage reads: the filed one, or the instance's default
     before the era's first process byte files it *)
  Definition gs_state (sd : lm_st M) (so : gstage) : lm_st M :=
    default sd (gs_st so).

  (* ================================================================== *)
  (*  2.  THE TRANSCRIPT DUE, THE BLOCK PENDING, THE CURSOR              *)
  (* ================================================================== *)
  Definition lm_pending (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) : list (bv 8) :=
    lm_pending_at M ps cs s (snd <$> E).

  (* THE TRANSCRIPT DUE AFTER E's LAST ECHO: structural on [E] from the
     LEFT with the input read so far as the accumulator, so that [cbn]
     reduces it on every [x :: E'] *)
  Fixpoint lm_D_from (ps cs : list nat) (s : lm_st M) (pre : list (bv 8))
      (E : list (list mobs * bv 8)) : list (bv 8) :=
    match E with
    | [] => []
    | x :: E' => lm_pending_at M ps cs s pre ++ [echo_of x.2]
                 ++ lm_D_from ps cs s (pre ++ [x.2]) E'
    end.

  Definition lm_D (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) : list (bv 8) :=
    lm_D_from ps cs s [] E.

  (* E's CONTENT LAW: the bytes of E ARE a disciplined input *)
  Definition lm_E_disc (E : list (list mobs * bv 8)) : Prop :=
    lm_disc_input M (snd <$> E).

  (* the era's process-byte cursor at the stage *)
  Definition lm_pcount (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) : nat :=
    length (lm_proc_before M ps cs s (snd <$> E)) + length w.

  Lemma lm_D_nil ps cs s : lm_D ps cs s [] = [].
  Proof using. reflexivity. Qed.

  Lemma lm_pending_nil ps cs s : lm_pending ps cs s [] = pro_of ps.
  Proof using.
    rewrite /lm_pending fmap_nil /lm_pending_at.
    case_decide as H; [done | by destruct (H eq_refl)].
  Qed.

  Lemma lm_pending_at_ps_mono ps ps' cs s I :
    ps `prefix_of` ps' ->
    lm_pending_at M ps cs s I `prefix_of` lm_pending_at M ps' cs s I.
  Proof using.
    intros Hp. rewrite /lm_pending_at. case_decide as H0.
    { by apply pro_of_mono. }
    case_decide as Hm; [| reflexivity].
    rewrite /lm_cont_at. apply prefix_app.
    destruct (lm_panic M (lm_at M cs (nlines I - 1))); [| reflexivity].
    by apply pro_of_from_mono.
  Qed.

  Lemma lm_pending_ps_mono ps ps' cs s E :
    ps `prefix_of` ps' -> lm_pending ps cs s E `prefix_of` lm_pending ps' cs s E.
  Proof using. intro Hp. by apply lm_pending_at_ps_mono. Qed.

  Lemma lm_pending_at_round_det (ps ps' cs : list nat) (s : lm_st M)
      (I : list (bv 8)) :
    rest_of I = [] ->
    (I = [] \/ lm_panic M (lm_at M cs (nlines I - 1)) = true) ->
    lm_pending_at M ps cs s I = lm_pending_at M ps' cs s I ->
    pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps)
    = pro_of (pro_from (lm_pro_idx M cs (nlines I)) ps').
  Proof using L.
    intros Hm Hopen Heq.
    rewrite (lm_pending_at_round_pre M L ps cs s I Hm Hopen) in Heq.
    rewrite (lm_pending_at_round_pre M L ps' cs s I Hm Hopen) in Heq.
    by apply app_inv_head in Heq.
  Qed.

  (* ---- the append laws ---- *)
  Lemma lm_D_from_pending_ext ps ps' cs s pre E :
    (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
       J <> pre ++ (snd <$> E) ->
       lm_pending_at M ps cs s J = lm_pending_at M ps' cs s J) ->
    lm_D_from ps cs s pre E = lm_D_from ps' cs s pre E.
  Proof using.
    revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
    assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
      by (by rewrite fmap_cons epu_app_snoc).
    assert (Hhere : lm_pending_at M ps cs s pre = lm_pending_at M ps' cs s pre).
    { apply Hj.
      - reflexivity.
      - by eexists.
      - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
    cbn [lm_D_from]. rewrite Hhere. do 2 f_equal.
    apply IH. intros J H1 H2 H3. apply Hj.
    - etrans; [| exact H1]. by eexists.
    - rewrite -Hshape. exact H2.
    - rewrite -Hshape. exact H3.
  Qed.

  Lemma lm_D_ps_ext ps ps' cs s E :
    ps `prefix_of` ps' -> lm_pro_pin M ps cs (snd <$> E) ->
    lm_D ps cs s E = lm_D ps' cs s E.
  Proof using.
    intros Hp Hpin. rewrite /lm_D. apply lm_D_from_pending_ext.
    intros J H1 H2 H3. rewrite app_nil_l in H2, H3.
    apply (lm_pending_at_ps_ext M ps ps' cs s J Hp).
    apply Hpin. exact (nstarted_strict J (snd <$> E) H2 H3).
  Qed.

  Lemma lm_D_from_app ps cs s pre E1 E2 :
    lm_D_from ps cs s pre (E1 ++ E2)
    = lm_D_from ps cs s pre E1 ++ lm_D_from ps cs s (pre ++ (snd <$> E1)) E2.
  Proof using.
    revert pre. induction E1 as [| x E1 IH]; intros pre.
    - cbn [lm_D_from app]. by rewrite fmap_nil app_nil_r.
    - change ((x :: E1) ++ E2) with (x :: (E1 ++ E2)).
      cbn [lm_D_from]. rewrite (IH (pre ++ [x.2])) fmap_cons epu_app_snoc.
      by rewrite -!app_assoc.
  Qed.

  Lemma lm_D_app ps cs s E x :
    lm_D ps cs s (E ++ [x]) = lm_D ps cs s E ++ lm_pending ps cs s E ++ [echo_of x.2].
  Proof using.
    rewrite /lm_D /lm_pending lm_D_from_app app_nil_l /=. by rewrite ?app_nil_r.
  Qed.

  (* ================================================================== *)
  (*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                  *)
  (* ================================================================== *)
  Lemma lm_echo_of_disc (I : list (bv 8)) (c : bv 8) :
    lm_disc_input M I -> c ∈ I -> echo_of c = c.
  Proof using B.
    intros Hd Hc. apply echo_of_other. intro Hq.
    apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [| by vm_compute].
    destruct (lm_disc_input_byte_val M B I c Hd Hc); lia.
  Qed.

  Lemma lm_E_disc_take (E : list (list mobs * bv 8)) (n : nat) :
    lm_E_disc E -> lm_E_disc (take n E).
  Proof using B.
    rewrite /lm_E_disc. intro HE.
    exact (lm_disc_input_prefix M B _ _ (epu_fmap_prefix snd _ _ (prefix_take _ _)) HE).
  Qed.

  Lemma lm_E_disc_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
    lm_E_disc (E ++ [x]) -> lm_E_disc E.
  Proof using B.
    rewrite /lm_E_disc fmap_app. intro H.
    exact (lm_disc_input_prefix M B _ _ ltac:(by eexists) H).
  Qed.

  Lemma lm_E_disc_echo (E : list (list mobs * bv 8)) (j : nat)
      (x : list mobs * bv 8) :
    lm_E_disc E -> E !! j = Some x -> echo_of x.2 = x.2.
  Proof using B.
    intros HE Hx. apply (lm_echo_of_disc (snd <$> E) x.2 HE).
    apply elem_of_list_lookup_2 with j. by rewrite list_lookup_fmap Hx.
  Qed.

  Lemma lm_E_disc_of_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
    E_index E ->
    (forall j x, E !! j = Some x -> x.1 `prefix_of` Sg) ->
    lm_disc_input M (ins Sg) -> lm_E_disc E.
  Proof using B.
    intros Hidx Hpre Hd.
    pose proof (E_length_le_hist E Sg Hidx Hpre) as Hlen.
    rewrite /lm_E_disc (E_bytes_of_hist E Sg Hidx Hpre Hlen).
    exact (lm_disc_input_prefix M B _ _ (prefix_take _ _) Hd).
  Qed.

  (* ================================================================== *)
  (*  4.  THE STAGE IS BELOW THE SESSION                                 *)
  (* ================================================================== *)
  Lemma lm_D_pending_sess (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) :
    lm_E_disc E ->
    lm_D ps cs s E ++ lm_pending ps cs s E = lm_sess M ps cs s (snd <$> E).
  Proof using B.
    induction E as [| x E IH] using rev_ind; intros HE.
    - by rewrite lm_D_nil lm_pending_nil app_nil_l fmap_nil lm_sess_nil.
    - pose proof (lm_E_disc_app_l E x HE) as HE0.
      pose proof (IH HE0) as IH'. rewrite /lm_pending in IH'.
      assert (Hb : echo_of x.2 = x.2).
      { apply (lm_E_disc_echo (E ++ [x]) (length E) x HE).
        rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]. }
      assert (Hfm : (snd <$> (E ++ [x])) = (snd <$> E) ++ [x.2])
        by (by rewrite fmap_app).
      rewrite lm_D_app /lm_pending Hfm Hb.
      rewrite (app_assoc (lm_D ps cs s E) (lm_pending_at M ps cs s (snd <$> E)) [x.2])
              IH'.
      destruct (decide (x.2 = wl_nl)) as [Hnl | Hnl].
      + assert (Hp : lm_pending_at M ps cs s ((snd <$> E) ++ [x.2])
                     = lm_cont_at M ps cs s
                         (bodies_of (snd <$> E) ++ [rest_of (snd <$> E)])
                         (nlines (snd <$> E))).
        { rewrite Hnl /lm_pending_at. case_decide as H1.
          { exfalso. apply (f_equal length) in H1.
            rewrite (length_app (snd <$> E) [wl_nl]) in H1.
            cbn [length] in H1. lia. }
          rewrite decide_True; [| exact (rest_of_snoc_nl (snd <$> E))].
          rewrite bodies_of_snoc_nl nlines_snoc_nl.
          by replace (S (nlines (snd <$> E)) - 1)%nat
            with (nlines (snd <$> E)) by lia. }
        rewrite Hp Hnl lm_sess_snoc_nl.
        by rewrite -(app_assoc (lm_sess M ps cs s (snd <$> E)) [wl_nl] _).
      + assert (Hp : lm_pending_at M ps cs s ((snd <$> E) ++ [x.2]) = []).
        { rewrite /lm_pending_at. case_decide as H1.
          { exfalso. apply (f_equal length) in H1.
            rewrite (length_app (snd <$> E) [x.2]) in H1.
            cbn [length] in H1. lia. }
          rewrite decide_False; [done |].
          rewrite (rest_of_snoc_other (snd <$> E) x.2 Hnl).
          intro Hq. apply (f_equal length) in Hq.
          rewrite (length_app (rest_of (snd <$> E)) [x.2]) in Hq.
          cbn [length] in Hq. lia. }
        rewrite Hp app_nil_r (lm_sess_snoc_other M ps cs s (snd <$> E) x.2 Hnl).
        reflexivity.
  Qed.

  Lemma lm_D_stage_prefix (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) :
    lm_E_disc E -> w `prefix_of` lm_pending ps cs s E ->
    (lm_D ps cs s E ++ w) `prefix_of` lm_sess M ps cs s (snd <$> E).
  Proof using B.
    intros HE Hw. rewrite -(lm_D_pending_sess ps cs s E HE).
    by apply prefix_app, Hw.
  Qed.

  (* ================================================================== *)
  (*  5.  THE CURSOR                                                     *)
  (* ================================================================== *)
  Lemma lm_pcount_write ps cs s E w b :
    lm_pcount ps cs s E (w ++ [b]) = S (lm_pcount ps cs s E w).
  Proof using. rewrite /lm_pcount length_app /=. lia. Qed.

  Lemma lm_pcount_echo ps cs s E x w :
    w = lm_pending ps cs s E ->
    lm_pcount ps cs s (E ++ [x]) [] = lm_pcount ps cs s E w.
  Proof using.
    intros ->. rewrite /lm_pcount fmap_app /=.
    rewrite (lm_proc_before_snoc M ps cs s (snd <$> E) x.2)
            /lm_proc_stream /lm_pending.
    rewrite length_app. cbn [length]. lia.
  Qed.

  Lemma lm_proc_stream_pcount ps cs s E w b :
    lm_pending ps cs s E !! length w = Some b ->
    lm_proc_stream M ps cs s (snd <$> E) !! lm_pcount ps cs s E w = Some b.
  Proof using.
    intros Hb. rewrite /lm_proc_stream /lm_pcount lookup_app_r; [| lia].
    replace (length (lm_proc_before M ps cs s (snd <$> E)) + length w
             - length (lm_proc_before M ps cs s (snd <$> E)))%nat
      with (length w) by lia.
    exact Hb.
  Qed.

  Lemma lm_proc_stream_pcount_inv ps cs s E w I b :
    (snd <$> E) `prefix_of` I ->
    (length w < length (lm_pending ps cs s E))%nat ->
    lm_proc_stream M ps cs s I !! lm_pcount ps cs s E w = Some b ->
    lm_pending ps cs s E !! length w = Some b.
  Proof using.
    intros HI Hlt Hl.
    destruct (lookup_lt_is_Some_2 (lm_pending ps cs s E) (length w) Hlt)
      as [b' Hb'].
    pose proof (lm_proc_stream_pcount ps cs s E w b' Hb') as Hfwd.
    assert (Heq : lm_proc_stream M ps cs s I !! lm_pcount ps cs s E w = Some b')
      by (eapply prefix_lookup_Some;
          [exact Hfwd | by apply lm_proc_stream_mono]).
    assert (Hbb : b = b') by congruence. by rewrite Hbb.
  Qed.

  (* ---- a stage read at a longer choice list: the same stream ---- *)
  Lemma lm_proc_stream_prefix ps0 ps cs0 cs s I0 :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> lm_pro_pin M ps0 cs0 I0 ->
    (nlines I0 <= length cs0)%nat ->
    lm_proc_stream M ps0 cs0 s I0 `prefix_of` lm_proc_stream M ps cs s I0.
  Proof using.
    intros Hps Hcs Hpin Hn.
    assert (Hb : lm_proc_before M ps0 cs0 s I0 = lm_proc_before M ps cs s I0).
    { apply (lm_proc_before_cs_prefix M ps0 ps cs0 cs s I0 Hps Hcs Hpin).
      etrans; [apply nlines_prefix, gop_removelast_prefix | exact Hn]. }
    rewrite /lm_proc_stream Hb. apply prefix_app.
    rewrite (lm_pending_at_cs_ext M ps0 cs0 cs s I0 Hcs Hn).
    by apply lm_pending_at_ps_mono.
  Qed.

  Lemma lm_pcount_cs_prefix ps0 ps cs0 cs s E w :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
    lm_pro_pin M ps0 cs0 (snd <$> E) ->
    (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
    lm_pcount ps0 cs0 s E w = lm_pcount ps cs s E w.
  Proof using.
    intros Hps Hcs Hpin Hn. rewrite /lm_pcount.
    by rewrite (lm_proc_before_cs_prefix M ps0 ps cs0 cs s (snd <$> E) Hps Hcs Hpin Hn).
  Qed.

  Lemma lm_D_from_ext ps0 ps cs0 cs s pre E :
    (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
       J <> pre ++ (snd <$> E) ->
       lm_pending_at M ps0 cs0 s J = lm_pending_at M ps cs s J) ->
    lm_D_from ps0 cs0 s pre E = lm_D_from ps cs s pre E.
  Proof using.
    revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
    assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
      by (by rewrite fmap_cons epu_app_snoc).
    assert (Hhere : lm_pending_at M ps0 cs0 s pre = lm_pending_at M ps cs s pre).
    { apply Hj.
      - reflexivity.
      - by eexists.
      - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
    cbn [lm_D_from]. rewrite Hhere. do 2 f_equal.
    apply IH. intros J H1 H2 H3. apply Hj.
    - etrans; [| exact H1]. by eexists.
    - rewrite -Hshape. exact H2.
    - rewrite -Hshape. exact H3.
  Qed.

  Lemma lm_D_cs_prefix ps0 ps cs0 cs s E :
    ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
    lm_pro_pin M ps0 cs0 (snd <$> E) ->
    (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
    lm_D ps0 cs0 s E = lm_D ps cs s E.
  Proof using.
    intros Hps Hcs Hpin Hn. rewrite /lm_D. apply lm_D_from_ext.
    intros J _ H2 H3. rewrite app_nil_l in H2, H3.
    exact (lm_pending_at_stage_ext M ps0 ps cs0 cs s (snd <$> E) J
             Hps Hcs Hpin Hn H2 H3).
  Qed.

  (* THE WRITE'S WHOLE PURE ARGUMENT: the writer names lower bounds of the
     era's choices, its INPUT and its cursor, and knows only that its byte
     is the [P]-th of the stream through [I0].  That alone pins the stage. *)
  Lemma lm_write_stage_byte (ps0 ps cs0 cs : list nat) (s : lm_st M)
        (E : list (list mobs * bv 8)) (w I0 : list (bv 8)) (P : nat) (b : bv 8) :
    ps0 `prefix_of` ps ->
    lm_pro_pin M ps0 cs0 I0 ->
    cs0 `prefix_of` cs ->
    (nlines I0 <= length cs0)%nat ->
    I0 `prefix_of` (snd <$> E) ->
    P = lm_pcount ps cs s E w ->
    lm_proc_stream M ps0 cs0 s I0 !! P = Some b ->
    (snd <$> E) = I0 /\ lm_pending ps cs s E !! length w = Some b.
  Proof using.
    intros Hps Hpin Hcs Hn HI HP Hb.
    pose proof (prefix_lookup_Some _ _ _ _ Hb
                  (lm_proc_stream_prefix ps0 ps cs0 cs s I0 Hps Hcs Hpin Hn))
      as Hb'.
    clear Hb. rename Hb' into Hb.
    assert (Hlt : (P < length (lm_proc_stream M ps cs s I0))%nat)
      by (by apply lookup_lt_Some in Hb).
    assert (HlenE : (snd <$> E) = I0).
    { destruct (decide ((snd <$> E) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (lm_proc_stream_before M ps cs s I0 (snd <$> E) HI
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre. rewrite HP /lm_pcount in Hlt. lia. }
    split; [exact HlenE |].
    rewrite -HlenE in Hb, Hlt.
    assert (Hstrict : (length w < length (lm_pending ps cs s E))%nat).
    { rewrite /lm_proc_stream length_app in Hlt.
      rewrite HP /lm_pcount in Hlt. rewrite /lm_pending. lia. }
    eapply (lm_proc_stream_pcount_inv ps cs s E w (snd <$> E) b);
      [reflexivity | exact Hstrict | by rewrite -HP].
  Qed.

  (* ---- no alternative prints nothing ---- *)
  Lemma lm_pending_nonnil (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) :
    lm_alts_pre M s (snd <$> E) cs -> (snd <$> E) <> [] ->
    rest_of (snd <$> E) = [] -> lm_pending ps cs s E <> [].
  Proof using K. rewrite /lm_pending. apply (lm_pending_at_nonnil M K). Qed.

  Lemma lm_pending_nil_inv (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) :
    lm_alts_pre M s (snd <$> E) cs -> rest_of (snd <$> E) = [] ->
    lm_pending ps cs s E = [] -> (snd <$> E) = [].
  Proof using K.
    intros Hao Hr Hnil.
    destruct (decide ((snd <$> E) = [])) as [? | Hne]; [done | exfalso].
    exact (lm_pending_nonnil ps cs s E Hao Hne Hr Hnil).
  Qed.


  (* ================================================================== *)
  (*  5b. THE PAD: a partial resolution completed to a full one          *)
  (*                                                                    *)
  (*  The discipline's and the claim's statements are at [lm_alts_ok] -- *)
  (*  one entry per completed line -- and the stage's list runs one short *)
  (*  at a block boundary.  The pad entry is the line's SILENT round      *)
  (*  ([lmh_noc]): admissible, never a panic, never coverage-ending,      *)
  (*  which is all a pad entry needs ([FileOutPure.ralt_def]/[PipeOutPure *)
  (*  .palt_def] were per-model choices of the same thing).               *)
  (* ================================================================== *)
  Definition lm_alts_pad (I : list (bv 8)) (cs : list nat) : list nat :=
    cs ++ ((fun b => lmh_noc K (lm_of M b)) <$> drop (length cs) (bodies_of I)).

  Lemma lm_alts_pad_prefix I cs : cs `prefix_of` lm_alts_pad I cs.
  Proof using. rewrite /lm_alts_pad. by eexists. Qed.

  Lemma lm_alts_pad_take I cs : take (length cs) (lm_alts_pad I cs) = cs.
  Proof using. rewrite /lm_alts_pad. by rewrite take_app_length. Qed.

  Lemma lm_alts_pad_length I cs :
    (length cs <= nlines I)%nat -> length (lm_alts_pad I cs) = nlines I.
  Proof using.
    intro Hle. rewrite /lm_alts_pad length_app length_fmap length_drop.
    rewrite /nlines in Hle |- *. lia.
  Qed.

  (* inside the pad, the entry is the line's silent round *)
  Lemma lm_alts_pad_at I cs j :
    (length cs <= j)%nat -> (j < nlines I)%nat ->
    lm_alts_pad I cs !!! j = lmh_noc K (lm_of M (bodies_of I !!! j)).
  Proof using.
    intros Hge Hlt. rewrite /nlines in Hlt.
    destruct (lookup_lt_is_Some_2 (bodies_of I) j Hlt) as [b Hb].
    rewrite (list_lookup_total_correct (bodies_of I) j b Hb).
    rewrite /lm_alts_pad list_lookup_total_alt lookup_app_r; [| lia].
    rewrite list_lookup_fmap lookup_drop.
    replace (length cs + (j - length cs))%nat with j by lia.
    by rewrite Hb.
  Qed.

  Lemma lm_alts_pad_ok s I cs :
    lm_alts_pre M s I cs -> lm_alts_ok M s I (lm_alts_pad I cs).
  Proof using.
    intros H. pose proof (lm_alts_pre_le M s I cs H) as Hle.
    split; [exact (lm_alts_pad_length I cs Hle) |].
    intros i Hi.
    destruct (decide (i < length cs)%nat) as [Hlt | Hge].
    - destruct (lookup_lt_is_Some_2 cs i Hlt) as [c Hc].
      destruct (H i c Hc) as [_ Hok].
      assert (Hpad : forall j, (j < length cs)%nat -> lm_alts_pad I cs !!! j = cs !!! j).
      { intros j Hj. rewrite /lm_alts_pad list_lookup_total_alt lookup_app_l; [| lia].
        by rewrite -list_lookup_total_alt. }
      rewrite (lm_upto_ext M (lm_alts_pad I cs) cs s (bodies_of I) (bodies_of I) i
                 ltac:(intros j Hj; apply Hpad; lia) ltac:(intros j _; reflexivity)).
      rewrite /lm_at (Hpad i Hlt) (list_lookup_total_correct _ _ _ Hc).
      exact Hok.
    - rewrite /lm_at (lm_alts_pad_at I cs i ltac:(lia) Hi). apply lmh_noc_ok.
  Qed.

  (* the pad changes no panic bit on the input's lines: below the stage's
     list it is the list, and past it both read a non-panicking round *)
  Lemma lm_alts_pad_panic I cs j :
    (j < nlines I)%nat ->
    lm_panic M (lm_at M (lm_alts_pad I cs) j) = lm_panic M (lm_at M cs j).
  Proof using B.
    intros Hj. destruct (decide (j < length cs)%nat) as [Hlt | Hge].
    - rewrite /lm_at /lm_alts_pad list_lookup_total_alt lookup_app_l; [| lia].
      by rewrite -list_lookup_total_alt.
    - rewrite (lm_panic_ge M B cs j ltac:(lia)).
      rewrite /lm_at (lm_alts_pad_at I cs j ltac:(lia) Hj).
      apply lmh_noc_nopanic.
  Qed.

  (* ...and the pad never ends coverage ([PipeOutPure.alts_pad_p_isforkS]) *)
  Lemma lm_alts_pad_term I cs j :
    (length cs <= j)%nat -> (j < nlines I)%nat ->
    lm_term M (lm_at M (lm_alts_pad I cs) j) = false.
  Proof using.
    intros Hge Hj. rewrite /lm_at (lm_alts_pad_at I cs j Hge Hj).
    apply (lmh_free_term K), (lmh_noc_free K).
  Qed.

  Lemma lm_alts_pad_pro_idx I cs q :
    (q <= nlines I)%nat -> lm_pro_idx M (lm_alts_pad I cs) q = lm_pro_idx M cs q.
  Proof using B.
    intros Hq. induction q as [| q IH]; [reflexivity |].
    cbn [lm_pro_idx]. rewrite IH; [| lia].
    by rewrite (lm_alts_pad_panic I cs q ltac:(lia)).
  Qed.

  Lemma lm_pro_idx_le cs i : (lm_pro_idx M cs i <= i)%nat.
  Proof using.
    induction i as [| i IH]; [cbn; lia |].
    cbn [lm_pro_idx]. destruct (lm_panic M (lm_at M cs i)); lia.
  Qed.

  (* past the choice list's end the round pointer stops moving *)
  Lemma lm_pro_idx_ge (cs : list nat) (q q' : nat) :
    (length cs <= q)%nat -> (q <= q')%nat ->
    lm_pro_idx M cs q' = lm_pro_idx M cs q.
  Proof using B.
    intros Hle Hq. induction q' as [| q' IH].
    - assert (Hz : q = 0%nat) by lia. by subst q.
    - destruct (decide (q = S q')) as [-> | Hne]; [reflexivity |].
      cbn [lm_pro_idx].
      rewrite (IH ltac:(lia)) (lm_panic_ge M B cs q' ltac:(lia)). lia.
  Qed.

  Lemma lm_pro_ok_pad ps cs m d :
    Forall (fun x => (x < length pro_alts)%nat) ps -> (m <= d)%nat ->
    lm_pro_ok M (ps ++ replicate (S d) 0%nat) cs m.
  Proof using.
    intros HF Hm. split.
    - apply Forall_app. split; [exact HF |].
      apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
      rewrite pro_alts_length. lia.
    - rewrite pro_rounds_app pro_rounds_replicate_0.
      pose proof (lm_pro_idx_le cs m). lia.
  Qed.

  (* THE STAGE'S TRANSCRIPT AT A FULL RESOLUTION (the file's former [stage_sessf_pad] once): the padded list agrees with the stage's
     wherever the stage reads it, and the stage's transcript is below the
     padded session *)
  Lemma lm_stage_sess_pad (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) :
    lm_alts_pre M s (snd <$> E) cs ->
    (nlines (removelast (snd <$> E)) <= length cs)%nat ->
    ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
    lm_E_disc E ->
    lm_pro_pin M ps cs (snd <$> E) ->
    w `prefix_of` lm_pending ps cs s E ->
    lm_alts_ok M s (snd <$> E) (lm_alts_pad (snd <$> E) cs)
    /\ lm_pro_pin M ps (lm_alts_pad (snd <$> E) cs) (snd <$> E)
    /\ lm_D ps cs s E = lm_D ps (lm_alts_pad (snd <$> E) cs) s E
    /\ w `prefix_of` lm_pending ps (lm_alts_pad (snd <$> E) cs) s E
    /\ (lm_D ps cs s E ++ w)
         `prefix_of` lm_sess M ps (lm_alts_pad (snd <$> E) cs) s (snd <$> E).
  Proof using B.
    intros Hao Hrl Hlast HE Hpin Hw.
    set (cs' := lm_alts_pad (snd <$> E) cs).
    assert (Hcc : cs `prefix_of` cs') by apply lm_alts_pad_prefix.
    assert (Hok : lm_alts_ok M s (snd <$> E) cs') by exact (lm_alts_pad_ok s _ cs Hao).
    assert (Hpin' : lm_pro_pin M ps cs' (snd <$> E)).
    { intros q Hq.
      assert (Hqle : (q <= nlines (snd <$> E))%nat).
      { pose proof (nstarted_le_S (snd <$> E)). lia. }
      rewrite /cs' (lm_alts_pad_pro_idx (snd <$> E) cs q Hqle). by apply Hpin. }
    assert (HD : lm_D ps cs s E = lm_D ps cs' s E)
      by (apply (lm_D_cs_prefix ps ps cs cs' s E ltac:(reflexivity) Hcc Hpin Hrl)).
    assert (Hw' : w `prefix_of` lm_pending ps cs' s E).
    { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
      rewrite /lm_pending
        -(lm_pending_at_cs_ext M ps cs cs' s (snd <$> E) Hcc Hle). exact Hw. }
    split_and!; [exact Hok | exact Hpin' | exact HD | exact Hw' |].
    rewrite HD. exact (lm_D_stage_prefix ps cs' s E w HE Hw').
  Qed.

  (* THE CLAIM GIVES [lm_good_out] AT THE SEGMENT, at the stage's own boot
     state (the file's former [good_out_f_of_stage] once): the prologue list is
     padded with settled rounds and the choice list with silent ones *)
  Lemma lm_good_out_of_stage (ps cs : list nat) (s : lm_st M)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) (seg : list mobs) :
    Forall (fun a => (a < length pro_alts)%nat) ps ->
    lm_alts_pre M s (ins seg) cs ->
    (nlines (removelast (snd <$> E)) <= length cs)%nat ->
    ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
    lm_E_disc E ->
    lm_pro_pin M ps cs (snd <$> E) ->
    w `prefix_of` lm_pending ps cs s E ->
    obs_wire Uart0 seg `prefix_of` (lm_D ps cs s E ++ w) ->
    (snd <$> E) `prefix_of` ins seg ->
    lm_good_out M s seg.
  Proof using B K.
    intros Hps Hao Hrl Hlast HE Hpin Hw Hwire Hinp.
    set (ps' := (ps ++ replicate (S (nlines (ins seg))) 0%nat)%list).
    set (cs' := lm_alts_pad (ins seg) cs).
    assert (Hpp : ps `prefix_of` ps') by (rewrite /ps'; by eexists).
    assert (Hcc : cs `prefix_of` cs') by apply lm_alts_pad_prefix.
    assert (Hpin' : lm_pro_pin M ps' cs (snd <$> E))
      by exact (lm_pro_pin_mono M ps ps' cs _ Hpp Hpin).
    exists ps', cs'. split.
    { apply lm_pro_ok_pad; [exact Hps | lia]. }
    split; [exact (lm_alts_pad_ok s (ins seg) cs Hao) |].
    etrans; [exact Hwire |].
    rewrite (lm_D_ps_ext ps ps' cs s E Hpp Hpin).
    rewrite (lm_D_cs_prefix ps' ps' cs cs' s E ltac:(reflexivity) Hcc Hpin' Hrl).
    assert (Hw' : w `prefix_of` lm_pending ps' cs' s E).
    { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
      etrans; [exact Hw |].
      etrans; [exact (lm_pending_ps_mono ps ps' cs s E Hpp) |].
      rewrite /lm_pending (lm_pending_at_cs_ext M ps' cs cs' s (snd <$> E) Hcc Hle).
      reflexivity. }
    etrans; [exact (lm_D_stage_prefix ps' cs' s E w HE Hw') |].
    by apply (lm_sess_mono M ps' cs' s (snd <$> E) (ins seg)).
  Qed.

  (* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
     that was good ([FileOutPure.good_out_f_step] once): the longer input
     may have one more complete line, so the resolution is padded; the pad
     moves no prologue round and changes no block of the shorter input *)
  Lemma lm_good_out_step (s : lm_st M) (seg : list mobs) (e : mobs) :
    obs_wire Uart0 [e] = [] -> lm_good_out M s seg -> lm_good_out M s (seg ++ [e]).
  Proof using B K.
    intros He (ps & cs & [Hpsb Hlt] & Hao & Hwire).
    set (I := ins seg). set (I' := ins (seg ++ [e])).
    assert (HII : I `prefix_of` I') by (rewrite /I /I' ins_app; by eexists).
    assert (Hlen : length cs = nlines I) by exact (lm_alts_ok_len M s _ _ Hao).
    assert (Hnl : (nlines I <= nlines I')%nat) by (by apply nlines_prefix).
    set (cs' := lm_alts_pad I' cs).
    exists ps, cs'. split.
    { split; [exact Hpsb |].
      rewrite /cs' (lm_alts_pad_pro_idx I' cs (nlines I') ltac:(lia)).
      rewrite (lm_pro_idx_ge cs (nlines I) (nlines I') ltac:(lia) Hnl).
      exact Hlt. }
    split.
    { rewrite /cs'. apply lm_alts_pad_ok.
      apply (lm_alts_pre_mono M s I I'); [exact HII |].
      exact (lm_alts_pre_of_alts_ok M s _ _ Hao). }
    rewrite /I' obs_wire_app He app_nil_r.
    etrans; [exact Hwire |].
    assert (Hcut : lm_sess M ps cs s I = lm_sess M ps cs' s I).
    { apply lm_sess_cs_ext. intros j Hj. symmetry.
      rewrite /cs' /lm_alts_pad list_lookup_total_alt lookup_app_l; [| lia].
      by rewrite -list_lookup_total_alt. }
    rewrite Hcut. by apply lm_sess_mono.
  Qed.

  (* ================================================================== *)
  (*  6.  THE TWO LENGTH LAWS OF THE CHOICE LISTS, AT THE STAGE          *)
  (* ================================================================== *)
  Context (sd : lm_st M).
  Local Notation st so := (gs_state sd so).

  (* THE CHOICE LIST records one alternative per COMPLETED line, and grows
     at the FIRST BYTE of that line's continuation -- so it is one short
     exactly while the writer stands at a block boundary with nothing of
     the block written *)
  Definition lm_cs_len_ok (so : gstage) : Prop :=
    length (gs_cs so)
    = (if decide (gs_w so = [] /\ rest_of (snd <$> gs_E so) = [])
       then (nlines (snd <$> gs_E so) - 1)%nat
       else nlines (snd <$> gs_E so)).

  Lemma lm_cs_len_ok_inv (so : gstage) :
    lm_cs_len_ok so ->
    ((gs_w so = [] /\ rest_of (snd <$> gs_E so) = [])
       /\ length (gs_cs so) = (nlines (snd <$> gs_E so) - 1)%nat)
    \/ (~ (gs_w so = [] /\ rest_of (snd <$> gs_E so) = [])
       /\ length (gs_cs so) = nlines (snd <$> gs_E so)).
  Proof using.
    rewrite /lm_cs_len_ok. case_decide as Hb; intros Hc.
    - left. by split.
    - right. by split.
  Qed.

  Lemma lm_cs_len_ok_intro (ps cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (o : option (lm_st M)) :
    ((w = [] /\ rest_of (snd <$> E) = []) ->
       length cs = (nlines (snd <$> E) - 1)%nat) ->
    (~ (w = [] /\ rest_of (snd <$> E) = []) ->
       length cs = nlines (snd <$> E)) ->
    lm_cs_len_ok (MkGS ps cs E w o).
  Proof using.
    rewrite /lm_cs_len_ok. cbn [gs_ps gs_cs gs_E gs_w gs_st]. unfold gs_state. cbn [gs_st].
    intros H1 H2. case_decide as Hb; [by apply H1 | by apply H2].
  Qed.

  Lemma lm_cs_len_ok_mid (so : gstage) :
    lm_cs_len_ok so -> gs_w so <> [] ->
    length (gs_cs so) = nlines (snd <$> gs_E so).
  Proof using.
    intros Hc Hw. destruct (lm_cs_len_ok_inv so Hc) as [[[Hw' _] _] | [_ ?]];
      [done | done].
  Qed.

  Lemma lm_cs_len_ok_echo (so : gstage) (x : list mobs * bv 8) :
    lm_alts_pre M (st so) (snd <$> gs_E so) (gs_cs so) ->
    gs_w so = lm_pending (gs_ps so) (gs_cs so) (st so) (gs_E so) ->
    lm_cs_len_ok so ->
    lm_cs_len_ok (MkGS (gs_ps so) (gs_cs so) (gs_E so ++ [x]) [] (gs_st so)).
  Proof using K.
    intros Hao Hw Hc.
    assert (Hq : length (gs_cs so) = nlines (snd <$> gs_E so)).
    { destruct (lm_cs_len_ok_inv so Hc) as [[[Hw' Hm] Hq] | [_ Hq]]; [| exact Hq].
      pose proof (lm_pending_nil_inv (gs_ps so) (gs_cs so) (st so) (gs_E so)
                    Hao Hm ltac:(by rewrite -Hw)) as Hz.
      rewrite Hz in Hq |- *. rewrite nlines_nil in Hq |- *. lia. }
    apply lm_cs_len_ok_intro; rewrite fmap_app /= Hq.
    - intros [_ Hm]. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
      + rewrite Hx nlines_snoc_nl. lia.
      + exfalso. rewrite (rest_of_snoc_other _ _ Hx) in Hm.
        by destruct (app_eq_nil (rest_of (snd <$> gs_E so)) [x.2] Hm) as [_ Hb].
    - intros Hne. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
      + exfalso. apply Hne. split; [reflexivity |].
        rewrite Hx. apply rest_of_snoc_nl.
      + by rewrite (nlines_snoc_other _ _ Hx).
  Qed.

  Lemma lm_cs_len_ok_write (so : gstage) (b : bv 8) :
    lm_cs_len_ok so ->
    (gs_w so <> [] \/ rest_of (snd <$> gs_E so) <> [] \/ (snd <$> gs_E so) = []) ->
    lm_cs_len_ok (MkGS (gs_ps so) (gs_cs so) (gs_E so) (gs_w so ++ [b]) (gs_st so)).
  Proof using.
    intros Hc Hcase. apply lm_cs_len_ok_intro.
    { intros [Hw _]. exfalso.
      by destruct (app_eq_nil (gs_w so) [b] Hw) as [_ Hb]. }
    intros _. destruct (lm_cs_len_ok_inv so Hc) as [[[Hw Hm] Hq] | [_ Hq]];
      [| exact Hq].
    destruct Hcase as [Hw' | [Hm' | Hn]]; [done | done |].
    rewrite Hq Hn nlines_nil. lia.
  Qed.

  Lemma lm_cs_len_ok_blk (so : gstage) (a : nat) (b : bv 8) :
    rest_of (snd <$> gs_E so) = [] ->
    (snd <$> gs_E so) <> [] ->
    gs_w so = [] ->
    lm_cs_len_ok so ->
    lm_cs_len_ok (MkGS (gs_ps so) (gs_cs so ++ [a]) (gs_E so) [b] (gs_st so)).
  Proof using.
    intros Hr Hne Hw Hc.
    pose proof (nlines_pos_of_rest_nil (snd <$> gs_E so) Hne Hr) as Hpos.
    destruct (lm_cs_len_ok_inv so Hc) as [[_ Hq] | [Hne' _]]; last first.
    { exfalso. by apply Hne'. }
    apply lm_cs_len_ok_intro.
    { intros [Hb _]. discriminate. }
    intros _. rewrite length_app. cbn [length]. rewrite Hq. lia.
  Qed.

  Lemma lm_cs_len_ok_0 : lm_cs_len_ok gstage0.
  Proof using.
    rewrite /gstage0. apply (lm_cs_len_ok_intro [] [] [] [] None); intros _;
      cbn [length]; rewrite fmap_nil nlines_nil; lia.
  Qed.

  (* ---- the prologue resolution's length law ---- *)
  Definition lm_ps_round (so : gstage) : nat :=
    lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so)).

  Definition lm_ps_opens (so : gstage) : Prop :=
    (snd <$> gs_E so) = []
    \/ (rest_of (snd <$> gs_E so) = []
        /\ lm_panic M (lm_at M (gs_cs so) (nlines (snd <$> gs_E so) - 1)) = true).

  Definition lm_ps_len_ok (so : gstage) : Prop :=
    pro_from (S (lm_ps_round so)) (gs_ps so) = []
    /\ (lm_ps_opens so ->
        forall ps' : list nat, ps' `prefix_of` gs_ps so ->
          pro_of (pro_from (lm_ps_round so) ps')
            <> pro_of (pro_from (lm_ps_round so) (gs_ps so)) ->
          (length (lm_pending_at M ps' (gs_cs so) (st so) (snd <$> gs_E so))
           < length (gs_w so))%nat).

  Lemma lm_ps_len_ok_empty_above (so : gstage) (R : nat) :
    lm_ps_len_ok so -> (lm_ps_round so <= R)%nat -> pro_from (S R) (gs_ps so) = [].
  Proof using.
    intros [HA _] HR.
    replace (S R) with (S (lm_ps_round so) + (R - lm_ps_round so))%nat by lia.
    rewrite -pro_from_add HA. apply pro_from_nil.
  Qed.

  Lemma lm_ps_len_ok_0 : lm_ps_len_ok gstage0.
  Proof using.
    rewrite /lm_ps_len_ok /lm_ps_round /gstage0.
    cbn [gs_ps gs_cs gs_E gs_w gs_st]. unfold gs_state. cbn [gs_st]. split.
    - apply pro_from_nil.
    - intros _ ps' Hp Hne. exfalso. apply Hne.
      by rewrite (prefix_nil_inv ps' Hp).
  Qed.

  Lemma lm_ps_len_ok_write (so : gstage) (b : bv 8) :
    lm_ps_len_ok so ->
    lm_ps_len_ok (MkGS (gs_ps so) (gs_cs so) (gs_E so) (gs_w so ++ [b]) (gs_st so)).
  Proof using.
    intros [HA HB]. rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB |- *. unfold gs_state in *. cbn [gs_st] in *. split; [exact HA |].
    intros Ho ps' Hp Hne. rewrite (length_app (gs_w so) [b]). cbn [length].
    pose proof (HB Ho ps' Hp Hne). lia.
  Qed.

  Lemma lm_ps_len_ok_blk (so : gstage) (a : nat) (b : bv 8) :
    rest_of (snd <$> gs_E so) = [] ->
    (snd <$> gs_E so) <> [] ->
    length (gs_cs so) = (nlines (snd <$> gs_E so) - 1)%nat ->
    lm_ps_len_ok so ->
    lm_ps_len_ok (MkGS (gs_ps so) (gs_cs so ++ [a]) (gs_E so) [b] (gs_st so)).
  Proof using B.
    intros Hr Hne Hq Hok.
    pose proof (nlines_pos_of_rest_nil (snd <$> gs_E so) Hne Hr) as Hpos.
    pose proof Hok as [HA HB].
    rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB |- *. unfold gs_state in *. cbn [gs_st] in *.
    assert (Hold : lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))
                   = lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so) - 1)%nat).
    { replace (nlines (snd <$> gs_E so))
        with (S (nlines (snd <$> gs_E so) - 1))%nat at 1 by lia.
      apply lm_pro_idx_Sn. apply (lm_panic_ge M B). lia. }
    assert (Hnew : (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))
                    <= lm_pro_idx M (gs_cs so ++ [a])
                         (nlines (snd <$> gs_E so)))%nat).
    { rewrite Hold.
      replace (nlines (snd <$> gs_E so))
        with (S (nlines (snd <$> gs_E so) - 1))%nat at 2 by lia.
      rewrite lm_pro_idx_S
        (lm_pro_idx_app_le M (gs_cs so) [a] (nlines (snd <$> gs_E so) - 1)%nat
           ltac:(lia)).
      destruct (lm_panic M _); lia. }
    split.
    - apply (lm_ps_len_ok_empty_above so); [exact Hok |].
      rewrite /lm_ps_round. exact Hnew.
    - intros Ho ps' Hp Hne2. exfalso.
      destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
      assert (Ha3 : lm_panic M (lm_dec M a) = true).
      { rewrite /lm_at list_lookup_total_alt lookup_app_r in H3; [| lia].
        rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
      assert (Heq : lm_pro_idx M (gs_cs so ++ [a]) (nlines (snd <$> gs_E so))
                    = S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so)))).
      { rewrite Hold
          -(lm_pro_idx_app_le M (gs_cs so) [a] (nlines (snd <$> gs_E so) - 1)%nat
              ltac:(lia)).
        replace (nlines (snd <$> gs_E so))
          with (S (nlines (snd <$> gs_E so) - 1))%nat at 1 by lia.
        apply lm_pro_idx_Sp.
        rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
        rewrite Hq Nat.sub_diag. by cbn. }
      rewrite Heq in Hne2. apply Hne2.
      assert (Hnil : pro_from
                       (S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
                       (gs_ps so) = []) by exact HA.
      assert (Hnil' : pro_from
                        (S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
                        ps' = []).
      { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
      by rewrite Hnil Hnil'.
  Qed.

  Lemma lm_ps_len_ok_echo (so : gstage) (x : list mobs * bv 8) :
    lm_ps_len_ok so ->
    lm_ps_len_ok (MkGS (gs_ps so) (gs_cs so) (gs_E so ++ [x]) [] (gs_st so)).
  Proof using.
    intros Hok. pose proof Hok as [HA HB].
    rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB |- *. unfold gs_state in *. cbn [gs_st] in *.
    rewrite fmap_app /=.
    assert (Hmono : (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))
                     <= lm_pro_idx M (gs_cs so)
                          (nlines ((snd <$> gs_E so) ++ [x.2])))%nat)
      by (apply lm_pro_idx_mono, nlines_app_le).
    split.
    - apply (lm_ps_len_ok_empty_above so); [exact Hok |].
      rewrite /lm_ps_round. exact Hmono.
    - intros Ho ps' Hp Hne. exfalso.
      destruct Ho as [Hz | [Hr H3]].
      { by destruct (app_eq_nil (snd <$> gs_E so) [x.2] Hz) as [_ Hb]. }
      assert (Hx : x.2 = wl_nl).
      { destruct (decide (x.2 = wl_nl)) as [Hx | Hx]; [exact Hx | exfalso].
        rewrite (rest_of_snoc_other (snd <$> gs_E so) x.2 Hx) in Hr.
        by destruct (app_eq_nil (rest_of (snd <$> gs_E so)) [x.2] Hr) as [_ Hb]. }
      rewrite Hx (nlines_snoc_nl (snd <$> gs_E so)) in H3.
      rewrite Hx (nlines_snoc_nl (snd <$> gs_E so)) in Hne.
      replace (S (nlines (snd <$> gs_E so)) - 1)%nat
        with (nlines (snd <$> gs_E so)) in H3 by lia.
      assert (Heq : lm_pro_idx M (gs_cs so) (S (nlines (snd <$> gs_E so)))
                    = S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
        by (apply lm_pro_idx_Sp; exact H3).
      rewrite Heq in Hne. apply Hne.
      assert (Hnil : pro_from
                       (S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
                       (gs_ps so) = []) by exact HA.
      assert (Hnil' : pro_from
                        (S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
                        ps' = []).
      { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
      by rewrite Hnil Hnil'.
  Qed.

  Lemma lm_ps_len_ok_pro (so : gstage) (a : nat) (b : bv 8) :
    (lm_ps_round so <= pro_rounds (gs_ps so))%nat ->
    ~ pro_done (pro_from (lm_ps_round so) (gs_ps so)) ->
    gs_w so = lm_pending (gs_ps so) (gs_cs so) (st so) (gs_E so) ->
    lm_ps_len_ok so ->
    lm_ps_len_ok (MkGS (gs_ps so ++ [a]) (gs_cs so) (gs_E so)
                   (gs_w so ++ [b]) (gs_st so)).
  Proof using.
    intros Hle Hnd Hw [HA HB].
    rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB, Hle, Hnd |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB, Hle, Hnd |- *. unfold gs_state in *. cbn [gs_st] in *. split.
    - replace (S (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so))))
        with (lm_pro_idx M (gs_cs so) (nlines (snd <$> gs_E so)) + 1)%nat by lia.
      rewrite -pro_from_add (pro_from_snoc_le _ (gs_ps so) a Hle).
      cbn [pro_from]. by apply pro_tail_open_snoc.
    - intros Ho ps' Hp Hne. rewrite (length_app (gs_w so) [b]). cbn [length].
      destruct (decide (length ps' <= length (gs_ps so))%nat) as [Hlen | Hlen].
      + assert (Hp2 : ps' `prefix_of` gs_ps so).
        { destruct (prefix_weak_total ps' (gs_ps so) (gs_ps so ++ [a]) Hp
                      ltac:(by eexists)) as [H | H]; [exact H |].
          rewrite (prefix_length_eq _ _ H ltac:(lia)). reflexivity. }
        pose proof (prefix_length _ _ (lm_pending_at_ps_mono ps' (gs_ps so)
                      (gs_cs so) (default sd (gs_st so)) (snd <$> gs_E so) Hp2))
          as Hlp.
        rewrite -/(lm_pending (gs_ps so) (gs_cs so) (default sd (gs_st so)) (gs_E so))
          -Hw in Hlp. lia.
      + rewrite (prefix_length_eq ps' (gs_ps so ++ [a]) Hp) in Hne;
          last by (rewrite (length_app (gs_ps so) [a]); cbn [length]; lia).
        by destruct (Hne eq_refl).
  Qed.

  (* ================================================================== *)
  (*  7.  THE STAGE'S WHOLE PURE ACCOUNT                                 *)
  (* ================================================================== *)
  Definition lm_out_pure (k : nat) (ho : list mobs) (so : gstage)
      (acc : list (bv 8)) : Prop :=
    acc = lm_D (gs_ps so) (gs_cs so) (st so) (gs_E so) ++ gs_w so
    /\ gs_w so `prefix_of` lm_pending (gs_ps so) (gs_cs so) (st so) (gs_E so)
    /\ E_index (gs_E so)
    /\ lm_E_disc (gs_E so)
    /\ Forall (fun a => (a < length pro_alts)%nat) (gs_ps so)
    /\ lm_pro_pin M (gs_ps so) (gs_cs so) (snd <$> gs_E so)
    /\ lm_alts_pre M (st so) (snd <$> gs_E so) (gs_cs so)
    /\ Forall (fun x => lm_disc_input M (ins x.1)) (gs_E so)
    /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (gs_E so)
    /\ (length (gs_E so) <= length (ins (open_seg ho)))%nat
    /\ (gs_E so = [] \/ obs_boots ho = k)
    (* the choice list names no terminal alternative (the pipe's
       [cs_nofork]; vacuous where no alternative is terminal) *)
    /\ Forall (fun c => lm_term M (lm_dec M c) = false) (gs_cs so)
    (* the boot state is not read before it is filed, and the filed one is
       well-formed (the file's two clauses; [None] and a trivial [lm_st_ok]
       make them vacuous elsewhere) *)
    /\ (gs_st so = None <-> (gs_E so = [] /\ gs_w so = []))
    /\ lm_st_ok M (st so).

  Lemma lm_out_pure_0 k ho : lm_st_ok M sd -> lm_out_pure k ho gstage0 [].
  Proof using.
    intro Hsd. rewrite /lm_out_pure /gstage0. cbn [gs_ps gs_cs gs_E gs_w gs_st]. unfold gs_state. cbn [gs_st].
    split_and!.
    - rewrite lm_D_nil. done.
    - rewrite lm_pending_nil. apply prefix_nil.
    - intros j x Hx. by rewrite lookup_nil in Hx.
    - rewrite /lm_E_disc fmap_nil. split_and!; [constructor | constructor |].
      rewrite rest_of_nil. cbn [length]. rewrite /line_max. lia.
    - constructor.
    - rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
    - apply lm_alts_pre_nil.
    - constructor.
    - constructor.
    - cbn [length]. lia.
    - by left.
    - constructor.
    - split; [by intros _ | by intros _].
    - exact Hsd.
  Qed.
End gen_out_pure.
