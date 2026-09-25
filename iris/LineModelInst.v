(* ===================================================================== *)
(*  LineModelInst.v -- THE STREAM FOLDS AT THE INSTANCES, AND THE ECHO    *)
(*  MODEL (app-both milestone M1).                                       *)
(*                                                                       *)
(*  The file's and the pipe's line models live with their models         *)
(*  ([FileDisc.file_lm], [PipeDisc.pipe_lm], with the session equations  *)
(*  and the determinacy corollaries).  What is left here is what needs   *)
(*  the stage files: the stream folds ([FileOutPure.proc_stream_f],       *)
(*  [PipeOutPure.proc_stream_p]) as [LineModel]'s, by induction -- the   *)
(*  state is a fixpoint PARAMETER there (at [option fstate] on the file   *)
(*  side, absent on the pipe side), so those fixes do not convert -- and *)
(*  the echo model, whose session is [EchoDisc.sess] by an equation      *)
(*  (its panic test is [decide], the model's [bool_decide]).             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.
Require Import PipeDisc.
Require Import FileOutPure.
Require Import PipeOutPure.
Require Import LineModel.
From stdpp Require Import ssreflect.

Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE FILE APPLICATION'S STREAM                                      *)
(* ====================================================================== *)
Lemma pending_at_f_lm ps cs s0 I :
  pending_at_f ps cs (Some s0) I = lm_pending_at file_lm ps cs s0 I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_f_lm ps cs s0 pre I :
  proc_before_from_f ps cs (Some s0) pre I
  = lm_proc_before_from file_lm ps cs s0 pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH pending_at_f_lm.
Qed.

Lemma proc_before_f_lm ps cs s0 I :
  proc_before_f ps cs (Some s0) I = lm_proc_before file_lm ps cs s0 I.
Proof using. apply proc_before_from_f_lm. Qed.

Lemma proc_stream_f_lm ps cs s0 I :
  proc_stream_f ps cs (Some s0) I = lm_proc_stream file_lm ps cs s0 I.
Proof using.
  rewrite /proc_stream_f /lm_proc_stream. by rewrite proc_before_f_lm pending_at_f_lm.
Qed.

(* ====================================================================== *)
(*  2.  THE PIPELINE APPLICATION'S STREAM                                  *)
(* ====================================================================== *)
Lemma pending_at_p_lm ps cs I :
  pending_at_p ps cs I = lm_pending_at pipe_lm ps cs tt I.
Proof using. reflexivity. Qed.

Lemma proc_before_from_p_lm ps cs pre I :
  proc_before_from_p ps cs pre I = lm_proc_before_from pipe_lm ps cs tt pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre; [reflexivity |].
  cbn. by rewrite IH pending_at_p_lm.
Qed.

Lemma proc_before_p_lm ps cs I :
  proc_before_p ps cs I = lm_proc_before pipe_lm ps cs tt I.
Proof using. apply proc_before_from_p_lm. Qed.

Lemma proc_stream_p_lm ps cs I :
  proc_stream_p ps cs I = lm_proc_stream pipe_lm ps cs tt I.
Proof using.
  rewrite /proc_stream_p /lm_proc_stream. by rewrite proc_before_p_lm pending_at_p_lm.
Qed.

(* ====================================================================== *)
(*  3.  THE ECHO APPLICATION -- the four alternatives are their own code   *)
(*                                                                        *)
(*  No byte-shape laws are stated: [EchoOutPure.sess_prefix_det] is       *)
(*  stated at [cs_ok] (every code below 4, at every index), not at the    *)
(*  model's range condition, and echo is the pipeline's corollary in the  *)
(*  landed tree ([PipeDisc.disc_disc_p]).                                 *)
(* ====================================================================== *)
Definition echo_lm : lmodel :=
  MkLM unit (list (list (bv 8))) wl_words nat (fun k => k)
       (fun k => bool_decide (k = 3))
       (fun _ ws k => line_alts_of ws !!! k)
       (fun _ _ _ => tt) (fun _ _ k => k < 4) body_ok wl_body_byte
       line_ok (fun _ => True) (fun _ => false) (fun _ => False).

Lemma echo_lm_byte_laws : lm_byte_laws echo_lm.
Proof using.
  constructor.
  - intros l Hl. exact (body_ok_bytes l Hl).
  - intros l Hl. exact (body_ok_short l Hl).
  - intros b Hb. destruct Hb as [Ha | ->].
    + destruct Ha as [H | [H | H]]; lia.
    + rewrite wl_sp_val. lia.
  - reflexivity.
Qed.

Lemma pro_idx_lm cs i : pro_idx cs i = lm_pro_idx echo_lm cs i.
Proof using.
  induction i as [| i IH]; [reflexivity |]. cbn. rewrite IH.
  rewrite /lm_at /=. by case_bool_decide; case_decide; lia.
Qed.

Lemma alt_cont_lm ps cs bs i :
  alt_cont ps cs bs i = lm_cont_at echo_lm ps cs tt bs i.
Proof using.
  rewrite /alt_cont /lm_cont_at /lm_at /= pro_idx_lm.
  by case_bool_decide; case_decide; try lia.
Qed.

Lemma alt_seq_lm ps cs bs q : alt_seq ps cs bs q = lm_seq echo_lm ps cs tt bs q.
Proof using.
  rewrite /alt_seq /lm_seq. f_equal. apply list_fmap_ext. intros i x _.
  rewrite /alt_blk /lm_blk. by rewrite alt_cont_lm.
Qed.

Lemma sess_lm ps cs I : sess ps cs I = lm_sess echo_lm ps cs tt I.
Proof using. rewrite /sess /lm_sess. by rewrite alt_seq_lm. Qed.

Lemma pro_ok_lm ps cs q : pro_ok ps cs q <-> lm_pro_ok echo_lm ps cs q.
Proof using. rewrite /pro_ok /lm_pro_ok pro_idx_lm. reflexivity. Qed.

(* ---- the discipline and the claim, as the model's.  Echo's range
   condition ([length cs = nlines] and every code below 4) IS the model's
   [lm_alts_ok], whose per-line admissibility ignores the line. ---- *)
Lemma alts_ok_lm I cs :
  length cs = nlines I /\ Forall (fun c => (c < 4)%nat) cs
  <-> lm_alts_ok echo_lm tt I cs.
Proof using.
  rewrite (lm_alts_ok_nostate echo_lm tt I cs (fun _ _ _ _ Hx => Hx)). split.
  - intros [Hl HF].
    apply Forall2_same_length_lookup_2; [by rewrite length_fmap Hl |].
    intros i l c _ Hc. exact (Forall_lookup_1 _ _ _ _ HF Hc).
  - intros H. split.
    + apply Forall2_length in H. by rewrite length_fmap in H.
    + apply Forall_lookup. intros i c Hc.
      destruct (Forall2_lookup_r _ _ _ _ _ H Hc) as (l & _ & Hok). exact Hok.
Qed.

Lemma disc_pt_lm ps cs p : disc_pt ps cs p <-> lm_disc_pt echo_lm ps cs tt p.
Proof using. rewrite /disc_pt /lm_disc_pt sess_lm. done. Qed.

Lemma disc_seg'_lm seg : disc_seg' seg <-> lm_disc_seg' echo_lm tt seg.
Proof using.
  rewrite /disc_seg' /lm_disc_seg' /disc_seg. split.
  - intros [Hd (ps & cs & Hl & HF & Hall)]. split; [exact Hd |]. exists ps, cs.
    split; [by apply alts_ok_lm |].
    split; [apply lm_d4_noterm; intro a; reflexivity |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_lm | by apply disc_pt_lm].
  - intros [Hd (ps & cs & Hao & _ & Hall)]. split; [exact Hd |]. exists ps, cs.
    destruct (proj2 (alts_ok_lm _ _) Hao) as [Hl HF].
    split; [exact Hl |]. split; [exact HF |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_lm | by apply disc_pt_lm].
Qed.

Lemma disc_lm h : disc h <-> lm_disc echo_lm h.
Proof using.
  rewrite /disc /lm_disc. split; intros H.
  - eapply Forall_impl; [exact H |]. intros seg Hd. exists tt. split; [exact Logic.I | by apply disc_seg'_lm].
  - eapply Forall_impl; [exact H |]. intros seg ([] & _ & Hd). by apply disc_seg'_lm.
Qed.

Lemma expected_rel_lm I out :
  expected_rel I out <-> lm_expected_rel echo_lm tt I out.
Proof using.
  rewrite /expected_rel /lm_expected_rel. split.
  - (* echo's resolution need not be as long as the input: pad it with
       [0]s, which neither the transcript nor the round pointer reads *)
    intros (ps & cs & Hok & HF & Hw).
    set (cs' := take (nlines I) (cs ++ replicate (nlines I) 0%nat)).
    assert (Hext : forall j, (j < nlines I)%nat -> cs' !!! j = cs !!! j).
    { intros j Hj. rewrite /cs' list_lookup_total_alt lookup_take; [| lia].
      destruct (decide (j < length cs)%nat) as [Hlt | Hge].
      - rewrite lookup_app_l; [| lia]. by rewrite -list_lookup_total_alt.
      - rewrite lookup_app_r; [| lia]. rewrite lookup_replicate_2; [| lia].
        rewrite list_lookup_total_alt (lookup_ge_None_2 cs j ltac:(lia)).
        reflexivity. }
    assert (Hlen : length cs' = nlines I).
    { rewrite /cs' length_take length_app length_replicate. lia. }
    assert (HF' : Forall (fun c => (c < 4)%nat) cs').
    { apply Forall_take, Forall_app. split; [exact HF |].
      apply Forall_replicate. lia. }
    exists ps, cs'. split.
    { apply pro_ok_lm. destruct Hok as [Hps Hlt]. split; [exact Hps |].
      by rewrite (pro_idx_ext cs' cs (nlines I) Hext (nlines I) (Nat.le_refl _)). }
    split; [by apply alts_ok_lm |].
    rewrite -(lm_sess_cs_ext echo_lm ps cs cs' tt I
                ltac:(intros j Hj; by rewrite Hext)).
    by rewrite -sess_lm.
  - intros (ps & cs & Hok & Hao & Hw). exists ps, cs.
    destruct (proj2 (alts_ok_lm _ _) Hao) as [_ HF].
    split; [by apply pro_ok_lm |]. split; [exact HF |]. by rewrite sess_lm.
Qed.

Lemma good_out_lm seg : good_out seg <-> lm_good_out echo_lm tt seg.
Proof using. rewrite /good_out /lm_good_out. apply expected_rel_lm. Qed.
