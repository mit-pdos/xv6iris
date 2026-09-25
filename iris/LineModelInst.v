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
