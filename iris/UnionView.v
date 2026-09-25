(* ===================================================================== *)
(* UnionView.v -- THE UNION MODEL'S PIPELINE VIEW (cut C9c'; design:     *)
(* claude-notes/design/union.md, review amendment B4).  Pure.            *)
(*                                                                        *)
(* [UnionDisc.ulm adm] read at its pipeline lines ([PipesView.pview]):   *)
(* a line [LPipe p fs] is the pipeline [LPipes p fs], its content        *)
(* function at the round's state is [FileDisc.files_of], and a pipeline  *)
(* alternative is coded as the union's [UPE] (an echo pipeline) or      *)
(* [UPC] (a [cat f] one).  Every law holds at EVERY                       *)
(* admission: the cross cases of [UnionDisc.uok] are [False]              *)
(* (amendment B2), so an admitted alternative at a pipeline line is a    *)
(* pipeline one ([pv_onto]).                                              *)
(*                                                                        *)
(* THE ENCODING IS THE MODEL'S, per line ([pv_enc] takes the pipeline):   *)
(* [uv_alt] cases on the line's producer (C9b2's split), and nothing       *)
(* above this file reads the encoding.                                    *)
(* ===================================================================== *)
From Stdlib Require Import Lia List.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel.
Require Import ProgTree ProgTreePipes PipesPair PipesDisc PipesView.
Require Import FileState FileDisc UnionDisc.
Require GrepTree GrepFilt.
From stdpp Require Import list.

Local Open Scope nat_scope.

(* which lines are pipelines *)
Definition uv_line (l : uline) : option pline' :=
  match l with LPipe p fs => Some (LPipes p fs) | _ => None end.

Lemma uv_line_some (l : uline) (pl : pline') :
  uv_line l = Some pl -> exists p fs, l = LPipe p fs /\ pl = LPipes p fs.
Proof using.
  destruct l as [ws | ws | | p fs]; cbn [uv_line]; try discriminate.
  intros Hq. injection Hq as <-. by exists p, fs.
Qed.

(* the union's code of a pipeline alternative: [UPE] at an echo
   pipeline, [UPC] at a [cat f] one (C9b2's split by producer) *)
Definition uv_alt (pl : pline') (a : plalt) : ualt :=
  match pl with LPipes (PrCatF _) _ => UPC a | _ => UPE a end.

Definition uv_enc (pl : pline') (a : plalt) : nat := ualt_code (uv_alt pl a).

Lemma uv_dec (pl : pline') (a : plalt) : ualt_dec (uv_enc pl a) = uv_alt pl a.
Proof using. unfold uv_enc. by rewrite ualt_dec_code. Qed.

Definition pview_union (adm : pline' -> bool) : pview (ulm adm).
Proof.
  refine (@MkPV (ulm adm) uv_line files_of adm uv_enc _ _ _ _ _ _).
  - intros s l pl a Hl. destruct (uv_line_some l pl Hl) as (p & n & -> & ->).
    cbn [ulm lm_ok lm_dec]. rewrite uv_dec. destruct p; reflexivity.
  - intros s l pl a Hl. destruct (uv_line_some l pl Hl) as (p & n & -> & ->).
    cbn [ulm lm_cont lm_dec]. rewrite uv_dec. destruct p; reflexivity.
  - intros pl a. cbn [ulm lm_panic lm_dec]. rewrite uv_dec.
    destruct pl as [ws | [ws | f] n]; reflexivity.
  - intros pl a. cbn [ulm lm_term lm_dec]. rewrite uv_dec.
    destruct pl as [ws | [ws | f] n]; reflexivity.
  - intros s l pl a Hl. destruct (uv_line_some l pl Hl) as (p & n & -> & ->).
    cbn [ulm lm_step lm_dec]. rewrite uv_dec. destruct p; reflexivity.
  - intros s l pl x Hl Hok. destruct (uv_line_some l pl Hl) as (p & n & -> & ->).
    cbn [ulm lm_ok] in Hok.
    destruct x as [r | a | a], p as [ws | f]; cbn [uok] in Hok; try contradiction;
      exists a; cbn [ulm lm_dec]; rewrite uv_dec; reflexivity.
Defined.

(* the round's content at a well-formed state is a word line's *)
Lemma pview_union_fc_ok (adm : pline' -> bool) (s : fstate) :
  fstate_ok s -> fc_ok (pv_fc (pview_union adm) s).
Proof using. exact (files_of_fc_ok s). Qed.

(* THE GATE AT THE UNION's ROUNDS (grep-pipes.md cut G8): the content a
   pipeline's producer puts in its pipe is one line with no NUL in it --
   echo's words are alphanumeric, [f]'s content is word-line bytes
   ([fcont_ok]) -- so every filter stage's gate [fok] holds *)
Lemma body_byte_not_nul (b : bv 8) : wl_body_byte b -> b <> GrepTree.c_nul.
Proof using.
  assert (H0 : bv_unsigned GrepTree.c_nul = 0%Z) by (vm_compute; reflexivity).
  intros Hb ->. destruct Hb as [Ha | Hs].
  - unfold wl_alnum in Ha. rewrite H0 in Ha. lia.
  - apply (f_equal bv_unsigned) in Hs. rewrite H0 in Hs. vm_compute in Hs. discriminate Hs.
Qed.

Lemma prod_content_grep_ok (s : fstate) (p : producer) :
  fstate_ok s -> prod_ok p -> GrepTree.grep_ok (prod_content (files_of s) p).
Proof using.
  assert (H0 : bv_unsigned GrepTree.c_nul = 0%Z) by (vm_compute; reflexivity).
  intros Hs Hp. unfold GrepTree.grep_ok. destruct p as [ws | g]; cbn [prod_content].
  - apply Forall_forall. intros b Hb ->.
    pose proof (wl_line_byte_val (drop 1 ws) GrepTree.c_nul
                  (lb_Forall_drop _ 1 ws (line_ok_wf ws Hp)) Hb) as Hv.
    rewrite H0 in Hv. lia.
  - destruct (files_of s g) as [c |] eqn:Hf; cbn [default]; [| constructor].
    apply files_of_some in Hf. subst s. cbn [fstate_ok] in Hs.
    destruct Hs as [HF | (v & HF & ->)].
    + exact (Forall_impl _ _ _ HF body_byte_not_nul).
    + apply Forall_app. split; [exact (Forall_impl _ _ _ HF body_byte_not_nul) |].
      constructor; [| constructor]. intros Hq.
      apply (f_equal bv_unsigned) in Hq. rewrite H0 in Hq. vm_compute in Hq. discriminate Hq.
Qed.

Lemma pview_union_gate (adm : pline' -> bool) (s : fstate) (p : producer) (fs : list filt) :
  fstate_ok s -> prod_ok p ->
  Forall (fun F => fok F (prod_content (pv_fc (pview_union adm) s) p)) fs.
Proof using.
  intros Hs Hp. apply Forall_forall. intros F _. destruct F as [| w]; [exact I |].
  split.
  - exact (proj2 (prod_content_shape _ p (files_of_fc_ok s Hs) Hp)).
  - exact (prod_content_grep_ok s p Hs Hp).
Qed.

(* the union's view at the union application's admission ([adm_u_g]:
   grep stages admitted, cut G8) *)
Definition pview_unionU : pview ulmG := pview_union adm_u_g.
