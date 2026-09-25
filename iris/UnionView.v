(* ===================================================================== *)
(* UnionView.v -- THE UNION MODEL'S PIPELINE VIEW (cut C9c'; design:     *)
(* claude-notes/design/union.md, review amendment B4).  Pure.            *)
(*                                                                        *)
(* [UnionDisc.ulm adm] read at its pipeline lines ([PipesView.pview]):   *)
(* a line [LPipe p n] is the pipeline [LPipes p n], its content function  *)
(* at the round's state is [FileDisc.files_of], and a pipeline            *)
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
From stdpp Require Import list.

Local Open Scope nat_scope.

(* which lines are pipelines *)
Definition uv_line (l : uline) : option pline' :=
  match l with LPipe p n => Some (LPipes p n) | _ => None end.

Lemma uv_line_some (l : uline) (pl : pline') :
  uv_line l = Some pl -> exists p n, l = LPipe p n /\ pl = LPipes p n.
Proof using.
  destruct l as [ws | ws | | p n]; cbn [uv_line]; try discriminate.
  intros Hq. injection Hq as <-. by exists p, n.
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

(* the union's view at the union application's admission *)
Definition pview_unionU : pview ulmU := pview_union adm_u_f.
