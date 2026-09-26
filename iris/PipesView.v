(* ===================================================================== *)
(* PipesView.v -- THE PIPELINE VIEW OF A LINE MODEL (cut C9c'; design:   *)
(* claude-notes/design/union.md, review amendment B4).  Pure.            *)
(*                                                                        *)
(* The N-stage layer (the open round's claim, the N-writer family, the    *)
(* stage and node laws) reads a line model at ITS PIPELINE LINES only:    *)
(* which line a round is, which of the model's alternatives are the       *)
(* pipeline's [PipesDisc.plalt]s, what [cat f] reads at the round's        *)
(* state.  [pview M] is exactly that reading, with the laws the layer      *)
(* uses, so the layer is stated over ANY model with a view:               *)
(*                                                                        *)
(*   [pv_line]   which lines are pipelines, and which pipeline;          *)
(*   [pv_fc]     the content function at a state ([fun _ => None] at the *)
(*               pipeline application, [FileDisc.files_of] at the union);*)
(*   [pv_adm]    the pipeline shapes the model admits;                    *)
(*   [pv_enc]    the model's code of a pipeline alternative AT A LINE --   *)
(*               the line, so a model may encode the alternatives of      *)
(*               different producers differently;                        *)
(*   the laws    at a pipeline line the model's range condition IS the    *)
(*               pipeline's at the content ([pv_ok]), its continuation    *)
(*               [plcont] ([pv_cont]), its panic and coverage flags the   *)
(*               pipeline's ([pv_panic] / [pv_term]), and a pipeline      *)
(*               round leaves the state alone ([pv_step]).  An admitted   *)
(*               alternative there need not be a pipeline one: the union  *)
(*               admits the shell's out-of-memory death at every line.    *)
(*                                                                        *)
(* The pipeline application's model is its own view: [pview_pipes] at     *)
(* [PipesDisc.pipes_lm fc adm] (every field by conversion).  The union's   *)
(* is [UnionView.pview_union].                                            *)
(* ===================================================================== *)
From Stdlib Require Import Lia List.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel.
Require Import ProgTree ProgTreePipes PipesPair PipesDisc.
From stdpp Require Import list.

Local Open Scope nat_scope.

Record pview (M : lmodel) := MkPV {
  pv_line : lm_line M -> option pline';
  pv_fc : lm_st M -> bytes -> option bytes;
  pv_adm : pline' -> bool;
  pv_enc : pline' -> plalt -> nat;
  pv_ok : forall s l pl a, pv_line l = Some pl ->
    lm_ok M s l (lm_dec M (pv_enc pl a))
    <-> plsafe pl a \/ (pv_adm pl = true /\ plalt_ok (pv_fc s) pl a);
  pv_cont : forall s l pl a, pv_line l = Some pl ->
    lm_cont M s l (lm_dec M (pv_enc pl a)) = plcont a;
  pv_panic : forall pl a, lm_panic M (lm_dec M (pv_enc pl a)) = plpanic a;
  pv_term : forall pl a, lm_term M (lm_dec M (pv_enc pl a)) = plterm a;
  pv_step : forall s l pl a, pv_line l = Some pl ->
    lm_step M s l (lm_dec M (pv_enc pl a)) = s;
}.
Global Arguments MkPV {M}.
Global Arguments pv_line {M} _ _.
Global Arguments pv_fc {M} _ _ _.
Global Arguments pv_adm {M} _ _.
Global Arguments pv_enc {M} _ _ _.
Global Arguments pv_ok {M} _ _ _ _ _ _.
Global Arguments pv_cont {M} _ _ _ _ _ _.
Global Arguments pv_panic {M} _ _ _.
Global Arguments pv_term {M} _ _ _.
Global Arguments pv_step {M} _ _ _ _ _ _.

Section view.
  Context {M : lmodel} (V : pview M).

  (* an admitted run of the line is an admitted alternative of the model *)
  Lemma pv_ok_intro (s : lm_st M) (l : lm_line M) (pl : pline') (a : plalt) :
    pv_line V l = Some pl -> pv_adm V pl = true -> plalt_ok (pv_fc V s) pl a ->
    lm_ok M s l (lm_dec M (pv_enc V pl a)).
  Proof using. intros Hl Ha Hok. apply (proj2 (pv_ok V s l pl a Hl)). right. by split. Qed.

  (* the shell's own three at every pipeline line *)
  Lemma pv_ok_safe (s : lm_st M) (l : lm_line M) (pl : pline') (a : plalt) :
    pv_line V l = Some pl -> plsafe pl a -> lm_ok M s l (lm_dec M (pv_enc V pl a)).
  Proof using. intros Hl Hs. apply (proj2 (pv_ok V s l pl a Hl)). by left. Qed.

  (* the round ran and printed [b] *)
  Lemma pv_run_ok (s : lm_st M) (l : lm_line M) (pl : pline') (b : bytes) :
    pv_line V l = Some pl -> pv_adm V pl = true -> line_blocks (pv_fc V s) pl b ->
    lm_ok M s l (lm_dec M (pv_enc V pl (PLRun b))).
  Proof using. intros Hl Ha Hb. exact (pv_ok_intro s l pl (PLRun b) Hl Ha Hb). Qed.

  Lemma pv_run_cont (s : lm_st M) (l : lm_line M) (pl : pline') (b : bytes) :
    pv_line V l = Some pl -> lm_cont M s l (lm_dec M (pv_enc V pl (PLRun b))) = b ++ u_prompt.
  Proof using. intros Hl. exact (pv_cont V s l pl (PLRun b) Hl). Qed.

  Lemma pv_run_panic (pl : pline') (b : bytes) :
    lm_panic M (lm_dec M (pv_enc V pl (PLRun b))) = false.
  Proof using. exact (pv_panic V pl (PLRun b)). Qed.

  Lemma pv_run_term (pl : pline') (b : bytes) :
    lm_term M (lm_dec M (pv_enc V pl (PLRun b))) = false.
  Proof using. exact (pv_term V pl (PLRun b)). Qed.

  (* a terminal block of the line is a coverage-ending alternative *)
  Lemma pv_term_ok (s : lm_st M) (l : lm_line M) (pl : pline') (b : bytes) :
    pv_line V l = Some pl -> pv_adm V pl = true -> plalt_ok (pv_fc V s) pl (PLTerm b) ->
    lm_ok M s l (lm_dec M (pv_enc V pl (PLTerm b)))
    /\ lm_term M (lm_dec M (pv_enc V pl (PLTerm b))) = true
    /\ lm_panic M (lm_dec M (pv_enc V pl (PLTerm b))) = false
    /\ lm_cont M s l (lm_dec M (pv_enc V pl (PLTerm b))) = b.
  Proof using.
    intros Hl Ha Hok. split_and!.
    - exact (pv_ok_intro s l pl (PLTerm b) Hl Ha Hok).
    - exact (pv_term V pl (PLTerm b)).
    - exact (pv_panic V pl (PLTerm b)).
    - exact (pv_cont V s l pl (PLTerm b) Hl).
  Qed.
End view.

(* ===================================================================== *)
(*  THE PIPELINE APPLICATION'S OWN VIEW: every line a pipeline line, the  *)
(*  content constant, the code [plalt_code] -- each law by conversion     *)
(* ===================================================================== *)

Definition pview_pipes (fc : bytes -> option bytes) (adm : pline' -> bool)
    : pview (pipes_lm fc adm).
Proof.
  refine (@MkPV (pipes_lm fc adm) (fun l : pline' => Some l) (fun _ => fc) adm
            (fun _ a => plalt_code a) _ _ _ _ _).
  - intros s l pl a Hl. injection Hl as <-. cbn [pipes_lm lm_ok lm_dec].
    rewrite plalt_of_code. reflexivity.
  - intros s l pl a Hl. cbn [pipes_lm lm_cont lm_dec]. by rewrite plalt_of_code.
  - intros pl a. cbn [pipes_lm lm_panic lm_dec]. by rewrite plalt_of_code.
  - intros pl a. cbn [pipes_lm lm_term lm_dec]. by rewrite plalt_of_code.
  - intros s l pl a Hl. by destruct s.
Defined.

(* the view's reading at the application, by conversion *)
Lemma pview_pipes_line fc adm l : pv_line (pview_pipes fc adm) l = Some l.
Proof using. reflexivity. Qed.
Lemma pview_pipes_fc fc adm s : pv_fc (pview_pipes fc adm) s = fc.
Proof using. reflexivity. Qed.
Lemma pview_pipes_adm fc adm : pv_adm (pview_pipes fc adm) = adm.
Proof using. reflexivity. Qed.
Lemma pview_pipes_enc fc adm pl a : pv_enc (pview_pipes fc adm) pl a = plalt_code a.
Proof using. reflexivity. Qed.
