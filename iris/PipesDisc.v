(* ===================================================================== *)
(* PipesDisc.v -- THE PER-STAGE OUTCOME MODEL of a pipeline of any        *)
(* length (design: claude-notes/design/pipes-general.md SS3.2, SS2.3,     *)
(* SS2.4, cut C2).  Pure; nothing in the application imports it yet.      *)
(*                                                                        *)
(*   1. The lines: [LEcho' ws] and [LPipes p fs], the producer [p]     *)
(*      (echo or [cat f]) followed by its filter stages [fs] (at least    *)
(*      one; each [cat] or [grep w], cut G3); their bodies and the parser *)
(*      that splits them at the bars.                                     *)
(*   2. The STAGE OUTCOMES [stage_out]: one constructor per behaviour a   *)
(*      stage has (exec failure, the argv[0] death, echo, echo halted,    *)
(*      cat f copied / halted / refused its open, a middle filter wrote   *)
(*      what it owes ([fapp]), a middle cat or grep halted, the last      *)
(*      filter printed what it owes), each read as a console stream, an   *)
(*      optional reader outcome and an optional writer outcome            *)
(*      ([PipesPair.rd_out]/[wr_out], adopted as they are).              *)
(*   3. The PAIRING through a pipe, [pipe_pairB], with the ruled corner   *)
(*      (B): a halted CAT writer beside a reader that saw end of file     *)
(*      after any prefix of the line.  It agrees with                     *)
(*      [PipesPair.pipe_pair] everywhere else.                            *)
(*   4. The runs: [sfx_run] (the suffix of cats below a pipe), [line_run] *)
(*      and [merge_all]; the round's blocks [line_blocks]; the terminal   *)
(*      runs (a fork failure at some node) and [line_term_blocks].        *)
(*   5. The alternatives [plalt] with an injective [nat] code, and the    *)
(*      line model [pipes_lm] with its laws.                              *)
(*   6. The bridges from the trees' exit lemmas of [ProgTreePipes] to the *)
(*      stage outcomes (the outcomes are DERIVED from the trees).         *)
(*   7. The n = 1 bridge to the landed one-pipe model [PipeDisc].         *)
(*                                                                        *)
(*  THE CONTENT OF [cat f].  The pipeline application's state is [unit], *)
(*  so this model takes a CONTENT FUNCTION [fc] as a parameter and its    *)
(*  [lm_ok] ignores the round's state; a union with the file application *)
(*  reads the content off the state the record's [lm_ok] is given.        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import StringBytes ProgTree ProgTreePipes PipesPair.
Require GrepTree GrepFilt.       (* the filter a grep stage applies (cut G3) *)
Require FileDisc.                (* [producer], moved down (cut C9b) *)
(* stdpp's list lemmas over the ones [ProgTree]'s Stdlib import re-exports *)
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE LINES                                                         *)
(* ===================================================================== *)

(* THE PRODUCER -- the first command of a pipeline, [echo w1 .. wk] (the
   words [ws], command name included) or [cat f] -- lives in [FileDisc]
   (cut C9b: the shell loop's line type names it); these are its names
   here, so every reader of this file sees them unchanged *)
Notation cmd_cat := FileDisc.fd_w_cat.
Notation producer := FileDisc.producer.
Notation PrEcho := FileDisc.PrEcho.
Notation PrCatF := FileDisc.PrCatF.
Notation prod_words := FileDisc.prod_words.
Notation prod_body := FileDisc.prod_body.
Notation prod_ok := FileDisc.prod_ok.
Notation cmd_cat_word := FileDisc.fd_w_cat_word.
Notation prod_wf := FileDisc.prod_wf.
Notation prod_body_bytes := FileDisc.prod_body_bytes.

(* THE FILTER STAGES (cut G3) -- every stage after the producer is [cat]
   or [grep w] -- live in [FileDisc] beside the producer; these are their
   names here *)
Notation filt := FileDisc.filt.
Notation FCat := FileDisc.FCat.
Notation FGrep := FileDisc.FGrep.
Notation filt_words := FileDisc.filt_words.
Notation filt_ok := FileDisc.filt_ok.
Notation filt_is_cat := FileDisc.filt_is_cat.
Notation cats := FileDisc.cats.
Notation all_cats := FileDisc.all_cats.

(* a line: a plain echo line, or the producer followed by its filter
   stages [fs] *)
Inductive pline' :=
  | LEcho' (ws : list bytes)
  | LPipes (p : producer) (fs : list filt).

Global Instance pline'_eq_dec : EqDecision pline'.
Proof using. solve_decision. Defined.

(* the canonical separator [ | ], and one filter stage's own body *)
Definition pl_sep : bytes := [wl_sp; wl_bar; wl_sp].
Definition filt_body (F : filt) : bytes := wl_body (filt_words F).

Lemma suf_filt_sep (F : filt) : FileDisc.suf_filt F = pl_sep ++ filt_body F.
Proof using. reflexivity. Qed.

Definition pl_body (l : pline') : bytes :=
  match l with
  | LEcho' ws => wl_body ws
  | LPipes p fs => prod_body p ++ FileDisc.suf_filts fs
  end.

(* a well-formed line: an admissible echo line, or a producer with at
   least one admissible filter stage, the whole line within sh's buffer *)
Definition pl_ok (l : pline') : Prop :=
  match l with
  | LEcho' ws => line_ok ws
  | LPipes p fs =>
      prod_ok p /\ fs <> [] /\ Forall filt_ok fs /\ S (length (pl_body l)) < line_max
  end.

Global Instance pl_ok_dec l : Decision (pl_ok l).
Proof using. destruct l; unfold pl_ok; apply _. Defined.

(* ---- THE PARSER: split the body at every [ | ], read the first segment
        as the producer and every later one as a filter stage.  The bar is
        never a word byte, so the split is the line's own. *)

Definition hd_cons (x : bv 8) (ss : list bytes) : list bytes :=
  match ss with [] => [[x]] | s :: ss' => (x :: s) :: ss' end.

Fixpoint split_sep (b : bytes) : list bytes :=
  match b with
  | [] => [[]]
  | x :: t =>
      match t with
      | y :: z :: r =>
          if decide ([x; y; z] = pl_sep) then [] :: split_sep r else hd_cons x (split_sep t)
      | _ => hd_cons x (split_sep t)
      end
  end.

Definition join_sep (ss : list bytes) : bytes :=
  match ss with [] => [] | s :: ss' => s ++ concat (map (fun t => pl_sep ++ t) ss') end.

Lemma split_sep_cons3 x y z r :
  split_sep (x :: y :: z :: r)
  = if decide ([x; y; z] = pl_sep) then [] :: split_sep r else hd_cons x (split_sep (y :: z :: r)).
Proof using. reflexivity. Qed.

Lemma hd_cons_ne x ss : hd_cons x ss <> [].
Proof using. destruct ss; discriminate. Qed.

Lemma split_sep_ne b : split_sep b <> [].
Proof using.
  destruct b as [| x [| y [| z r]]]; [discriminate | intros H; discriminate H
                                     | intros H; discriminate H |].
  rewrite split_sep_cons3. case_decide; [discriminate | apply hd_cons_ne].
Qed.

Lemma wl_sp_ne_bar : wl_sp <> wl_bar.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* a byte in front of a list that does not start on the bar starts the
   first segment *)
Lemma split_sep_nb x u : head u <> Some wl_bar -> split_sep (x :: u) = hd_cons x (split_sep u).
Proof using.
  intros Hh. destruct u as [| y [| z r]]; [reflexivity | reflexivity |].
  rewrite split_sep_cons3, decide_False; [reflexivity |].
  intros Heq. unfold pl_sep in Heq. injection Heq as _ Hy _. apply Hh. rewrite Hy. reflexivity.
Qed.

Lemma split_sep_nosep (s : bytes) : wl_bar ∉ s -> split_sep s = [s].
Proof using.
  induction s as [| x t IH]; intros Hs; [reflexivity |].
  assert (Ht : wl_bar ∉ t) by (intros H; apply Hs; apply elem_of_list_further; exact H).
  assert (Hh : head t <> Some wl_bar).
  { destruct t as [| y t']; cbn [head]; [discriminate |].
    intros Hy. injection Hy as ->. apply Ht. apply elem_of_list_here. }
  rewrite (split_sep_nb x t Hh), (IH Ht). reflexivity.
Qed.

Lemma split_sep_app (s t : bytes) : wl_bar ∉ s -> split_sep (s ++ pl_sep ++ t) = s :: split_sep t.
Proof using.
  induction s as [| x s' IH]; intros Hs.
  - cbn [app]. unfold pl_sep. cbn [app].
    rewrite split_sep_cons3. rewrite decide_True by reflexivity. reflexivity.
  - assert (Hs' : wl_bar ∉ s') by (intros H; apply Hs; apply elem_of_list_further; exact H).
    assert (Hh : head (s' ++ pl_sep ++ t) <> Some wl_bar).
    { destruct s' as [| y s'']; cbn [head app].
      - unfold pl_sep. cbn [app head]. intros Hy. exact (wl_sp_ne_bar (f_equal (default wl_sp) Hy)).
      - intros Hy. injection Hy as ->. apply Hs'. apply elem_of_list_here. }
    cbn [app]. rewrite (split_sep_nb x _ Hh), (IH Hs'). reflexivity.
Qed.

Lemma join_sep_cons2 s s' ss : join_sep (s :: s' :: ss) = s ++ pl_sep ++ join_sep (s' :: ss).
Proof using. cbn [join_sep map concat]. rewrite <- !app_assoc. reflexivity. Qed.

Lemma join_hd_cons x ss : ss <> [] -> join_sep (hd_cons x ss) = x :: join_sep ss.
Proof using.
  destruct ss as [| s ss]; [intros H; exfalso; exact (H eq_refl) | intros _; reflexivity].
Qed.

Lemma join_nil_cons ss : ss <> [] -> join_sep ([] :: ss) = pl_sep ++ join_sep ss.
Proof using.
  destruct ss as [| s ss]; [intros H; exfalso; exact (H eq_refl) |]. intros _.
  cbn [join_sep map concat app].
  rewrite <- app_assoc. reflexivity.
Qed.

(* the split loses nothing *)
Lemma split_sep_join_aux k b : length b <= k -> join_sep (split_sep b) = b.
Proof using.
  revert b. induction k as [| k IH]; intros b Hk.
  - destruct b; [reflexivity | cbn in Hk; lia].
  - destruct b as [| x [| y [| z r]]]; [reflexivity | reflexivity | reflexivity |].
    rewrite split_sep_cons3. case_decide as Hs.
    + rewrite join_nil_cons by apply split_sep_ne. rewrite (IH r) by (cbn in Hk; lia).
      rewrite <- Hs. reflexivity.
    + rewrite join_hd_cons by apply split_sep_ne.
      rewrite (IH (y :: z :: r)) by (cbn in Hk |- *; lia). reflexivity.
Qed.

Lemma split_sep_join b : join_sep (split_sep b) = b.
Proof using. exact (split_sep_join_aux (length b) b (le_n _)). Qed.

(* ...and a join of bar-free segments splits back into them *)
Lemma split_sep_join_nb (s : bytes) (ss : list bytes) :
  wl_bar ∉ s -> Forall (fun t => wl_bar ∉ t) ss -> split_sep (join_sep (s :: ss)) = s :: ss.
Proof using.
  revert s. induction ss as [| s' ss IH]; intros s Hs HF.
  - cbn [join_sep map concat]. rewrite app_nil_r. exact (split_sep_nosep s Hs).
  - apply Forall_cons_1 in HF as [Hs' HF].
    rewrite join_sep_cons2, (split_sep_app s _ Hs), (IH s' Hs' HF). reflexivity.
Qed.

Definition filt_parse (s : bytes) : option filt :=
  if decide (s = cmd_cat) then Some FCat
  else match wl_words s with
       | [g; w] =>
           if decide (g = FileDisc.fd_w_grep /\ wl_word w /\ wl_body [g; w] = s)
           then Some (FGrep w) else None
       | _ => None
       end.

Fixpoint filts_parse (segs : list bytes) : option (list filt) :=
  match segs with
  | [] => Some []
  | s :: segs' =>
      match filt_parse s, filts_parse segs' with
      | Some F, Some fs => Some (F :: fs)
      | _, _ => None
      end
  end.

Definition prod_parse (r : bytes) : option producer :=
  if decide (body_ok r) then Some (PrEcho (wl_words r))
  else match wl_words r with
       | [c; f] =>
           if decide (c = cmd_cat /\ fn_word f /\ wl_body [c; f] = r)
           then Some (PrCatF f) else None
       | _ => None
       end.

Definition pl_parse (b : bytes) : option pline' :=
  match split_sep b with
  | [r] => if decide (body_ok r) then Some (LEcho' (wl_words r)) else None
  | r :: segs =>
      if decide (S (length b) < line_max)
      then match prod_parse r, filts_parse segs with
           | Some p, Some fs => Some (LPipes p fs)
           | _, _ => None
           end
      else None
  | [] => None
  end.

Definition pl_of (b : bytes) : pline' := default (LEcho' []) (pl_parse b).

Lemma cmd_cat_ne_echo : cmd_cat <> cmd_echo.
Proof using. intros H. apply (f_equal (@length _)) in H. vm_compute in H. discriminate H. Qed.

Lemma cat_not_echo_ok (f : bytes) : fn_word f -> ~ body_ok (wl_body [cmd_cat; f]).
Proof using.
  intros Hf [_ Hok].
  rewrite (wl_words_body_fn [cmd_cat; f] (prod_wf (PrCatF f) Hf)) in Hok.
  apply line_ok_head in Hok. change (Some cmd_cat = Some cmd_echo) in Hok.
  exact (cmd_cat_ne_echo (inj Some _ _ Hok)).
Qed.

Lemma prod_parse_body (p : producer) : prod_ok p -> prod_parse (prod_body p) = Some p.
Proof using.
  intros Hp. pose proof (prod_wf p Hp) as Hwf. unfold prod_parse, prod_body.
  destruct p as [ws | f]; cbn [prod_words prod_ok] in *.
  - rewrite decide_True; [by rewrite (wl_words_body_fn ws Hwf) |].
    unfold body_ok. rewrite (wl_words_body_fn ws Hwf). split; [reflexivity | exact Hp].
  - rewrite decide_False; [| exact (cat_not_echo_ok f Hp)].
    rewrite (wl_words_body_fn _ Hwf). rewrite decide_True; [reflexivity |].
    split; [reflexivity | split; [exact Hp | reflexivity]].
Qed.

Lemma prod_parse_some r p : prod_parse r = Some p -> prod_ok p /\ r = prod_body p.
Proof using.
  unfold prod_parse. destruct (decide (body_ok r)) as [Hb | Hb].
  - intros [= <-]. destruct Hb as [Hbody Hok]. split; [exact Hok |].
    unfold prod_body. cbn [prod_words]. symmetry. exact Hbody.
  - destruct (wl_words r) as [| c [| f [| x rest]]]; try discriminate.
    case_decide as H; [| discriminate]. intros [= <-]. destruct H as (-> & Hf & Hr).
    split; [exact Hf |]. unfold prod_body. cbn [prod_words]. symmetry. exact Hr.
Qed.

Lemma filt_parse_body (F : filt) : filt_ok F -> filt_parse (filt_body F) = Some F.
Proof using.
  intros HF. unfold filt_parse. destruct F as [| w].
  - rewrite decide_True; reflexivity.
  - rewrite decide_False.
    + change (filt_body (FGrep w)) with (wl_body (filt_words (FGrep w))).
      rewrite (wl_words_body _ (FileDisc.filt_wf _ HF)). cbn [filt_words].
      rewrite decide_True; [reflexivity |].
      split; [reflexivity | split; [exact HF | reflexivity]].
    + intros H. apply (f_equal wl_words) in H.
      change (filt_body (FGrep w)) with (wl_body (filt_words (FGrep w))) in H.
      rewrite (wl_words_body _ (FileDisc.filt_wf _ HF)) in H.
      change (wl_words cmd_cat) with [cmd_cat] in H. discriminate H.
Qed.

Lemma filt_parse_some s F : filt_parse s = Some F -> filt_ok F /\ s = filt_body F.
Proof using.
  unfold filt_parse. case_decide as Hc.
  - intros [= <-]. split; [exact I | exact Hc].
  - destruct (wl_words s) as [| g [| w [| x rest]]]; try discriminate.
    case_decide as H; [| discriminate]. intros [= <-]. destruct H as (-> & Hw & Hs).
    split; [exact Hw | symmetry; exact Hs].
Qed.

Lemma filts_parse_body (fs : list filt) :
  Forall filt_ok fs -> filts_parse (map filt_body fs) = Some fs.
Proof using.
  induction fs as [| F fs IH]; intros HF; [reflexivity |].
  apply Forall_cons_1 in HF as [HF1 HF]. cbn [map filts_parse].
  rewrite (filt_parse_body F HF1), (IH HF). reflexivity.
Qed.

Lemma filts_parse_some segs fs :
  filts_parse segs = Some fs -> Forall filt_ok fs /\ segs = map filt_body fs.
Proof using.
  revert fs. induction segs as [| s segs IH]; intros fs; cbn [filts_parse].
  - intros [= <-]. split; [constructor | reflexivity].
  - destruct (filt_parse s) as [F |] eqn:Hs; [| discriminate].
    destruct (filts_parse segs) as [fs' |] eqn:Hr; [| discriminate].
    intros [= <-]. destruct (filt_parse_some s F Hs) as [HF ->].
    destruct (IH fs' eq_refl) as [HF' ->]. split; [constructor; assumption | reflexivity].
Qed.

(* the bar is in no producer and no filter stage *)
Lemma prod_body_nobar p : prod_ok p -> wl_bar ∉ prod_body p.
Proof using.
  intros Hp Hin.
  destruct (proj1 (Forall_forall _ _) (prod_body_bytes p Hp) _ Hin) as [Hb | Hb].
  - apply fn_byte_val in Hb.
    assert (Hbar : bv_unsigned wl_bar = 124%Z) by (vm_compute; reflexivity). lia.
  - exact (wl_bar_not_body (or_intror Hb)).
Qed.

Lemma filt_body_nobar F : filt_ok F -> wl_bar ∉ filt_body F.
Proof using.
  intros HF Hin.
  exact (wl_bar_not_body
           (proj1 (Forall_forall _ _) (wl_body_bytes _ (FileDisc.filt_wf F HF)) _ Hin)).
Qed.

Lemma suf_filts_join (fs : list filt) :
  FileDisc.suf_filts fs = concat (map (fun t => pl_sep ++ t) (map filt_body fs)).
Proof using. unfold FileDisc.suf_filts. rewrite map_map. reflexivity. Qed.

Lemma pl_body_join (p : producer) (fs : list filt) :
  pl_body (LPipes p fs) = join_sep (prod_body p :: map filt_body fs).
Proof using. cbn [pl_body join_sep]. rewrite suf_filts_join. reflexivity. Qed.

Lemma split_sep_pl (p : producer) (fs : list filt) :
  prod_ok p -> Forall filt_ok fs ->
  split_sep (pl_body (LPipes p fs)) = prod_body p :: map filt_body fs.
Proof using.
  intros Hp HF. rewrite pl_body_join. apply split_sep_join_nb; [exact (prod_body_nobar p Hp) |].
  apply Forall_forall. intros t Ht. apply elem_of_list_fmap in Ht as (F & -> & HFin).
  exact (filt_body_nobar F (proj1 (Forall_forall _ _) HF F HFin)).
Qed.

(* the parser inverts the body at every well-formed line *)
Lemma pl_parse_body (l : pline') : pl_ok l -> pl_parse (pl_body l) = Some l.
Proof using.
  destruct l as [ws | p fs]; intros Hok.
  - unfold pl_parse. cbn [pl_body].
    rewrite (split_sep_nosep (wl_body ws) (fun H => wl_bar_not_body
               (proj1 (Forall_forall _ _) (wl_body_bytes ws (line_ok_wf ws Hok)) _ H))).
    cbv beta iota.
    rewrite decide_True; [by rewrite (wl_words_body ws (line_ok_wf ws Hok)) |].
    unfold body_ok. rewrite (wl_words_body ws (line_ok_wf ws Hok)).
    split; [reflexivity | exact Hok].
  - destruct Hok as (Hp & Hne & HF & Hlen). unfold pl_parse.
    rewrite (split_sep_pl p fs Hp HF).
    destruct fs as [| F fs']; [exfalso; exact (Hne eq_refl) |]. cbn [map].
    rewrite decide_True by exact Hlen.
    rewrite (prod_parse_body p Hp).
    change (filt_body F :: map filt_body fs') with (map filt_body (F :: fs')).
    rewrite (filts_parse_body _ HF). reflexivity.
Qed.

(* ...and answers only well-formed lines, whose body is what was parsed *)
Lemma pl_parse_some b l : pl_parse b = Some l -> pl_ok l /\ b = pl_body l.
Proof using.
  pose proof (split_sep_join b) as Hj. revert Hj. unfold pl_parse.
  destruct (split_sep b) as [| r [| s segs]]; intros Hj; [discriminate | |].
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody Hok]. split; [exact Hok |].
    cbn [join_sep map concat] in Hj. rewrite app_nil_r in Hj. subst b.
    cbn [pl_body]. symmetry. exact Hbody.
  - case_decide as Hlen; [| discriminate].
    destruct (prod_parse r) as [p |] eqn:Hp; [| discriminate].
    destruct (filts_parse (s :: segs)) as [fs |] eqn:Hf; [| discriminate].
    intros [= <-].
    destruct (prod_parse_some r p Hp) as [Hpok ->].
    destruct (filts_parse_some _ _ Hf) as [HF Hseg].
    assert (Hb : b = pl_body (LPipes p fs)).
    { rewrite pl_body_join, <- Hseg. symmetry. exact Hj. }
    split; [| exact Hb].
    split; [exact Hpok |]. split; [intros ->; discriminate Hseg |].
    split; [exact HF |]. rewrite <- Hb. exact Hlen.
Qed.

Lemma pl_of_body (l : pline') : pl_ok l -> pl_of (pl_body l) = l.
Proof using. intros H. unfold pl_of. rewrite (pl_parse_body l H). reflexivity. Qed.

(* THE INPUT DISCIPLINE's reading of a body, at an ADMISSION predicate on
   lines ([adm]): the application says which line shapes it admits *)
Definition pl_body_ok (adm : pline' -> bool) (b : bytes) : Prop :=
  match pl_parse b with Some l => adm l = true | None => False end.

Global Instance pl_body_ok_dec adm b : Decision (pl_body_ok adm b).
Proof using. unfold pl_body_ok. destruct (pl_parse b); apply _. Defined.

Lemma pl_body_ok_line adm b :
  pl_body_ok adm b -> adm (pl_of b) = true /\ pl_ok (pl_of b) /\ b = pl_body (pl_of b).
Proof using.
  unfold pl_body_ok, pl_of. destruct (pl_parse b) as [l |] eqn:Hp; [| intros []].
  intros Ha. cbn [default]. destruct (pl_parse_some b l Hp) as [Hok Hb].
  split; [exact Ha | split; [exact Hok | exact Hb]].
Qed.

Lemma pl_body_ok_of adm l : adm l = true -> pl_ok l -> pl_body_ok adm (pl_body l).
Proof using. intros Ha Hok. unfold pl_body_ok. rewrite (pl_parse_body l Hok). exact Ha. Qed.

(* ===================================================================== *)
(*  2.  THE STAGE OUTCOMES                                                *)
(*                                                                        *)
(*  A stage is the producer (stage 0), a middle cat (between two pipes)   *)
(*  or the last cat (at the console).  What one did is recorded as        *)
(*  [st_out]: the bytes it wrote to the CONSOLE (its fd 2, and for the    *)
(*  last cat its fd 1), what its READER end saw (a producer has none),    *)
(*  and what its WRITER end did (the last cat has none).                  *)
(* ===================================================================== *)

Record st_out := MkSO {
  so_cons : bytes;
  so_rd : option rd_out;
  so_wr : option wr_out;
}.

Inductive stage :=
  | SProd (p : producer)
  | SMid (F : filt)
  | SLast (F : filt).

Definition rd_of (so : st_out) : rd_out :=
  match so_rd so with Some r => r | None => RdGone end.
Definition wr_of (so : st_out) : wr_out :=
  match so_wr so with Some w => w | None => WrNone end.

(* a stage that never ran its program: no reader it vouches for, no write *)
Definition st_rd_dead (st : stage) : option rd_out :=
  match st with SProd _ => None | _ => Some RdGone end.
Definition st_wr_dead (st : stage) : option wr_out :=
  match st with SLast _ => None | _ => Some WrNone end.

(* sh's [fprintf(2, exec %s failed, argv[0])] (user/sh.c:80): argv[0] is
   [echo] at an echo producer, [grep] at a grep stage and [cat]
   everywhere else *)
Definition dg_exec_grep : list bytes := [sb "exec"%string; sb "grep"%string; sb "failed"%string].
Definition dg_execG : bytes := wl_line dg_exec_grep.

Definition filt_dg_exec (F : filt) : bytes :=
  match F with FCat => dg_execR | FGrep _ => dg_execG end.

Definition st_dg_exec (st : stage) : bytes :=
  match st with
  | SProd (PrEcho _) => dg_execL
  | SProd (PrCatF _) => dg_execR
  | SMid F | SLast F => filt_dg_exec F
  end.

(* WHAT A FILTER STAGE OWES for the input [D] it read: a cat copies it, a
   grep prints the matching complete lines ([GrepTree.grep_out]) *)
Definition fapp (F : filt) (D : bytes) : bytes :=
  match F with FCat => D | FGrep w => GrepTree.grep_out w D end.

(* on a content of one line (the union's every content) a filter passes
   the line or nothing, so what it owes of a prefix is a prefix
   ([GrepFilt.grep_out_line_prefix], the gate) *)
Lemma fapp_prefix (F : filt) (L D : bytes) :
  GrepFilt.oneline L -> D `prefix_of` L -> fapp F D `prefix_of` L.
Proof using.
  intros HL HD. destruct F as [| w]; [exact HD | exact (GrepFilt.grep_out_line_prefix w L D HL HD)].
Qed.

(* THE FILTER DEVICE A STAGE RUNS ([ProgTree.pfilter]): cat's identity, or
   grep's (cut G5) -- what it owes is [fapp] *)
Definition filt_pf (F : filt) : pfilter :=
  match F with FCat => flt_id | FGrep w => GrepFilt.flt_grep w end.

Lemma filt_pf_out (F : filt) (D : bytes) : flt_out (filt_pf F) D = fapp F D.
Proof using. destruct F; reflexivity. Qed.

Lemma fapp_nil (F : filt) : fapp F [] = [].
Proof using. destruct F as [| w]; [reflexivity | exact (GrepFilt.grep_out_nil w)]. Qed.

(* a chunk read adds exactly the device's [flt_new] *)
Lemma fapp_app (F : filt) (R c : bytes) : fapp F (R ++ c) = fapp F R ++ flt_new (filt_pf F) R c.
Proof using. rewrite <- !filt_pf_out. apply flt_app. Qed.

(* a filter that owes a byte of a prefix of a one-line content passed it
   whole: what it owes is what it read, and it passes the line *)
Lemma fapp_pass (F : filt) (L D : bytes) :
  GrepFilt.oneline L -> D `prefix_of` L -> fapp F D <> [] -> fapp F D = D /\ fapp F L = L.
Proof using.
  intros HF HD Hne. destruct F as [| w]; [split; reflexivity |]. cbn [fapp] in *.
  destruct (GrepFilt.grep_out_line w L D HF HD) as [Hq | [-> Hq]]; [by destruct (Hne Hq) |].
  split; exact Hq.
Qed.

(* THE GATE A FILTER NEEDS OF THE LINE: nothing for cat; for grep one line
   (the union's every content is one, [lshape]) with no NUL in it (what
   grep's conformance asks, [GrepFilt.grep_filter_conforms]) *)
Definition fok (F : filt) (L : bytes) : Prop :=
  match F with FCat => True | FGrep _ => GrepFilt.oneline L /\ GrepTree.grep_ok L end.

Lemma fok_prefix (F : filt) (L D : bytes) :
  fok F L -> D `prefix_of` L -> fapp F D `prefix_of` L.
Proof using. intros HF HD. destruct F as [| w]; [exact HD | exact (fapp_prefix (FGrep w) L D (proj1 HF) HD)]. Qed.

(* ...and a filter that owes a byte of a prefix of the line passed it
   whole: what it owes is what it read, and it passes the line *)
Lemma fok_pass (F : filt) (L D : bytes) :
  fok F L -> D `prefix_of` L -> fapp F D <> [] -> fapp F D = D /\ fapp F L = L.
Proof using.
  intros HF HD Hne. destruct F as [| w]; [split; reflexivity |].
  exact (fapp_pass (FGrep w) L D (proj1 HF) HD Hne).
Qed.

(* the gate at a grep stage: the line's shape and its bytes *)
Lemma fok_grep (w L : bytes) : fok (FGrep w) L <-> GrepFilt.oneline L /\ GrepTree.grep_ok L.
Proof using. reflexivity. Qed.

(* EVERY FILTER OF THE LINE PASSES ITS CONTENT: what the content writer's
   commit needs (the flow chain's filters and its own) *)
Definition passes (fs : list filt) (L : bytes) : Prop := Forall (fun F => fapp F L = L) fs.

Lemma fok_cats (n : nat) (L : bytes) : Forall (fun F => fok F L) (FileDisc.cats n).
Proof using. unfold FileDisc.cats. apply Forall_replicate. exact I. Qed.

Lemma passes_cats (n : nat) (L : bytes) : passes (cats n) L.
Proof using. unfold passes, FileDisc.cats. apply Forall_replicate. reflexivity. Qed.

(* THE LINE'S CONTENT: what the producer writes when all goes well --
   echo's words minus the command name, or the file's content (the empty
   list when the content function has none) *)
Definition prod_content (fc : bytes -> option bytes) (p : producer) : bytes :=
  match p with
  | PrEcho ws => wl_line (drop 1 ws)
  | PrCatF f => default [] (fc f)
  end.

(* whether the producer is a CAT (its halt prints) *)
Definition prod_cat (p : producer) : bool :=
  match p with PrEcho _ => false | PrCatF _ => true end.

(* ONE CONSTRUCTOR PER BEHAVIOUR.  [L] is the line's content; every pipe
   carries a prefix of it (the protocol's flow clause).  The exec failure
   and the argv[0] death are sh's (user/sh.c:77-81); the rest are the
   programs' exits, derived from their trees in section 6. *)
Inductive stage_out (fc : bytes -> option bytes) (L : bytes) : stage -> st_out -> Prop :=
  (* the exec failed: sh's diagnostic, and the process exits *)
  | so_exec st :
      stage_out fc L st (MkSO (st_dg_exec st) (st_rd_dead st) (st_wr_dead st))
  (* argv[0] empty: exit 1, silently (PSilent) *)
  | so_silent st :
      stage_out fc L st (MkSO [] (st_rd_dead st) (st_wr_dead st))
  (* echo wrote the whole line *)
  | so_echo ws :
      L = wl_line (drop 1 ws) ->
      stage_out fc L (SProd (PrEcho ws)) (MkSO [] None (Some (WrAll L)))
  (* echo's reader went: a write answered -1, echo went on silently *)
  | so_echo_halt ws D :
      L = wl_line (drop 1 ws) -> D `prefix_of` L ->
      stage_out fc L (SProd (PrEcho ws)) (MkSO [] None (Some (WrHalt D)))
  (* cat f copied the file whole *)
  | so_catf f :
      fc f = Some L ->
      stage_out fc L (SProd (PrCatF f)) (MkSO [] None (Some (WrAll L)))
  (* cat f's reader went: [cat: write error] *)
  | so_catf_halt f D :
      fc f = Some L -> D `prefix_of` L ->
      stage_out fc L (SProd (PrCatF f)) (MkSO cat_dg_write None (Some (WrHalt D)))
  (* the open answered -1 (absent, or refused on a present file) *)
  | so_catf_open f :
      stage_out fc L (SProd (PrCatF f)) (MkSO (cat_dg_open f) None (Some WrNone))
  (* a middle filter read to end of file and wrote what it owes *)
  | so_mid_f F D :
      D `prefix_of` L ->
      stage_out fc L (SMid F) (MkSO [] (Some (RdEof D)) (Some (WrAll (fapp F D))))
  (* a middle cat's reader went: [cat: write error] *)
  | so_mid_halt D :
      D `prefix_of` L ->
      stage_out fc L (SMid FCat) (MkSO cat_dg_write (Some RdGone) (Some (WrHalt D)))
  (* a middle grep's reader went: its write answered -1, it went on
     reading to end of file, silently (grep ignores its write's return) *)
  | so_grep_halt w D W :
      D `prefix_of` L -> W `prefix_of` GrepTree.grep_out w D ->
      stage_out fc L (SMid (FGrep w)) (MkSO [] (Some (RdEof D)) (Some (WrHalt W)))
  (* the last filter read to end of file and printed what it owes *)
  | so_last_f F D :
      D `prefix_of` L ->
      stage_out fc L (SLast F) (MkSO (fapp F D) (Some (RdEof D)) None).

(* the cat instances, by their landed names *)
Lemma so_mid_copy fc L D :
  D `prefix_of` L -> stage_out fc L (SMid FCat) (MkSO [] (Some (RdEof D)) (Some (WrAll D))).
Proof using. exact (so_mid_f fc L FCat D). Qed.

Lemma so_last fc L D :
  D `prefix_of` L -> stage_out fc L (SLast FCat) (MkSO D (Some (RdEof D)) None).
Proof using. exact (so_last_f fc L FCat D). Qed.

(* ===================================================================== *)
(*  3.  THE PAIRING THROUGH A PIPE, WITH THE RULED CORNER (B)             *)
(* ===================================================================== *)

(* [wc]: the writer is a CAT.  A halted cat writer beside an end-of-file
   reader is the loose corner (design SS2.4, ruled (B)): the reader may
   have seen any prefix of the line.  Everywhere else the pairing is
   [PipesPair.pipe_pair] (an echo writer's halt keeps [False], and so does
   a grep writer's: grep's halt prints nothing, so it pairs EXACTLY).
   Below a filter the corner stays the LOOSE one (grep-pipes.md section 2,
   the owner's question 1 open): a reader behind a halted cat may see any
   prefix of the LINE, even bytes a grep above it filtered out. *)
Definition pipe_pairB (L : bytes) (wc : bool) (w : wr_out) (r : rd_out) : Prop :=
  match w, r with
  | WrHalt _, RdEof D' => wc = true /\ D' `prefix_of` L
  | _, _ => pipe_pair w r
  end.

Global Instance pipe_pair_dec w r : Decision (pipe_pair w r).
Proof using. destruct w, r; unfold pipe_pair; apply _. Defined.
Global Instance pipe_pairB_dec L wc w r : Decision (pipe_pairB L wc w r).
Proof using. destruct w, r; unfold pipe_pairB; apply _. Defined.

(* THE AGREEMENT with [PipesPair]: the exact pairing is admitted at every
   writer; at an echo writer the two are the same; at a cat writer the
   corner is the only addition *)
Lemma pipe_pairB_of_pair L wc w r : pipe_pair w r -> pipe_pairB L wc w r.
Proof using. destruct w, r; cbn; tauto. Qed.

Lemma pipe_pairB_echo L w r : pipe_pairB L false w r <-> pipe_pair w r.
Proof using. destruct w, r; cbn; intuition discriminate. Qed.

Lemma pipe_pairB_cat L w r :
  pipe_pairB L true w r <->
  pipe_pair w r \/ exists D D', w = WrHalt D /\ r = RdEof D' /\ D' `prefix_of` L.
Proof using.
  destruct w as [D | D |], r as [D' |]; cbn; split;
    try (intros H; left; exact H);
    try (intros [H | (? & ? & ? & ? & ?)]; [exact H | discriminate]).
  - intros [_ H]. right. exists D, D'. done.
  - intros [[] | (? & ? & [= <-] & [= <-] & H)]. done.
Qed.

(* ===================================================================== *)
(*  4.  MERGES, RUNS AND BLOCKS                                           *)
(* ===================================================================== *)

(* [merge_all ss b]: [b] is a byte-wise interleaving of the streams [ss],
   each taken whole *)
Inductive merge_all : list bytes -> bytes -> Prop :=
  | ma_done ss :
      Forall (fun s => s = []) ss -> merge_all ss []
  | ma_take ss i x s b :
      ss !! i = Some (x :: s) -> merge_all (<[i := s]> ss) b -> merge_all ss (x :: b).

(* sh's two panics as bytes: [pipe] and [fork] (user/sh.c:103, 194) *)
Definition dg_pipe_b : bytes := wl_line dg_pipe.
Definition dg_fork_b : bytes := wl_line dg_fork.

(* THE SUFFIX BELOW A PIPE: the filter stages [fs] (at least one)
   reading a pipe whose writer did [win] ([wc]: the writer is a cat, whose
   halt is the ruled corner).  At [[F]] it is the last stage itself; at
   two or more it is the sh node that runs [F | ...]: its [pipe()] fails
   (it prints [pipe] and nothing below it runs; the incoming reader is
   gone), or it forks the middle stage and the next suffix, the middle
   stage's writer paired with the suffix's reader.  The node's own stream
   is empty; the streams are the stages', in order. *)
Inductive sfx_run (fc : bytes -> option bytes) (L : bytes)
    : list filt -> wr_out -> bool -> list bytes -> Prop :=
  | sr_last F win wc so :
      stage_out fc L (SLast F) so -> pipe_pairB L wc win (rd_of so) ->
      sfx_run fc L [F] win wc [so_cons so]
  | sr_pipe_fail F F' fs win wc :
      sfx_run fc L (F :: F' :: fs) win wc [dg_pipe_b]
  | sr_node F F' fs win wc so ss :
      stage_out fc L (SMid F) so -> pipe_pairB L wc win (rd_of so) ->
      sfx_run fc L (F' :: fs) (wr_of so) (filt_is_cat F) ss ->
      sfx_run fc L (F :: F' :: fs) win wc (so_cons so :: ss).

(* A ROUND THAT RAN: the runcmd child execs echo, or runs the pipeline's
   top node (its [pipe()] fails, or it forks the producer and the suffix
   of its filter stages) *)
Inductive line_run (fc : bytes -> option bytes) : pline' -> list bytes -> Prop :=
  | lr_echo ws : line_run fc (LEcho' ws) [wl_line (drop 1 ws)]
  | lr_echo_exec ws : line_run fc (LEcho' ws) [dg_execL]
  | lr_echo_silent ws : line_run fc (LEcho' ws) [[]]
  | lr_pipe_fail p fs : fs <> [] -> line_run fc (LPipes p fs) [dg_pipe_b]
  | lr_node p fs so ss :
      stage_out fc (prod_content fc p) (SProd p) so ->
      sfx_run fc (prod_content fc p) fs (wr_of so) (prod_cat p) ss ->
      line_run fc (LPipes p fs) (so_cons so :: ss).

(* THE BLOCKS A ROUND MAY PRINT before sh's prompt *)
Definition line_blocks (fc : bytes -> option bytes) (l : pline') (b : bytes) : Prop :=
  exists ss, line_run fc l ss /\ merge_all ss b.

(* THE TERMINAL RUNS: a [fork] fails at some node.  The node prints
   [fork] and exits; every stage above it was waited, so its stream is
   complete; the left child the node had already forked (if its second
   fork failed) is a STRAY, which may print any prefix of its stream at
   any time.  The waited writer just above the failing node is paired
   with a reader that vouches for nothing. *)
Inductive sfx_term (fc : bytes -> option bytes) (L : bytes)
    : list filt -> wr_out -> bool -> list bytes -> bytes -> Prop :=
  | stt_here F F' fs win wc so :
      stage_out fc L (SMid F) so ->
      sfx_term fc L (F :: F' :: fs) win wc [dg_fork_b] (so_cons so)
  | stt_next F F' fs win wc so W s :
      stage_out fc L (SMid F) so -> pipe_pairB L wc win (rd_of so) ->
      sfx_term fc L (F' :: fs) (wr_of so) (filt_is_cat F) W s ->
      sfx_term fc L (F :: F' :: fs) win wc (so_cons so :: W) s.

Inductive line_term (fc : bytes -> option bytes) : pline' -> list bytes -> bytes -> Prop :=
  | lt_here p fs so :
      fs <> [] -> stage_out fc (prod_content fc p) (SProd p) so ->
      line_term fc (LPipes p fs) [dg_fork_b] (so_cons so)
  | lt_next p fs so W s :
      stage_out fc (prod_content fc p) (SProd p) so ->
      sfx_term fc (prod_content fc p) fs (wr_of so) (prod_cat p) W s ->
      line_term fc (LPipes p fs) (so_cons so :: W) s.

(* the waited streams, then sh's prompt, shuffled with a prefix of the
   stray's stream *)
Definition line_term_blocks (fc : bytes -> option bytes) (l : pline') (b : bytes) : Prop :=
  exists W s Wm sp,
    line_term fc l W s /\ merge_all W Wm /\ sp `prefix_of` s
    /\ merge_all [Wm ++ u_prompt; sp] b.

(* ===================================================================== *)
(*  5.  THE ALTERNATIVES AND THE LINE MODEL                               *)
(* ===================================================================== *)

(* [PLPanic]: the MAIN loop's fork panic (the shell dies, init restarts
   it); [PLRun b]: the round ran and printed [b], then the prompt;
   [PLTerm b]: a fork failed inside the round, and [b] is a nonempty
   prefix of a terminal block -- coverage ends there *)
Inductive plalt :=
  | PLPanic
  | PLRun (b : bytes)
  | PLTerm (b : bytes).

Global Instance plalt_eq_dec : EqDecision plalt.
Proof using. solve_decision. Defined.

(* THE CODE: positional mod 3 over [encode_nat] of the block.  It is
   BUILT, NEVER COMPUTED -- a block's code is astronomically large, as
   [PipeDisc.palt_code_both_big] already shows for two diagnostics --
   and everything below reads it through [plalt_of_code]. *)
Definition plalt_code (a : plalt) : nat :=
  match a with
  | PLRun b => 3 * encode_nat b
  | PLTerm b => 3 * encode_nat b + 1
  | PLPanic => 2
  end.

Definition plalt_of (n : nat) : plalt :=
  if decide (n mod 3 = 0) then PLRun (default [] (decode_nat (n / 3)))
  else if decide (n mod 3 = 1) then PLTerm (default [] (decode_nat (n / 3)))
  else PLPanic.

Lemma div3 (n : nat) : n = 3 * (n / 3) + n mod 3 /\ n mod 3 < 3.
Proof using. split; [apply Nat.div_mod; lia | apply Nat.mod_upper_bound; lia]. Qed.

Lemma plalt_of_code (a : plalt) : plalt_of (plalt_code a) = a.
Proof using.
  unfold plalt_of.
  destruct a as [| b | b]; cbn [plalt_code].
  - destruct (div3 2) as [H1 H2]. rewrite decide_False; [| lia].
    rewrite decide_False; [reflexivity | lia].
  - destruct (div3 (3 * encode_nat b)) as [H1 H2].
    assert (Hq : 3 * encode_nat b / 3 = encode_nat b) by lia.
    rewrite decide_True; [| lia]. rewrite Hq, decode_encode_nat. reflexivity.
  - destruct (div3 (3 * encode_nat b + 1)) as [H1 H2].
    assert (Hq : (3 * encode_nat b + 1) / 3 = encode_nat b) by lia.
    rewrite decide_False; [| lia]. rewrite decide_True; [| lia].
    rewrite Hq, decode_encode_nat. reflexivity.
Qed.

Lemma plalt_code_inj (a b : plalt) : plalt_code a = plalt_code b -> a = b.
Proof using. intros H. by rewrite <- (plalt_of_code a), <- (plalt_of_code b), H. Qed.

Definition plpanic (a : plalt) : bool := match a with PLPanic => true | _ => false end.
Definition plterm (a : plalt) : bool := match a with PLTerm _ => true | _ => false end.

(* the console continuation: the panic line, the block and the prompt, or
   the terminal block as it stands *)
Definition plcont (a : plalt) : bytes :=
  match a with
  | PLPanic => alt_panic
  | PLRun b => b ++ u_prompt
  | PLTerm b => b
  end.

Definition plalt_ok (fc : bytes -> option bytes) (l : pline') (a : plalt) : Prop :=
  match a with
  | PLPanic => True
  | PLRun b => line_blocks fc l b
  | PLTerm b => b <> [] /\ exists b', line_term_blocks fc l b' /\ b `prefix_of` b'
  end.

(* WHAT A COVERAGE-ENDING ALTERNATIVE CAN HAVE PUT ON THE WIRE: the
   prefix-closure of the admitted lines' terminal blocks *)
Definition pl_merge (fc : bytes -> option bytes) (adm : pline' -> bool) (u : bytes) : Prop :=
  exists l b, adm l = true /\ plalt_ok fc l (PLTerm b) /\ u `prefix_of` b.

(* THE SHELL'S OWN ALTERNATIVES.  The shell reads ANY line, and names
   three alternatives at it whatever the line is ([LineModelLinks.lm_hooks]:
   the main loop's fork panic, the silent round, the exec diagnostic of the
   round's first process).  They are admissible at EVERY line; every other
   alternative only at an admitted one.  At an admitted line with a cat
   ([pl_nz]) the three are blocks of the line anyway ([plsafe_ok]), so the
   range condition there is exactly [plalt_ok] ([pipes_lm_ok_iff]); at a
   line the application does not admit the discipline never lets a body
   parse to it. *)
Definition pl_exfb (l : pline') : bytes :=
  match l with LEcho' _ => dg_execL | LPipes p _ => st_dg_exec (SProd p) end.

Definition plsafe (l : pline') (a : plalt) : Prop :=
  a = PLPanic \/ a = PLRun [] \/ a = PLRun (pl_exfb l).

Global Instance plsafe_dec l a : Decision (plsafe l a).
Proof using. unfold plsafe. apply _. Defined.

(* a line with at least one filter stage, or an echo line: a line with
   runs *)
Definition pl_nz (l : pline') : Prop :=
  match l with LPipes _ [] => False | _ => True end.

Lemma pl_ok_nz l : pl_ok l -> pl_nz l.
Proof using. destruct l as [ws | p [| F fs]]; cbn; [done | intros (_ & H & _); exact (H eq_refl) | done]. Qed.

(* the partial line's alphabet: [PipeDisc]'s, and the dot a [cat N]
   producer's file name is typed through (cut W4) *)
Definition psbyte (b : bv 8) : Prop := pbody_byte b \/ b = fn_dot.

Global Instance psbyte_dec b : Decision (psbyte b).
Proof using. unfold psbyte. apply _. Defined.

Lemma psbyte_of_body b : wl_body_byte b -> psbyte b.
Proof using. intros H. left. exact (pbody_byte_of_body b H). Qed.

(* THE LINE MODEL.  State [unit]: nothing survives a round; [fc] is the
   content function [cat f] reads, [adm] the line shapes the application
   admits. *)
Definition pipes_lm (fc : bytes -> option bytes) (adm : pline' -> bool) : lmodel :=
  MkLM unit pline' pl_of plalt plalt_of plpanic (fun _ _ a => plcont a)
       (fun _ _ _ => tt) (fun _ l a => plsafe l a \/ (adm l = true /\ plalt_ok fc l a))
       (pl_body_ok adm) psbyte pl_ok (fun _ => True) plterm (pl_merge fc adm).

Lemma pipes_lm_cont_run fc adm s l b : lm_cont (pipes_lm fc adm) s l (PLRun b) = b ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma pipes_lm_ok_intro fc adm s l a :
  adm l = true -> plalt_ok fc l a -> lm_ok (pipes_lm fc adm) s l a.
Proof using. intros Ha Hok. right. split; [exact Ha | exact Hok]. Qed.

(* a coverage-ending alternative is never one of the shell's own *)
Lemma pipes_lm_ok_term fc adm s l b :
  lm_ok (pipes_lm fc adm) s l (PLTerm b) <-> adm l = true /\ plalt_ok fc l (PLTerm b).
Proof using.
  split; [| intros H; right; exact H].
  intros [Hs | H]; [| exact H]. exfalso. destruct Hs as [H | [H | H]]; discriminate H.
Qed.
Lemma pipes_lm_term fc adm a : lm_term (pipes_lm fc adm) a = true <-> exists b, a = PLTerm b.
Proof using. destruct a; cbn; split; try discriminate; try (intros [? ?]; discriminate); eauto. Qed.
Lemma pipes_lm_merge fc adm u :
  lm_merge (pipes_lm fc adm) u <->
  exists l b, adm l = true /\ plalt_ok fc l (PLTerm b) /\ u `prefix_of` b.
Proof using. reflexivity. Qed.

(* ===================================================================== *)
(*  4b.  READING A MERGE                                                  *)
(* ===================================================================== *)

Lemma merge_all_forall (P : bv 8 -> Prop) ss b :
  merge_all ss b -> Forall (Forall P) ss -> Forall P b.
Proof using.
  induction 1 as [ss Hnil | ss i x s b Hi Hm IH]; intros HF; [constructor |].
  pose proof (Forall_lookup_1 _ _ _ _ HF Hi) as Hxs.
  apply Forall_cons_1 in Hxs as [Hx Hs].
  constructor; [exact Hx |]. apply IH. apply Forall_insert; [exact HF | exact Hs].
Qed.

(* a stream whose first byte, if any, is not in [p] *)
Definition nohd (p : bytes) (s : bytes) : Prop :=
  match s with [] => True | x :: _ => x ∉ p end.

Global Instance nohd_dec p s : Decision (nohd p s).
Proof using. destruct s; unfold nohd; apply _. Defined.

Lemma merge_all_head_nohd p ss x b :
  merge_all ss (x :: b) -> Forall (nohd p) ss -> x ∉ p.
Proof using.
  intros Hm HF. inversion Hm as [| ss' i x' s b' Hi Hm']; subst.
  exact (Forall_lookup_1 _ _ _ _ HF Hi).
Qed.

(* THE FIRST BYTES OF A MERGE: if no other stream may START inside [p],
   all of [p] came from stream [j] *)
Lemma merge_prefix_from (p : bytes) : forall ss j s0 r,
  merge_all ss (p ++ r) -> ss !! j = Some s0 ->
  (forall i s, i <> j -> ss !! i = Some s -> nohd p s) ->
  p `prefix_of` s0 /\ merge_all (<[j := drop (length p) s0]> ss) r.
Proof using.
  induction p as [| x p IH]; intros ss j s0 r Hm Hj Hoth.
  - split; [apply prefix_nil |].
    change (drop (length (@nil (bv 8))) s0) with s0.
    rewrite list_insert_id; [exact Hm | exact Hj].
  - cbn [app] in Hm. inversion Hm as [| ss' i x' s b' Hi Hm']; subst.
    destruct (decide (i = j)) as [-> | Hne].
    + rewrite Hj in Hi. injection Hi as ->.
      destruct (IH (<[j := s]> ss) j s r Hm') as [Hp Hr].
      * apply list_lookup_insert. exact (lookup_lt_Some _ _ _ Hj).
      * intros i s' Hne Hi. rewrite list_lookup_insert_ne in Hi; [| done].
        pose proof (Hoth i s' Hne Hi) as H. destruct s' as [| y s'']; [exact I |].
        cbn in H |- *. intros Hy. apply H. by right.
      * split; [by apply prefix_cons |]. cbn [length drop].
        rewrite list_insert_insert in Hr. exact Hr.
    + exfalso. pose proof (Hoth i (x :: s) Hne Hi) as H. cbn in H. apply H. by left.
Qed.

Lemma merge_all_one x u : merge_all [x] u <-> u = x.
Proof using.
  split.
  - intros Hm. remember [x] as ss eqn:Hss. revert x Hss.
    induction Hm as [ss HF | ss i y s b Hi Hm IH]; intros x ->.
    + apply Forall_cons_1 in HF as [-> _]. reflexivity.
    + destruct i as [| i]; cbn in Hi; [| discriminate Hi].
      injection Hi as ->. rewrite (IH s eq_refl). reflexivity.
  - intros ->. induction x as [| y x IH].
    + constructor. repeat constructor.
    + apply (ma_take _ 0 y x); [reflexivity | exact IH].
Qed.

(* one stream taken as a block, anywhere *)
Lemma merge_all_block ss i x y u :
  ss !! i = Some (x ++ y) -> merge_all (<[i := y]> ss) u -> merge_all ss (x ++ u).
Proof using.
  revert ss. induction x as [| z x IH]; intros ss Hi Hm.
  - change ([] ++ y) with y in Hi. change ([] ++ u) with u.
    rewrite list_insert_id in Hm; [exact Hm | exact Hi].
  - change ((z :: x) ++ u) with (z :: (x ++ u)).
    apply (ma_take _ i z (x ++ y)); [exact Hi |].
    apply IH; [apply list_lookup_insert; exact (lookup_lt_Some _ _ _ Hi) |].
    rewrite list_insert_insert. exact Hm.
Qed.

(* ---- two streams: the textbook shuffle, and [PipeDisc.pmerge] -------- *)

Inductive shuf2 : bytes -> bytes -> bytes -> Prop :=
  | sh2_nil : shuf2 [] [] []
  | sh2_l x a b u : shuf2 a b u -> shuf2 (x :: a) b (x :: u)
  | sh2_r x a b u : shuf2 a b u -> shuf2 a (x :: b) (x :: u).

Lemma merge2_shuf2 a b u : merge_all [a; b] u <-> shuf2 a b u.
Proof using.
  split.
  - intros Hm. remember [a; b] as ss eqn:Hss. revert a b Hss.
    induction Hm as [ss HF | ss i x s u Hi Hm IH]; intros a b ->.
    + apply Forall_cons_1 in HF as [-> HF]. apply Forall_cons_1 in HF as [-> _].
      constructor.
    + destruct i as [| [| i]]; cbn in Hi.
      * injection Hi as ->. apply sh2_l. apply IH. reflexivity.
      * injection Hi as ->. apply sh2_r. apply IH. reflexivity.
      * discriminate Hi.
  - induction 1 as [| x a b u H IH | x a b u H IH].
    + constructor. repeat constructor.
    + apply (ma_take _ 0 x a); [reflexivity | exact IH].
    + apply (ma_take _ 1 x b); [reflexivity | exact IH].
Qed.

Lemma shuf2_cons_inv a b x u :
  shuf2 a b (x :: u) ->
  (exists a', a = x :: a' /\ shuf2 a' b u) \/ (exists b', b = x :: b' /\ shuf2 a b' u).
Proof using.
  intros H. inversion H as [| x' a' b' u' Hs | x' a' b' u' Hs]; subst.
  - left. exists a'. split; [reflexivity | exact Hs].
  - right. exists b'. split; [reflexivity | exact Hs].
Qed.

Lemma shuf2_nil_inv a b : shuf2 a b [] -> a = [] /\ b = [].
Proof using. intros H. inversion H. split; reflexivity. Qed.

Lemma shuf2_nil_l b u : shuf2 [] b u <-> u = b.
Proof using.
  split.
  - revert b. induction u as [| x u IH]; intros b H.
    + by destruct (shuf2_nil_inv _ _ H) as [_ ->].
    + destruct (shuf2_cons_inv _ _ _ _ H) as [(a' & Ha & _) | (b' & -> & Hs)];
        [discriminate Ha |]. rewrite (IH b' Hs). reflexivity.
  - intros ->. induction b as [| x b IH]; [constructor | apply sh2_r; exact IH].
Qed.

Lemma shuf2_nil_r a u : shuf2 a [] u <-> u = a.
Proof using.
  split.
  - revert a. induction u as [| x u IH]; intros a H.
    + by destruct (shuf2_nil_inv _ _ H) as [-> _].
    + destruct (shuf2_cons_inv _ _ _ _ H) as [(a' & -> & Hs) | (b' & Hb & _)];
        [| discriminate Hb]. rewrite (IH a' Hs). reflexivity.
  - intros ->. induction a as [| x a IH]; [constructor | apply sh2_l; exact IH].
Qed.

Lemma shuf2_comm a b u : shuf2 a b u -> shuf2 b a u.
Proof using.
  induction 1 as [| x a b u H IH | x a b u H IH];
    [constructor | apply sh2_r; exact IH | apply sh2_l; exact IH].
Qed.

Lemma shuf2_app_l a b u c : shuf2 a b u -> shuf2 (a ++ c) b (u ++ c).
Proof using.
  induction 1 as [| x a b u H IH | x a b u H IH]; cbn [app].
  - apply shuf2_nil_r. reflexivity.
  - apply sh2_l. exact IH.
  - apply sh2_r. exact IH.
Qed.

Lemma shuf2_app_r a b u c : shuf2 a b u -> shuf2 a (b ++ c) (u ++ c).
Proof using.
  intros H. apply shuf2_comm. apply shuf2_app_l. apply shuf2_comm. exact H.
Qed.

(* A PREFIX OF A SHUFFLE IS A SHUFFLE OF PREFIXES *)
Lemma shuf2_prefix a b u u' :
  shuf2 a b u -> u' `prefix_of` u ->
  exists a' b', a' `prefix_of` a /\ b' `prefix_of` b /\ shuf2 a' b' u'.
Proof using.
  intros H. revert u'. induction H as [| x a b u H IH | x a b u H IH]; intros u' Hp.
  - apply prefix_nil_inv in Hp. subst u'. exists [], [].
    split; [apply prefix_nil | split; [apply prefix_nil | constructor]].
  - destruct u' as [| y u'].
    + exists [], []. split; [apply prefix_nil | split; [apply prefix_nil | constructor]].
    + pose proof (prefix_cons_inv_1 _ _ _ _ Hp) as Hxy. apply prefix_cons_inv_2 in Hp.
      subst y. destruct (IH u' Hp) as (a' & b' & Ha & Hb & Hs).
      exists (x :: a'), b'. split; [by apply prefix_cons | split; [exact Hb |]].
      apply sh2_l. exact Hs.
  - destruct u' as [| y u'].
    + exists [], []. split; [apply prefix_nil | split; [apply prefix_nil | constructor]].
    + pose proof (prefix_cons_inv_1 _ _ _ _ Hp) as Hxy. apply prefix_cons_inv_2 in Hp.
      subst y. destruct (IH u' Hp) as (a' & b' & Ha & Hb & Hs).
      exists a', (x :: b'). split; [exact Ha | split; [by apply prefix_cons |]].
      apply sh2_r. exact Hs.
Qed.

(* A SHUFFLE IS A [pmerge] AT A SELECTOR OF THE RIGHT COUNTS *)
Lemma shuf2_pmerge a b u :
  shuf2 a b u <->
  exists sel, length sel = length a + length b /\ count_true sel = length a
              /\ u = pmerge sel a b.
Proof using.
  split.
  - induction 1 as [| x a b u H (sel & H1 & H2 & H3) | x a b u H (sel & H1 & H2 & H3)].
    + exists []. split; [reflexivity | split; reflexivity].
    + exists (true :: sel). cbn [length count_true]. split; [lia |]. split; [lia |].
      rewrite pmerge_true_cons, H3. reflexivity.
    + exists (false :: sel). cbn [length count_true]. split; [lia |]. split; [lia |].
      rewrite pmerge_false_cons, H3. reflexivity.
  - intros (sel & H1 & H2 & ->). revert a b H1 H2.
    induction sel as [| [|] s IH]; intros a b H1 H2.
    + destruct a, b; cbn [length] in H1; try lia. constructor.
    + cbn [length count_true] in H1, H2.
      destruct a as [| x a]; cbn [length] in H1, H2; [lia |].
      rewrite pmerge_true_cons. apply sh2_l. apply IH; lia.
    + cbn [length count_true] in H1, H2. pose proof (count_true_le s) as Hc.
      destruct b as [| y b]; cbn [length] in H1; [lia |].
      rewrite pmerge_false_cons. apply sh2_r. apply IH; lia.
Qed.

(* [PipeDisc.shufb] tests a shuffle of PREFIXES of its two sources *)
Lemma shufb_shuf2 u d1 d2 :
  shufb u d1 d2 = true <->
  exists p1 p2, p1 `prefix_of` d1 /\ p2 `prefix_of` d2 /\ shuf2 p1 p2 u.
Proof using.
  revert d1 d2. induction u as [| x u IH]; intros d1 d2; split.
  - intros _. exists [], []. split; [apply prefix_nil | split; [apply prefix_nil | constructor]].
  - intros _. reflexivity.
  - cbn [shufb]. intros Hs. apply orb_prop in Hs as [Hs | Hs].
    + destruct d1 as [| y d1']; [discriminate |]. apply andb_prop in Hs as [Hy Hs].
      apply bool_decide_eq_true in Hy. subst y.
      destruct (proj1 (IH d1' d2) Hs) as (p1 & p2 & H1 & H2 & H3).
      exists (x :: p1), p2. split; [by apply prefix_cons | split; [exact H2 |]].
      apply sh2_l. exact H3.
    + destruct d2 as [| y d2']; [discriminate |]. apply andb_prop in Hs as [Hy Hs].
      apply bool_decide_eq_true in Hy. subst y.
      destruct (proj1 (IH d1 d2') Hs) as (p1 & p2 & H1 & H2 & H3).
      exists p1, (x :: p2). split; [exact H1 | split; [by apply prefix_cons |]].
      apply sh2_r. exact H3.
  - intros (p1 & p2 & H1 & H2 & H3). cbn [shufb].
    destruct (shuf2_cons_inv _ _ _ _ H3) as [(a' & -> & Hs) | (b' & -> & Hs)].
    + destruct d1 as [| y d1']; [by apply prefix_nil_not in H1 |].
      pose proof (prefix_cons_inv_1 _ _ _ _ H1) as Hxy. apply prefix_cons_inv_2 in H1.
      subst y. rewrite bool_decide_eq_true_2; [| reflexivity].
      rewrite (proj2 (IH d1' d2) (ex_intro _ a' (ex_intro _ p2 (conj H1 (conj H2 Hs))))).
      reflexivity.
    + destruct d2 as [| y d2']; [by apply prefix_nil_not in H2 |].
      pose proof (prefix_cons_inv_1 _ _ _ _ H2) as Hxy. apply prefix_cons_inv_2 in H2.
      subst y. rewrite bool_decide_eq_true_2; [| reflexivity].
      rewrite (proj2 (IH d1 d2') (ex_intro _ p1 (ex_intro _ b' (conj H1 (conj H2 Hs))))).
      apply orb_true_r.
Qed.

(* ===================================================================== *)
(*  4c.  WHAT THE STREAMS OF A RUN LOOK LIKE                              *)
(* ===================================================================== *)

Local Ltac bdec := apply (bool_decide_unpack _); vm_compute; exact I.

Lemma nohd_app p s t : s <> [] -> nohd p s -> nohd p (s ++ t).
Proof using. destruct s; [done |]. intros _ H. exact H. Qed.

Lemma nohd_execL : nohd alt_panic dg_execL.
Proof using. bdec. Qed.
Lemma nohd_execR : nohd alt_panic dg_execR.
Proof using. bdec. Qed.
Lemma nohd_execG : nohd alt_panic dg_execG.
Proof using. bdec. Qed.
Lemma nohd_write : nohd alt_panic cat_dg_write.
Proof using. bdec. Qed.
Lemma nohd_pipe : nohd alt_panic dg_pipe_b.
Proof using. bdec. Qed.
Lemma nohd_open f : nohd alt_panic (cat_dg_open f).
Proof using.
  unfold cat_dg_open. apply nohd_app; [discriminate | bdec].
Qed.

(* a stage that is not the last *)
Definition st_notlast (st : stage) : Prop := match st with SLast _ => False | _ => True end.

Lemma stage_out_nohd fc L st so :
  stage_out fc L st so -> st_notlast st -> nohd alt_panic (so_cons so).
Proof using.
  destruct 1 as [st | st | | | | | f | | | | F D HD]; intros Hst; cbn [so_cons];
    try exact I; try exact nohd_write; try exact (nohd_open f); try (exfalso; exact Hst).
  destruct st as [[ws | f] | [| w] | F]; cbn [st_dg_exec filt_dg_exec];
    [exact nohd_execL | exact nohd_execR | exact nohd_execR | exact nohd_execG | exfalso; exact Hst].
Qed.

(* NOR DOES ANY START ON 'i', the letter every line of init's opens on:
   what follows the panic line on the wire is init's next prologue round,
   and a diagnostic after a whole panic line is never read as one *)
Definition pan_i : bytes := alt_panic ++ [Z_to_bv 8 105].

Lemma nohd_mono p q s : (forall x, x ∈ p -> x ∈ q) -> nohd q s -> nohd p s.
Proof using. destruct s as [| y s]; [done |]. cbn. intros Hpq Hq Hy. exact (Hq (Hpq y Hy)). Qed.

Lemma nohd_pan_i s : nohd pan_i s -> nohd alt_panic s.
Proof using. apply nohd_mono. intros x Hx. unfold pan_i. apply elem_of_app. by left. Qed.

Lemma nohd_i_execL : nohd pan_i dg_execL.
Proof using. bdec. Qed.
Lemma nohd_i_execR : nohd pan_i dg_execR.
Proof using. bdec. Qed.
Lemma nohd_i_execG : nohd pan_i dg_execG.
Proof using. bdec. Qed.
Lemma nohd_i_write : nohd pan_i cat_dg_write.
Proof using. bdec. Qed.
Lemma nohd_i_pipe : nohd pan_i dg_pipe_b.
Proof using. bdec. Qed.
Lemma nohd_i_open f : nohd pan_i (cat_dg_open f).
Proof using.
  unfold cat_dg_open. apply nohd_app; [discriminate | bdec].
Qed.

Lemma nohd_i_filt_exec F : nohd pan_i (filt_dg_exec F).
Proof using. destruct F; [exact nohd_i_execR | exact nohd_i_execG]. Qed.

Lemma stage_out_nohd_i fc L st so :
  stage_out fc L st so -> st_notlast st -> nohd pan_i (so_cons so).
Proof using.
  destruct 1 as [st | st | | | | | f | | | | F D HD]; intros Hst; cbn [so_cons];
    try exact I; try exact nohd_i_write; try exact (nohd_i_open f);
    try (exfalso; exact Hst).
  destruct st as [[ws | f] | F | F]; cbn [st_dg_exec];
    [exact nohd_i_execL | exact nohd_i_execR | exact (nohd_i_filt_exec F) | exfalso; exact Hst].
Qed.

(* ---- the inversions, one per stage kind ---- *)

Lemma stage_out_echo_inv fc L ws so :
  stage_out fc L (SProd (PrEcho ws)) so ->
  so = MkSO dg_execL None (Some WrNone) \/ so = MkSO [] None (Some WrNone)
  \/ (L = wl_line (drop 1 ws) /\ so = MkSO [] None (Some (WrAll L)))
  \/ exists D, L = wl_line (drop 1 ws) /\ D `prefix_of` L /\ so = MkSO [] None (Some (WrHalt D)).
Proof using.
  intros H. remember (SProd (PrEcho ws)) as st eqn:Hst.
  destruct H as [st' | st' | ws' HL | ws' D HL HD | | | | | | |]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right; left. split; [exact HL | reflexivity].
  - injection Hst as ->. right; right; right. exists D. split; [exact HL | split; [exact HD | reflexivity]].
Qed.

Lemma stage_out_catf_inv fc L f so :
  stage_out fc L (SProd (PrCatF f)) so ->
  so = MkSO dg_execR None (Some WrNone) \/ so = MkSO [] None (Some WrNone)
  \/ (fc f = Some L /\ so = MkSO [] None (Some (WrAll L)))
  \/ (exists D, fc f = Some L /\ D `prefix_of` L /\ so = MkSO cat_dg_write None (Some (WrHalt D)))
  \/ so = MkSO (cat_dg_open f) None (Some WrNone).
Proof using.
  intros H. remember (SProd (PrCatF f)) as st eqn:Hst.
  destruct H as [st' | st' | | | f' Hf | f' D Hf HD | f' | | | |]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right; left. split; [exact Hf | reflexivity].
  - injection Hst as ->. right; right; right; left. exists D. split; [exact Hf | split; [exact HD | reflexivity]].
  - injection Hst as ->. right; right; right; right. reflexivity.
Qed.

(* a middle cat *)
Lemma stage_out_mid_inv fc L so :
  stage_out fc L (SMid FCat) so ->
  so = MkSO dg_execR (Some RdGone) (Some WrNone) \/ so = MkSO [] (Some RdGone) (Some WrNone)
  \/ (exists D, D `prefix_of` L /\ so = MkSO [] (Some (RdEof D)) (Some (WrAll D)))
  \/ (exists D, D `prefix_of` L /\ so = MkSO cat_dg_write (Some RdGone) (Some (WrHalt D))).
Proof using.
  intros H. remember (SMid FCat) as st eqn:Hst.
  destruct H as [st' | st' | | | | | | F D HD | D HD | w D W HD HW |]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right; left. exists D. split; [exact HD | reflexivity].
  - right; right; right. exists D. split; [exact HD | reflexivity].
Qed.

(* a middle grep: never a diagnostic of its own, and it reads to the end
   whether its reader stayed or went *)
Lemma stage_out_mid_grep_inv fc L w so :
  stage_out fc L (SMid (FGrep w)) so ->
  so = MkSO dg_execG (Some RdGone) (Some WrNone) \/ so = MkSO [] (Some RdGone) (Some WrNone)
  \/ (exists D, D `prefix_of` L
                /\ so = MkSO [] (Some (RdEof D)) (Some (WrAll (GrepTree.grep_out w D))))
  \/ (exists D W, D `prefix_of` L /\ W `prefix_of` GrepTree.grep_out w D
                  /\ so = MkSO [] (Some (RdEof D)) (Some (WrHalt W))).
Proof using.
  intros H. remember (SMid (FGrep w)) as st eqn:Hst.
  destruct H as [st' | st' | | | | | | F D HD | D HD | w' D W HD HW |]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right; left. exists D. split; [exact HD | reflexivity].
  - injection Hst as ->. right; right; right. exists D, W. split_and!; [exact HD | exact HW | reflexivity].
Qed.

(* the last cat *)
Lemma stage_out_last_inv fc L so :
  stage_out fc L (SLast FCat) so ->
  so = MkSO dg_execR (Some RdGone) None \/ so = MkSO [] (Some RdGone) None
  \/ exists D, D `prefix_of` L /\ so = MkSO D (Some (RdEof D)) None.
Proof using.
  intros H. remember (SLast FCat) as st eqn:Hst.
  destruct H as [st' | st' | | | | | | | | | F D HD]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right. exists D. split; [exact HD | reflexivity].
Qed.

(* the last stage, at any filter *)
Lemma stage_out_last_f_inv fc L F so :
  stage_out fc L (SLast F) so ->
  so = MkSO (filt_dg_exec F) (Some RdGone) None \/ so = MkSO [] (Some RdGone) None
  \/ exists D, D `prefix_of` L /\ so = MkSO (fapp F D) (Some (RdEof D)) None.
Proof using.
  intros H. remember (SLast F) as st eqn:Hst.
  destruct H as [st' | st' | | | | | | | | | F' D HD]; try discriminate Hst.
  - subst st'. left. reflexivity.
  - subst st'. right; left. reflexivity.
  - injection Hst as ->. right; right. exists D. split; [exact HD | reflexivity].
Qed.

(* EVERY STREAM OF A RUN IS A DIAGNOSTIC (no stream starts inside the
   panic line, nor on init's 'i') BUT THE LAST STAGE'S, which is a prefix
   of the line -- on a content of one line, the gate *)
Lemma sfx_run_shape_i fc L fs w wc ss :
  GrepFilt.oneline L -> sfx_run fc L fs w wc ss ->
  Forall (nohd pan_i) ss
  \/ exists ds c, ss = ds ++ [c] /\ Forall (nohd pan_i) ds /\ c `prefix_of` L.
Proof using.
  intros HL.
  induction 1 as [F win wc so Hso Hp | F F' fs win wc | F F' fs win wc so ss Hso Hp Hr IH].
  - destruct (stage_out_last_f_inv fc L F so Hso) as [-> | [-> | (D & HD & ->)]].
    + left. constructor; [exact (nohd_i_filt_exec F) | constructor].
    + left. constructor; [exact I | constructor].
    + right. exists [], (fapp F D).
      split; [reflexivity | split; [constructor | exact (fapp_prefix F L D HL HD)]].
  - left. constructor; [exact nohd_i_pipe | constructor].
  - pose proof (stage_out_nohd_i fc L (SMid F) so Hso I) as Hn.
    destruct IH as [IH | (ds & c & -> & Hds & Hc)]; [left; constructor; [exact Hn | exact IH] | right].
    exists (so_cons so :: ds), c. split; [reflexivity | split; [constructor; [exact Hn | exact Hds] | exact Hc]].
Qed.

Lemma line_run_shape_i fc p fs ss :
  GrepFilt.oneline (prod_content fc p) ->
  line_run fc (LPipes p fs) ss ->
  Forall (nohd pan_i) ss
  \/ exists ds c, ss = ds ++ [c] /\ Forall (nohd pan_i) ds /\ c `prefix_of` prod_content fc p.
Proof using.
  intros HL H. remember (LPipes p fs) as l eqn:Hl.
  destruct H as [ws | ws | ws | p' fs' Hn | p' fs' so ss Hso Hr]; try discriminate Hl.
  - left. constructor; [exact nohd_i_pipe | constructor].
  - injection Hl as -> ->.
    pose proof (stage_out_nohd_i _ _ _ _ Hso I) as Hn.
    destruct (sfx_run_shape_i _ _ _ _ _ _ HL Hr) as [Hf | (ds & c & -> & Hds & Hc)];
      [left; constructor; [exact Hn | exact Hf] | right].
    exists (so_cons so :: ds), c. split; [reflexivity | split; [constructor; [exact Hn | exact Hds] | exact Hc]].
Qed.

(* ...and read against the panic line alone *)
Lemma sfx_run_shape fc L fs w wc ss :
  GrepFilt.oneline L -> sfx_run fc L fs w wc ss ->
  Forall (nohd alt_panic) ss
  \/ exists ds c, ss = ds ++ [c] /\ Forall (nohd alt_panic) ds /\ c `prefix_of` L.
Proof using.
  intros HL Hr. destruct (sfx_run_shape_i fc L fs w wc ss HL Hr) as [HF | (ds & c & -> & Hds & Hc)];
    [left; exact (Forall_impl _ _ _ HF nohd_pan_i) | right].
  exists ds, c. split; [reflexivity | split; [exact (Forall_impl _ _ _ Hds nohd_pan_i) | exact Hc]].
Qed.

Lemma line_run_shape fc p fs ss :
  GrepFilt.oneline (prod_content fc p) ->
  line_run fc (LPipes p fs) ss ->
  Forall (nohd alt_panic) ss
  \/ exists ds c, ss = ds ++ [c] /\ Forall (nohd alt_panic) ds /\ c `prefix_of` prod_content fc p.
Proof using.
  intros HL Hr. destruct (line_run_shape_i fc p fs ss HL Hr) as [HF | (ds & c & -> & Hds & Hc)];
    [left; exact (Forall_impl _ _ _ HF nohd_pan_i) | right].
  exists ds, c. split; [reflexivity | split; [exact (Forall_impl _ _ _ Hds nohd_pan_i) | exact Hc]].
Qed.

(* ...AND AT [echo ws | cat] THE CONTENT COMES ALONE: the last cat printed
   something only if echo wrote it all, silently *)
Lemma line_run_one fc ws ss :
  line_run fc (LPipes (PrEcho ws) [FCat]) ss ->
  Forall (nohd alt_panic) ss \/ ss = [[]; wl_line (drop 1 ws)].
Proof using.
  intros H. remember (LPipes (PrEcho ws) [FCat]) as l eqn:Hl.
  destruct H as [ws0 | ws0 | ws0 | p fs Hn | p fs so ss Hso Hr]; try discriminate Hl.
  - left. constructor; [exact nohd_pipe | constructor].
  - injection Hl as -> ->. cbn [prod_content prod_cat] in Hso, Hr.
    set (L := wl_line (drop 1 ws)) in Hso, Hr.
    remember [FCat] as m eqn:Hm in Hr. remember (wr_of so) as w0 eqn:Hw in Hr.
    remember false as b0 eqn:Hb in Hr.
    destruct Hr as [F win wc so1 Hso1 Hp | F F' fs' win wc | F F' fs' win wc so' ss' Hso' Hp Hr'];
      [| discriminate Hm | discriminate Hm].
    injection Hm as ->. subst win wc.
    destruct (stage_out_echo_inv _ _ _ _ Hso) as [-> | [-> | [[_ ->] | (D0 & _ & HD0 & ->)]]];
    destruct (stage_out_last_inv _ _ _ Hso1) as [-> | [-> | (D & HD & ->)]];
    cbn [so_cons so_rd so_wr rd_of wr_of pipe_pairB pipe_pair] in Hp |- *;
    try (left; constructor; [first [exact nohd_execL | exact I] |
                             constructor; [first [exact nohd_execR | exact I] | constructor]]).
    + subst D. left. constructor; [exact nohd_execL | constructor; [exact I | constructor]].
    + subst D. left. constructor; [exact I | constructor; [exact I | constructor]].
    + subst D. right. reflexivity.
    + destruct Hp as [Hf _]. discriminate Hf.
Qed.

(* ---- '$'-freedom ---- *)

Lemma word_nodollar f : fn_word f -> Forall nodollar f.
Proof using.
  intros [_ Hf]. eapply Forall_impl; [exact Hf |].
  intros b Hb. apply fn_byte_val in Hb. unfold nodollar. lia.
Qed.

Lemma prefix_forall {A} (P : A -> Prop) (l1 l2 : list A) :
  l1 `prefix_of` l2 -> Forall P l2 -> Forall P l1.
Proof using. intros [k ->] H. apply Forall_app in H as [H _]. exact H. Qed.

Lemma dg_execG_nodollar : Forall nodollar dg_execG.
Proof using. bdec. Qed.

Lemma filt_dg_exec_nodollar F : Forall nodollar (filt_dg_exec F).
Proof using. destruct F; [exact dg_execR_nodollar | exact dg_execG_nodollar]. Qed.

Lemma stage_out_nodollar fc L st so :
  Forall nodollar L -> GrepFilt.oneline L -> (forall f, st = SProd (PrCatF f) -> fn_word f) ->
  stage_out fc L st so -> Forall nodollar (so_cons so).
Proof using.
  intros HL HL1 Hf H.
  destruct H as [st | st | | | | | f | F D HD | D HD | w D W HD HW | F D HD]; cbn [so_cons].
  - destruct st as [[ws | f] | F | F]; cbn [st_dg_exec];
      [exact dg_execL_nodollar | exact dg_execR_nodollar
      | exact (filt_dg_exec_nodollar F) | exact (filt_dg_exec_nodollar F)].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - bdec.
  - unfold cat_dg_open. apply Forall_app. split; [bdec |].
    apply Forall_app. split; [exact (word_nodollar f (Hf f eq_refl)) | bdec].
  - constructor.
  - bdec.
  - constructor.
  - exact (prefix_forall _ _ L (fapp_prefix F L D HL1 HD) HL).
Qed.

Lemma sfx_run_nodollar fc L fs w wc ss :
  Forall nodollar L -> GrepFilt.oneline L -> sfx_run fc L fs w wc ss -> Forall (Forall nodollar) ss.
Proof using.
  intros HL HL1. induction 1 as [F win wc so Hso Hp | F F' fs win wc | F F' fs win wc so ss Hso Hp Hr IH].
  - constructor; [| constructor].
    apply (stage_out_nodollar fc L (SLast F) so HL HL1); [intros f Hf; discriminate Hf | exact Hso].
  - constructor; [bdec | constructor].
  - constructor; [| exact IH].
    apply (stage_out_nodollar fc L (SMid F) so HL HL1); [intros f Hf; discriminate Hf | exact Hso].
Qed.

(* ===================================================================== *)
(*  5b.  THE LAWS                                                         *)
(*                                                                        *)
(*  The laws hold at every admission whose content has a word line's      *)
(*  shape ([fc_ok]): [pipes_lm_laws_fc].  [lml_cont_shape] -- a round     *)
(*  that did not panic is a '$'-free run then the prompt, and below one   *)
(*  wire with sh's panic line FOLLOWED BY INIT'S NEXT PROLOGUE ROUND it   *)
(*  IS that line -- holds at [echo fork | cat | cat] too: the corner (B)  *)
(*  admits the whole line [fork] followed by a middle cat's               *)
(*  [cat: write error] ([fork2_corner]), which looks like the panic line  *)
(*  followed by something, but that something opens on 'c' and init's    *)
(*  round on '$' or 'i'.  The owner's ruling (2026-09-24) admits every    *)
(*  echo pipeline whatever its output looks like ([adm_echo]), and the    *)
(*  law no longer asks the output to be unlike the panic line followed by *)
(*  ANY bytes.  The stronger reading ([pipes_block_shape], under          *)
(*  [adm_ok]) is kept for the claim's non-terminal witness.               *)
(* ===================================================================== *)

(* a content the determinacy argument can read: '$'-free, and its only
   newline (if any) is its last byte -- a word line's shape *)
Definition lshape (L : bytes) : Prop :=
  Forall nodollar L /\ (wl_nl ∉ L \/ exists v, wl_nl ∉ v /\ L = v ++ [wl_nl]).

Definition fc_ok (fc : bytes -> option bytes) : Prop :=
  forall f c, fc f = Some c -> lshape c.

(* an admitted line whose content IS the panic line has no cat writer *)
Definition adm_ok (fc : bytes -> option bytes) (adm : pline' -> bool) : Prop :=
  forall p fs, adm (LPipes p fs) = true -> pl_ok (LPipes p fs) ->
    prod_content fc p = alt_panic -> exists ws, p = PrEcho ws /\ fs = [FCat].

Lemma prod_content_shape fc p : fc_ok fc -> prod_ok p -> lshape (prod_content fc p).
Proof using.
  intros Hfc Hp. destruct p as [ws | f]; cbn [prod_content].
  - exact (pd_wl_line_shape' (drop 1 ws) (lb_Forall_drop _ 1 ws (line_ok_wf ws Hp))).
  - destruct (fc f) as [c |] eqn:Hf; cbn [default].
    + exact (Hfc f c Hf).
    + split; [constructor | left; apply not_elem_of_nil].
Qed.

Lemma line_run_nodollar fc l ss :
  fc_ok fc -> pl_ok l -> line_run fc l ss -> Forall (Forall nodollar) ss.
Proof using.
  intros Hfc Hl Hr. destruct Hr as [ws | ws | ws | p fs Hn | p fs so ss Hso Hr].
  - constructor; [| constructor].
    exact (proj1 (pd_wl_line_shape (drop 1 ws) (lb_Forall_drop _ 1 ws (line_ok_wf ws Hl)))).
  - constructor; [exact dg_execL_nodollar | constructor].
  - constructor; constructor.
  - constructor; [bdec | constructor].
  - destruct Hl as (Hp & _ & _). pose proof (prod_content_shape fc p Hfc Hp) as [HL HL1].
    constructor.
    + apply (stage_out_nodollar fc _ (SProd p) so HL HL1); [| exact Hso].
      intros f Hf. injection Hf as Hf. subst p. exact Hp.
    + exact (sfx_run_nodollar _ _ _ _ _ _ HL HL1 Hr).
Qed.

(* below one wire with the panic line, a '$'-free run followed by the
   prompt starts with the panic line *)
Lemma cmp_panic_prefix (u Y Z : bytes) :
  ((u ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ Z)
   \/ (alt_panic ++ Z) `prefix_of` (u ++ u_prompt ++ Y)) ->
  alt_panic `prefix_of` u.
Proof using.
  intros Hcmp.
  assert (H5 : 5 <= length u).
  { destruct (decide (length u < 5)) as [Hlt | Hge]; [| lia]. exfalso.
    destruct (lookup_lt_is_Some_2 alt_panic (length u) ltac:(rewrite lb_panic_len; lia))
      as [b Hb].
    assert (H2 : (alt_panic ++ Z) !! (length u) = Some b)
      by (rewrite lookup_app_l; [exact Hb | rewrite lb_panic_len; lia]).
    pose proof (lb_cmp_at _ _ _ _ _ Hcmp (lb_dollar_at u Y) H2) as Heq.
    pose proof (Forall_lookup_1 _ _ _ _ lb_panic_nd Hb) as Hb'.
    unfold nodollar in Hb'. rewrite <- Heq in Hb'. apply Hb'. by vm_compute. }
  assert (Hp1 : u `prefix_of` (u ++ u_prompt ++ Y)) by (by exists (u_prompt ++ Y)).
  assert (Hp2 : alt_panic `prefix_of` (alt_panic ++ Z)) by (by exists Z).
  assert (Htot : u `prefix_of` alt_panic \/ alt_panic `prefix_of` u).
  { destruct Hcmp as [Hc | Hc].
    - assert (H1 : u `prefix_of` (alt_panic ++ Z)) by (etrans; [exact Hp1 | exact Hc]).
      exact (prefix_weak_total _ _ _ H1 Hp2).
    - assert (H1 : alt_panic `prefix_of` (u ++ u_prompt ++ Y)) by (etrans; [exact Hp2 | exact Hc]).
      exact (prefix_weak_total _ _ _ Hp1 H1). }
  destruct Htot as [Hu | Hu]; [| exact Hu].
  rewrite (prefix_length_eq u alt_panic Hu ltac:(rewrite lb_panic_len; lia)). reflexivity.
Qed.

(* a prefix of a word-line-shaped content that starts with the panic line
   is the whole content, and the content IS the panic line *)
Lemma panic_prefix_shape L c :
  lshape L -> c `prefix_of` L -> alt_panic `prefix_of` c -> L = alt_panic /\ c = L.
Proof using.
  intros [_ HL] HcL Hpc.
  assert (HpL : alt_panic `prefix_of` L) by (etrans; [exact Hpc | exact HcL]).
  assert (HL' : L = alt_panic).
  { destruct HL as [HnL | (v & Hv & ->)].
    - exfalso. apply HnL. apply (elem_of_prefix alt_panic); [| exact HpL].
      rewrite lb_panic_split. apply elem_of_app. right. by left.
    - rewrite lb_panic_split in HpL |- *.
      destruct (wl_raw_line_prefix_det _ v [] [] lb_fork_nonl Hv HpL) as [Hfv _].
      rewrite <- Hfv. reflexivity. }
  split; [exact HL' |].
  apply (prefix_length_eq c L HcL). rewrite HL'. exact (prefix_length _ _ Hpc).
Qed.

(* a merge of streams none of which starts inside the panic line does not
   start with it *)
Lemma nohd_no_panic ss b :
  merge_all ss b -> Forall (nohd alt_panic) ss -> ~ alt_panic `prefix_of` b.
Proof using.
  intros Hm HF Hp. destruct b as [| x b].
  - apply prefix_nil_inv in Hp. apply (f_equal (@length _)) in Hp.
    rewrite lb_panic_len in Hp. discriminate Hp.
  - apply (merge_all_head_nohd _ _ _ _ Hm HF).
    pose proof (prefix_lookup_Some _ _ _ _ alt_panic_head Hp) as Hx.
    change (Some x = Some (Z_to_bv 8 102)) in Hx.
    rewrite (inj Some _ _ Hx). exact (elem_of_list_lookup_2 _ _ _ alt_panic_head).
Qed.

(* ---- THE SHELL'S OWN ALTERNATIVES ARE BLOCKS of a line with runs ---- *)

(* a suffix every stage of which exits silently: nothing below a pipe
   vouches for anything *)
Lemma sfx_run_silent fc L fs win wc :
  fs <> [] -> sfx_run fc L fs win wc (replicate (length fs) []).
Proof using.
  intros Hne. revert win wc. induction fs as [| F fs IH]; intros win wc; [exfalso; exact (Hne eq_refl) |].
  destruct fs as [| F' fs'].
  - apply (sr_last fc L F win wc (MkSO [] (st_rd_dead (SLast F)) (st_wr_dead (SLast F)))).
    + apply so_silent.
    + cbn. destruct win; exact I.
  - cbn [length replicate].
    apply (sr_node fc L F F' fs' win wc (MkSO [] (st_rd_dead (SMid F)) (st_wr_dead (SMid F)))).
    + apply so_silent.
    + cbn. destruct win; exact I.
    + exact (IH ltac:(discriminate) _ _).
Qed.

(* one stream beside silent ones merges to itself *)
Lemma merge_all_nils (x : bytes) (k : nat) : merge_all (x :: replicate k []) x.
Proof using.
  induction x as [| y x IH].
  - apply ma_done. constructor; [reflexivity |]. apply Forall_replicate. reflexivity.
  - apply (ma_take _ 0 y x); [reflexivity | exact IH].
Qed.

Lemma plsafe_ok fc l a : pl_nz l -> plsafe l a -> plalt_ok fc l a.
Proof using.
  intros Hnz [-> | [-> | ->]]; [exact I | |].
  - destruct l as [ws | p [| F fs]]; [| destruct Hnz |].
    + exists [[]]. split; [apply lr_echo_silent | apply merge_all_one; reflexivity].
    + exists ([] :: replicate (length (F :: fs)) []).
      split; [| exact (merge_all_nils [] _)].
      apply (lr_node fc p (F :: fs) (MkSO [] (st_rd_dead (SProd p)) (st_wr_dead (SProd p)))).
      * apply so_silent.
      * exact (sfx_run_silent _ _ (F :: fs) _ _ ltac:(discriminate)).
  - destruct l as [ws | p [| F fs]]; [| destruct Hnz |].
    + exists [dg_execL]. split; [apply lr_echo_exec | apply merge_all_one; reflexivity].
    + exists (st_dg_exec (SProd p) :: replicate (length (F :: fs)) []).
      split; [| exact (merge_all_nils _ _)].
      apply (lr_node fc p (F :: fs)
               (MkSO (st_dg_exec (SProd p)) (st_rd_dead (SProd p)) (st_wr_dead (SProd p)))).
      * apply so_exec.
      * exact (sfx_run_silent _ _ (F :: fs) _ _ ltac:(discriminate)).
Qed.

(* AT AN ADMITTED LINE WITH RUNS the range condition is [plalt_ok] *)
Lemma pipes_lm_ok_iff fc adm s l a :
  adm l = true -> pl_nz l -> (lm_ok (pipes_lm fc adm) s l a <-> plalt_ok fc l a).
Proof using.
  intros Ha Hnz. cbn [pipes_lm lm_ok]. split.
  - intros [Hs | [_ Hok]]; [exact (plsafe_ok fc l a Hnz Hs) | exact Hok].
  - intros Hok. right. split; [exact Ha | exact Hok].
Qed.

Lemma pipes_lm_ok_run fc adm s l b :
  adm l = true -> pl_nz l -> (lm_ok (pipes_lm fc adm) s l (PLRun b) <-> line_blocks fc l b).
Proof using. intros Ha Hnz. exact (pipes_lm_ok_iff fc adm s l (PLRun b) Ha Hnz). Qed.

(* the exec diagnostic has a word line's shape *)
Lemma pl_exfb_shape l : lshape (pl_exfb l).
Proof using.
  destruct l as [ws | [ws | f] fs]; cbn [pl_exfb st_dg_exec].
  - exact (pd_wl_line_shape' dg_exec ltac:(bdec)).
  - exact (pd_wl_line_shape' dg_exec ltac:(bdec)).
  - exact (pd_wl_line_shape' dg_exec_cat ltac:(bdec)).
Qed.

(* THE BYTE SHAPE OF A BLOCK *)
Lemma pipes_block_shape fc adm l b :
  fc_ok fc -> adm_ok fc adm -> adm l = true -> pl_ok l -> line_blocks fc l b ->
  Forall nodollar b
  /\ (forall Y Z, ((b ++ u_prompt ++ Y) `prefix_of` (alt_panic ++ Z)
                   \/ (alt_panic ++ Z) `prefix_of` (b ++ u_prompt ++ Y)) -> b = alt_panic).
Proof using.
  intros Hfc Hadm Ha Hl (ss & Hr & Hm).
  destruct l as [ws | p fs].
  - (* an echo line: the line, the exec diagnostic, or nothing *)
    assert (Hsh : lshape b).
    { assert (Hwf : wl_wf ws) by exact (line_ok_wf ws Hl).
      inversion Hr; subst; apply merge_all_one in Hm; subst b.
      - exact (pd_wl_line_shape' (drop 1 ws) (lb_Forall_drop _ 1 ws Hwf)).
      - exact (pd_wl_line_shape' dg_exec ltac:(bdec)).
      - split; [constructor | left; apply not_elem_of_nil]. }
    destruct Hsh as [Hnd Hnl]. split; [exact Hnd |].
    intros Y Z Hcmp. exact (lb_out_eq_panic b Y Z Hnd Hnl Hcmp).
  - pose proof Hl as (Hp & Hn & _).
    pose proof (prod_content_shape fc p Hfc Hp) as HL.
    split; [exact (merge_all_forall _ ss b Hm (line_run_nodollar fc _ ss Hfc Hl Hr)) |].
    intros Y Z Hcmp. pose proof (cmp_panic_prefix b Y Z Hcmp) as Hpb.
    destruct (line_run_shape fc p fs ss (proj2 HL) Hr) as [HF | (ds & c & -> & Hds & Hc)].
    + exfalso. exact (nohd_no_panic _ _ Hm HF Hpb).
    + destruct Hpb as [r ->].
      destruct (merge_prefix_from alt_panic (ds ++ [c]) (length ds) c r Hm) as [Hpc _].
      { apply list_lookup_middle. reflexivity. }
      { intros i s Hne Hi. apply lookup_app_Some in Hi as [Hi | [Hge Hi]].
        - exact (Forall_lookup_1 _ _ _ _ Hds Hi).
        - apply list_lookup_singleton_Some in Hi as [Hi0 _]. lia. }
      destruct (panic_prefix_shape _ c HL Hc Hpc) as [HLp _].
      destruct (Hadm p fs Ha Hl HLp) as (ws & -> & ->).
      destruct (line_run_one fc ws _ Hr) as [HF | Hss].
      * exfalso. apply (nohd_no_panic _ _ Hm HF). by exists r.
      * rewrite Hss in Hm. apply merge2_shuf2, shuf2_nil_l in Hm.
        cbn [prod_content] in HLp. rewrite HLp in Hm. exact Hm.
Qed.

Lemma pl_body_bytes l : pl_ok l -> Forall psbyte (pl_body l).
Proof using.
  destruct l as [ws | p fs]; cbn [pl_ok pl_body]; intros Hok.
  - eapply Forall_impl; [exact (wl_body_bytes ws (line_ok_wf ws Hok)) | exact psbyte_of_body].
  - destruct Hok as (Hp & _ & HF & _). apply Forall_app. split.
    + eapply Forall_impl; [exact (prod_body_bytes p Hp) |].
      intros b [[Ha | ->] | ->];
        [left; left; left; exact Ha | right; reflexivity | left; left; right; reflexivity].
    + clear Hp. induction fs as [| F fs IH]; [constructor |].
      apply Forall_cons_1 in HF as [HF1 HF].
      rewrite FileDisc.suf_filts_cons, suf_filt_sep. apply Forall_app. split; [| exact (IH HF)].
      apply Forall_app. split.
      * unfold pl_sep. constructor; [left; left; right; reflexivity |].
        constructor; [left; right; reflexivity |].
        constructor; [left; left; right; reflexivity | constructor].
      * eapply Forall_impl; [exact (wl_body_bytes _ (FileDisc.filt_wf F HF1)) | exact psbyte_of_body].
Qed.

Lemma pl_body_short l : pl_ok l -> S (length (pl_body l)) < line_max.
Proof using.
  destruct l as [ws | p fs]; intros Hok.
  - pose proof (line_ok_len ws Hok) as H. rewrite wl_line_length in H. cbn [pl_body]. lia.
  - destruct Hok as (_ & _ & _ & H). exact H.
Qed.

(* ---- THE BYTES AFTER A PANIC LINE: init's next round ---- *)

(* init's round opens on '$' (the prompt alone) or 'i' (its own lines) *)
Lemma pro_of_head ps z :
  Forall (fun a => a < length pro_alts) ps -> pro_of ps !! 0 = Some z ->
  bv_unsigned z = 36%Z \/ bv_unsigned z = 105%Z.
Proof using.
  intros HF Hz. destruct ps as [| a ps]; [discriminate Hz |].
  apply Forall_cons_1 in HF as [Ha _].
  assert (Hpos : 0 < length (pro_alts !!! a)).
  { destruct (pro_alts !!! a) as [| y ys] eqn:Hy;
      [exfalso; exact (pro_alts_nonnil a Ha Hy) | cbn [length]; lia]. }
  rewrite pro_of_cons, (lookup_app_l _ _ 0 Hpos) in Hz.
  rewrite pro_alts_length in Ha.
  destruct a as [|[|[|[|a]]]]; [| | | | lia]; vm_compute in Hz; injection Hz as Hz; subst z;
    [left | right | right | right]; by vm_compute.
Qed.

(* ...so a byte that sits where that round starts is one of the two *)
Lemma pro_below_head ps W x t :
  Forall (fun a => a < length pro_alts) ps ->
  ((W = [] \/ pro_done ps) /\ (x :: t) `prefix_of` (pro_of ps ++ W))
  \/ (pro_done ps /\ (pro_of ps ++ W) `prefix_of` (x :: t)) ->
  bv_unsigned x = 36%Z \/ bv_unsigned x = 105%Z.
Proof using.
  intros HF Hb.
  assert (Hne : pro_of ps <> []).
  { intros He. destruct Hb as [[[-> | Hd] Hp] | [Hd Hp]].
    - rewrite He in Hp. cbn [app] in Hp. by apply prefix_nil_not in Hp.
    - assert (Hps : ps <> []) by (intros ->; by apply Exists_nil in Hd).
      pose proof (pro_of_pos ps HF Hps) as Hpos. rewrite He in Hpos. cbn [length] in Hpos. lia.
    - assert (Hps : ps <> []) by (intros ->; by apply Exists_nil in Hd).
      pose proof (pro_of_pos ps HF Hps) as Hpos. rewrite He in Hpos. cbn [length] in Hpos. lia. }
  assert (Hlen : 0 < length (pro_of ps)).
  { destruct (decide (length (pro_of ps) = 0)) as [H0 | H0];
      [exfalso; exact (Hne (nil_length_inv _ H0)) | lia]. }
  destruct (lookup_lt_is_Some_2 (pro_of ps) 0 Hlen) as [z Hz].
  assert (Hz' : (pro_of ps ++ W) !! 0 = Some z)
    by (rewrite lookup_app_l; [exact Hz | exact Hlen]).
  assert (Hzx : z = x).
  { destruct Hb as [[_ Hp] | [_ Hp]].
    - pose proof (prefix_lookup_Some (x :: t) _ 0 x eq_refl Hp) as H.
      rewrite Hz' in H. injection H as H. exact H.
    - pose proof (prefix_lookup_Some _ (x :: t) 0 z Hz' Hp) as H.
      cbn in H. injection H as H. symmetry. exact H. }
  subst z. exact (pro_of_head ps x HF Hz).
Qed.

(* an echo line's block is a word line's shape *)
Lemma echo_block_shape fc ws b :
  pl_ok (LEcho' ws) -> line_blocks fc (LEcho' ws) b -> lshape b.
Proof using.
  intros Hl (ss & Hr & Hm).
  assert (Hwf : wl_wf ws) by exact (line_ok_wf ws Hl).
  inversion Hr; subst; apply merge_all_one in Hm; subst b.
  - exact (pd_wl_line_shape' (drop 1 ws) (lb_Forall_drop _ 1 ws Hwf)).
  - exact (pd_wl_line_shape' dg_exec ltac:(bdec)).
  - split; [constructor | left; apply not_elem_of_nil].
Qed.

Lemma pipes_block_nodollar fc l b :
  fc_ok fc -> pl_ok l -> line_blocks fc l b -> Forall nodollar b.
Proof using.
  intros Hfc Hl Hb. destruct l as [ws | p fs].
  - exact (proj1 (echo_block_shape fc ws b Hl Hb)).
  - destruct Hb as (ss & Hr & Hm).
    exact (merge_all_forall _ ss b Hm (line_run_nodollar fc _ ss Hfc Hl Hr)).
Qed.

(* THE BYTE SHAPE OF A BLOCK BESIDE A PANIC: below one wire with the panic
   line and init's next round, a block IS the panic line.  No admission
   premise: the corner's [fork] then [cat: write error] is the panic line
   followed by a 'c', and init's round opens on '$' or 'i'. *)
Lemma pipes_block_below_panic fc l b Y ps W :
  fc_ok fc -> pl_ok l -> line_blocks fc l b ->
  Forall (fun x => x < length pro_alts) ps ->
  lm_below_panic b Y ps W -> b = alt_panic.
Proof using.
  intros Hfc Hl Hb Hps Hbp.
  pose proof (lm_below_panic_any b Y ps W Hbp) as Hcmp.
  destruct l as [ws | p fs].
  - destruct (echo_block_shape fc ws b Hl Hb) as [Hnd Hnl].
    exact (lb_out_eq_panic b Y _ Hnd Hnl Hcmp).
  - pose proof (pipes_block_nodollar fc _ b Hfc Hl Hb) as Hnd.
    destruct Hb as (ss & Hr & Hm).
    pose proof Hl as (Hp & _ & _).
    pose proof (prod_content_shape fc p Hfc Hp) as HL.
    pose proof (cmp_panic_prefix b Y _ Hcmp) as Hpb.
    destruct (line_run_shape_i fc p fs ss (proj2 HL) Hr) as [HF | (ds & c & -> & Hds & Hc)].
    + exfalso. exact (nohd_no_panic _ _ Hm (Forall_impl _ _ _ HF nohd_pan_i) Hpb).
    + destruct Hpb as [r ->].
      destruct (merge_prefix_from alt_panic (ds ++ [c]) (length ds) c r Hm) as [Hpc Hr'].
      { apply list_lookup_middle. reflexivity. }
      { intros i s Hne Hi. apply lookup_app_Some in Hi as [Hi | [Hge Hi]].
        - exact (nohd_pan_i _ (Forall_lookup_1 _ _ _ _ Hds Hi)).
        - apply list_lookup_singleton_Some in Hi as [Hi0 _]. lia. }
      destruct (panic_prefix_shape _ c HL Hc Hpc) as [HLp Hcl].
      assert (Hc0 : c = alt_panic) by (rewrite Hcl, HLp; reflexivity).
      destruct r as [| x r]; [by rewrite app_nil_r |]. exfalso.
      rewrite (insert_app_r_alt ds [c] (length ds) _ (Nat.le_refl _)) in Hr'.
      rewrite Nat.sub_diag, Hc0, drop_all in Hr'.
      (* the byte after the panic line is a diagnostic's first *)
      assert (Hxi : x ∉ pan_i).
      { apply (merge_all_head_nohd pan_i _ x r Hr').
        apply Forall_app. split; [exact Hds | constructor; [exact I | constructor]]. }
      assert (Hxd : nodollar x).
      { apply Forall_app in Hnd as [_ Hnd]. apply Forall_cons_1 in Hnd as [Hxd _]. exact Hxd. }
      (* ...and where init's round starts *)
      assert (Hx : bv_unsigned x = 36%Z \/ bv_unsigned x = 105%Z).
      { apply (pro_below_head ps W x (r ++ u_prompt ++ Y) Hps).
        unfold lm_below_panic in Hbp. rewrite <- !app_assoc in Hbp.
        destruct Hbp as [[HW Hp'] | [Hd Hp']]; apply prefix_app_inv in Hp';
          [left | right]; split; assumption. }
      destruct Hx as [Hx | Hx]; [exact (Hxd Hx) |].
      apply Hxi. unfold pan_i. apply elem_of_app. right. apply elem_of_list_singleton.
      apply bv_eq. rewrite Hx. by vm_compute.
Qed.

Theorem pipes_lm_laws_fc fc adm : fc_ok fc -> lm_laws (pipes_lm fc adm).
Proof using.
  intros Hfc. constructor;
    cbn [pipes_lm lm_ok lm_cont lm_merge lm_panic lm_term lm_line_ok lm_body_ok lm_of
         lm_st_ok lm_step].
  - intros b Hb. exact (proj1 (proj2 (pl_body_ok_line adm b Hb))).
  - intros s l a _ _ _. exact I.
  - intros s l a H. destruct a; [reflexivity | cbn in H; discriminate H | cbn in H; discriminate H].
  - intros a H. destruct a; [cbn in H; discriminate H | cbn in H; discriminate H | reflexivity].
  - intros s l a _ Hok Ht. destruct a as [| b | b]; [cbn in Ht; discriminate Ht | cbn in Ht; discriminate Ht |].
    apply (pipes_lm_ok_term fc adm s) in Hok as [Ha Hok].
    exists l, b. split; [exact Ha | split; [exact Hok | reflexivity]].
  - intros u' u Hp (l & b & Ha & Hok & Hu). exists l, b.
    split; [exact Ha | split; [exact Hok | etrans; [exact Hp | exact Hu]]].
  - intros s l a _ Hl Hok Hp Ht. destruct a as [| b | b];
      [cbn in Hp; discriminate Hp | | cbn in Ht; discriminate Ht].
    destruct Hok as [Hs | [_ Hok]].
    + (* the shell's own: the silent round, or the exec diagnostic *)
      assert (Hsh : lshape b).
      { destruct Hs as [Hq | [Hq | Hq]]; [discriminate Hq | injection Hq as -> | injection Hq as ->].
        - split; [constructor | left; apply not_elem_of_nil].
        - exact (pl_exfb_shape l). }
      destruct Hsh as [Hnd Hnl]. exists b. split; [reflexivity |].
      split; [exact Hnd |]. intros Y ps W _ Hcmp.
      exact (lb_out_eq_panic b Y _ Hnd Hnl (lm_below_panic_any b Y ps W Hcmp)).
    + exists b. split; [reflexivity | split; [exact (pipes_block_nodollar fc l b Hfc Hl Hok) |]].
      intros Y ps W Hps Hcmp. exact (pipes_block_below_panic fc l b Y ps W Hfc Hl Hok Hps Hcmp).
  - intros s l c Hc Ht s'. exists c. split; [exact Hc | exact Ht].
Qed.

Theorem pipes_lm_laws fc adm : fc_ok fc -> adm_ok fc adm -> lm_laws (pipes_lm fc adm).
Proof using. intros Hfc _. exact (pipes_lm_laws_fc fc adm Hfc). Qed.

Theorem pipes_lm_byte_laws fc adm : lm_byte_laws (pipes_lm fc adm).
Proof using.
  constructor; cbn [pipes_lm lm_body_ok lm_body_byte lm_panic lm_dec].
  - intros b Hb. destruct (pl_body_ok_line adm b Hb) as (_ & Hok & Hbeq). rewrite Hbeq.
    exact (pl_body_bytes _ Hok).
  - intros b Hb. destruct (pl_body_ok_line adm b Hb) as (_ & Hok & Hbeq). rewrite Hbeq.
    exact (pl_body_short _ Hok).
  - intros b Hb. destruct Hb as [[[Ha | ->] | ->] | ->].
    + destruct Ha as [H | [H | H]]; lia.
    + rewrite wl_sp_val. lia.
    + assert (Hbar : bv_unsigned wl_bar = 124%Z) by (vm_compute; reflexivity). rewrite Hbar. lia.
    + rewrite fn_dot_val. lia.
  - unfold plalt_of. rewrite decide_True; reflexivity.
Qed.

(* THE CONTENT FUNCTION of the pipeline application: no [cat f] *)
Lemma fc_none_ok : fc_ok (fun _ => None).
Proof using. intros f c H. discriminate H. Qed.

(* ---- THE ADMISSIONS ---- *)

(* the landed one-pipe application's lines: [echo ..] and [echo .. | cat] *)
Definition adm1 (l : pline') : bool :=
  match l with LEcho' _ => true | LPipes (PrEcho _) [FCat] => true | _ => false end.
(* every echo pipeline: THE PIPELINE APPLICATION'S ADMISSION (owner ruling
   2026-09-24: the user may type [echo fork | cat | cat]; its output need
   not be distinguishable from a panic) *)
Definition adm_echo (l : pline') : bool :=
  match l with LEcho' _ => true | LPipes (PrEcho _) fs => all_cats fs | _ => false end.
(* every echo pipeline but [echo fork | cat | cat ..]: what the laws
   asked before the ruling, kept for the demos *)
Definition adm_echo_safe (l : pline') : bool :=
  match l with
  | LEcho' _ => true
  | LPipes (PrEcho ws) fs =>
      all_cats fs && bool_decide (fs = [FCat] \/ wl_line (drop 1 ws) <> alt_panic)
  | _ => false
  end.

Lemma adm1_ok fc : adm_ok fc adm1.
Proof using.
  intros p fs Ha _ _. destruct p as [ws | f]; [| discriminate Ha].
  destruct fs as [| [| w] [| F fs]]; try discriminate Ha. exists ws. split; reflexivity.
Qed.

Lemma adm_echo_safe_ok fc : adm_ok fc adm_echo_safe.
Proof using.
  intros p fs Ha _ Hc. destruct p as [ws | f]; [| discriminate Ha].
  cbn [adm_echo_safe] in Ha. apply andb_true_iff in Ha as [_ Ha].
  apply bool_decide_eq_true in Ha. cbn [prod_content] in Hc.
  destruct Ha as [-> | Hne]; [exists ws; split; reflexivity | exfalso; exact (Hne Hc)].
Qed.

Corollary pipes_lm1_laws : lm_laws (pipes_lm (fun _ => None) adm1).
Proof using. exact (pipes_lm_laws _ _ fc_none_ok (adm1_ok _)). Qed.

Corollary pipes_lm_echo_safe_laws : lm_laws (pipes_lm (fun _ => None) adm_echo_safe).
Proof using. exact (pipes_lm_laws _ _ fc_none_ok (adm_echo_safe_ok _)). Qed.

(* THE PIPELINE APPLICATION'S MODEL: every echo pipeline, no [cat f] *)
Definition pipes_lmE : lmodel := pipes_lm (fun _ => None) adm_echo.

Corollary pipes_lm_echo_laws : lm_laws pipes_lmE.
Proof using. exact (pipes_lm_laws_fc _ adm_echo fc_none_ok). Qed.

(* DETERMINACY, as the line model's: two witnesses below one wire put the
   same bytes on it (they may still be two different runs: the bytes need
   not say which) *)
Definition pipes_sess_prefix_det fc adm (Hfc : fc_ok fc) (Hadm : adm_ok fc adm) :=
  lm_sess_prefix_det (pipes_lm fc adm) (pipes_lm_laws fc adm Hfc Hadm).

Definition pipes_echo_sess_prefix_det :=
  lm_sess_prefix_det pipes_lmE pipes_lm_echo_laws.

(* ---- [echo fork | cat | cat]: AN OUTPUT THAT OPENS ON THE PANIC LINE ---- *)

Definition ws_fork : list bytes := [cmd_echo; sb "fork"%string].
Definition l_fork2 : pline' := LPipes (PrEcho ws_fork) (cats 2).

Lemma l_fork2_ok : pl_ok l_fork2.
Proof using. bdec. Qed.

Lemma merge_all_block' ss i x u v :
  ss !! i = Some x -> merge_all (<[i := []]> ss) u -> v = x ++ u -> merge_all ss v.
Proof using.
  intros Hi Hm ->. apply (merge_all_block ss i x [] u); [rewrite app_nil_r; exact Hi | exact Hm].
Qed.

(* the corner at [echo fork | cat | cat]: the last cat printed the whole
   line, the middle cat's writer halted -- admitted by (B) *)
Lemma fork2_corner fc : line_blocks fc l_fork2 (alt_panic ++ cat_dg_write).
Proof using.
  exists [[]; cat_dg_write; alt_panic]. split.
  - apply (lr_node fc (PrEcho ws_fork) (cats 2) (MkSO [] None (Some (WrAll alt_panic)))).
    + change (prod_content fc (PrEcho ws_fork)) with alt_panic.
      apply so_echo. reflexivity.
    + change (prod_content fc (PrEcho ws_fork)) with alt_panic.
      apply (sr_node fc alt_panic FCat FCat [] (WrAll alt_panic) false
               (MkSO cat_dg_write (Some RdGone) (Some (WrHalt [])))).
      * apply so_mid_halt. apply prefix_nil.
      * exact I.
      * apply (sr_last fc alt_panic FCat (WrHalt []) true
                 (MkSO alt_panic (Some (RdEof alt_panic)) None)).
        -- apply so_last. reflexivity.
        -- split; reflexivity.
  - apply (merge_all_block' _ 2 alt_panic cat_dg_write); [reflexivity | | reflexivity].
    apply (merge_all_block' _ 1 cat_dg_write []); [reflexivity | | by rewrite app_nil_r].
    constructor. cbn. repeat constructor.
Qed.

(* ...admitted at the application's model, and on the wire it is the
   panic line followed by bytes init never prints after one: the laws
   hold ([pipes_lm_echo_laws]) because they only compare it with init's
   next round *)
Lemma pipes_lmE_fork2 :
  lm_ok pipes_lmE tt l_fork2 (PLRun (alt_panic ++ cat_dg_write))
  /\ lm_cont pipes_lmE tt l_fork2 (PLRun (alt_panic ++ cat_dg_write))
     = alt_panic ++ cat_dg_write ++ u_prompt.
Proof using.
  split; [right; split; [reflexivity | exact (fork2_corner _)] |].
  cbn [pipes_lmE pipes_lm lm_cont plcont]. by rewrite <- app_assoc.
Qed.

(* ===================================================================== *)
(*  6.  THE OUTCOMES ARE THE TREES' EXITS                                 *)
(*                                                                        *)
(*  Every exit [ProgTreePipes.reach_exit] finds for a stage's program at  *)
(*  its environment is a stage outcome of section 2: its console stream   *)
(*  is what the console device took (echo at a pipe has no descriptor 2, *)
(*  so it takes nothing; the last cat's sink IS the console), and its     *)
(*  reader / writer outcome is the kind its copy or pipe device ended in. *)
(*  The BYTES a pipe carried (the [D]s) are not the tree's to say -- the *)
(*  devices do not record them -- and come from the pipe protocol         *)
(*  (C4's [wr_final]/[rd_final]); every prefix of the line is admitted.   *)
(*  The exec failure and the argv[0] death are sh's and have no tree.    *)
(* ===================================================================== *)

Theorem echo_stage_of_exit fc (ws : list bytes) files (E' : penv) :
  reach_exit (pipe_env (DOutH [wl_line (drop 1 ws)]) files) (echo_tree ws) E' ->
  (E' = pipe_env (DOutH [[]]) files
   /\ stage_out fc (wl_line (drop 1 ws)) (SProd (PrEcho ws))
        (MkSO [] None (Some (WrAll (wl_line (drop 1 ws))))))
  \/ (E' = pipe_env DHalt files
      /\ forall D, D `prefix_of` wl_line (drop 1 ws) ->
           stage_out fc (wl_line (drop 1 ws)) (SProd (PrEcho ws)) (MkSO [] None (Some (WrHalt D)))).
Proof using.
  intros Hr. destruct (echo_pipe_exits ws _ files E' Hr) as [-> | ->].
  - left. split; [reflexivity | apply so_echo; reflexivity].
  - right. split; [reflexivity |]. intros D HD. apply so_echo_halt; [reflexivity | exact HD].
Qed.

(* a middle cat: copy device at a sink that may halt, the console owing
   nothing or the write diagnostic *)
Theorem cat_mid_stage_of_exit fc (L S : bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy flt_id true [] S []) [[]; cat_dg_write] files paths) (cat_tree [sb "cat"]) E' ->
  (E' = copy_env (DCopyEnd flt_id true []) [[]; cat_dg_write] files paths
   /\ forall D, D `prefix_of` L ->
        stage_out fc L (SMid FCat) (MkSO [] (Some (RdEof D)) (Some (WrAll D))))
  \/ ((exists S', E' = copy_env (DCopyHalt (Some S')) [[]] files paths)
      /\ forall D, D `prefix_of` L ->
           stage_out fc L (SMid FCat) (MkSO cat_dg_write (Some RdGone) (Some (WrHalt D)))).
Proof using.
  intros Hr. destruct (cat_copy_exits true S _ files paths E' Hr) as [-> | (_ & _ & S' & ->)].
  - left. split; [reflexivity |]. intros D HD. apply so_mid_copy. exact HD.
  - right. split; [by exists S' |]. intros D HD. apply so_mid_halt. exact HD.
Qed.

(* the last cat: copy device at the console, which never halts *)
Theorem cat_last_stage_of_exit fc (L S : bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy flt_id false [] S []) [[]] files paths) (cat_tree [sb "cat"]) E' ->
  E' = copy_env (DCopyEnd flt_id false []) [[]] files paths
  /\ forall D, D `prefix_of` L -> stage_out fc L (SLast FCat) (MkSO D (Some (RdEof D)) None).
Proof using.
  intros Hr. destruct (cat_copy_exits false S _ files paths E' Hr) as [-> | (Hf & _)];
    [| discriminate Hf].
  split; [reflexivity |]. intros D HD. apply so_last. exact HD.
Qed.

(* a middle grep (cut G3): the filter device at a sink that may halt.  It
   reads to end of file either way, prints nothing of its own, and owes
   [GrepTree.grep_out w] of what it read -- all of it, or (its reader
   gone) a prefix *)
Theorem grep_mid_stage_of_exit fc (w L S : bytes) (alts : list bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy (GrepFilt.flt_grep w) true [] S []) alts files paths)
             (GrepTree.grep_tree [sb "grep"%string; w]) E' ->
  [] ∈ alts
  /\ ((E' = copy_env (DCopyEnd (GrepFilt.flt_grep w) true []) alts files paths
       /\ forall D, D `prefix_of` L ->
            stage_out fc L (SMid (FGrep w))
              (MkSO [] (Some (RdEof D)) (Some (WrAll (GrepTree.grep_out w D)))))
      \/ (E' = copy_env (DCopyHalt None) alts files paths
          /\ forall D W, D `prefix_of` L -> W `prefix_of` GrepTree.grep_out w D ->
               stage_out fc L (SMid (FGrep w)) (MkSO [] (Some (RdEof D)) (Some (WrHalt W))))).
Proof using.
  intros Hr. destruct (GrepFilt.grep_filt_exits w true S alts files paths E' Hr) as [Ha [-> | [_ ->]]].
  - split; [exact Ha |]. left. split; [reflexivity |].
    intros D HD. exact (so_mid_f fc L (FGrep w) D HD).
  - split; [exact Ha |]. right. split; [reflexivity |].
    intros D W HD HW. exact (so_grep_halt fc L w D W HD HW).
Qed.

(* the last grep: the filter device at the console, which never halts *)
Theorem grep_last_stage_of_exit fc (w L S : bytes) (alts : list bytes) files paths (E' : penv) :
  reach_exit (copy_env (DCopy (GrepFilt.flt_grep w) false [] S []) alts files paths)
             (GrepTree.grep_tree [sb "grep"%string; w]) E' ->
  [] ∈ alts
  /\ E' = copy_env (DCopyEnd (GrepFilt.flt_grep w) false []) alts files paths
  /\ forall D, D `prefix_of` L ->
       stage_out fc L (SLast (FGrep w)) (MkSO (GrepTree.grep_out w D) (Some (RdEof D)) None).
Proof using.
  intros Hr. destruct (GrepFilt.grep_filt_exits w false S alts files paths E' Hr)
    as [Ha [-> | [Hf _]]]; [| discriminate Hf].
  split; [exact Ha |]. split; [reflexivity |].
  intros D HD. exact (so_last_f fc L (FGrep w) D HD).
Qed.

(* cat f at a pipe's write end, the file present with content [c] *)
Theorem catf_stage_of_exit fc (f c : bytes) (E' : penv) :
  fc f = Some c ->
  reach_exit (catf_env (DOutH [c]) [[]; cat_dg_open f; cat_dg_write] fc [f])
             (cat_tree [sb "cat"; f]) E' ->
  (pe_dev E' 0 = DOut [[]; cat_dg_open f; cat_dg_write] /\ pe_dev E' 1 = DOutH [[]]
   /\ stage_out fc c (SProd (PrCatF f)) (MkSO [] None (Some (WrAll c))))
  \/ (pe_dev E' 1 = DHalt /\ pe_dev E' 0 = DOut [[]]
      /\ forall D, D `prefix_of` c ->
           stage_out fc c (SProd (PrCatF f)) (MkSO cat_dg_write None (Some (WrHalt D))))
  \/ (pe_dev E' 0 = DOut [[]]
      /\ stage_out fc c (SProd (PrCatF f)) (MkSO (cat_dg_open f) None (Some WrNone))).
Proof using.
  intros Hf Hr.
  destruct (cat_file_pipe_exits f [c] _ fc E' Hr)
    as [(H0 & c' & A & Hc' & H1 & HA) | [(H1 & _ & H0) | (_ & _ & H0)]].
  - left. rewrite Hf in Hc'. injection Hc' as <-. split; [exact H0 |]. split.
    + rewrite H1. destruct HA as [[Hc0 ->] | (_ & a & Ha & _ & ->)].
      * rewrite Hc0. reflexivity.
      * apply elem_of_list_singleton in Ha. subst a. rewrite drop_all. reflexivity.
    + apply so_catf. exact Hf.
  - right; left. split; [exact H1 | split; [exact H0 |]].
    intros D HD. apply so_catf_halt; [exact Hf | exact HD].
  - right; right. split; [exact H0 | apply so_catf_open].
Qed.

(* ===================================================================== *)
(*  7.  n = 1: THE LANDED ONE-PIPE MODEL                                  *)
(* ===================================================================== *)

(* the landed lines, read as this model's *)
Definition ptr (l : pline) : pline' :=
  match l with
  | PipeDisc.LEcho ws => LEcho' ws
  | LPipe ws => LPipes (PrEcho ws) [FCat]
  end.

(* the landed alternatives, read as this model's: the block they print *)
Definition palt_to (l : pline) (a : palt) : plalt :=
  match a with
  | PEcho k =>
      match k with
      | 0 => PLRun (wl_line (drop 1 (pline_ws l)))
      | 1 => PLRun dg_execL
      | 3 => PLPanic
      | _ => PLRun []
      end
  | PRan => PLRun (wl_line (drop 1 (pline_ws l)))
  | PExecL => PLRun dg_execL
  | PExecR => PLRun dg_execR
  | PBoth sel => PLRun (pmerge sel dg_execL dg_execR)
  | PPipe => PLRun dg_pipe_b
  | PForkS sel => PLTerm (pmerge sel dg_execL alt_forkc)
  | PSilent => PLRun []
  end.

Lemma palt_to_cont l pa : palt_ok l pa -> plcont (palt_to l pa) = pcont l pa.
Proof using.
  destruct l as [ws | ws]; intros Hok.
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try contradiction.
    destruct k as [| [| [| [| k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try reflexivity.
    subst k. reflexivity.
Qed.

Lemma palt_to_panic l pa : palt_ok l pa -> plpanic (palt_to l pa) = palt_panic pa.
Proof using.
  destruct l as [ws | ws]; intros Hok.
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try contradiction.
    destruct k as [| [| [| [| k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try reflexivity.
    subst k. reflexivity.
Qed.

Lemma palt_to_term l pa : palt_ok l pa -> plterm (palt_to l pa) = palt_isforkS pa.
Proof using.
  destruct l as [ws | ws]; intros Hok.
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try contradiction.
    destruct k as [| [| [| [| k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try reflexivity.
    subst k. reflexivity.
Qed.

Local Ltac pick6 :=
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
        | right; right; right; right; right; reflexivity ].

(* THE RUNS OF [echo ws | cat], all six *)
Lemma line_run_one_iff fc ws ss :
  line_run fc (LPipes (PrEcho ws) [FCat]) ss <->
  ss = [dg_pipe_b] \/ ss = [dg_execL; dg_execR] \/ ss = [dg_execL; []]
  \/ ss = [[]; dg_execR] \/ ss = [[]; []] \/ ss = [[]; wl_line (drop 1 ws)].
Proof using.
  split.
  - intros H. remember (LPipes (PrEcho ws) [FCat]) as l eqn:Hl.
    destruct H as [ws0 | ws0 | ws0 | p fs Hn | p fs so ss Hso Hr]; try discriminate Hl.
    + left. reflexivity.
    + injection Hl as -> ->. cbn [prod_content prod_cat] in Hso, Hr.
      set (L := wl_line (drop 1 ws)) in Hso, Hr.
      remember [FCat] as m eqn:Hm in Hr. remember (wr_of so) as w0 eqn:Hw in Hr.
      remember false as b0 eqn:Hb in Hr.
      destruct Hr as [F win wc so1 Hso1 Hp | F F' fs' win wc | F F' fs' win wc so' ss' Hso' Hp Hr'];
        [| discriminate Hm | discriminate Hm].
      injection Hm as ->. subst win wc.
      destruct (stage_out_echo_inv _ _ _ _ Hso) as [-> | [-> | [[_ ->] | (D0 & _ & HD0 & ->)]]];
      destruct (stage_out_last_inv _ _ _ Hso1) as [-> | [-> | (D & HD & ->)]];
      cbn [so_cons so_rd so_wr rd_of wr_of pipe_pairB pipe_pair] in Hp |- *;
      try subst D; try pick6.
      destruct Hp as [Hf _]. discriminate Hf.
  - pose (L := wl_line (drop 1 ws)).
    assert (Hex : stage_out fc L (SProd (PrEcho ws)) (MkSO dg_execL None (Some WrNone)))
      by exact (so_exec fc L (SProd (PrEcho ws))).
    assert (Hsi : stage_out fc L (SProd (PrEcho ws)) (MkSO [] None (Some WrNone)))
      by exact (so_silent fc L (SProd (PrEcho ws))).
    assert (Hok : stage_out fc L (SProd (PrEcho ws)) (MkSO [] None (Some (WrAll L))))
      by (apply so_echo; reflexivity).
    assert (Rex : forall w, sfx_run fc L [FCat] w false [dg_execR]).
    { intros w. refine (sr_last fc L FCat w false (MkSO dg_execR (Some RdGone) None) _ _).
      - exact (so_exec fc L (SLast FCat)).
      - cbn. destruct w; exact I. }
    assert (Rsi : forall w, sfx_run fc L [FCat] w false [[]]).
    { intros w. refine (sr_last fc L FCat w false (MkSO [] (Some RdGone) None) _ _).
      - exact (so_silent fc L (SLast FCat)).
      - cbn. destruct w; exact I. }
    intros [-> | [-> | [-> | [-> | [-> | ->]]]]].
    + apply lr_pipe_fail. discriminate.
    + exact (lr_node fc (PrEcho ws) [FCat] _ _ Hex (Rex _)).
    + exact (lr_node fc (PrEcho ws) [FCat] _ _ Hex (Rsi _)).
    + exact (lr_node fc (PrEcho ws) [FCat] _ _ Hok (Rex _)).
    + exact (lr_node fc (PrEcho ws) [FCat] _ _ Hsi (Rsi _)).
    + refine (lr_node fc (PrEcho ws) [FCat] _ [L] Hok _).
      refine (sr_last fc L FCat (WrAll L) false (MkSO L (Some (RdEof L)) None) _ _).
      * apply so_last. reflexivity.
      * exact eq_refl.
Qed.

(* ---- a terminal block of [echo ws | cat] is a [PForkS] one ---- *)

Lemma prefix_take_eq (y d : bytes) : y `prefix_of` d -> y = take (length y) d.
Proof using. intros [k ->]. by rewrite take_app_length. Qed.

Lemma forks_sel (y x b d1 d2 : bytes) :
  y `prefix_of` d1 -> x `prefix_of` d2 -> shuf2 y x b ->
  exists sel, count_true sel <= length d1 /\ length sel - count_true sel <= length d2
              /\ b = pmerge sel d1 d2 /\ length sel = length b.
Proof using.
  intros Hy Hx Hs. destruct (proj1 (shuf2_pmerge y x b) Hs) as (sel & Hl & Hc & ->).
  exists sel. pose proof (prefix_length _ _ Hy). pose proof (prefix_length _ _ Hx).
  split; [lia |]. split; [lia |]. split.
  - rewrite (prefix_take_eq y d1 Hy), (prefix_take_eq x d2 Hx).
    apply pmerge_take_lr; lia.
  - rewrite pmerge_length; lia.
Qed.

Lemma line_term_one fc ws W s :
  line_term fc (LPipes (PrEcho ws) [FCat]) W s -> W = [dg_fork_b] /\ (s = dg_execL \/ s = []).
Proof using.
  intros H. remember (LPipes (PrEcho ws) [FCat]) as l eqn:Hl.
  destruct H as [p fs so Hn Hso | p fs so W s Hso Ht]; injection Hl as -> ->.
  - split; [reflexivity |].
    destruct (stage_out_echo_inv _ _ _ _ Hso) as [-> | [-> | [[_ ->] | (D0 & _ & HD0 & ->)]]];
      [left | right | right | right]; reflexivity.
  - exfalso. remember [FCat] as m eqn:Hm in Ht. destruct Ht; discriminate Hm.
Qed.

(* ---- the two directions of the n = 1 bridge, alternative by alternative *)

Lemma palt_to_ok fc l pa : palt_ok l pa -> plalt_ok fc (ptr l) (palt_to l pa).
Proof using.
  destruct l as [ws | ws]; intros Hok.
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok; try contradiction.
    destruct k as [| [| [| [| k]]]]; cbn [palt_to ptr pline_ws plalt_ok]; [| | | exact I | lia].
    + exists [wl_line (drop 1 ws)]. split; [apply lr_echo | apply merge_all_one; reflexivity].
    + exists [dg_execL]. split; [apply lr_echo_exec | apply merge_all_one; reflexivity].
    + exists [[]]. split; [apply lr_echo_silent | apply merge_all_one; reflexivity].
  - destruct pa as [k | | | | sel | | sel |]; cbn [palt_ok] in Hok;
      cbn [palt_to ptr pline_ws plalt_ok].
    + subst k. exact I.
    + exists [[]; wl_line (drop 1 ws)]. split; [apply line_run_one_iff; pick6 |].
      apply merge2_shuf2, shuf2_nil_l. reflexivity.
    + exists [dg_execL; []]. split; [apply line_run_one_iff; pick6 |].
      apply merge2_shuf2, shuf2_nil_r. reflexivity.
    + exists [[]; dg_execR]. split; [apply line_run_one_iff; pick6 |].
      apply merge2_shuf2, shuf2_nil_l. reflexivity.
    + exists [dg_execL; dg_execR]. split; [apply line_run_one_iff; pick6 |].
      apply merge2_shuf2, shuf2_pmerge. exists sel. destruct Hok as [H1 H2].
      split; [exact H1 | split; [exact H2 | reflexivity]].
    + exists [dg_pipe_b]. split; [apply line_run_one_iff; pick6 | apply merge_all_one; reflexivity].
    + (* the terminal round: the stray is echo's exec diagnostic *)
      destruct Hok as (Hne & H1 & H2).
      set (c := count_true sel). set (p1 := take c dg_execL).
      set (p2 := take (length sel - c) alt_forkc).
      assert (Hlc : c <= length sel) by exact (count_true_le sel).
      assert (Hu : pmerge sel dg_execL alt_forkc = pmerge sel p1 p2)
        by (symmetry; apply pmerge_take_lr; lia).
      assert (Hs : shuf2 p1 p2 (pmerge sel p1 p2)).
      { apply shuf2_pmerge. exists sel. unfold p1, p2. rewrite !length_take.
        split; [lia | split; [lia | reflexivity]]. }
      split.
      * intros Hn. apply (f_equal (@length _)) in Hn. rewrite pmerge_length in Hn; [| lia | lia].
        destruct sel; [exact (Hne eq_refl) | discriminate Hn].
      * exists (pmerge sel dg_execL alt_forkc ++ drop (length sel - c) alt_forkc).
        split; [| by exists (drop (length sel - c) alt_forkc)].
        exists [dg_fork_b], dg_execL, dg_fork_b, p1. split.
        { refine (lt_here fc (PrEcho ws) [FCat] (MkSO dg_execL None (Some WrNone)) _ _);
            [discriminate |].
          exact (so_exec fc _ (SProd (PrEcho ws))). }
        split; [apply merge_all_one; reflexivity |]. split; [apply prefix_take |].
        apply merge2_shuf2. rewrite Hu.
        change (dg_fork_b ++ u_prompt) with alt_forkc.
        rewrite <- (take_drop (length sel - c) alt_forkc) at 1. fold p2.
        apply shuf2_app_l. apply shuf2_comm. exact Hs.
    + exists [[]; []]. split; [apply line_run_one_iff; pick6 |].
      apply merge2_shuf2, shuf2_nil_l. reflexivity.
Qed.

Lemma palt_of_ok fc l a :
  plalt_ok fc (ptr l) a -> exists pa, palt_ok l pa /\ a = palt_to l pa.
Proof using.
  intros Hok. destruct a as [| b | b].
  - exists (PEcho 3). split; [| destruct l; reflexivity].
    destruct l; cbn [palt_ok]; [lia | reflexivity].
  - destruct Hok as (ss & Hr & Hm). destruct l as [ws | ws]; cbn [ptr] in Hr.
    + inversion Hr; subst; apply merge_all_one in Hm; subst b.
      * exists (PEcho 0). split; [cbn; lia | reflexivity].
      * exists (PEcho 1). split; [cbn; lia | reflexivity].
      * exists (PEcho 2). split; [cbn; lia | reflexivity].
    + apply line_run_one_iff in Hr as [-> | [-> | [-> | [-> | [-> | ->]]]]].
      * apply merge_all_one in Hm. subst b. exists PPipe. split; reflexivity.
      * apply merge2_shuf2, shuf2_pmerge in Hm as (sel & H1 & H2 & ->).
        exists (PBoth sel). split; [split; [exact H1 | exact H2] | reflexivity].
      * apply merge2_shuf2, shuf2_nil_r in Hm. subst b. exists PExecL. split; reflexivity.
      * apply merge2_shuf2, shuf2_nil_l in Hm. subst b. exists PExecR. split; reflexivity.
      * apply merge2_shuf2, shuf2_nil_l in Hm. subst b. exists PSilent. split; reflexivity.
      * apply merge2_shuf2, shuf2_nil_l in Hm. subst b. exists PRan. split; reflexivity.
  - destruct Hok as (Hne & b' & (W & s & Wm & sp & Ht & HW & Hsp & Hm) & Hb).
    destruct l as [ws | ws]; cbn [ptr] in Ht.
    + exfalso. inversion Ht.
    + destruct (line_term_one fc ws W s Ht) as [-> Hs].
      apply merge_all_one in HW. subst Wm.
      apply merge2_shuf2 in Hm. change (dg_fork_b ++ u_prompt) with alt_forkc in Hm.
      assert (Hsp' : sp `prefix_of` dg_execL).
      { destruct Hs as [-> | ->]; [exact Hsp | apply prefix_nil_inv in Hsp; subst sp; apply prefix_nil]. }
      destruct (shuf2_prefix _ _ _ _ Hm Hb) as (x & y & Hx & Hy & Hxy).
      destruct (forks_sel y x b dg_execL alt_forkc ltac:(etrans; [exact Hy | exact Hsp']) Hx
                  (shuf2_comm _ _ _ Hxy)) as (sel & H1 & H2 & -> & Hlen).
      exists (PForkS sel). split; [| reflexivity].
      split; [| split; [exact H1 | exact H2]].
      intros ->. apply Hne. destruct (pmerge [] dg_execL alt_forkc); [reflexivity | discriminate Hlen].
Qed.

(* THE n = 1 BRIDGE: at [echo ws | cat] the admitted alternatives are
   exactly the landed ones, read as the blocks they print, with the same
   continuation, the same panic bit and the same coverage-ending bit *)
Theorem pipes_one_iff fc adm s ws a :
  adm (LPipes (PrEcho ws) [FCat]) = true ->
  (lm_ok (pipes_lm fc adm) s (LPipes (PrEcho ws) [FCat]) a
   <-> exists pa, palt_ok (LPipe ws) pa /\ a = palt_to (LPipe ws) pa).
Proof using.
  intros Ha. rewrite (pipes_lm_ok_iff fc adm s _ a Ha I). split.
  - intros Hok. exact (palt_of_ok fc (LPipe ws) a Hok).
  - intros (pa & Hok & ->). exact (palt_to_ok fc (LPipe ws) pa Hok).
Qed.

Theorem pipes_echo_iff fc adm s ws a :
  adm (LEcho' ws) = true ->
  (lm_ok (pipes_lm fc adm) s (LEcho' ws) a
   <-> exists pa, palt_ok (PipeDisc.LEcho ws) pa /\ a = palt_to (PipeDisc.LEcho ws) pa).
Proof using.
  intros Ha. rewrite (pipes_lm_ok_iff fc adm s _ a Ha I). split.
  - intros Hok. exact (palt_of_ok fc (PipeDisc.LEcho ws) a Hok).
  - intros (pa & Hok & ->). exact (palt_to_ok fc (PipeDisc.LEcho ws) pa Hok).
Qed.

Theorem pipes_one_cont fc adm s l pa :
  palt_ok l pa ->
  lm_cont (pipes_lm fc adm) s (ptr l) (palt_to l pa) = pcont l pa
  /\ lm_panic (pipes_lm fc adm) (palt_to l pa) = palt_panic pa
  /\ lm_term (pipes_lm fc adm) (palt_to l pa) = palt_isforkS pa.
Proof using.
  intros Hok. cbn [pipes_lm lm_cont lm_panic lm_term].
  split; [exact (palt_to_cont l pa Hok) | split; [exact (palt_to_panic l pa Hok) | exact (palt_to_term l pa Hok)]].
Qed.

(* ---- the D4 guard: at the landed lines, what a coverage-ending
        alternative can have written is exactly [PipeDisc.pmergeable] ---- *)

Lemma pl_merge1_pmergeable fc u : pl_merge fc adm1 u <-> pmergeable u.
Proof using.
  split.
  - intros (l & b & Ha & Hok & Hu).
    destruct l as [ws | [ws | f] [| [| w] [| F fs]]]; cbn [adm1] in Ha; try discriminate Ha.
    + exfalso. destruct Hok as (_ & b' & (W & s & Wm & sp & Ht & _) & _). inversion Ht.
    + destruct (palt_of_ok fc (LPipe ws) (PLTerm b) Hok) as (pa & Hpa & Heq).
      destruct pa as [[| [| [| [| k]]]] | | | | sel | | sel |]; cbn [palt_to] in Heq;
        try discriminate Heq.
      injection Heq as ->. apply (pmergeable_prefix u _ Hu).
      exact (pmergeable_forkS (LPipe ws) sel Hpa).
  - intros Hm. apply shufb_shuf2 in Hm as (p1 & p2 & H1 & H2 & Hs).
    set (ws := [cmd_echo]).
    destruct u as [| x u'].
    + exists (LPipes (PrEcho ws) [FCat]), (pmerge sel_forkc dg_execL alt_forkc).
      split; [reflexivity | split; [| apply prefix_nil]].
      exact (palt_to_ok fc (LPipe ws) (PForkS sel_forkc) (palt_ok_forkS_old ws)).
    + destruct (forks_sel p1 p2 (x :: u') dg_execL alt_forkc H1 H2 Hs)
        as (sel & Hc1 & Hc2 & Hu & Hlen).
      exists (LPipes (PrEcho ws) [FCat]), (x :: u').
      split; [reflexivity | split; [| reflexivity]].
      assert (Hpa : palt_ok (LPipe ws) (PForkS sel)).
      { split; [intros ->; discriminate Hlen | split; [exact Hc1 | exact Hc2]]. }
      pose proof (palt_to_ok fc (LPipe ws) (PForkS sel) Hpa) as Hok.
      cbn [palt_to] in Hok. rewrite <- Hu in Hok. exact Hok.
Qed.

(* ---- the landed lines are this model's, at [adm1] ---- *)

(* the one-pipe application's model, as an instance of this one *)
Definition pipes_lm1 : lmodel := pipes_lm (fun _ => None) adm1.

Lemma suf_filts_1 : FileDisc.suf_filts [FCat] = suf_pipecat.
Proof using. vm_compute. reflexivity. Qed.

Lemma ptr_body l : pl_body (ptr l) = line_body l.
Proof using.
  destruct l as [ws | ws]; cbn [ptr pl_body line_body]; [reflexivity |].
  rewrite suf_filts_1. reflexivity.
Qed.

Lemma ptr_pl_ok l : pl_ok (ptr l) <-> pline_ok l.
Proof using.
  destruct l as [ws | ws]; [reflexivity |].
  pose proof (ptr_body (LPipe ws)) as E. cbn [ptr] in E.
  cbn [ptr pl_ok pline_ok prod_ok]. rewrite E. unfold line_bytes. rewrite length_app. cbn [length].
  split; [intros (H1 & _ & _ & H2); split; [exact H1 | lia]
         | intros [H1 H2]; split; [exact H1 |]].
  split; [discriminate | split; [constructor; [exact I | constructor] | lia]].
Qed.

Lemma ptr_adm1 l : adm1 (ptr l) = true.
Proof using. destruct l; reflexivity. Qed.

Lemma pl_of_adm1 b : pbody_ok b -> pl_of b = ptr (pline_of b).
Proof using.
  intros Hb. destruct (pbody_ok_line b Hb) as [Hok Hbeq].
  rewrite Hbeq at 1. rewrite <- ptr_body. apply pl_of_body. apply ptr_pl_ok. exact Hok.
Qed.

(* D3 is the same at both models *)
Lemma pbody_ok_adm1 b : pbody_ok b <-> pl_body_ok adm1 b.
Proof using.
  split.
  - intros Hb. destruct (pbody_ok_line b Hb) as [Hok Hbeq]. rewrite Hbeq, <- ptr_body.
    apply pl_body_ok_of; [apply ptr_adm1 | apply ptr_pl_ok; exact Hok].
  - intros Hb. destruct (pl_body_ok_line adm1 b Hb) as (Ha & Hok & Hbeq).
    rewrite Hbeq. revert Ha Hok.
    destruct (pl_of b) as [ws | [ws | f] [| [| w] [| F fs]]]; intros Ha Hok; cbn [adm1] in Ha;
      try discriminate Ha.
    + exact (pbody_ok_of (PipeDisc.LEcho ws) Hok).
    + change (pbody_ok (pl_body (ptr (LPipe ws)))). rewrite ptr_body.
      apply pbody_ok_of. apply ptr_pl_ok. exact Hok.
Qed.

(* an admitted reading of ANY body is the landed reading of it *)
Lemma pl_of_adm1_any b : adm1 (pl_of b) = true -> pl_of b = ptr (pline_of b).
Proof using.
  intros Ha. destruct (decide (pbody_ok b)) as [Hb | Hb]; [exact (pl_of_adm1 b Hb) |].
  assert (Hp : parse_pline b = None).
  { destruct (parse_pline b) as [l |] eqn:E; [| reflexivity].
    exfalso. apply Hb. exists l. exact E. }
  assert (Hq : pl_parse b = None).
  { destruct (pl_parse b) as [l |] eqn:E; [| reflexivity].
    exfalso. apply Hb. apply pbody_ok_adm1. unfold pl_body_ok. rewrite E.
    unfold pl_of in Ha. rewrite E in Ha. exact Ha. }
  unfold pl_of, pline_of. rewrite Hq, Hp. reflexivity.
Qed.

(* ---- ONE ROUND, READ AT BOTH MODELS ---- *)

(* the landed code [c] and this model's [c'] name the same block at [b] *)
Definition corr (b : bytes) (c c' : nat) : Prop :=
  palt_ok (pline_of b) (palt_of c)
  /\ plalt_of c' = palt_to (pline_of b) (palt_of c)
  /\ pl_of b = ptr (pline_of b).

Lemma corr_cont b c c' :
  corr b c c' ->
  lm_panic pipe_lm (lm_dec pipe_lm c) = lm_panic pipes_lm1 (lm_dec pipes_lm1 c')
  /\ (forall s s', lm_cont pipe_lm s (lm_of pipe_lm b) (lm_dec pipe_lm c)
                   = lm_cont pipes_lm1 s' (lm_of pipes_lm1 b) (lm_dec pipes_lm1 c')).
Proof using.
  intros (Hok & Hc & _). cbn [pipe_lm pipes_lm1 pipes_lm lm_panic lm_dec lm_cont lm_of].
  rewrite Hc. split; [symmetry; exact (palt_to_panic _ _ Hok) |].
  intros _ _. symmetry. exact (palt_to_cont _ _ Hok).
Qed.

Lemma corr_ok s b c c' :
  corr b c c' -> lm_ok pipes_lm1 s (lm_of pipes_lm1 b) (lm_dec pipes_lm1 c').
Proof using.
  intros (Hok & Hc & Hof). cbn [pipes_lm1 pipes_lm lm_ok lm_of lm_dec].
  rewrite Hof, Hc. right. split; [apply ptr_adm1 | exact (palt_to_ok _ _ _ Hok)].
Qed.

Lemma adm1_nz l : adm1 l = true -> pl_nz l.
Proof using. destruct l as [ws | [ws | f] [| [| w] [| F fs]]]; cbn; done. Qed.

(* ...at a line the landed application admits: the shell's own
   alternatives at a line it does not admit have no landed twin *)
Lemma corr_of_ok s b c' :
  adm1 (pl_of b) = true ->
  lm_ok pipes_lm1 s (lm_of pipes_lm1 b) (lm_dec pipes_lm1 c') -> exists c, corr b c c'.
Proof using.
  intros Ha Hok0. cbn [pipes_lm1 lm_of lm_dec] in Hok0.
  apply (pipes_lm_ok_iff _ _ s _ _ Ha (adm1_nz _ Ha)) in Hok0 as Hok.
  pose proof (pl_of_adm1_any b Ha) as Hof. rewrite Hof in Hok.
  destruct (palt_of_ok _ _ _ Hok) as (pa & Hpa & Heq).
  exists (palt_code pa). unfold corr. rewrite palt_of_code.
  split; [exact Hpa | split; [exact Heq | exact Hof]].
Qed.

Lemma lm_pro_idx_cross (M1 M2 : lmodel) cs1 cs2 q :
  (forall i, i < q -> lm_panic M1 (lm_at M1 cs1 i) = lm_panic M2 (lm_at M2 cs2 i)) ->
  lm_pro_idx M1 cs1 q = lm_pro_idx M2 cs2 q.
Proof using.
  induction q as [| q IH]; intros H; [reflexivity |]. cbn [lm_pro_idx].
  rewrite IH by (intros i Hi; apply H; lia). rewrite (H q ltac:(lia)). reflexivity.
Qed.

(* two models' sessions agree where every round's panic bit and
   continuation agree *)
Lemma lm_sess_cross (M1 M2 : lmodel) (s1 : lm_st M1) (s2 : lm_st M2) ps cs1 cs2 I :
  (forall i, i < nlines I ->
     lm_panic M1 (lm_at M1 cs1 i) = lm_panic M2 (lm_at M2 cs2 i)
     /\ lm_cont M1 (lm_upto M1 cs1 s1 (bodies_of I) i) (lm_of M1 (bodies_of I !!! i)) (lm_at M1 cs1 i)
        = lm_cont M2 (lm_upto M2 cs2 s2 (bodies_of I) i) (lm_of M2 (bodies_of I !!! i))
            (lm_at M2 cs2 i)) ->
  lm_sess M1 ps cs1 s1 I = lm_sess M2 ps cs2 s2 I.
Proof using.
  intros H. unfold lm_sess, lm_seq. f_equal. f_equal. f_equal.
  apply list_fmap_ext. intros k x Hk. apply lookup_seq in Hk as [-> Hk]. cbn [Nat.add].
  destruct (H k Hk) as [Hp Hc]. unfold lm_blk, lm_cont_at.
  rewrite Hc, Hp, (lm_pro_idx_cross M1 M2 cs1 cs2 k); [reflexivity |].
  intros i Hi. apply (H i). lia.
Qed.

Lemma corr_panics cs cs' J q :
  q <= nlines J ->
  (forall i, i < nlines J -> corr (bodies_of J !!! i) (cs !!! i) (cs' !!! i)) ->
  lm_pro_idx pipe_lm cs q = lm_pro_idx pipes_lm1 cs' q.
Proof using.
  intros Hq H. apply lm_pro_idx_cross. intros i Hi.
  exact (proj1 (corr_cont _ _ _ (H i ltac:(lia)))).
Qed.

Lemma corr_sess ps cs cs' J :
  (forall i, i < nlines J -> corr (bodies_of J !!! i) (cs !!! i) (cs' !!! i)) ->
  lm_sess pipe_lm ps cs tt J = lm_sess pipes_lm1 ps cs' tt J.
Proof using.
  intros H. apply lm_sess_cross. intros i Hi. destruct (corr_cont _ _ _ (H i Hi)) as [Hp Hc].
  split; [exact Hp | apply Hc].
Qed.

(* the landed resolution, read as this model's *)
Definition cs_to (I : list (bv 8)) (cs : list nat) : list nat :=
  (fun i => plalt_code (palt_to (pline_of (bodies_of I !!! i)) (palt_of (cs !!! i))))
    <$> seq 0 (length cs).

Lemma cs_to_length I cs : length (cs_to I cs) = length cs.
Proof using. unfold cs_to. rewrite length_fmap, length_seq. reflexivity. Qed.

Lemma corr_cs_to I cs i :
  disc_input_p I -> alts_ok_p I cs -> i < nlines I ->
  corr (bodies_of I !!! i) (cs !!! i) (cs_to I cs !!! i).
Proof using.
  intros Hd Hao Hi. pose proof (alts_ok_p_length _ _ Hao) as Hlen.
  split; [exact (alts_ok_p_at I cs i Hao Hi) | split].
  - unfold cs_to.
    rewrite (list_lookup_total_correct _ i
               (plalt_code (palt_to (pline_of (bodies_of I !!! i)) (palt_of (cs !!! i))))).
    + apply plalt_of_code.
    + rewrite list_lookup_fmap, lookup_seq_lt; [reflexivity | lia].
  - apply pl_of_adm1. unfold nlines in Hi.
    destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
    rewrite (list_lookup_total_correct _ _ _ Hb). exact (disc_input_p_body I i b Hd Hb).
Qed.

Lemma alts_ok_of_corr I (cs' cs : list nat) :
  length cs' = nlines I ->
  (forall i, i < nlines I -> corr (bodies_of I !!! i) (cs !!! i) (cs' !!! i)) ->
  lm_alts_ok pipes_lm1 tt I cs'.
Proof using.
  intros Hlen H. apply (lm_alts_ok_nostate pipes_lm1 tt I cs' (fun _ _ _ _ Hx => Hx)).
  apply Forall2_same_length_lookup_2.
  { rewrite length_fmap, Hlen. reflexivity. }
  intros i l c Hl Hc. rewrite list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate Hl]. injection Hl as <-.
  assert (Hi : i < nlines I) by exact (lookup_lt_Some _ _ _ Hb).
  pose proof (H i Hi) as Hcr.
  rewrite (list_lookup_total_correct _ _ _ Hb), (list_lookup_total_correct _ _ _ Hc) in Hcr.
  exact (corr_ok tt _ _ _ Hcr).
Qed.

(* the rounds a prefix of the input has are the input's own *)
Lemma bodies_done_in (p seg : list mobs) i :
  p ∈ in_pres seg -> i < nlines (done_of (ins p)) ->
  i < nlines (ins seg) /\ bodies_of (done_of (ins p)) !!! i = bodies_of (ins seg) !!! i.
Proof using.
  intros Hp Hi.
  assert (Hple : ins p `prefix_of` ins seg)
    by (apply ins_prefix; exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp)).
  rewrite nlines_done in Hi. unfold nlines in Hi. rewrite bodies_of_done.
  destruct (lookup_lt_is_Some_2 (bodies_of (ins p)) i Hi) as [b Hb].
  pose proof (prefix_lookup_Some _ _ _ _ Hb (bodies_of_prefix _ _ Hple)) as Hb'.
  split; [exact (lookup_lt_Some _ _ _ Hb') |].
  rewrite (list_lookup_total_correct _ _ _ Hb), (list_lookup_total_correct _ _ _ Hb'). reflexivity.
Qed.

(* THE LANDED DISCIPLINE IS THIS MODEL'S, at [adm1] *)
Lemma disc_seg_p'_ps seg : disc_seg_p' seg -> lm_disc_seg' pipes_lm1 tt seg.
Proof using.
  intros [Hdi (ps & cs & Hao & Hd4 & Hall)].
  pose proof (alts_ok_p_length _ _ Hao) as Hlen.
  assert (Hcorr : forall i, i < nlines (ins seg) ->
                    corr (bodies_of (ins seg) !!! i) (cs !!! i) (cs_to (ins seg) cs !!! i))
    by (intros i Hi; exact (corr_cs_to _ cs i Hdi Hao Hi)).
  split.
  - destruct Hdi as (Hb & Hr & Hs). unfold lm_disc_input.
    cbn [pipes_lm1 pipes_lm lm_body_ok lm_body_byte].
    split; [| split; [eapply Forall_impl; [exact Hr | intros b Hb'; by left] | exact Hs]].
    eapply Forall_impl; [exact Hb |]. intros b. apply pbody_ok_adm1.
  - exists ps, (cs_to (ins seg) cs). split; [| split].
    + apply (alts_ok_of_corr _ _ cs); [rewrite cs_to_length; exact Hlen | exact Hcorr].
    + (* D4 *)
      intros i Hi (c & Hc & Ht) Hm.
      pose proof (Hcorr i Hi) as Hcr. destruct Hcr as (Hpa & Hc' & Hof).
      apply (d4_p_at cs (ins seg) i Hd4 Hi).
      * change (plsafe (pl_of (bodies_of (ins seg) !!! i)) c
                \/ (adm1 (pl_of (bodies_of (ins seg) !!! i)) = true
                    /\ plalt_ok (fun _ => None) (pl_of (bodies_of (ins seg) !!! i)) c)) in Hc.
        change (plterm c = true) in Ht.
        destruct Hc as [Hs | [_ Hok]].
        { exfalso. destruct Hs as [Hq | [Hq | Hq]]; rewrite Hq in Ht; discriminate Ht. }
        rewrite Hof in Hok.
        destruct (palt_of_ok _ _ _ Hok) as (pa & Hpa' & ->).
        rewrite (palt_to_term _ _ Hpa') in Ht.
        exact (palt_ok_isforkS_pipe _ _ Hpa' Ht).
      * change (pl_merge (fun _ => None) adm1 (plcont (plalt_of (cs_to (ins seg) cs !!! i)))) in Hm.
        rewrite Hc', (palt_to_cont _ _ Hpa) in Hm.
        exact (proj1 (pl_merge1_pmergeable _ _) Hm).
    + intros p Hp. destruct (Hall p Hp) as [[Hps Hidx] Hpt].
      assert (Hcd : forall i, i < nlines (done_of (ins p)) ->
                      corr (bodies_of (done_of (ins p)) !!! i) (cs !!! i)
                           (cs_to (ins seg) cs !!! i)).
      { intros i Hi. destruct (bodies_done_in p seg i Hp Hi) as [Hi' Heq].
        exact (eq_ind _ (fun b => corr b (cs !!! i) (cs_to (ins seg) cs !!! i))
                 (Hcorr i Hi') _ (eq_sym Heq)). }
      split.
      * split; [exact Hps |].
        rewrite <- (corr_panics cs (cs_to (ins seg) cs) (done_of (ins p)) (nlines (ins p)));
          [| rewrite nlines_done; lia | exact Hcd].
        rewrite <- pro_idx_p_lm. exact Hidx.
      * unfold lm_disc_pt. rewrite <- (corr_sess ps cs _ _ Hcd), <- sessp_lm. exact Hpt.
Qed.

Theorem disc_p_disc_ps h : disc_p h -> lm_disc pipes_lm1 h.
Proof using.
  intros Hd. unfold lm_disc. eapply Forall_impl; [exact Hd |]. intros seg Hs.
  exists tt. split; [exact I | exact (disc_seg_p'_ps seg Hs)].
Qed.

Lemma nat_choice_list (P : nat -> nat -> Prop) (n : nat) :
  (forall i, i < n -> exists c, P i c) ->
  exists cs, length cs = n /\ forall i, i < n -> P i (cs !!! i).
Proof using.
  induction n as [| n IH]; intros H.
  - exists []. split; [reflexivity | intros i Hi; lia].
  - destruct IH as (cs & Hl & Hc); [intros i Hi; apply H; lia |].
    destruct (H n ltac:(lia)) as [c Hcn].
    exists (cs ++ [c]). split; [rewrite length_app, Hl; cbn [length]; lia |].
    intros i Hi. destruct (decide (i < n)) as [Hlt | Hge].
    + rewrite lookup_total_app_l by lia. exact (Hc i Hlt).
    + assert (i = n) as -> by lia. rewrite lookup_total_app_r by lia.
      rewrite Hl, Nat.sub_diag. exact Hcn.
Qed.

(* THIS MODEL'S CLAIM IS THE LANDED ONE, at [adm1] *)
(* at a segment whose lines the landed application admits (the
   discipline's [lm_disc_input] gives it) *)
Theorem good_out_ps_good_out_p seg :
  Forall (fun b => adm1 (pl_of b) = true) (bodies_of (ins seg)) ->
  lm_good_out pipes_lm1 tt seg -> good_out_p seg.
Proof using.
  intros Hadm (ps & cs' & [Hps Hidx] & Hao & Hout).
  assert (Hch : forall i, i < nlines (ins seg) ->
                  exists c, corr (bodies_of (ins seg) !!! i) c (cs' !!! i)).
  { intros i Hi. eapply corr_of_ok; [| exact (lm_alts_ok_at pipes_lm1 _ _ _ i Hao Hi)].
    apply (Forall_lookup_1 _ _ i _ Hadm). apply list_lookup_lookup_total_lt. exact Hi. }
  destruct (nat_choice_list _ _ Hch) as (cs & Hlen & Hcs).
  exists ps, cs. split; [split; [exact Hps |] | split].
  - rewrite pro_idx_p_lm, (corr_panics cs cs' (ins seg) (nlines (ins seg))); [exact Hidx | lia | exact Hcs].
  - unfold alts_ok_p. apply Forall2_same_length_lookup_2.
    { unfold plines_of. rewrite length_fmap, Hlen. reflexivity. }
    intros i l c Hl Hc. unfold plines_of in Hl. rewrite list_lookup_fmap in Hl.
    destruct (bodies_of (ins seg) !! i) as [b |] eqn:Hb; [| discriminate Hl]. injection Hl as <-.
    assert (Hi : i < nlines (ins seg)) by exact (lookup_lt_Some _ _ _ Hb).
    destruct (Hcs i Hi) as (Hpa & _ & _).
    rewrite (list_lookup_total_correct _ _ _ Hb), (list_lookup_total_correct _ _ _ Hc) in Hpa.
    exact Hpa.
  - rewrite sessp_lm, (corr_sess ps cs cs' (ins seg) Hcs). exact Hout.
Qed.
