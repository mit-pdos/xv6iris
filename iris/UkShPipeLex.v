(* ===================================================================== *)
(* UkShPipeLex.v -- THE PIPE LINE'S LEXICAL MODEL, lane SH-PARSE-PIPE     *)
(* (design/app-pipe.md SS1 and SS5.1).                                     *)
(*                                                                        *)
(*     echo w1 ... wn | cat                                               *)
(*                                                                        *)
(* is the PIPELINE application's second line shape.  Positionally it is    *)
(* the FILE application's redirect line with '>' replaced by '|' and the   *)
(* file name by the right command's single word, so this file is           *)
(* [UkShParseSym] SS2-SS4 and [UkShRedirLine] SS3 at the other symbol byte  *)
(* -- and that is the first finding: NOTHING in the token model, the two   *)
(* scans or the tokenization had to be generalised again.  What is new     *)
(* here is only                                                           *)
(*                                                                        *)
(*   - the byte: [ushq_bar] = '|' = 124, a symbol like '>' but with NO     *)
(*     lookahead (sh's [gettoken] has a '>>' case and no '||' case), so    *)
(*     the pipe shape carries NO not-doubled side condition  where        *)
(*     [UkShParseSym.ushs_redir] needs two;                               *)
(*   - ONE premise for gettoken covering BOTH symbols ([ushq_sym_ok]),     *)
(*     which [UkShParseSym.ushs_gt_ok] implies -- the walk in              *)
(*     [UkShPipeTok] is stated at it and the landed '>'-only walk          *)
(*     ([UkShRedirGtk.wp_kshp_gettoken_sym]) is its instance;              *)
(*   - the RIGHT command's tokens.  The left command's argument list is    *)
(*     ECHO'S OWN ([LineWords.wl_toks ws], SH-LEX-REDIR's ruling 1,        *)
(*     verbatim: below the symbol the buffer is echo's line with its       *)
(*     newline replaced by a blank, and neither scan can tell those        *)
(*     apart), and the right command's is one token measured by the SAME   *)
(*     induction ([UShLexRedir.ushs_toks_tail]) at the line's own          *)
(*     newline.  So the pipe line's LEXABILITY costs no new mathematics    *)
(*     at all: [ush_line_toks_holds_pipe] below is a theorem from          *)
(*     [EchoDisc.line_ok] and nothing else, exactly as obligation 13 was.  *)
(*                                                                        *)
(* Iris-free, and a leaf: nothing in the tree recompiles because of it.    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List String.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.
Require Import LineWords.
Require Import EchoDisc.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import RefParse.
Require Import UkShWords.
Require Import UkShRedirLine.
Require Import UShLexRedir.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* §1 THE BYTE                                                            *)
(* ===================================================================== *)

Definition ushq_bar : bv 8 := Z_to_bv 8 124.

Lemma ushq_bar_val : bv_unsigned ushq_bar = 124.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushq_bar_sym : ushp_is_sym ushq_bar = true.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushq_bar_not_ws : ushp_is_ws ushq_bar = false.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushq_bar_not_nul : ushq_bar <> ubyte0.
Proof using. vm_compute. discriminate. Qed.

(* the two symbol bytes are different, which is what keeps the '>' arm of
   gettoken's switch refuted on a pipe line and vice versa *)
Lemma ushq_bar_not_gt : ushq_bar <> ushs_gt.
Proof using. vm_compute. discriminate. Qed.

Lemma ushq_ws_not_bar (b : bv 8) : ushp_is_ws b = true -> b <> ushq_bar.
Proof using.
  intros Hws ->. rewrite ushq_bar_not_ws in Hws. discriminate.
Qed.


(* ===================================================================== *)
(* §2 THE LINE MODEL: AT MOST ONE SYMBOL BYTE, AND IT IS A '|'            *)
(*                                                                        *)
(* [UkShParseSym.ushs_one] at the other byte.  The two are DELIBERATELY   *)
(* separate predicates and not one predicate with the byte a parameter:   *)
(* the landed one is in landed statements, and a shared parameter would   *)
(* move every one of them.  What IS shared is everything below §4 --      *)
(* the scans, the token model, the tokenization -- because none of those  *)
(* ever mentions which symbol byte stopped them.                          *)
(* ===================================================================== *)

Definition ushq_one (len : nat) (f : nat -> bv 8) (o : option nat) : Prop :=
  (forall j : nat, (j < len)%nat -> ushp_is_sym (f j) = true -> o = Some j)
  /\ (forall p : nat, o = Some p -> (p < len)%nat /\ f p = ushq_bar).

Lemma ushq_one_none (len : nat) (f : nat -> bv 8) :
  ushq_one len f None <-> ushp_no_symbols len f.
Proof using.
  split.
  - intros [ H1 _ ] j Hj.
    destruct (ushp_is_sym (f j)) eqn:E; [ | reflexivity ].
    exfalso. discriminate (H1 j Hj E).
  - intro H. split; [ | intros p Hp; discriminate Hp ].
    intros j Hj Hs. rewrite (H j Hj) in Hs. discriminate.
Qed.

Lemma ushq_one_some_at (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_one len f (Some p) -> (p < len)%nat /\ f p = ushq_bar.
Proof using. intros [ _ H ]. exact (H p eq_refl). Qed.

Lemma ushq_one_some_off (len : nat) (f : nat -> bv 8) (p j : nat) :
  ushq_one len f (Some p) -> (j < len)%nat -> j <> p ->
  ushp_is_sym (f j) = false.
Proof using.
  intros [ H1 _ ] Hj Hne.
  destruct (ushp_is_sym (f j)) eqn:E; [ | reflexivity ].
  exfalso. apply Hne. injection (H1 j Hj E) as He. exact (eq_sym He).
Qed.

(* the prefix below the symbol is symbol-free, so every landed stage-4
   lemma about it applies unchanged *)
Lemma ushq_one_nosym_below (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_one len f (Some p) -> ushp_no_symbols p f.
Proof using.
  intros Hone j Hj.
  destruct (ushq_one_some_at len f p Hone) as [ Hp _ ].
  exact (ushq_one_some_off len f p j Hone ltac:(lia) ltac:(lia)).
Qed.


(* ===================================================================== *)
(* §3 THE CANONICAL PIPE SHAPE                                            *)
(*                                                                        *)
(*   ... w   |   r \n                                                     *)
(*         ^p                                                             *)
(* one blank at [p-1], one blank at [p+1], the right command's word is    *)
(* the run [[S (S p), e)] and everything from [e] to the end of the line  *)
(* is blank (the newline [gets] kept).  design/app-pipe.md §1: one blank  *)
(* each side of the '|', the right command a single word.                 *)
(* ===================================================================== *)

Definition ushq_pipe (len : nat) (f : nat -> bv 8) (p e : nat) : Prop :=
  ushq_one len f (Some p)
  /\ (0 < p)%nat
  /\ ushp_is_ws (f (p - 1)%nat) = true
  /\ ushp_is_ws (f (S p)) = true
  /\ (S (S p) < e)%nat
  /\ (e < len)%nat
  /\ (forall j : nat, (S (S p) <= j < e)%nat -> ushp_is_ws (f j) = false)
  /\ (forall j : nat, (e <= j < len)%nat -> ushp_is_ws (f j) = true).

Lemma ushq_pipe_one (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushq_one len f (Some p).
Proof using. by intros (H & _ & _ & _ & _ & _ & _ & _). Qed.

Lemma ushq_pipe_bar (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> f p = ushq_bar.
Proof using.
  intro H. exact (proj2 (ushq_one_some_at len f p (ushq_pipe_one _ _ _ _ H))).
Qed.

Lemma ushq_pipe_lt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> (p < len)%nat.
Proof using.
  intro H. exact (proj1 (ushq_one_some_at len f p (ushq_pipe_one _ _ _ _ H))).
Qed.

Lemma ushq_pipe_sp_lt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> (S p < len)%nat.
Proof using. intros (_ & _ & _ & _ & H1 & H2 & _ & _). lia. Qed.

Lemma ushq_pipe_right_lt (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> (S (S p) < len)%nat.
Proof using. intros (_ & _ & _ & _ & H1 & H2 & _ & _). lia. Qed.

(* the right command's bytes are neither blank nor symbol, so
   [ushp_toklen] measures the word exactly *)
Lemma ushq_pipe_right_byte (len : nat) (f : nat -> bv 8) (p e j : nat) :
  ushq_pipe len f p e -> (S (S p) <= j < e)%nat ->
  ushp_is_ws (f j) = false /\ ushp_is_sym (f j) = false.
Proof using.
  intros Hq Hj.
  destruct Hq as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  split; [ exact (Hfw j Hj) | ].
  exact (ushq_one_some_off len f p j Hone ltac:(lia) ltac:(lia)).
Qed.


(* ===================================================================== *)
(* §4 THE SCAN MEASURES AT THE PIPE SHAPE                                 *)
(*                                                                        *)
(* [UkShParseSym.ushs_skipws_exact] / [ushs_toklen_exact] are the general *)
(* measures and are reused verbatim; only the five readings below are     *)
(* about this shape.                                                      *)
(* ===================================================================== *)

(* the blank scan stops dead at the '|' *)
Lemma ushq_skipws_at_bar (len : nat) (f : nat -> bv 8) (p e n : nat) :
  ushq_pipe len f p e -> ushp_skipws n p f = 0%nat.
Proof using.
  intro Hq. apply ushp_skipws_stop.
  destruct (ushp_is_ws (f p)) eqn:E; [ exfalso | reflexivity ].
  rewrite (ushq_pipe_bar len f p e Hq), ushq_bar_not_ws in E. discriminate.
Qed.

(* the token scan does too: [gettoken] at the '|' takes the SWITCH arm *)
Lemma ushq_toklen_at_bar (len : nat) (f : nat -> bv 8) (p e n : nat) :
  ushq_pipe len f p e -> ushp_toklen n p f = 0%nat.
Proof using.
  intro Hq. destruct n as [| n ]; cbn [ushp_toklen]; [ reflexivity | ].
  rewrite (ushq_pipe_bar len f p e Hq), ushq_bar_sym, orb_true_r. reflexivity.
Qed.

(* ONE blank between the '|' and the right command *)
Lemma ushq_skipws_after_bar (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushp_skipws (len - S p) (S p) f = 1%nat.
Proof using.
  intro Hq. pose proof Hq as HQ.
  destruct HQ as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_skipws_exact (len - S p) (S p) 1 f).
  - lia.
  - intros j Hj. replace j with (S p) by lia. exact Hb2.
  - right. replace (S p + 1)%nat with (S (S p)) by lia.
    exact (Hfw (S (S p)) ltac:(lia)).
Qed.

(* the right command is the token [[S (S p), e)] *)
Lemma ushq_toklen_right (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e ->
  ushp_toklen (len - S (S p)) (S (S p)) f = (e - S (S p))%nat.
Proof using.
  intro Hq. pose proof Hq as HQ.
  destruct HQ as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_toklen_exact (len - S (S p)) (S (S p)) (e - S (S p)) f).
  - lia.
  - intros j Hj. exact (ushq_pipe_right_byte len f p e j Hq ltac:(lia)).
  - left. replace (S (S p) + (e - S (S p)))%nat with e by lia.
    exact (Htail e ltac:(lia)).
Qed.

(* ...and past it there is nothing but blanks, so the line ends there *)
Lemma ushq_skipws_tail (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushp_skipws (len - e) e f = (len - e)%nat.
Proof using.
  intro Hq. pose proof Hq as HQ.
  destruct HQ as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  apply (ushs_skipws_exact (len - e) e (len - e) f).
  - lia.
  - intros j Hj. exact (Htail j ltac:(lia)).
  - left. reflexivity.
Qed.


(* ===================================================================== *)
(* §4½ WHAT THE RIGHT COMMAND'S PARSE NEEDS: NO SYMBOL AT OR ABOVE ITS    *)
(* CURSOR                                                                 *)
(*                                                                        *)
(* The pipe line's RIGHT command is parsed by a SECOND run of [parseexec]  *)
(* (through [parsepipe]'s recursive call), and that run is symbol-free --  *)
(* but not because the LINE is: the '|' is behind its cursor.  Every use   *)
(* [UkShParseExec.wp_kshp_parseexec] and the landed [parsepipe] /          *)
(* [parseline] walks make of [UkShParse.ushp_no_symbols] is at or above    *)
(* THEIR OWN cursor (a peek that must miss, a gettoken answer), so this is *)
(* the premise those walks want re-stated at, and the pipe line satisfies  *)
(* it at [S (S p)].  Stating it here means the re-statement above is       *)
(* mechanical and carries no new obligation.                              *)
(* ===================================================================== *)

Definition ushq_nosym_from (len : nat) (f : nat -> bv 8) (c : nat) : Prop :=
  forall j : nat, (c <= j < len)%nat -> ushp_is_sym (f j) = false.

(* at the bottom of the line it IS the landed premise, both ways *)
Lemma ushq_nosym_from_0 (len : nat) (f : nat -> bv 8) :
  ushq_nosym_from len f 0%nat <-> ushp_no_symbols len f.
Proof using.
  split.
  - intros H j Hj. exact (H j ltac:(lia)).
  - intros H j Hj. exact (H j ltac:(lia)).
Qed.

Lemma ushq_nosym_from_mono (len : nat) (f : nat -> bv 8) (c c' : nat) :
  (c <= c')%nat -> ushq_nosym_from len f c -> ushq_nosym_from len f c'.
Proof using. intros Hle H j Hj. exact (H j ltac:(lia)). Qed.

(* ...and the pipe line satisfies it AT THE RIGHT COMMAND'S CURSOR *)
Lemma ushq_pipe_nosym_from (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushq_nosym_from len f (S (S p)).
Proof using.
  intros Hq j Hj.
  exact (ushq_one_some_off len f p j (ushq_pipe_one _ _ _ _ Hq)
           ltac:(lia) ltac:(lia)).
Qed.

(* the mirror fact, for the LEFT command: its whole parse runs below the
   '|', and there the line IS symbol-free ([ushq_one_nosym_below]) -- which
   is why the left [parseexec]'s peeks miss exactly as the landed ones do,
   and only its argument loop's LAST round differs. *)
Lemma ushq_pipe_nosym_below (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushp_no_symbols p f.
Proof using.
  intro Hq. exact (ushq_one_nosym_below len f p (ushq_pipe_one _ _ _ _ Hq)).
Qed.

(* ===================================================================== *)
(* §5 ONE PREMISE FOR gettoken, COVERING BOTH SYMBOL BYTES                *)
(*                                                                        *)
(* [UkShRedirGtk.wp_kshp_gettoken_sym] is stated at                        *)
(* [UkShParseSym.ushs_gt_ok] -- every symbol byte is a '>' that is        *)
(* neither last nor doubled -- and a pipe line falsifies it.  The         *)
(* weakest thing gettoken's switch needs is this disjunction: each symbol *)
(* byte is a '|' (whose arm has no lookahead) or a '>' with the lookahead *)
(* refuted.  [ushq_sym_ok_gt] shows the landed premise implies it, so the *)
(* walk in [UkShPipeTok] stated at [ushq_sym_ok] SUBSUMES the landed one  *)
(* rather than sitting beside it.                                        *)
(* ===================================================================== *)

Definition ushq_sym_ok (len : nat) (f : nat -> bv 8) : Prop :=
  forall j : nat, (j < len)%nat -> ushp_is_sym (f j) = true ->
    f j = ushq_bar
    \/ (f j = ushs_gt /\ (S j < len)%nat /\ f (S j) <> ushs_gt).

Lemma ushq_sym_ok_gt (len : nat) (f : nat -> bv 8) :
  ushs_gt_ok len f -> ushq_sym_ok len f.
Proof using.
  intros Hgt j Hj Hs. right. exact (Hgt j Hj Hs).
Qed.

Lemma ushq_sym_ok_nosym (len : nat) (f : nat -> bv 8) :
  ushp_no_symbols len f -> ushq_sym_ok len f.
Proof using.
  intros Hns j Hj Hs. rewrite (Hns j Hj) in Hs. discriminate.
Qed.

Lemma ushq_sym_ok_pipe (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushq_sym_ok len f.
Proof using.
  intros Hq j Hj Hs. left.
  destruct (Nat.eq_dec j p) as [ -> | Hne ];
    [ exact (ushq_pipe_bar len f p e Hq) | ].
  exfalso.
  rewrite (ushq_one_some_off len f p j (ushq_pipe_one _ _ _ _ Hq) Hj Hne)
    in Hs. discriminate.
Qed.

(* ...and it IS the reference parser's symbol scope ([RefParse.ref_sym_scope]
   spells the same disjunction with [rb_bar]/[rb_gt]), which is what lets
   the one general gettoken walk (UkShGettoken.wp_ref_gettoken) stand in
   for the pipe tier's *)
Lemma ushq_sym_ok_scope (len : nat) (f : nat -> bv 8) :
  ushq_sym_ok len f -> ref_sym_scope len f.
Proof using. intro H. exact H. Qed.


(* ===================================================================== *)
(* §6 GETTOKEN'S ANSWER AT THE PIPE SHAPE                                 *)
(*                                                                        *)
(* [UkShParseSym.ushs_gettok_res] / [_end] / [_fin] are SYMBOL-GENERIC    *)
(* (the answer at a symbol is the byte itself and the cursor advances by  *)
(* one), so the pipe line reuses the landed definitions and only their    *)
(* readings are new.                                                     *)
(* ===================================================================== *)

Lemma ushq_gettok_res_bar (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_res len f p = 124.
Proof using.
  intro Hq. unfold ushs_gettok_res.
  rewrite (bool_decide_eq_true_2 _ (ushq_pipe_lt len f p e Hq)).
  rewrite (ushq_pipe_bar len f p e Hq), ushq_bar_sym, ushq_bar_val.
  reflexivity.
Qed.

Lemma ushq_gettok_end_bar (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_end len f p = S p.
Proof using.
  intro Hq. unfold ushs_gettok_end.
  rewrite (bool_decide_eq_true_2 _ (ushq_pipe_lt len f p e Hq)).
  rewrite (ushq_pipe_bar len f p e Hq), ushq_bar_sym. reflexivity.
Qed.

(* the cursor after the '|' token: one blank, then the right command *)
Lemma ushq_gettok_fin_bar (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_fin len f p = S (S p).
Proof using.
  intro Hq. unfold ushs_gettok_fin.
  rewrite (ushq_gettok_end_bar len f p e Hq).
  rewrite (ushq_skipws_after_bar len f p e Hq). lia.
Qed.

(* ...and the right command's token that follows it *)
Lemma ushq_gettok_res_right (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_res len f (S (S p)) = 97.
Proof using.
  intro Hq. unfold ushs_gettok_res.
  rewrite (bool_decide_eq_true_2 _ (ushq_pipe_right_lt len f p e Hq)).
  rewrite (proj2 (ushq_pipe_right_byte len f p e (S (S p)) Hq
                    ltac:(destruct Hq as (_ & _ & _ & _ & H1 & _); lia))).
  reflexivity.
Qed.

Lemma ushq_gettok_end_right (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_end len f (S (S p)) = e.
Proof using.
  intro Hq. unfold ushs_gettok_end.
  rewrite (bool_decide_eq_true_2 _ (ushq_pipe_right_lt len f p e Hq)).
  rewrite (proj2 (ushq_pipe_right_byte len f p e (S (S p)) Hq
                    ltac:(destruct Hq as (_ & _ & _ & _ & H1 & _); lia))).
  rewrite (ushq_toklen_right len f p e Hq).
  destruct Hq as (_ & _ & _ & _ & H1 & H2 & _ & _). lia.
Qed.

Lemma ushq_gettok_fin_right (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushs_gettok_fin len f (S (S p)) = len.
Proof using.
  intro Hq. unfold ushs_gettok_fin.
  rewrite (ushq_gettok_end_right len f p e Hq).
  rewrite (ushq_skipws_tail len f p e Hq).
  destruct Hq as (_ & _ & _ & _ & H1 & H2 & _ & _). lia.
Qed.


(* ===================================================================== *)
(* §7 THE PIPE LINE, STATED POSITIONALLY                                  *)
(*                                                                        *)
(*   <the words of ws>  ' '  '|'  ' '  <right>  '\n'                      *)
(*                       ^p0  ^p                                          *)
(*                                                                        *)
(* [UkShRedirLine.ushs_line_is] at the other byte.  The right command is  *)
(* a PARAMETER and [ushq_cat] its canonical instance, because SH-PIPE     *)
(* needs the walk at `cat` and nothing about the lexer does.              *)
(* ===================================================================== *)

Definition ushq_cat : list (bv 8) := sb "cat"%string.

Lemma ushq_cat_word : wl_word ushq_cat.
Proof using. apply (bool_decide_unpack _); vm_compute; exact I. Qed.

Lemma ushq_cat_len : length ushq_cat = 3%nat.
Proof using. vm_compute. reflexivity. Qed.

Definition ushq_line_is (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) : Prop :=
  let p0 := length (wl_body ws) in
  line_ok ws
  /\ wl_word right
  /\ len = (p0 + 3 + length right + 1)%nat
  /\ (forall j : nat, (j < p0)%nat -> f (k + j)%nat = wl_body ws !!! j)
  /\ f (k + p0)%nat = wl_sp
  /\ f (k + p0 + 1)%nat = ushq_bar
  /\ f (k + p0 + 2)%nat = wl_sp
  /\ (forall j : nat, (j < length right)%nat ->
        f (k + p0 + 3 + j)%nat = right !!! j)
  /\ f (k + p0 + 3 + length right)%nat = wl_nl.

(* ...and it IS the canonical pipe shape the parser walks are stated over *)
Lemma ushq_line_is_pipe (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ushq_pipe len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat
    (length (wl_body ws) + 3 + length right)%nat.
Proof using.
  intros (Hok & Hright & Hlen & Hbody & Hsp1 & Hbar & Hsp2 & Hrb & Hnl).
  set (p0 := length (wl_body ws)) in *.
  assert (Hrpos : (0 < length right)%nat)
    by (destruct Hright as [ Hne _ ]; destruct right; [ done | cbn; lia ]).
  assert (Hbodycl : forall j : nat, (j < p0)%nat ->
            ushp_is_sym (f (k + j)%nat) = false).
  { intros j Hj. rewrite (Hbody j Hj). apply ushs_body_not_sym.
    refine (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws (line_ok_wf ws Hok)) _).
    exact (list_lookup_lookup_total_lt (wl_body ws) j Hj). }
  assert (Hrightcl : forall j : nat, (j < length right)%nat ->
            wl_alnum (f (k + p0 + 3 + j)%nat)).
  { intros j Hj. rewrite (Hrb j Hj).
    destruct Hright as [ _ Hall ].
    refine (Forall_lookup_1 _ _ _ _ Hall _).
    exact (list_lookup_lookup_total_lt right j Hj). }
  assert (Hclass : forall j : nat, (j < len)%nat ->
            j <> (p0 + 1)%nat -> ushp_is_sym (f (k + j)%nat) = false).
  { intros j Hj Hne.
    destruct (lt_dec j p0) as [ Hlo | Hge ]; [ exact (Hbodycl j Hlo) | ].
    destruct (Nat.eq_dec j p0) as [ -> | Hn0 ].
    { rewrite Hsp1. exact ushs_sp_not_sym. }
    destruct (Nat.eq_dec j (p0 + 2)%nat) as [ -> | Hn2 ].
    { replace (k + (p0 + 2))%nat with (k + p0 + 2)%nat by lia.
      rewrite Hsp2. exact ushs_sp_not_sym. }
    destruct (lt_dec j (p0 + 3 + length right)%nat) as [ Hri | Hgr ].
    { assert (Hd : (j - (p0 + 3) < length right)%nat) by lia.
      replace (k + j)%nat with (k + p0 + 3 + (j - (p0 + 3)))%nat by lia.
      exact (ushs_alnum_not_sym _ (Hrightcl (j - (p0 + 3))%nat Hd)). }
    assert (Hj' : j = (p0 + 3 + length right)%nat) by lia. subst j.
    replace (k + (p0 + 3 + length right))%nat
      with (k + p0 + 3 + length right)%nat by lia.
    rewrite Hnl. exact ushs_nl_not_sym. }
  assert (Hone : ushq_one len (fun j : nat => f (k + j)%nat)
                   (Some (p0 + 1)%nat)).
  { split.
    - intros j Hj Hs.
      destruct (Nat.eq_dec j (p0 + 1)%nat) as [ -> | Hne ]; [ reflexivity | ].
      exfalso. rewrite (Hclass j Hj Hne) in Hs. discriminate.
    - intros q Hq. injection Hq as <-. split; [ lia | ].
      cbn beta. replace (k + (p0 + 1))%nat with (k + p0 + 1)%nat by lia.
      exact Hbar. }
  unfold ushq_pipe. split; [ exact Hone | ].
  repeat split.
  - lia.
  - replace (k + (p0 + 1 - 1))%nat with (k + p0)%nat by lia.
    rewrite Hsp1. exact ushs_sp_ws.
  - replace (k + S (p0 + 1))%nat with (k + p0 + 2)%nat by lia.
    rewrite Hsp2. exact ushs_sp_ws.
  - lia.
  - lia.
  - intros j Hj.
    assert (Hd : (j - (p0 + 3) < length right)%nat) by lia.
    replace (k + j)%nat with (k + p0 + 3 + (j - (p0 + 3)))%nat by lia.
    exact (ushs_alnum_not_ws _ (Hrightcl (j - (p0 + 3))%nat Hd)).
  - intros j Hj.
    assert (Hj' : j = (p0 + 3 + length right)%nat) by lia. subst j.
    replace (k + (p0 + 3 + length right))%nat
      with (k + p0 + 3 + length right)%nat by lia.
    rewrite Hnl. exact ushs_nl_ws.
Qed.

(* a pipe line NEVER satisfies the landed symbol-free premise -- the one
   fact that says why every walk above has to be re-stated and not
   instantiated (and the twin of [UkShRedirLine.ushs_line_is_nosym]'s
   role for the redirect line) *)
Lemma ushq_pipe_not_nosym (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushp_no_symbols len f -> False.
Proof using.
  intros Hq Hns.
  pose proof (Hns p (ushq_pipe_lt len f p e Hq)) as Hfalse.
  rewrite (ushq_pipe_bar len f p e Hq) in Hfalse.
  rewrite ushq_bar_sym in Hfalse. discriminate.
Qed.

Lemma ushq_line_is_not_nosym (ws : list (list (bv 8)))
    (right : list (bv 8)) (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ushp_no_symbols len (fun j : nat => f (k + j)%nat) -> False.
Proof using.
  intro Hl.
  exact (ushq_pipe_not_nosym len (fun j : nat => f (k + j)%nat) _ _
           (ushq_line_is_pipe ws right f k len Hl)).
Qed.


(* ===================================================================== *)
(* §8 THE PIPE LINE LEXES                                                 *)
(*                                                                        *)
(* The twin of SH-LEX-REDIR's obligation 13.  BOTH token lists come off   *)
(* [UShLexRedir]'s one induction, which is stated at a closing byte and a *)
(* terminator and mentions no symbol at all:                              *)
(*                                                                        *)
(*   - the LEFT command's arguments are [LineWords.wl_toks ws] terminated *)
(*     at the '|' ([ushs_toks_line] at [c := wl_sp], [stop := p]);        *)
(*   - the RIGHT command's one argument is [ushs_toks_tail] at the        *)
(*     blank that opens the tail [' ' ++ right] and at the line's own     *)
(*     newline, terminating at [len].                                     *)
(*                                                                        *)
(* So the pipe line's lexability costs NO new induction and no new        *)
(* premise: [EchoDisc.line_ok ws] and [wl_word right] are the whole bill. *)
(* ===================================================================== *)

(* the left command's arguments, at the terminator the '|' makes *)
Lemma ushq_line_is_toks_l (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ushs_toks len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat 0%nat (wl_toks ws).
Proof using.
  intro Hl. pose proof Hl as HL.
  destruct HL as (Hok & Hright & Hlen & Hbody & Hsp1 & Hbar & Hsp2 & Hrb & Hnl).
  assert (Hrpos : (0 < length right)%nat)
    by (destruct Hright as [ Hne _ ]; destruct right; [ done | cbn; lia ]).
  apply (ushs_toks_line ws (fun j : nat => f (k + j)%nat) wl_sp len
           (length (wl_body ws) + 1)%nat).
  - exact (wl_wf_fn ws (line_ok_wf ws Hok)).
  - exact wl_sp_ws.
  - reflexivity.
  - lia.
  - right. cbn beta.
    replace (k + (length (wl_body ws) + 1))%nat
      with (k + length (wl_body ws) + 1)%nat by lia.
    rewrite Hbar. exact ushq_bar_not_ws.
  - intros j Hj. cbn beta.
    destruct (Nat.eq_dec j (length (wl_body ws))) as [ -> | Hne ].
    + rewrite Hsp1.
      pose proof (wl_lta_app_r (wl_body ws) [wl_sp] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. rewrite Hr. reflexivity.
    + rewrite (Hbody j ltac:(lia)). symmetry.
      exact (wl_lta_app_l (wl_body ws) [wl_sp] j ltac:(lia)).
Qed.

(* the right command's one argument, at the blank the '|' left behind *)
Lemma ushq_line_is_toks_r_sp (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ushs_toks len (fun j : nat => f (k + j)%nat) len
    (length (wl_body ws) + 2)%nat
    [((length (wl_body ws) + 3)%nat,
      (length (wl_body ws) + 3 + length right)%nat)].
Proof using.
  intro Hl. pose proof Hl as HL.
  destruct HL as (Hok & Hright & Hlen & Hbody & Hsp1 & Hbar & Hsp2 & Hrb & Hnl).
  set (p0 := length (wl_body ws)) in *.
  assert (Hrpos : (0 < length right)%nat)
    by (destruct Hright as [ Hne _ ]; destruct right; [ done | cbn; lia ]).
  assert (Hwf : wl_wf [right]) by (apply Forall_cons; [ exact Hright | done ]).
  assert (Htl : wl_tail [right] = wl_sp :: right)
    by (cbn [wl_tail]; rewrite app_nil_r; reflexivity).
  assert (Hlentl : length (wl_tail [right]) = S (length right))
    by (rewrite Htl; cbn [length]; reflexivity).
  (* the bytes of [' ' ++ right ++ '\n'] at [p0 + 2] *)
  assert (Hf : forall j : nat, (j < length (wl_tail [right]) + 1)%nat ->
            (fun i : nat => f (k + i)%nat) (p0 + 2 + j)%nat
            = (wl_tail [right] ++ [wl_nl]) !!! j).
  { intros j Hj. cbn beta. rewrite Hlentl in Hj.
    destruct j as [| j ].
    - rewrite Nat.add_0_r.
      replace (k + (p0 + 2))%nat with (k + p0 + 2)%nat by lia.
      rewrite Hsp2. rewrite Htl. reflexivity.
    - destruct (lt_dec j (length right)) as [ Hjr | Hjr ].
      + replace (k + (p0 + 2 + S j))%nat with (k + p0 + 3 + j)%nat by lia.
        rewrite (Hrb j Hjr). rewrite Htl. cbn [app].
        symmetry.
        pose proof (wl_lta_app_l right [wl_nl] j Hjr) as Hq.
        change ((wl_sp :: right ++ [wl_nl]) !!! S j)
          with ((right ++ [wl_nl]) !!! j).
        rewrite Hq. reflexivity.
      + assert (Hje : j = length right) by lia. subst j.
        replace (k + (p0 + 2 + S (length right)))%nat
          with (k + p0 + 3 + length right)%nat by lia.
        rewrite Hnl. rewrite Htl. cbn [app].
        change ((wl_sp :: right ++ [wl_nl]) !!! S (length right))
          with ((right ++ [wl_nl]) !!! length right).
        pose proof (wl_lta_app_r right [wl_nl] 0%nat) as Hq.
        rewrite Nat.add_0_r in Hq. rewrite Hq. reflexivity. }
  pose proof (ushs_toks_tail [right] (wl_wf_fn _ Hwf) (fun j : nat => f (k + j)%nat)
                wl_nl (p0 + 2)%nat len len wl_nl_ws
                ltac:(rewrite Hlentl; lia) ltac:(lia)
                (or_introl eq_refl) Hf) as Ht.
  cbn [wl_toks_at] in Ht.
  replace (S (p0 + 2))%nat with (p0 + 3)%nat in Ht by lia.
  replace (p0 + 3 + length right)%nat with (p0 + 3 + length right)%nat in Ht
    by lia.
  exact Ht.
Qed.

(* ...and at the cursor gettoken actually leaves, [S (S p)] = [p0 + 3] *)
Lemma ushq_line_is_toks_r (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ushs_toks len (fun j : nat => f (k + j)%nat) len
    (length (wl_body ws) + 3)%nat
    [((length (wl_body ws) + 3)%nat,
      (length (wl_body ws) + 3 + length right)%nat)].
Proof using.
  intro Hl.
  pose proof (ushq_line_is_pipe ws right f k len Hl) as Hq.
  pose proof (ushq_line_is_toks_r_sp ws right f k len Hl) as Ht.
  set (p0 := length (wl_body ws)) in *.
  pose proof (ushs_toks_skip len len (fun j : nat => f (k + j)%nat)
                (p0 + 2)%nat _ ltac:(destruct Hq as (_ & _ & _ & _ & H1 & H2 & _); lia) Ht)
    as Hs.
  assert (Hsk : ushp_skipws (len - (p0 + 2))%nat (p0 + 2)%nat
                  (fun j : nat => f (k + j)%nat) = 1%nat).
  { replace (p0 + 2)%nat with (S (p0 + 1))%nat by lia.
    exact (ushq_skipws_after_bar len (fun j : nat => f (k + j)%nat)
             (p0 + 1)%nat (p0 + 3 + length right)%nat Hq). }
  rewrite Hsk in Hs.
  replace (p0 + 2 + 1)%nat with (p0 + 3)%nat in Hs by lia.
  exact Hs.
Qed.

(* THE THEOREM: everything a pipe-line parser walk asks of the LINE.
   [UShLexRedir.ush_line_toks_redir]'s twin, and stated the same way --
   at the positional predicate, with the token lists NAMED, because an
   existential cannot tell a walk what argv to build. *)
Definition ush_line_toks_pipe : Prop :=
  forall (ws : list (list (bv 8))) (right : list (bv 8))
         (f : nat -> bv 8) (k len : nat),
    ushq_line_is ws right f k len ->
    ushq_pipe len (fun j : nat => f (k + j)%nat)
      (length (wl_body ws) + 1)%nat
      (length (wl_body ws) + 3 + length right)%nat
    /\ ushs_toks len (fun j : nat => f (k + j)%nat)
         (length (wl_body ws) + 1)%nat 0%nat (wl_toks ws)
    /\ (0 < length (wl_toks ws))%nat
    /\ (length (wl_toks ws) < 10)%nat
    /\ ushs_toks len (fun j : nat => f (k + j)%nat) len
         (length (wl_body ws) + 3)%nat
         [((length (wl_body ws) + 3)%nat,
           (length (wl_body ws) + 3 + length right)%nat)].

Lemma ush_line_toks_holds_pipe : ush_line_toks_pipe.
Proof using.
  intros ws right f k len Hl. pose proof Hl as HL.
  destruct HL as (Hok & _).
  split_and!.
  - exact (ushq_line_is_pipe ws right f k len Hl).
  - exact (ushq_line_is_toks_l ws right f k len Hl).
  - rewrite wl_toks_length. exact (line_ok_pos ws Hok).
  - rewrite wl_toks_length. exact (line_ok_lt10 ws Hok).
  - exact (ushq_line_is_toks_r ws right f k len Hl).
Qed.

(* ...and the EXISTENTIAL form, which is what a widened line predicate
   would be quantified over.  It is NOT stated in [UkShLoop] beside
   [ush_line_lexable] / [ush_line_lexable_redir]: nothing below this file
   consumes a pipe line yet (SH-LEX-REDIR §4 shows the disjunct in
   [UkSh.ush_rest_line] and the three-way case in
   [UkShFork.ushf_rest_of_body] are ONE coupled change with the child
   WALK, and the pipe line's walk does not exist), so putting the
   definition lower would buy a premise no caller can discharge. *)
Definition ush_line_lexable_pipe : Prop :=
  forall (ws : list (list (bv 8))) (right : list (bv 8))
         (f : nat -> bv 8) (k len : nat),
    ushq_line_is ws right f k len ->
    ushq_pipe len (fun j : nat => f (k + j)%nat)
      (length (wl_body ws) + 1)%nat
      (length (wl_body ws) + 3 + length right)%nat
    /\ (exists args : list (nat * nat),
          ushs_toks len (fun j : nat => f (k + j)%nat)
            (length (wl_body ws) + 1)%nat 0%nat args
          /\ (0 < length args)%nat /\ (length args < 10)%nat)
    /\ (exists rtok : nat * nat,
          ushs_toks len (fun j : nat => f (k + j)%nat) len
            (length (wl_body ws) + 3)%nat [rtok]).

Lemma ush_line_lexable_pipe_holds : ush_line_lexable_pipe.
Proof using.
  intros ws right f k len Hl.
  destruct (ush_line_toks_holds_pipe ws right f k len Hl)
    as (Hq & Ht & Hpos & Hlt & Hr).
  split; [ exact Hq | ].
  split.
  - exists (wl_toks ws). exact (conj Ht (conj Hpos Hlt)).
  - eexists. exact Hr.
Qed.


(* ===================================================================== *)
(* §9 A DEMO, AT THE APPLICATION'S OWN LINE                               *)
(*                                                                        *)
(* [UShLexRedir] §4's reason, verbatim: [ushq_line_is] is a PREMISE of    *)
(* everything above, so a lane that never instantiates it cannot tell a   *)
(* threaded premise from an unsatisfiable one (durable-notes, Vacuity).   *)
(* The line is design/app-pipe.md §0's: [echo hello world | cat].          *)
(* ===================================================================== *)

Definition ushq_demo_ws : list (list (bv 8)) :=
  [sb "echo"%string; sb "hello"%string; sb "world"%string].

(* the whole buffer, including the newline [gets] keeps *)
Definition ushq_demo_bytes : list (bv 8) :=
  wl_body ushq_demo_ws ++ [wl_sp; ushq_bar; wl_sp] ++ ushq_cat ++ [wl_nl].

Definition ushq_demo_f : nat -> bv 8 := fun j : nat => ushq_demo_bytes !!! j.

Lemma ushq_demo_len : length ushq_demo_bytes = 23%nat.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushq_demo_line_is :
  ushq_line_is ushq_demo_ws ushq_cat ushq_demo_f 0%nat 23%nat.
Proof using.
  unfold ushq_line_is, ushq_demo_f, ushq_demo_bytes, ushq_demo_ws, ushq_cat.
  split_and!.
  - apply (bool_decide_unpack _); vm_compute; exact I.
  - exact ushq_cat_word.
  - vm_compute. reflexivity.
  - intros j Hj. cbn beta.
    vm_compute (length (wl_body [sb "echo"%string; sb "hello"%string;
                                sb "world"%string])) in Hj.
    destruct j as [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| [| j
      ]]]]]]]]]]]]]]]]; try (vm_compute; reflexivity). lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros j Hj. cbn beta.
    vm_compute (length (sb "cat"%string)) in Hj.
    destruct j as [| [| [| j ]]]; try (vm_compute; reflexivity). lia.
  - vm_compute. reflexivity.
Qed.

Lemma ushq_demo_toks : wl_toks ushq_demo_ws = [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat].
Proof using. vm_compute. reflexivity. Qed.

(* the two token lists the two [parseexec] calls build their argv from *)
Lemma ushq_demo_lexes :
  ushq_pipe 23%nat (fun j : nat => ushq_demo_f (0 + j)%nat) 17%nat 22%nat
  /\ ushs_toks 23%nat (fun j : nat => ushq_demo_f (0 + j)%nat) 17%nat 0%nat
       [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat]
  /\ ushs_toks 23%nat (fun j : nat => ushq_demo_f (0 + j)%nat) 23%nat 19%nat
       [(19, 22)%nat].
Proof using.
  destruct (ush_line_toks_holds_pipe ushq_demo_ws ushq_cat ushq_demo_f
              0%nat 23%nat ushq_demo_line_is) as (Hq & Ht & _ & _ & Hr).
  rewrite ushq_demo_toks in Ht.
  vm_compute (length (wl_body ushq_demo_ws) + 1)%nat in Hq, Ht.
  vm_compute (length (wl_body ushq_demo_ws) + 3 + length ushq_cat)%nat in Hq.
  vm_compute (length (wl_body ushq_demo_ws) + 3)%nat in Hr.
  vm_compute (length (wl_body ushq_demo_ws) + 3 + length ushq_cat)%nat in Hr.
  exact (conj Hq (conj Ht Hr)).
Qed.

(* THE NEGATIVE WITNESS (durable-notes, Vacuity): the pipe line is NOT
   symbol-free, so no landed stage-4 walk applies to it.  This is the
   fact that makes every re-state-do-not-instantiate below honest. *)
Lemma ushq_demo_not_nosym :
  ushp_no_symbols 23%nat (fun j : nat => ushq_demo_f (0 + j)%nat) -> False.
Proof using.
  exact (ushq_line_is_not_nosym ushq_demo_ws ushq_cat ushq_demo_f
           0%nat 23%nat ushq_demo_line_is).
Qed.
