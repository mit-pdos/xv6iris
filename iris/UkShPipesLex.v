(* ===================================================================== *)
(* UkShPipesLex.v -- THE LINE OF A PIPELINE OF ANY LENGTH, lane PIPES-C3 *)
(* (design/pipes-general.md SS0 and SS5, cut C3).                         *)
(*                                                                        *)
(*     P0 a1 ... | P1 ... | ... | Pn ...                                  *)
(*                                                                        *)
(* [UkShPipeLex.ushq_pipe] is the ONE-bar line: exactly one symbol byte   *)
(* in the whole line, and one word after it.  A line with k bars          *)
(* falsifies it at every bar, so the parser's walks, which are stated at  *)
(* it, could not be reused one bar at a time.  What those walks actually  *)
(* read of the line at a bar is LOCAL, and it is this file's [ushq_barw]: *)
(*                                                                        *)
(*   - the bar itself, and a blank after it and a non-blank after that    *)
(*     (gettoken's answer and the cursor it leaves, [S (S p)]);           *)
(*   - every symbol byte of the line is a bar or a lookahead-free '>'     *)
(*     ([UkShPipeLex.ushq_sym_ok], gettoken's own premise).               *)
(*                                                                        *)
(* [ushq_barw_of_pipe] is the one-bar line's instance, so every walk      *)
(* re-stated at [ushq_barw] SUBSUMES its landed statement.                *)
(*                                                                        *)
(* [ushq_bars] is the LINE OF A PIPELINE, stage by stage, in the line's   *)
(* own coordinates: every stage but the last is a non-empty token list    *)
(* ending at its bar (sh's [parseexec] leaves the cursor there), and the  *)
(* last one is a token list at the line's end over a symbol-free tail     *)
(* (the landed symbol-free walk's premise).  Its derivation is what the   *)
(* parse walk [UkShPipesParse.wp_kshp_parsepipe_bars] inducts on.         *)
(*                                                                        *)
(* Iris-free.                                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import LineWords.
Require Import EchoDisc.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShWords.
Require Import UkShRedirLine.
Require Import UShLexRedir.
Require Import UkShPipeLex.
Local Open Scope Z_scope.


(* ===================================================================== *)
(* §1 A BAR, READ LOCALLY                                                 *)
(* ===================================================================== *)

Definition ushq_barw (len : nat) (f : nat -> bv 8) (p : nat) : Prop :=
  (S (S p) < len)%nat
  /\ f p = ushq_bar
  /\ ushp_is_ws (f (S p)) = true
  /\ ushp_is_ws (f (S (S p))) = false
  /\ ushq_sym_ok len f.

(* the one-bar line is an instance *)
Lemma ushq_barw_of_pipe (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushq_barw len f p.
Proof using.
  intro Hq. pose proof Hq as HQ.
  destruct HQ as (Hone & Hp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
  split; [ lia | ].
  split; [ exact (ushq_pipe_bar len f p e Hq) | ].
  split; [ exact Hb2 | ].
  split; [ exact (Hfw (S (S p)) ltac:(lia)) | ].
  exact (ushq_sym_ok_pipe len f p e Hq).
Qed.

Lemma ushq_barw_lt (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> (p < len)%nat.
Proof using. intros (H & _). lia. Qed.

Lemma ushq_barw_bar (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> f p = ushq_bar.
Proof using. intros (_ & H & _). exact H. Qed.

Lemma ushq_barw_sym_ok (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> ushq_sym_ok len f.
Proof using. intros (_ & _ & _ & _ & H). exact H. Qed.

(* the blank scan stops dead at the bar *)
Lemma ushq_skipws_at_barw (len : nat) (f : nat -> bv 8) (p n : nat) :
  ushq_barw len f p -> ushp_skipws n p f = 0%nat.
Proof using.
  intro Hb. apply ushp_skipws_stop.
  rewrite (ushq_barw_bar len f p Hb). exact ushq_bar_not_ws.
Qed.

(* gettoken at the bar: the symbol arm, one byte *)
Lemma ushq_gettok_end_barw (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> ushs_gettok_end len f p = S p.
Proof using.
  intro Hb. unfold ushs_gettok_end.
  rewrite (bool_decide_eq_true_2 _ (ushq_barw_lt len f p Hb)).
  rewrite (ushq_barw_bar len f p Hb), ushq_bar_sym. reflexivity.
Qed.

(* ONE blank between the bar and the next stage *)
Lemma ushq_skipws_after_barw (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> ushp_skipws (len - S p) (S p) f = 1%nat.
Proof using.
  intros (Hlt & _ & Hb2 & Hnw & _).
  apply (ushs_skipws_exact (len - S p) (S p) 1 f).
  - lia.
  - intros j Hj. replace j with (S p) by lia. exact Hb2.
  - right. replace (S p + 1)%nat with (S (S p)) by lia. exact Hnw.
Qed.

(* ...so the cursor gettoken leaves is the next stage's first byte *)
Lemma ushq_gettok_fin_barw (len : nat) (f : nat -> bv 8) (p : nat) :
  ushq_barw len f p -> ushs_gettok_fin len f p = S (S p).
Proof using.
  intro Hb. unfold ushs_gettok_fin.
  rewrite (ushq_gettok_end_barw len f p Hb).
  rewrite (ushq_skipws_after_barw len f p Hb). lia.
Qed.


(* ===================================================================== *)
(* §2 THE LAST STAGE, READ FROM ITS OWN CURSOR                            *)
(*                                                                        *)
(* The landed symbol-free walk is stated at a whole STRING, so the last   *)
(* stage is parsed on the line's suffix (UkShPipeRight's finding).  The   *)
(* two scans read only from their own index on, so a token list of the   *)
(* line at or above a cursor [c] is a token list of the suffix at [c],    *)
(* shifted -- the one re-basing that takes.                               *)
(* ===================================================================== *)

Lemma ushp_skipws_shift (n c i : nat) (f : nat -> bv 8) :
  ushp_skipws n (c + i) f = ushp_skipws n i (fun j : nat => f (c + j)%nat).
Proof using.
  revert i. induction n as [| n IH ]; intros i; cbn; [ reflexivity | ].
  destruct (ushp_is_ws (f (c + i)%nat)); [ | reflexivity ].
  f_equal. replace (S (c + i)) with (c + S i)%nat by lia. exact (IH (S i)).
Qed.

Lemma ushp_toklen_shift (n c i : nat) (f : nat -> bv 8) :
  ushp_toklen n (c + i) f = ushp_toklen n i (fun j : nat => f (c + j)%nat).
Proof using.
  revert i. induction n as [| n IH ]; intros i; cbn; [ reflexivity | ].
  destruct (ushp_is_ws (f (c + i)%nat) || ushp_is_sym (f (c + i)%nat));
    [ reflexivity | ].
  f_equal. replace (S (c + i)) with (c + S i)%nat by lia. exact (IH (S i)).
Qed.

Definition ushq_rebase (c : nat) (toks : list (nat * nat)) :
    list (nat * nat) :=
  map (fun tk : nat * nat => ((c + fst tk)%nat, (c + snd tk)%nat)) toks.

Lemma ushq_rebase_length (c : nat) (toks : list (nat * nat)) :
  length (ushq_rebase c toks) = length toks.
Proof using. unfold ushq_rebase. apply length_map. Qed.

Lemma ushs_toks_rel (len c : nat) (f : nat -> bv 8) :
  forall (off : nat) (toks : list (nat * nat)),
    ushs_toks len f len off toks -> (c <= off)%nat ->
    exists rel : list (nat * nat),
      ushs_toks (len - c) (fun j : nat => f (c + j)%nat) (len - c)
        (off - c) rel
      /\ toks = ushq_rebase c rel.
Proof using.
  induction 1 as [ off Hnil | off toks k n Hn Ht IH ]; intros Hc.
  - exists []. split; [ | reflexivity ].
    apply ushs_toks_nil'.
    replace (len - c - (off - c))%nat with (len - off)%nat by lia.
    rewrite <- ushp_skipws_shift.
    replace (c + (off - c))%nat with off by lia. lia.
  - destruct (IH ltac:(lia)) as (rel & Hrel & ->).
    assert (Ek : ushp_skipws (len - c - (off - c)) (off - c)
                   (fun j : nat => f (c + j)%nat) = k).
    { replace (len - c - (off - c))%nat with (len - off)%nat by lia.
      rewrite <- ushp_skipws_shift.
      replace (c + (off - c))%nat with off by lia. reflexivity. }
    assert (En : ushp_toklen (len - c - (off - c + k)) (off - c + k)
                   (fun j : nat => f (c + j)%nat) = n).
    { replace (len - c - (off - c + k))%nat with (len - (off + k))%nat
        by lia.
      rewrite <- ushp_toklen_shift.
      replace (c + (off - c + k))%nat with (off + k)%nat by lia.
      reflexivity. }
    exists (((off - c + k)%nat, (off - c + k + n)%nat) :: rel).
    split.
    + pose proof (UshsTokCons (len - c) (fun j : nat => f (c + j)%nat)
                    (len - c) (off - c) rel) as C.
      cbv zeta in C. rewrite Ek in C. rewrite En in C.
      apply C; [ exact Hn | ].
      replace (off - c + k + n)%nat with (off + k + n - c)%nat by lia.
      exact Hrel.
    + unfold ushq_rebase. cbn [map fst snd]. f_equal. f_equal; lia.
Qed.


(* ===================================================================== *)
(* §3 THE LINE OF A PIPELINE                                              *)
(*                                                                        *)
(* [ushq_bars len f c a rest]: from cursor [c] the line is the stage [a]  *)
(* followed by [length rest] more stages, one bar before each.  Every     *)
(* token list is in the LINE's coordinates.                               *)
(* ===================================================================== *)

Inductive ushq_bars (len : nat) (f : nat -> bv 8)
  : nat -> list (nat * nat) -> list (list (nat * nat)) -> Prop :=
| UshqBarsLast (c : nat) (toks : list (nat * nat)) :
    (c <= len)%nat ->
    ushq_nosym_from len f c ->
    ushs_toks len f len c toks ->
    (length toks < 10)%nat ->
    ushq_bars len f c toks []
| UshqBarsCons (c gp : nat) (toks b : list (nat * nat))
    (rest : list (list (nat * nat))) :
    (c <= len)%nat ->
    ushq_barw len f gp ->
    ushs_toks len f gp c toks ->
    (0 < length toks)%nat ->
    (length toks < 10)%nat ->
    ushq_bars len f (S (S gp)) b rest ->
    ushq_bars len f c toks (b :: rest).

(* the one-bar line, with its two landed token facts, is the two-stage
   member *)
Lemma ushq_bars_of_pipe (len : nat) (f : nat -> bv 8) (p e : nat)
    (args : list (nat * nat)) :
  ushq_pipe len f p e ->
  ushs_toks len f p 0%nat args ->
  (0 < length args)%nat -> (length args < 10)%nat ->
  ushs_toks len f len (S (S p)) [(S (S p), e)] ->
  ushq_bars len f 0%nat args [[(S (S p), e)]].
Proof using.
  intros Hq Ht Hpos Hlt Hr.
  pose proof (ushq_pipe_right_lt len f p e Hq) as Hrl.
  apply (UshqBarsCons len f 0%nat p args [(S (S p), e)] []).
  - lia.
  - exact (ushq_barw_of_pipe len f p e Hq).
  - exact Ht.
  - exact Hpos.
  - exact Hlt.
  - apply UshqBarsLast.
    + lia.
    + exact (ushq_pipe_nosym_from len f p e Hq).
    + exact Hr.
    + cbn [length]. lia.
Qed.


(* ===================================================================== *)
(* §4 THE APPLICATION'S LINE LEXES: [echo w1 ... | r1 | ... | rn]         *)
(*                                                                        *)
(* [UkShPipeLex.ushq_line_is] at any number of right-hand words: echo's    *)
(* words, then for each [r] one blank, a '|', one blank and the word, and *)
(* the newline.  [ushq_tail_is] is the part after the first bar, one word *)
(* at a time, so everything below is ONE induction on the right-hand      *)
(* words; the left command's argument list is the landed one              *)
(* ([UShLexRedir.ushs_toks_line] at the first '|').                       *)
(* ===================================================================== *)

Fixpoint ushq_tail_is (g : nat -> bv 8) (c len : nat)
    (rs : list (list (bv 8))) : Prop :=
  match rs with
  | [] => False
  | r :: rs' =>
      wl_word r
      /\ (forall j : nat, (j < length r)%nat -> g (c + j)%nat = r !!! j)
      /\ match rs' with
         | [] => len = (c + length r + 1)%nat /\ g (c + length r)%nat = wl_nl
         | _ :: _ =>
             g (c + length r)%nat = wl_sp
             /\ g (c + length r + 1)%nat = ushq_bar
             /\ g (c + length r + 2)%nat = wl_sp
             /\ ushq_tail_is g (c + length r + 3) len rs'
         end
  end.

(* what the lexing needs of the left command's words: well formed, and
   between one and nine of them -- echo's admissible lines, and [cat f] *)
Definition ushq_ws_ok (ws : list (list (bv 8))) : Prop :=
  wl_wf ws /\ (0 < length ws)%nat /\ (length ws < 10)%nat.

Lemma ushq_ws_ok_of_line_ok (ws : list (list (bv 8))) : line_ok ws -> ushq_ws_ok ws.
Proof using.
  intros Hok. split_and!; [exact (line_ok_wf ws Hok) | exact (line_ok_pos ws Hok)
                          | exact (line_ok_lt10 ws Hok)].
Qed.

Definition ushq_lines_is (ws rs : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) : Prop :=
  let p0 := length (wl_body ws) in
  ushq_ws_ok ws
  /\ (forall j : nat, (j < p0)%nat -> f (k + j)%nat = wl_body ws !!! j)
  /\ f (k + p0)%nat = wl_sp
  /\ f (k + p0 + 1)%nat = ushq_bar
  /\ f (k + p0 + 2)%nat = wl_sp
  /\ ushq_tail_is (fun j : nat => f (k + j)%nat) (p0 + 3) len rs.

(* the right-hand stages' token lists, one word each *)
Fixpoint ushq_rtoks (c : nat) (rs : list (list (bv 8)))
    : list (list (nat * nat)) :=
  match rs with
  | [] => []
  | r :: rs' => [(c, (c + length r)%nat)] :: ushq_rtoks (c + length r + 3) rs'
  end.


(* the two readings of the Fixpoint a proof steps through *)
Lemma ushq_tail_is_one (g : nat -> bv 8) (c len : nat) (r : list (bv 8)) :
  ushq_tail_is g c len [r] <->
  wl_word r
  /\ (forall j : nat, (j < length r)%nat -> g (c + j)%nat = r !!! j)
  /\ (len = (c + length r + 1)%nat /\ g (c + length r)%nat = wl_nl).
Proof using. split; intros H; exact H. Qed.

Lemma ushq_tail_is_two (g : nat -> bv 8) (c len : nat) (r r2 : list (bv 8))
    (rs : list (list (bv 8))) :
  ushq_tail_is g c len (r :: r2 :: rs) <->
  wl_word r
  /\ (forall j : nat, (j < length r)%nat -> g (c + j)%nat = r !!! j)
  /\ (g (c + length r)%nat = wl_sp
      /\ g (c + length r + 1)%nat = ushq_bar
      /\ g (c + length r + 2)%nat = wl_sp
      /\ ushq_tail_is g (c + length r + 3) len (r2 :: rs)).
Proof using. split; intros H; exact H. Qed.

(* the landed one-word line is the one-element member *)
Lemma ushq_lines_is_one (ws : list (list (bv 8))) (r : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws r f k len -> ushq_lines_is ws [r] f k len.
Proof using.
  intros (Hok & Hr & Hlen & Hbody & Hsp1 & Hbar & Hsp2 & Hrb & Hnl).
  unfold ushq_lines_is. cbv zeta.
  split; [ exact (ushq_ws_ok_of_line_ok ws Hok) | ].
  split; [ exact Hbody | ].
  split; [ exact Hsp1 | ].
  split; [ exact Hbar | ].
  split; [ exact Hsp2 | ].
  apply ushq_tail_is_one.
  split; [ exact Hr | ]. split.
  - intros j Hj. cbv beta. replace (k + (length (wl_body ws) + 3 + j))%nat
                   with (k + length (wl_body ws) + 3 + j)%nat by lia.
    exact (Hrb j Hj).
  - split; [ lia | ]. cbv beta.
    replace (k + (length (wl_body ws) + 3 + length r))%nat
      with (k + length (wl_body ws) + 3 + length r)%nat by lia.
    exact Hnl.
Qed.

Lemma ushq_word_pos (r : list (bv 8)) : wl_word r -> (0 < length r)%nat.
Proof using. intros [ Hne _ ]. destruct r; [ done | cbn; lia ]. Qed.

Lemma ushq_word_byte (r : list (bv 8)) (j : nat) :
  wl_word r -> (j < length r)%nat -> wl_alnum (r !!! j).
Proof using.
  intros [ _ Hall ] Hj.
  refine (Forall_lookup_1 _ _ _ _ Hall _).
  exact (list_lookup_lookup_total_lt r j Hj).
Qed.

(* the bytes of a word are neither blank nor symbol *)
Lemma ushq_tail_word (g : nat -> bv 8) (c : nat) (r : list (bv 8)) :
  wl_word r ->
  (forall j : nat, (j < length r)%nat -> g (c + j)%nat = r !!! j) ->
  forall j : nat, (c <= j < c + length r)%nat ->
    ushp_is_ws (g j) = false /\ ushp_is_sym (g j) = false.
Proof using.
  intros Hw Hb j Hj.
  replace j with (c + (j - c))%nat by lia.
  rewrite (Hb (j - c)%nat ltac:(lia)).
  pose proof (ushq_word_byte r (j - c) Hw ltac:(lia)) as Ha.
  split; [ exact (ushs_alnum_not_ws _ Ha) | exact (ushs_alnum_not_sym _ Ha) ].
Qed.

Lemma ushq_tail_lt (g : nat -> bv 8) (len : nat) :
  forall (rs : list (list (bv 8))) (c : nat),
    ushq_tail_is g c len rs -> (c < len)%nat.
Proof using.
  induction rs as [| r rs IH ]; intros c H; [ destruct H | ].
  destruct rs as [| r2 rs ].
  - apply ushq_tail_is_one in H. destruct H as (Hw & _ & Hlen & _).
    pose proof (ushq_word_pos r Hw). lia.
  - apply ushq_tail_is_two in H. destruct H as (_ & _ & _ & _ & _ & Ht).
    pose proof (IH _ Ht). lia.
Qed.

(* every symbol byte after the first bar is a bar *)
Lemma ushq_tail_sym (g : nat -> bv 8) (len : nat) :
  forall (rs : list (list (bv 8))) (c : nat),
    ushq_tail_is g c len rs ->
    forall j : nat, (c <= j < len)%nat -> ushp_is_sym (g j) = true ->
      g j = ushq_bar.
Proof using.
  induction rs as [| r rs IH ]; intros c H j Hj Hs; [ destruct H | ].
  destruct rs as [| r2 rs ].
  - apply ushq_tail_is_one in H. destruct H as (Hw & Hb & Hlen & Hnl).
    exfalso.
    destruct (lt_dec j (c + length r)%nat) as [ Hlt | Hge ].
    + rewrite (proj2 (ushq_tail_word g c r Hw Hb j ltac:(lia))) in Hs.
      discriminate.
    + assert (Hje : j = (c + length r)%nat) by lia. rewrite Hje in Hs.
      rewrite Hnl, ushs_nl_not_sym in Hs. discriminate.
  - apply ushq_tail_is_two in H.
    destruct H as (Hw & Hb & Hsp1 & Hbar & Hsp2 & Ht).
    destruct (lt_dec j (c + length r)%nat) as [ Hlt | Hge ].
    { exfalso.
      rewrite (proj2 (ushq_tail_word g c r Hw Hb j ltac:(lia))) in Hs.
      discriminate. }
    destruct (Nat.eq_dec j (c + length r)%nat) as [ Hj0 | Hn0 ].
    { exfalso. rewrite Hj0, Hsp1, ushs_sp_not_sym in Hs. discriminate. }
    destruct (Nat.eq_dec j (c + length r + 1)%nat) as [ Hj1 | Hn1 ].
    { rewrite Hj1. exact Hbar. }
    destruct (Nat.eq_dec j (c + length r + 2)%nat) as [ Hj2 | Hn2 ].
    { exfalso. rewrite Hj2, Hsp2, ushs_sp_not_sym in Hs. discriminate. }
    exact (IH _ Ht j ltac:(lia) Hs).
Qed.

(* a word followed by the byte [b], which stops the token *)
Lemma ushq_word_toks (len stop : nat) (g : nat -> bv 8) (c : nat)
    (r : list (bv 8)) :
  wl_word r ->
  (forall j : nat, (j < length r)%nat -> g (c + j)%nat = r !!! j) ->
  (c + length r < len)%nat ->
  ushp_is_ws (g (c + length r)%nat) = true ->
  (c + length r + ushp_skipws (len - (c + length r)) (c + length r) g
   = stop)%nat ->
  ushs_toks len g stop c [(c, (c + length r)%nat)].
Proof using.
  intros Hw Hb Hlt Hend Hstop.
  pose proof (ushq_word_pos r Hw) as Hrpos.
  pose proof (ushq_tail_word g c r Hw Hb) as Hwb.
  apply (ushs_toks_cons' len stop g c (length r) []).
  - apply ushp_skipws_stop. exact (proj1 (Hwb c ltac:(lia))).
  - apply (ushs_toklen_exact (len - c) c (length r) g).
    + lia.
    + exact Hwb.
    + left. exact Hend.
  - exact Hrpos.
  - apply ushs_toks_nil'. exact Hstop.
Qed.

(* the stages after the first bar are a pipeline tail *)
Lemma ushq_tail_bars (g : nat -> bv 8) (len : nat) :
  ushq_sym_ok len g ->
  forall (rs : list (list (bv 8))) (r : list (bv 8)) (c : nat),
    ushq_tail_is g c len (r :: rs) ->
    ushq_bars len g c [(c, (c + length r)%nat)]
      (ushq_rtoks (c + length r + 3) rs).
Proof using.
  intros Hsym.
  induction rs as [| r2 rs IH ]; intros r c H.
  - apply ushq_tail_is_one in H. destruct H as (Hw & Hb & Hlen & Hnl).
    pose proof (ushq_word_pos r Hw) as Hrpos.
    cbn [ushq_rtoks].
    apply UshqBarsLast.
    + lia.
    + intros j Hj.
      destruct (lt_dec j (c + length r)%nat) as [ Hlt | Hge ].
      * exact (proj2 (ushq_tail_word g c r Hw Hb j ltac:(lia))).
      * assert (Hje : j = (c + length r)%nat) by lia. rewrite Hje, Hnl.
        exact ushs_nl_not_sym.
    + apply ushq_word_toks; [ exact Hw | exact Hb | lia | | ].
      * rewrite Hnl. exact ushs_nl_ws.
      * assert (Hsk : ushp_skipws (len - (c + length r)) (c + length r) g
                      = 1%nat).
        { apply (ushs_skipws_exact _ _ 1 g); [ lia | | left; lia ].
          intros j Hj. replace j with (c + length r)%nat by lia.
          rewrite Hnl. exact ushs_nl_ws. }
        rewrite Hsk. lia.
    + cbn [length]. lia.
  - apply ushq_tail_is_two in H.
    destruct H as (Hw & Hb & Hsp1 & Hbar & Hsp2 & Ht).
    pose proof (ushq_tail_lt g len _ _ Ht) as Hlt'.
    pose proof Ht as Ht'. destruct Ht' as (Hw2 & Hb2 & _).
    pose proof (ushq_word_pos r2 Hw2) as Hr2pos.
    cbn [ushq_rtoks].
    apply (UshqBarsCons len g c (c + length r + 1)%nat).
    + lia.
    + unfold ushq_barw.
      split; [ lia | ].
      split; [ exact Hbar | ].
      split.
      { replace (S (c + length r + 1)) with (c + length r + 2)%nat by lia.
        rewrite Hsp2. exact ushs_sp_ws. }
      split; [ | exact Hsym ].
      replace (S (S (c + length r + 1)))
        with (c + length r + 3 + 0)%nat by lia.
      rewrite (Hb2 0%nat Hr2pos).
      exact (ushs_alnum_not_ws _ (ushq_word_byte r2 0 Hw2 Hr2pos)).
    + apply ushq_word_toks; [ exact Hw | exact Hb | lia | | ].
      * rewrite Hsp1. exact ushs_sp_ws.
      * assert (Hsk : ushp_skipws (len - (c + length r)) (c + length r) g
                      = 1%nat).
        { apply (ushs_skipws_exact _ _ 1 g); [ lia | | right ].
          - intros j Hj. replace j with (c + length r)%nat by lia.
            rewrite Hsp1. exact ushs_sp_ws.
          - replace (c + length r + 1)%nat with (c + length r + 1)%nat
              by lia.
            rewrite Hbar. exact ushq_bar_not_ws. }
        rewrite Hsk. lia.
    + cbn [length]. lia.
    + cbn [length]. lia.
    + replace (S (S (c + length r + 1))) with (c + length r + 3)%nat by lia.
      exact (IH r2 (c + length r + 3)%nat Ht).
Qed.

(* THE THEOREM: the application's pipeline line is a line of a pipeline,
   stage by stage -- echo's argument list, then one word per stage *)
Lemma ushq_lines_bars (ws rs : list (list (bv 8))) (f : nat -> bv 8)
    (k len : nat) :
  ushq_lines_is ws rs f k len ->
  ushq_bars len (fun j : nat => f (k + j)%nat) 0%nat (wl_toks ws)
    (ushq_rtoks (length (wl_body ws) + 3) rs).
Proof using.
  intros ((Hwf & Hpos & Hlt10) & Hbody & Hsp1 & Hbar & Hsp2 & Htail).
  set (g := fun j : nat => f (k + j)%nat) in *.
  assert (Eg : forall j : nat, g j = f (k + j)%nat) by reflexivity.
  destruct rs as [| r rs ]; [ destruct Htail | ].
  pose proof (ushq_tail_lt g len _ _ Htail) as Hlt.
  pose proof Htail as Ht'. destruct Ht' as (Hw & Hb & _).
  pose proof (ushq_word_pos r Hw) as Hrpos.
  assert (Hg0 : g (length (wl_body ws) + 1)%nat = ushq_bar).
  { rewrite Eg.
    replace (k + (length (wl_body ws) + 1))%nat
      with (k + length (wl_body ws) + 1)%nat by lia.
    exact Hbar. }
  (* every symbol of the line is a bar *)
  assert (Hsym : ushq_sym_ok len g).
  { intros j Hj Hs. left. rewrite Eg in Hs.
    destruct (lt_dec j (length (wl_body ws))%nat) as [ Hlo | Hge ].
    { exfalso. rewrite (Hbody j Hlo) in Hs.
      rewrite (ushs_body_not_sym _
                 (Forall_lookup_1 _ _ _ _
                    (wl_body_bytes ws Hwf)
                    (list_lookup_lookup_total_lt (wl_body ws) j Hlo))) in Hs.
      discriminate. }
    destruct (Nat.eq_dec j (length (wl_body ws))%nat) as [ Hj0 | Hn0 ].
    { exfalso. rewrite Hj0, Hsp1, ushs_sp_not_sym in Hs. discriminate. }
    destruct (Nat.eq_dec j (length (wl_body ws) + 1)%nat) as [ Hj1 | Hn1 ].
    { rewrite Hj1. exact Hg0. }
    destruct (Nat.eq_dec j (length (wl_body ws) + 2)%nat) as [ Hj2 | Hn2 ].
    { exfalso.
      replace (k + j)%nat with (k + length (wl_body ws) + 2)%nat in Hs
        by lia.
      rewrite Hsp2, ushs_sp_not_sym in Hs. discriminate. }
    rewrite <- Eg in Hs.
    exact (ushq_tail_sym g len _ _ Htail j ltac:(lia) Hs). }
  cbn [ushq_rtoks].
  apply (UshqBarsCons len g 0%nat (length (wl_body ws) + 1)%nat).
  - lia.
  - unfold ushq_barw.
    split; [ lia | ].
    split; [ exact Hg0 | ].
    split.
    { rewrite Eg.
      replace (k + S (length (wl_body ws) + 1))%nat
        with (k + length (wl_body ws) + 2)%nat by lia.
      rewrite Hsp2. exact ushs_sp_ws. }
    split; [ | exact Hsym ].
    replace (S (S (length (wl_body ws) + 1)))
      with (length (wl_body ws) + 3 + 0)%nat by lia.
    rewrite (Hb 0%nat Hrpos).
    exact (ushs_alnum_not_ws _ (ushq_word_byte r 0 Hw Hrpos)).
  - (* the left command's arguments: the landed lexing at the first bar *)
    apply (ushs_toks_line ws g wl_sp len (length (wl_body ws) + 1)%nat).
    + exact Hwf.
    + exact wl_sp_ws.
    + reflexivity.
    + lia.
    + right. rewrite Hg0. exact ushq_bar_not_ws.
    + intros j Hj. rewrite Eg.
      destruct (Nat.eq_dec j (length (wl_body ws))%nat) as [ -> | Hne ].
      * rewrite Hsp1.
        pose proof (wl_lta_app_r (wl_body ws) [wl_sp] 0%nat) as Hr.
        rewrite Nat.add_0_r in Hr. rewrite Hr. reflexivity.
      * rewrite (Hbody j ltac:(lia)). symmetry.
        exact (wl_lta_app_l (wl_body ws) [wl_sp] j ltac:(lia)).
  - rewrite wl_toks_length. exact Hpos.
  - rewrite wl_toks_length. exact Hlt10.
  - replace (S (S (length (wl_body ws) + 1)))
      with (length (wl_body ws) + 3)%nat by lia.
    exact (ushq_tail_bars g len Hsym rs r (length (wl_body ws) + 3)%nat
             Htail).
Qed.


(* ===================================================================== *)
(* §4b THE LINE OF A FILTER PIPELINE (cut G7, grep-pipes SS4):            *)
(*                                                                        *)
(*     p w1 .. wm | c1 a1 .. | ... | cn b1 ..                             *)
(*                                                                        *)
(* [ushq_tail_is] fixed ONE word per right stage; a filter stage has a    *)
(* WORD LIST ([cat], or [grep w]), lexed exactly as the left command's    *)
(* is ([UShLexRedir.ushs_toks_line], at the stage's own offset: the scans *)
(* read only from their index on, [ushs_toks_unrel]).  [ushq_tail_ws] is  *)
(* the tail stage by stage, [ushq_rtoks_ws] its token lists, and          *)
(* [ushq_lines_ws_bars] the line of a pipeline the parse walk             *)
(* ([UkShPipesParse.wp_kshp_parsepipe_bars]) inducts on -- no walk        *)
(* changes: the walk already takes any token list per stage.              *)
(* ===================================================================== *)

(* the shift back up: a token list of the suffix at [c] is the line's *)
Lemma ushs_toks_unrel (len c stop : nat) (f : nat -> bv 8) :
  (c <= stop)%nat -> (stop <= len)%nat ->
  forall (off : nat) (rel : list (nat * nat)),
    ushs_toks (len - c) (fun j : nat => f (c + j)%nat) (stop - c) off rel ->
    ushs_toks len f stop (c + off) (ushq_rebase c rel).
Proof using.
  intros Hcs Hsl off rel H.
  induction H as [ off Hnil | off toks k n Hn Ht IH ].
  - apply UshsTokNil.
    replace (len - (c + off))%nat with (len - c - off)%nat by lia.
    rewrite ushp_skipws_shift. lia.
  - assert (Ek : ushp_skipws (len - (c + off)) (c + off) f = k).
    { replace (len - (c + off))%nat with (len - c - off)%nat by lia.
      rewrite ushp_skipws_shift. reflexivity. }
    assert (En : ushp_toklen (len - (c + off + k)) (c + off + k) f = n).
    { replace (len - (c + off + k))%nat with (len - c - (off + k))%nat by lia.
      replace (c + off + k)%nat with (c + (off + k))%nat by lia.
      rewrite ushp_toklen_shift. reflexivity. }
    pose proof (UshsTokCons len f stop (c + off) (ushq_rebase c toks)) as C.
    cbv zeta in C. rewrite Ek, En in C.
    cbn [ushq_rebase map fst snd].
    replace (c + (off + k))%nat with (c + off + k)%nat by lia.
    replace (c + (off + k + n))%nat with (c + off + k + n)%nat by lia.
    apply C; [exact Hn |].
    replace (c + off + k + n)%nat with (c + (off + k + n))%nat by lia. exact IH.
Qed.

(* a nonempty word list's body starts with a word byte *)
Lemma ushq_ws_first_nonws (r : list (list (bv 8))) :
  wl_wf r -> (0 < length r)%nat -> ushp_is_ws (wl_body r !!! 0%nat) = false.
Proof using.
  intros Hwf Hpos. destruct r as [| w rest]; [cbn in Hpos; lia |].
  destruct (wl_wf_cons w rest Hwf) as [Hw _].
  rewrite wl_body_cons, (wl_lta_app_l w _ 0 (wl_word_pos w Hw)).
  exact (ushs_alnum_not_ws _ (ushq_word_byte w 0 Hw (wl_word_pos w Hw))).
Qed.

Lemma ushq_ws_body_pos (r : list (list (bv 8))) :
  wl_wf r -> (0 < length r)%nat -> (0 < length (wl_body r))%nat.
Proof using.
  intros Hwf Hpos. destruct r as [| w rest]; [cbn in Hpos; lia |].
  destruct (wl_wf_cons w rest Hwf) as [Hw _].
  rewrite wl_body_cons, length_app. pose proof (wl_word_pos w Hw). lia.
Qed.

(* A STAGE's WORDS at offset [c], ended by a blank [b]: the left
   command's lexing, at the stage's offset *)
Lemma ushq_stage_toks (len stop : nat) (g : nat -> bv 8) (c : nat)
    (r : list (list (bv 8))) (b : bv 8) :
  wl_wf r ->
  (forall j : nat, (j < length (wl_body r))%nat -> g (c + j)%nat = wl_body r !!! j) ->
  g (c + length (wl_body r))%nat = b -> ushp_is_ws b = true ->
  stop = (c + length (wl_body r) + 1)%nat -> (stop <= len)%nat ->
  (stop = len \/ ushp_is_ws (g stop) = false) ->
  ushs_toks len g stop c (ushq_rebase c (wl_toks r)).
Proof using.
  intros Hwf Hbody Hb Hbw Hstop Hle Hend.
  enough (H : ushs_toks len g stop (c + 0) (ushq_rebase c (wl_toks r)))
    by (rewrite Nat.add_0_r in H; exact H).
  apply (ushs_toks_unrel len c stop g ltac:(lia) Hle 0 (wl_toks r)).
  apply (ushs_toks_line r (fun j : nat => g (c + j)%nat) b (len - c) (stop - c) Hwf Hbw).
  - lia.
  - lia.
  - destruct Hend as [He | He]; [left; lia | right; cbv beta].
    replace (c + (stop - c))%nat with stop by lia. exact He.
  - intros j Hj. cbv beta. destruct (decide (j < length (wl_body r))%nat) as [Hlt | Hge].
    + rewrite (Hbody j Hlt). symmetry. exact (wl_lta_app_l _ _ j Hlt).
    + assert (Hj' : j = length (wl_body r)) by lia. rewrite Hj', Hb.
      pose proof (wl_lta_app_r (wl_body r) [b] 0) as Hr. rewrite Nat.add_0_r in Hr. rewrite Hr.
      reflexivity.
Qed.

(* the tail after the first bar, a word list per stage *)
Fixpoint ushq_tail_ws (g : nat -> bv 8) (c len : nat)
    (rs : list (list (list (bv 8)))) : Prop :=
  match rs with
  | [] => False
  | r :: rs' =>
      ushq_ws_ok r
      /\ (forall j : nat, (j < length (wl_body r))%nat -> g (c + j)%nat = wl_body r !!! j)
      /\ match rs' with
         | [] => len = (c + length (wl_body r) + 1)%nat
                 /\ g (c + length (wl_body r))%nat = wl_nl
         | _ :: _ =>
             g (c + length (wl_body r))%nat = wl_sp
             /\ g (c + length (wl_body r) + 1)%nat = ushq_bar
             /\ g (c + length (wl_body r) + 2)%nat = wl_sp
             /\ ushq_tail_ws g (c + length (wl_body r) + 3) len rs'
         end
  end.

Definition ushq_lines_ws (ws : list (list (bv 8))) (rs : list (list (list (bv 8))))
    (f : nat -> bv 8) (k len : nat) : Prop :=
  let p0 := length (wl_body ws) in
  ushq_ws_ok ws
  /\ (forall j : nat, (j < p0)%nat -> f (k + j)%nat = wl_body ws !!! j)
  /\ f (k + p0)%nat = wl_sp
  /\ f (k + p0 + 1)%nat = ushq_bar
  /\ f (k + p0 + 2)%nat = wl_sp
  /\ ushq_tail_ws (fun j : nat => f (k + j)%nat) (p0 + 3) len rs.

(* the right-hand stages' token lists: each stage's words at its offset *)
Fixpoint ushq_rtoks_ws (c : nat) (rs : list (list (list (bv 8))))
    : list (list (nat * nat)) :=
  match rs with
  | [] => []
  | r :: rs' => ushq_rebase c (wl_toks r) :: ushq_rtoks_ws (c + length (wl_body r) + 3) rs'
  end.

Lemma ushq_rtoks_ws_length (c : nat) (rs : list (list (list (bv 8)))) :
  length (ushq_rtoks_ws c rs) = length rs.
Proof using.
  revert c. induction rs as [| r rs IH]; intros c; [reflexivity |].
  cbn [ushq_rtoks_ws length]. by rewrite IH.
Qed.

Lemma ushq_tail_ws_lt (g : nat -> bv 8) (len : nat) :
  forall (rs : list (list (list (bv 8)))) (c : nat),
    ushq_tail_ws g c len rs -> (c < len)%nat.
Proof using.
  induction rs as [| r rs IH ]; intros c H; [ destruct H | ].
  destruct rs as [| r2 rs ].
  - destruct H as (_ & _ & Hlen & _). lia.
  - destruct H as (_ & _ & _ & _ & _ & Ht). pose proof (IH _ Ht). lia.
Qed.

(* a stage's body bytes are neither blank-free symbols *)
Lemma ushq_body_not_sym (g : nat -> bv 8) (c : nat) (r : list (list (bv 8))) :
  wl_wf r ->
  (forall j : nat, (j < length (wl_body r))%nat -> g (c + j)%nat = wl_body r !!! j) ->
  forall j : nat, (c <= j < c + length (wl_body r))%nat -> ushp_is_sym (g j) = false.
Proof using.
  intros Hwf Hb j Hj. replace j with (c + (j - c))%nat by lia.
  rewrite (Hb (j - c)%nat ltac:(lia)).
  apply ushs_body_not_sym.
  exact (Forall_lookup_1 _ _ _ _ (wl_body_bytes r Hwf)
           (list_lookup_lookup_total_lt (wl_body r) (j - c) ltac:(lia))).
Qed.

(* every symbol byte after the first bar is a bar *)
Lemma ushq_tail_ws_sym (g : nat -> bv 8) (len : nat) :
  forall (rs : list (list (list (bv 8)))) (c : nat),
    ushq_tail_ws g c len rs ->
    forall j : nat, (c <= j < len)%nat -> ushp_is_sym (g j) = true ->
      g j = ushq_bar.
Proof using.
  induction rs as [| r rs IH ]; intros c H j Hj Hs; [ destruct H | ].
  destruct H as ((Hwf & _ & _) & Hb & Hrest).
  destruct (lt_dec j (c + length (wl_body r))%nat) as [ Hlt | Hge ].
  { exfalso. rewrite (ushq_body_not_sym g c r Hwf Hb j ltac:(lia)) in Hs. discriminate. }
  destruct rs as [| r2 rs ].
  - destruct Hrest as (Hlen & Hnl). exfalso.
    assert (Hje : j = (c + length (wl_body r))%nat) by lia. rewrite Hje in Hs.
    rewrite Hnl, ushs_nl_not_sym in Hs. discriminate.
  - destruct Hrest as (Hsp1 & Hbar & Hsp2 & Ht).
    destruct (Nat.eq_dec j (c + length (wl_body r))%nat) as [ Hj0 | Hn0 ].
    { exfalso. rewrite Hj0, Hsp1, ushs_sp_not_sym in Hs. discriminate. }
    destruct (Nat.eq_dec j (c + length (wl_body r) + 1)%nat) as [ Hj1 | Hn1 ].
    { rewrite Hj1. exact Hbar. }
    destruct (Nat.eq_dec j (c + length (wl_body r) + 2)%nat) as [ Hj2 | Hn2 ].
    { exfalso. rewrite Hj2, Hsp2, ushs_sp_not_sym in Hs. discriminate. }
    exact (IH _ Ht j ltac:(lia) Hs).
Qed.

(* the stages after the first bar are a pipeline tail *)
Lemma ushq_tail_ws_bars (g : nat -> bv 8) (len : nat) :
  ushq_sym_ok len g ->
  forall (rs : list (list (list (bv 8)))) (r : list (list (bv 8))) (c : nat),
    ushq_tail_ws g c len (r :: rs) ->
    ushq_bars len g c (ushq_rebase c (wl_toks r))
      (ushq_rtoks_ws (c + length (wl_body r) + 3) rs).
Proof using.
  intros Hsym.
  induction rs as [| r2 rs IH ]; intros r c H.
  - destruct H as ((Hwf & Hpos & Hlt10) & Hb & Hlen & Hnl).
    cbn [ushq_rtoks_ws].
    apply UshqBarsLast.
    + lia.
    + intros j Hj.
      destruct (lt_dec j (c + length (wl_body r))%nat) as [ Hlt | Hge ].
      * exact (ushq_body_not_sym g c r Hwf Hb j ltac:(lia)).
      * assert (Hje : j = (c + length (wl_body r))%nat) by lia. rewrite Hje, Hnl.
        exact ushs_nl_not_sym.
    + apply (ushq_stage_toks len len g c r wl_nl Hwf Hb Hnl ushs_nl_ws); [lia | lia | left; reflexivity].
    + rewrite ushq_rebase_length, wl_toks_length. exact Hlt10.
  - pose proof H as Hall.
    destruct H as ((Hwf & Hpos & Hlt10) & Hb & Hsp1 & Hbar & Hsp2 & Ht).
    pose proof (ushq_tail_ws_lt g len _ _ Ht) as Hlt'.
    pose proof Ht as Ht'. destruct Ht' as ((Hwf2 & Hpos2 & _) & Hb2 & _).
    pose proof (ushq_ws_body_pos r2 Hwf2 Hpos2) as Hb2pos.
    cbn [ushq_rtoks_ws].
    apply (UshqBarsCons len g c (c + length (wl_body r) + 1)%nat).
    + lia.
    + unfold ushq_barw.
      split; [ lia | ].
      split; [ exact Hbar | ].
      split.
      { replace (S (c + length (wl_body r) + 1)) with (c + length (wl_body r) + 2)%nat by lia.
        rewrite Hsp2. exact ushs_sp_ws. }
      split; [ | exact Hsym ].
      replace (S (S (c + length (wl_body r) + 1)))
        with (c + length (wl_body r) + 3 + 0)%nat by lia.
      rewrite (Hb2 0%nat Hb2pos).
      exact (ushq_ws_first_nonws r2 Hwf2 Hpos2).
    + apply (ushq_stage_toks len _ g c r wl_sp Hwf Hb Hsp1 ushs_sp_ws); [lia | lia |].
      right. rewrite Hbar. exact ushq_bar_not_ws.
    + rewrite ushq_rebase_length, wl_toks_length. exact Hpos.
    + rewrite ushq_rebase_length, wl_toks_length. exact Hlt10.
    + replace (S (S (c + length (wl_body r) + 1))) with (c + length (wl_body r) + 3)%nat by lia.
      exact (IH r2 (c + length (wl_body r) + 3)%nat Ht).
Qed.

(* THE THEOREM: a filter pipeline's line is a line of a pipeline, stage by
   stage -- the left command's arguments, then each stage's words *)
Lemma ushq_lines_ws_bars (ws : list (list (bv 8))) (rs : list (list (list (bv 8))))
    (f : nat -> bv 8) (k len : nat) :
  ushq_lines_ws ws rs f k len ->
  ushq_bars len (fun j : nat => f (k + j)%nat) 0%nat (wl_toks ws)
    (ushq_rtoks_ws (length (wl_body ws) + 3) rs).
Proof using.
  intros ((Hwf & Hpos & Hlt10) & Hbody & Hsp1 & Hbar & Hsp2 & Htail).
  set (g := fun j : nat => f (k + j)%nat) in *.
  assert (Eg : forall j : nat, g j = f (k + j)%nat) by reflexivity.
  destruct rs as [| r rs ]; [ destruct Htail | ].
  pose proof (ushq_tail_ws_lt g len _ _ Htail) as Hlt.
  pose proof Htail as Ht'. destruct Ht' as ((Hwf2 & Hpos2 & _) & Hb & _).
  pose proof (ushq_ws_body_pos r Hwf2 Hpos2) as Hrpos.
  assert (Hg0 : g (length (wl_body ws) + 1)%nat = ushq_bar).
  { rewrite Eg.
    replace (k + (length (wl_body ws) + 1))%nat
      with (k + length (wl_body ws) + 1)%nat by lia.
    exact Hbar. }
  (* every symbol of the line is a bar *)
  assert (Hsym : ushq_sym_ok len g).
  { intros j Hj Hs. left. rewrite Eg in Hs.
    destruct (lt_dec j (length (wl_body ws))%nat) as [ Hlo | Hge ].
    { exfalso. rewrite (Hbody j Hlo) in Hs.
      rewrite (ushs_body_not_sym _
                 (Forall_lookup_1 _ _ _ _
                    (wl_body_bytes ws Hwf)
                    (list_lookup_lookup_total_lt (wl_body ws) j Hlo))) in Hs.
      discriminate. }
    destruct (Nat.eq_dec j (length (wl_body ws))%nat) as [ Hj0 | Hn0 ].
    { exfalso. rewrite Hj0, Hsp1, ushs_sp_not_sym in Hs. discriminate. }
    destruct (Nat.eq_dec j (length (wl_body ws) + 1)%nat) as [ Hj1 | Hn1 ].
    { rewrite Hj1. exact Hg0. }
    destruct (Nat.eq_dec j (length (wl_body ws) + 2)%nat) as [ Hj2 | Hn2 ].
    { exfalso.
      replace (k + j)%nat with (k + length (wl_body ws) + 2)%nat in Hs
        by lia.
      rewrite Hsp2, ushs_sp_not_sym in Hs. discriminate. }
    rewrite <- Eg in Hs.
    exact (ushq_tail_ws_sym g len _ _ Htail j ltac:(lia) Hs). }
  cbn [ushq_rtoks_ws].
  apply (UshqBarsCons len g 0%nat (length (wl_body ws) + 1)%nat).
  - lia.
  - unfold ushq_barw.
    split; [ lia | ].
    split; [ exact Hg0 | ].
    split.
    { rewrite Eg.
      replace (k + S (length (wl_body ws) + 1))%nat
        with (k + length (wl_body ws) + 2)%nat by lia.
      rewrite Hsp2. exact ushs_sp_ws. }
    split; [ | exact Hsym ].
    replace (S (S (length (wl_body ws) + 1)))
      with (length (wl_body ws) + 3 + 0)%nat by lia.
    rewrite (Hb 0%nat Hrpos).
    exact (ushq_ws_first_nonws r Hwf2 Hpos2).
  - (* the left command's arguments: the landed lexing at the first bar *)
    apply (ushs_toks_line ws g wl_sp len (length (wl_body ws) + 1)%nat).
    + exact Hwf.
    + exact wl_sp_ws.
    + reflexivity.
    + lia.
    + right. rewrite Hg0. exact ushq_bar_not_ws.
    + intros j Hj. rewrite Eg.
      destruct (Nat.eq_dec j (length (wl_body ws))%nat) as [ -> | Hne ].
      * rewrite Hsp1.
        pose proof (wl_lta_app_r (wl_body ws) [wl_sp] 0%nat) as Hr.
        rewrite Nat.add_0_r in Hr. rewrite Hr. reflexivity.
      * rewrite (Hbody j ltac:(lia)). symmetry.
        exact (wl_lta_app_l (wl_body ws) [wl_sp] j ltac:(lia)).
  - rewrite wl_toks_length. exact Hpos.
  - rewrite wl_toks_length. exact Hlt10.
  - replace (S (S (length (wl_body ws) + 1)))
      with (length (wl_body ws) + 3)%nat by lia.
    exact (ushq_tail_ws_bars g len Hsym rs r (length (wl_body ws) + 3)%nat
             Htail).
Qed.

(* ===================================================================== *)
(* §5 A DEMO: [echo hello world | cat | cat]                              *)
(*                                                                        *)
(* [ushq_lines_is] is a PREMISE of the theorem above, so it is shown       *)
(* satisfiable at a three-stage line (durable-notes, Vacuity).             *)
(* ===================================================================== *)

Definition ushq_demo3_bytes : list (bv 8) :=
  wl_body ushq_demo_ws ++ [wl_sp; ushq_bar; wl_sp] ++ ushq_cat
  ++ [wl_sp; ushq_bar; wl_sp] ++ ushq_cat ++ [wl_nl].

Definition ushq_demo3_f : nat -> bv 8 := fun j : nat => ushq_demo3_bytes !!! j.

Lemma ushq_demo3_len : length ushq_demo3_bytes = 29%nat.
Proof using. vm_compute. reflexivity. Qed.

Lemma ushq_demo3_lines_is :
  ushq_lines_is ushq_demo_ws [ushq_cat; ushq_cat] ushq_demo3_f 0%nat 29%nat.
Proof using.
  unfold ushq_lines_is. cbv zeta.
  split; [ apply ushq_ws_ok_of_line_ok; apply (bool_decide_unpack _); vm_compute; exact I | ].
  split.
  { intros j Hj.
    vm_compute (length (wl_body ushq_demo_ws)) in Hj.
    do 16 (destruct j as [| j ]; [ vm_compute; reflexivity | ]). lia. }
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  apply ushq_tail_is_two.
  split; [ exact ushq_cat_word | ].
  split.
  { intros j Hj. rewrite ushq_cat_len in Hj.
    do 3 (destruct j as [| j ]; [ vm_compute; reflexivity | ]). lia. }
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  split; [ vm_compute; reflexivity | ].
  apply ushq_tail_is_one.
  split; [ exact ushq_cat_word | ].
  split.
  { intros j Hj. rewrite ushq_cat_len in Hj.
    do 3 (destruct j as [| j ]; [ vm_compute; reflexivity | ]). lia. }
  split; vm_compute; reflexivity.
Qed.

(* ...and its three stages: echo's arguments and two one-word stages *)
Lemma ushq_demo3_bars :
  ushq_bars 29%nat (fun j : nat => ushq_demo3_f (0 + j)%nat) 0%nat
    [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat]
    [[(19, 22)%nat]; [(25, 28)%nat]].
Proof using.
  pose proof (ushq_lines_bars ushq_demo_ws [ushq_cat; ushq_cat] ushq_demo3_f
                0%nat 29%nat ushq_demo3_lines_is) as H.
  rewrite ushq_demo_toks in H.
  exact H.
Qed.
