(* ===================================================================== *)
(* LineWords.v -- A CONSOLE LINE AS A LIST OF WORDS.                      *)
(*                                                                        *)
(* The vocabulary, and nothing that needs a lexer: a line is a list of     *)
(* WORDS joined by single spaces and closed by a newline, [wl_line], and   *)
(* word [i] of it sits at [wl_off] and is named by token [i] of            *)
(* [wl_toks].  That is the shape of line a disciplined console session     *)
(* types, and every statement about such a line reads it through these     *)
(* four definitions rather than through its bytes.                         *)
(*                                                                        *)
(* WHAT SH'S LEXER MAKES OF IT is [UkShWords.v], which sits above          *)
(* [UkShParse]; this file depends on nothing but stdpp, so the discipline  *)
(* ([EchoDisc.v]) can spell its line with it.                              *)
(*                                                                        *)
(* THE CUT.  A line is not a uniform join: the FIRST word has no separator *)
(* before it and the LAST has the newline rather than a space after it.    *)
(* So the body is [wl_body (w :: r) = w ++ wl_tail r] with [wl_tail        *)
(* (w :: r) = ' ' :: wl_body (w :: r)], and every induction over a line    *)
(* runs on [wl_tail] -- whose offset always points AT a blank.  The first  *)
(* word is then the only special case.                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import list bitvector.definitions.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  S1  THE TWO BLANKS A DISCIPLINED LINE USES                            *)
(* ===================================================================== *)

Definition wl_sp : bv 8 := Z_to_bv 8 32%Z.   (* ' '  -- the ONE separator *)
Definition wl_nl : bv 8 := Z_to_bv 8 10%Z.   (* '\n' -- what [gets] keeps *)

(* their numeric readings, so that a proof refuting a byte reasons with
   [lia] and never with [vm_compute] inside a [Prop] *)
Lemma wl_sp_val : bv_unsigned wl_sp = 32%Z.
Proof. by vm_compute. Qed.
Lemma wl_nl_val : bv_unsigned wl_nl = 10%Z.
Proof. by vm_compute. Qed.

(* ===================================================================== *)
(*  S2  THE LINE                                                          *)
(* ===================================================================== *)

(* the separator-led tail: every word after the first is ONE space and the
   word.  [wl_tail (w :: r) = ' ' :: wl_body (w :: r)] is the equation
   every induction over a line turns on. *)
Fixpoint wl_tail (ws : list (list (bv 8))) : list (bv 8) :=
  match ws with
  | [] => []
  | w :: r => wl_sp :: (w ++ wl_tail r)
  end.

Definition wl_body (ws : list (list (bv 8))) : list (bv 8) :=
  match ws with
  | [] => []
  | w :: r => w ++ wl_tail r
  end.

(* ...and the LINE is the body plus the newline [gets] stops at and keeps *)
Definition wl_line (ws : list (list (bv 8))) : list (bv 8) :=
  wl_body ws ++ [wl_nl].

Lemma wl_tail_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_tail (w :: r) = wl_sp :: wl_body (w :: r).
Proof. reflexivity. Qed.

Lemma wl_body_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_body (w :: r) = w ++ wl_tail r.
Proof. reflexivity. Qed.

Lemma wl_line_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_line (w :: r) = w ++ (wl_tail r ++ [wl_nl]).
Proof. rewrite /wl_line wl_body_cons -app_assoc. reflexivity. Qed.

Lemma wl_line_nil : wl_line [] = [wl_nl].
Proof. reflexivity. Qed.

Lemma wl_line_length (ws : list (list (bv 8))) :
  length (wl_line ws) = length (wl_body ws) + 1.
Proof. rewrite /wl_line length_app. cbn [length]. reflexivity. Qed.

(* every line has its newline, so no line is empty -- which is what the
   discipline's [star_prefix] and every division by the line's length
   need, and all either of them needs *)
Lemma wl_line_pos (ws : list (list (bv 8))) : 0 < length (wl_line ws).
Proof. rewrite wl_line_length. lia. Qed.

(* a nonempty tail is a separator and the rest of the body *)
Lemma wl_tail_length_cons (r : list (list (bv 8))) :
  r <> [] -> length (wl_tail r) = S (length (wl_body r)).
Proof. destruct r as [| w0 r0]; [done |]. intros _. reflexivity. Qed.

(* ===================================================================== *)
(*  S3  WHAT A WORD MAY CARRY                                             *)
(*                                                                        *)
(*  ALPHANUMERIC, and nonempty.  Stated POSITIVELY, as the admissible set  *)
(*  rather than as a list of things to avoid, because everything the line  *)
(*  must avoid is then a consequence proved once: sh's five blanks and     *)
(*  seven metacharacters ([UkShWords.wl_alnum_plain]), the console's       *)
(*  carriage return, its three erase characters, its end-of-file byte and  *)
(*  the NUL -- all of them from [wl_line_byte_val] below.  A literal line  *)
(*  used to answer each of those by case analysis over its own bytes.      *)
(* ===================================================================== *)

Definition wl_alnum (b : bv 8) : Prop :=
  (48 <= bv_unsigned b <= 57)%Z        (* 0-9 *)
  \/ (65 <= bv_unsigned b <= 90)%Z     (* A-Z *)
  \/ (97 <= bv_unsigned b <= 122)%Z.   (* a-z *)

Global Instance wl_alnum_dec b : Decision (wl_alnum b).
Proof. rewrite /wl_alnum. apply _. Defined.

Definition wl_word (w : list (bv 8)) : Prop :=
  w <> [] /\ Forall wl_alnum w.

Global Instance wl_word_dec w : Decision (wl_word w).
Proof. rewrite /wl_word. apply _. Defined.

Definition wl_wf (ws : list (list (bv 8))) : Prop := Forall wl_word ws.

Global Instance wl_wf_dec ws : Decision (wl_wf ws).
Proof. rewrite /wl_wf. apply _. Defined.

Lemma wl_wf_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_wf (w :: r) -> wl_word w /\ wl_wf r.
Proof. rewrite /wl_wf. apply Forall_cons_1. Qed.

Lemma wl_word_pos (w : list (bv 8)) : wl_word w -> 0 < length w.
Proof. intros [Hne _]. destruct w as [| b w']; [done | cbn; lia]. Qed.

(* ---- every byte of the line, and which ones they are ------------------ *)

Definition wl_body_byte (b : bv 8) : Prop := wl_alnum b \/ b = wl_sp.

Lemma wl_alnum_body (w : list (bv 8)) :
  Forall wl_alnum w -> Forall wl_body_byte w.
Proof.
  induction w as [| b w' IH]; intro Hw; [constructor |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  constructor; [by left | exact (IH Hw')].
Qed.

Lemma wl_tail_bytes (ws : list (list (bv 8))) :
  wl_wf ws -> Forall wl_body_byte (wl_tail ws).
Proof.
  induction ws as [| w r IH]; intro Hwf; cbn [wl_tail]; [constructor |].
  destruct (wl_wf_cons w r Hwf) as [[_ Hw] Hr].
  constructor; [by right |].
  apply Forall_app. split; [exact (wl_alnum_body w Hw) | exact (IH Hr)].
Qed.

Lemma wl_body_bytes (ws : list (list (bv 8))) :
  wl_wf ws -> Forall wl_body_byte (wl_body ws).
Proof.
  intro Hwf. destruct ws as [| w r]; cbn [wl_body]; [constructor |].
  destruct (wl_wf_cons w r Hwf) as [[_ Hw] Hr].
  apply Forall_app.
  split; [exact (wl_alnum_body w Hw) | exact (wl_tail_bytes r Hr)].
Qed.

(* THE ONE BYTE-LEVEL FACT EVERY CONSUMER SPENDS: a numeric reading of
   every byte the line can carry.  A caller that has to refute one
   particular byte -- '\r', ^U, backspace, DEL, ^D, NUL -- gets it from
   this by [lia] and never by looking at a literal. *)
Lemma wl_line_byte_val (ws : list (list (bv 8))) (b : bv 8) :
  wl_wf ws -> b ∈ wl_line ws ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intros Hwf Hb. rewrite /wl_line in Hb.
  apply elem_of_app in Hb as [Hb | Hb].
  - apply elem_of_list_lookup_1 in Hb as [i Hi].
    destruct (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws Hwf) Hi)
      as [[H | [H | H]] | ->].
    + right. right. by left.
    + right. right. right. by left.
    + right. right. right. by right.
    + right. left. exact wl_sp_val.
  - apply elem_of_list_singleton in Hb as ->. left. exact wl_nl_val.
Qed.

(* ...AND ITS POSITIONAL HALF: the ONLY newline is the last byte, which is
   what [gets] stopping at the first one says about the buffer it read. *)
Lemma wl_line_nl_last (ws : list (list (bv 8))) (k : nat) :
  wl_wf ws -> wl_line ws !! k = Some wl_nl -> k = length (wl_body ws).
Proof.
  intros Hwf Hk.
  destruct (decide (k < length (wl_body ws))) as [Hlt | Hge].
  - exfalso. rewrite /wl_line (lookup_app_l _ _ k Hlt) in Hk.
    destruct (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws Hwf) Hk)
      as [Ha | Hsp].
    + rewrite /wl_alnum wl_nl_val in Ha. lia.
    + apply (f_equal bv_unsigned) in Hsp.
      rewrite wl_nl_val wl_sp_val in Hsp. lia.
  - apply lookup_lt_Some in Hk. rewrite wl_line_length in Hk. lia.
Qed.

(* ===================================================================== *)
(*  S4  WHERE THE WORDS SIT                                               *)
(* ===================================================================== *)

(* word [i] of a line whose body starts at [off] begins here.  Recursive
   on the word list (not on [i]), so it is the same recursion the token
   list and the [wl_tail] induction run on. *)
Fixpoint wl_off (off : nat) (ws : list (list (bv 8))) (i : nat) : nat :=
  match ws with
  | [] => off
  | w :: r =>
      match i with
      | O => off
      | S i' => wl_off (S (off + length w)) r i'
      end
  end.

(* ...and the token list [UkShParse.ushp_tokens] names: one [(start, end)]
   per word, the next word's start ONE blank past the previous end. *)
Fixpoint wl_toks_at (off : nat) (ws : list (list (bv 8)))
  : list (nat * nat) :=
  match ws with
  | [] => []
  | w :: r => (off, off + length w) :: wl_toks_at (S (off + length w)) r
  end.

Definition wl_toks (ws : list (list (bv 8))) : list (nat * nat) :=
  wl_toks_at 0 ws.

Lemma wl_off_0 (off : nat) (ws : list (list (bv 8))) : wl_off off ws 0 = off.
Proof. by destruct ws. Qed.

Lemma wl_off_ge (ws : list (list (bv 8))) :
  forall off i : nat, off <= wl_off off ws i.
Proof.
  induction ws as [| w r IH]; intros off i; cbn; [lia |].
  destruct i as [| i']; [lia |].
  pose proof (IH (S (off + length w)) i'). lia.
Qed.

Lemma wl_toks_at_length (ws : list (list (bv 8))) :
  forall off : nat, length (wl_toks_at off ws) = length ws.
Proof.
  induction ws as [| w r IH]; intro off; cbn; [reflexivity |].
  by rewrite IH.
Qed.

Lemma wl_toks_length (ws : list (list (bv 8))) :
  length (wl_toks ws) = length ws.
Proof. apply wl_toks_at_length. Qed.

Lemma wl_toks_at_lookup (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w ->
    wl_toks_at off ws !! i
    = Some (wl_off off ws i, wl_off off ws i + length w).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi; [by destruct i |].
  destruct i as [| i']; cbn in Hi |- *.
  - by injection Hi as <-.
  - exact (IH (S (off + length w0)) i' w Hi).
Qed.

(* every token of a list laid out from [p] lies at or past [p] -- the one
   fact the cut's non-interference argument spends *)
Lemma wl_toks_at_ge (ws : list (list (bv 8))) :
  forall (p : nat) (tk : nat * nat),
    tk ∈ wl_toks_at p ws -> p <= fst tk /\ p <= snd tk.
Proof.
  induction ws as [| w r IH]; intros p tk Htk; cbn in Htk.
  - by apply elem_of_nil in Htk.
  - apply elem_of_cons in Htk as [-> | Htk]; cbn; [lia |].
    pose proof (IH (S (p + length w)) tk Htk). lia.
Qed.

(* ...and no word runs past the body's end, so every index a word names is
   inside the line *)
Lemma wl_off_le_body (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (j : nat),
    ws !! i = Some w -> j <= length w ->
    wl_off off ws i + j <= off + length (wl_body ws).
Proof.
  induction ws as [| w0 r IH]; intros off i w j Hi Hj; [by destruct i |].
  rewrite wl_body_cons length_app.
  destruct i as [| i']; cbn [wl_off] in *.
  - injection Hi as <-. lia.
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    pose proof (IH (S (off + length w0)) i' w j Hi Hj) as Hle.
    rewrite (wl_tail_length_cons r Hrne). lia.
Qed.

Lemma wl_off_lt_line (ws : list (list (bv 8))) (i : nat) (w : list (bv 8))
    (j : nat) :
  ws !! i = Some w -> j <= length w ->
  wl_off 0 ws i + j < length (wl_line ws).
Proof.
  intros Hi Hj. rewrite wl_line_length.
  pose proof (wl_off_le_body ws 0 i w j Hi Hj). lia.
Qed.

(* ===================================================================== *)
(*  S4  READING THE LINE                                                  *)
(*                                                                        *)
(*  Three [!!!] laws, so the byte bookkeeping over a join is rewriting and *)
(*  not a fresh [lia] each time.                                          *)
(* ===================================================================== *)

Lemma wl_lta_app_l {A} `{Inhabited A} (u v : list A) (j : nat) :
  j < length u -> (u ++ v) !!! j = u !!! j.
Proof.
  intro Hj. rewrite !list_lookup_total_alt (lookup_app_l u v j Hj).
  reflexivity.
Qed.

Lemma wl_lta_app_r {A} `{Inhabited A} (u v : list A) (j : nat) :
  (u ++ v) !!! (length u + j) = v !!! j.
Proof.
  rewrite !list_lookup_total_alt
    (lookup_app_r u v (length u + j) ltac:(lia)).
  by replace (length u + j - length u) with j by lia.
Qed.

Lemma wl_lta_cons_S {A} `{Inhabited A} (x : A) (l : list A) (j : nat) :
  (x :: l) !!! S j = l !!! j.
Proof. reflexivity. Qed.

(* WORD [i]'S BYTES ARE THE LINE'S, at the offset the join puts them --
   so a statement about the line's byte at [wl_off ws i + j] is a
   statement about the word, which is what lets a caller stop naming the
   line's bytes at all.  Proved with the already-joined PREFIX explicit,
   because that is what the induction consumes. *)
Lemma wl_line_word_pre (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (j : nat) (pre : list (bv 8)),
    ws !! i = Some w -> j < length w -> off = length pre ->
    (pre ++ wl_body ws ++ [wl_nl]) !!! (wl_off off ws i + j) = w !!! j.
Proof.
  induction ws as [| w0 r IH]; intros off i w j pre Hi Hj Hoff;
    [by destruct i |].
  destruct i as [| i']; cbn [wl_off].
  - cbn in Hi. injection Hi as Heq. subst w0.
    rewrite wl_body_cons -!app_assoc Hoff.
    rewrite (wl_lta_app_r pre (w ++ wl_tail r ++ [wl_nl]) j).
    exact (wl_lta_app_l w _ j Hj).
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    assert (Hsplit : pre ++ wl_body (w0 :: r) ++ [wl_nl]
                     = (pre ++ w0 ++ [wl_sp]) ++ wl_body r ++ [wl_nl]).
    { destruct r as [| w1 r1]; [exfalso; by apply Hrne |].
      rewrite wl_body_cons wl_tail_cons.
      change (wl_sp :: wl_body (w1 :: r1))
        with ([wl_sp] ++ wl_body (w1 :: r1)).
      by rewrite -!app_assoc. }
    rewrite Hsplit.
    exact (IH (S (off + length w0)) i' w j (pre ++ w0 ++ [wl_sp])
             Hi Hj ltac:(rewrite !length_app; cbn [length]; lia)).
Qed.

(* THE NEXT WORD STARTS ONE BLANK PAST THIS ONE'S END -- the recurrence
   every cursor that walks the line spends, and the reason a write chain
   over the words needs no offset arithmetic of its own. *)
Lemma wl_off_S_at (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w -> wl_off off ws (S i) = S (wl_off off ws i + length w).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi; [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    cbn [wl_off]. by rewrite wl_off_0.
  - cbn [wl_off]. exact (IH (S (off + length w0)) i' w Hi).
Qed.

(* ...AND WHAT SITS THERE: a separator while another word follows, and the
   closing newline once none does. *)
(* a lookup at the junction of a three-way join, with the index EXPLICIT:
   an [ltac:(lia)] inside [lookup_app_r] sees the index as an evar and
   fails (durable-notes, "Inline [ltac:] and evar-typed holes"). *)
Lemma wl_lookup_mid {A} (u m v : list A) (x : A) (j : nat) :
  j = length u + length m ->
  (u ++ m ++ x :: v) !! j = Some x.
Proof.
  intros ->.
  rewrite (lookup_app_r u (m ++ x :: v) (length u + length m) ltac:(lia)).
  replace (length u + length m - length u) with (length m) by lia.
  rewrite (lookup_app_r m (x :: v) (length m) ltac:(lia)) Nat.sub_diag.
  reflexivity.
Qed.

Lemma wl_line_sep_pre (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (pre : list (bv 8)),
    ws !! i = Some w -> (S i < length ws)%nat -> off = length pre ->
    (pre ++ wl_body ws ++ [wl_nl]) !! (wl_off off ws i + length w)
    = Some wl_sp.
Proof.
  induction ws as [| w0 r IH]; intros off i w pre Hi Hlen Hoff;
    [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    destruct r as [| w1 r1]; [cbn [length] in Hlen; lia |].
    assert (Hshape : wl_body (w :: w1 :: r1) ++ [wl_nl]
                     = w ++ wl_sp :: (wl_body (w1 :: r1) ++ [wl_nl])).
    { rewrite wl_body_cons wl_tail_cons. symmetry.
      exact (app_assoc w (wl_sp :: wl_body (w1 :: r1)) [wl_nl]). }
    rewrite wl_off_0 Hoff Hshape.
    exact (wl_lookup_mid pre w (wl_body (w1 :: r1) ++ [wl_nl]) wl_sp
             (length pre + length w) eq_refl).
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    assert (Hsplit : pre ++ wl_body (w0 :: r) ++ [wl_nl]
                     = (pre ++ w0 ++ [wl_sp]) ++ wl_body r ++ [wl_nl]).
    { destruct r as [| w1 r1]; [exfalso; by apply Hrne |].
      rewrite wl_body_cons wl_tail_cons.
      change (wl_sp :: wl_body (w1 :: r1))
        with ([wl_sp] ++ wl_body (w1 :: r1)).
      by rewrite -!app_assoc. }
    cbn [wl_off]. rewrite Hsplit.
    exact (IH (S (off + length w0)) i' w (pre ++ w0 ++ [wl_sp]) Hi
             ltac:(cbn [length] in Hlen; lia)
             ltac:(rewrite !length_app; cbn [length]; lia)).
Qed.

Lemma wl_line_sep (ws : list (list (bv 8))) (i : nat) (w : list (bv 8)) :
  ws !! i = Some w -> (S i < length ws)%nat ->
  wl_line ws !! (wl_off 0 ws i + length w) = Some wl_sp.
Proof.
  intros Hi Hlen.
  exact (wl_line_sep_pre ws 0 i w [] Hi Hlen eq_refl).
Qed.

(* the LAST word's end IS the body's end, which is where the newline is *)
Lemma wl_off_last (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w -> S i = length ws ->
    wl_off off ws i + length w = off + length (wl_body ws).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi Hlen; [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    destruct r as [| w1 r1]; [| cbn [length] in Hlen; lia].
    rewrite wl_off_0 wl_body_cons. cbn [wl_tail]. rewrite app_nil_r. lia.
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    cbn [wl_off].
    rewrite (IH (S (off + length w0)) i' w Hi
               ltac:(cbn [length] in Hlen; lia)).
    rewrite wl_body_cons length_app (wl_tail_length_cons r Hrne). lia.
Qed.

Lemma wl_line_nl_at (ws : list (list (bv 8))) :
  wl_line ws !! length (wl_body ws) = Some wl_nl.
Proof.
  rewrite /wl_line
    (lookup_app_r (wl_body ws) [wl_nl] (length (wl_body ws)) ltac:(lia))
    Nat.sub_diag.
  reflexivity.
Qed.

Lemma wl_line_word (ws : list (list (bv 8))) (i : nat) (w : list (bv 8))
    (j : nat) :
  ws !! i = Some w -> j < length w ->
  wl_line ws !!! (wl_off 0 ws i + j) = w !!! j.
Proof.
  intros Hi Hj.
  exact (wl_line_word_pre ws 0 i w j [] Hi Hj eq_refl).
Qed.

(* ===================================================================== *)
(*  S5  THE LINE IS PARSEABLE: what was typed is a function of the wire   *)
(* ===================================================================== *)

(* A claim of the shape "whatever you type, echo prints it back" only says
   something if the observer can tell WHAT was typed.  The wire carries the
   console's echo of the line and then whatever ran; the line ends at the
   first newline, and inside it each word ends at the first blank.  Both
   readings are the same fact -- a WORD is alphanumeric and a SEPARATOR is
   not -- so both are this one lemma.

   Stated as a SPLITTING law rather than as injectivity of [wl_line]: the
   consumer is a wire with a remainder after the line, and it needs the
   remainder to match too. *)
Lemma wl_split_pred (P : bv 8 -> Prop) (u1 t1 u2 t2 : list (bv 8)) :
  Forall P u1 -> Forall P u2 ->
  (forall b, head t1 = Some b -> ~ P b) ->
  (forall b, head t2 = Some b -> ~ P b) ->
  u1 ++ t1 = u2 ++ t2 -> u1 = u2 /\ t1 = t2.
Proof.
  revert u2. induction u1 as [| a u1' IH]; intros u2 H1 H2 Ht1 Ht2 Heq.
  - destruct u2 as [| b u2']; [by split |].
    exfalso. cbn in Heq.
    destruct (Forall_cons_1 _ _ _ H2) as [Hb _].
    exact (Ht1 b ltac:(by rewrite Heq) Hb).
  - destruct u2 as [| b u2'].
    + exfalso. cbn in Heq.
      destruct (Forall_cons_1 _ _ _ H1) as [Ha _].
      exact (Ht2 a ltac:(by rewrite -Heq) Ha).
    + cbn in Heq. injection Heq as Hab Hrest. subst b.
      destruct (Forall_cons_1 _ _ _ H1) as [_ H1'].
      destruct (Forall_cons_1 _ _ _ H2) as [_ H2'].
      destruct (IH u2' H1' H2' Ht1 Ht2 Hrest) as [-> ->]. by split.
Qed.

(* the two bytes that are not word bytes, which is what makes the split
   land where it does *)
Lemma wl_alnum_not_sp : ~ wl_alnum wl_sp.
Proof. rewrite /wl_alnum wl_sp_val. lia. Qed.

Lemma wl_body_byte_not_nl : ~ wl_body_byte wl_nl.
Proof.
  rewrite /wl_body_byte /wl_alnum wl_nl_val. intros [H | H]; [lia |].
  apply (f_equal bv_unsigned) in H. rewrite wl_nl_val wl_sp_val in H. lia.
Qed.

(* a tail either is empty or opens on the blank [wl_tail] puts there, so
   it never opens on a word byte *)
Lemma wl_tail_head_not_alnum (ws : list (list (bv 8))) (b : bv 8) :
  head (wl_tail ws) = Some b -> ~ wl_alnum b.
Proof.
  destruct ws as [| w r]; cbn [wl_tail]; [done |].
  intros [= <-]. exact wl_alnum_not_sp.
Qed.

Lemma wl_nl_head_not_body (t : list (bv 8)) (b : bv 8) :
  head (wl_nl :: t) = Some b -> ~ wl_body_byte b.
Proof. intros [= <-]. exact wl_body_byte_not_nl. Qed.

Lemma wl_tail_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_tail ws1 = wl_tail ws2 -> ws1 = ws2.
Proof.
  revert ws2. induction ws1 as [| w1 r1 IH]; intros ws2 Hw1 Hw2 Heq.
  - by destruct ws2 as [| w2 r2]; [| cbn in Heq].
  - destruct ws2 as [| w2 r2]; [by cbn in Heq |].
    cbn [wl_tail] in Heq. injection Heq as Heq.
    destruct (wl_wf_cons w1 r1 Hw1) as [[_ Ha1] Hr1].
    destruct (wl_wf_cons w2 r2 Hw2) as [[_ Ha2] Hr2].
    destruct (wl_split_pred wl_alnum w1 (wl_tail r1) w2 (wl_tail r2)
                Ha1 Ha2 (wl_tail_head_not_alnum r1)
                (wl_tail_head_not_alnum r2) Heq) as [-> Hr].
    by rewrite (IH r2 Hr1 Hr2 Hr).
Qed.

Lemma wl_body_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_body ws1 = wl_body ws2 -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Heq.
  destruct ws1 as [| w1 r1]; destruct ws2 as [| w2 r2]; [done | | |].
  - exfalso. destruct (wl_wf_cons w2 r2 Hw2) as [Hwd2 _].
    pose proof (wl_word_pos w2 Hwd2).
    apply (f_equal length) in Heq. rewrite wl_body_cons length_app in Heq.
    cbn in Heq. lia.
  - exfalso. destruct (wl_wf_cons w1 r1 Hw1) as [Hwd1 _].
    pose proof (wl_word_pos w1 Hwd1).
    apply (f_equal length) in Heq. rewrite wl_body_cons length_app in Heq.
    cbn in Heq. lia.
  - rewrite !wl_body_cons in Heq.
    destruct (wl_wf_cons w1 r1 Hw1) as [[_ Ha1] Hr1].
    destruct (wl_wf_cons w2 r2 Hw2) as [[_ Ha2] Hr2].
    destruct (wl_split_pred wl_alnum w1 (wl_tail r1) w2 (wl_tail r2)
                Ha1 Ha2 (wl_tail_head_not_alnum r1)
                (wl_tail_head_not_alnum r2) Heq) as [-> Hr].
    by rewrite (wl_tail_inj r1 r2 Hr1 Hr2 Hr).
Qed.

(* THE READING THE WIRE GIVES.  Two lines followed by two remainders make
   the same wire only if they are the same line AND the same remainder --
   so a session's rounds can each carry their OWN word list and the
   observer still knows which one each round typed. *)
Lemma wl_line_det (ws1 ws2 : list (list (bv 8))) (t1 t2 : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 ++ t1 = wl_line ws2 ++ t2 -> ws1 = ws2 /\ t1 = t2.
Proof.
  intros Hw1 Hw2 Heq.
  rewrite /wl_line -!app_assoc /= in Heq.
  destruct (wl_split_pred wl_body_byte
              (wl_body ws1) (wl_nl :: t1) (wl_body ws2) (wl_nl :: t2)
              (wl_body_bytes ws1 Hw1) (wl_body_bytes ws2 Hw2)
              (wl_nl_head_not_body t1) (wl_nl_head_not_body t2) Heq)
    as [Hb Ht].
  split; [exact (wl_body_inj ws1 ws2 Hw1 Hw2 Hb) | by injection Ht].
Qed.

(* the plain injectivity, for a consumer that has no remainder *)
Lemma wl_line_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_line ws1 = wl_line ws2 -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Heq.
  destruct (wl_line_det ws1 ws2 [] [] Hw1 Hw2 ltac:(by rewrite !Heq))
    as [H _].
  exact H.
Qed.

(* THE FORM THE DISCIPLINE SPENDS.  A session claim compares what the
   model says the wire holds against a PREFIX of the real wire, so the
   reading has to survive a prefix: the line is still determined, and the
   remainder is still comparable.  It is [wl_line_det] with the prefix's
   witness folded into the first remainder. *)
Lemma wl_line_prefix_det (ws1 ws2 : list (list (bv 8)))
    (t1 t2 : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 ++ t1 `prefix_of` wl_line ws2 ++ t2 ->
  ws1 = ws2 /\ t1 `prefix_of` t2.
Proof.
  intros Hw1 Hw2 [k Hk]. rewrite -app_assoc in Hk.
  destruct (wl_line_det ws1 ws2 (t1 ++ k) t2 Hw1 Hw2 (eq_sym Hk))
    as [-> Ht].
  split; [reflexivity | by exists k].
Qed.

(* ...and the bare one: a line that is a prefix of a WIRE opening with a
   line is that line.  This is what says the observer reads the typed
   words off the wire without knowing them in advance. *)
Lemma wl_line_of_wire (ws1 ws2 : list (list (bv 8))) (t : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 `prefix_of` wl_line ws2 ++ t -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Hp.
  destruct (wl_line_prefix_det ws1 ws2 [] t Hw1 Hw2
              ltac:(by rewrite app_nil_r)) as [H _].
  exact H.
Qed.

(* ANTI-VACUITY: the encoding is not degenerate -- the blank is load
   bearing, so one two-letter word and two one-letter words are different
   lines, and the reading above tells them apart. *)
Definition wl_demo_a : bv 8 := Z_to_bv 8 97%Z.
Definition wl_demo_b : bv 8 := Z_to_bv 8 98%Z.

Lemma wl_demo_wf1 : wl_wf [[wl_demo_a; wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_wf2 : wl_wf [[wl_demo_a]; [wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_distinct :
  wl_line [[wl_demo_a; wl_demo_b]] <> wl_line [[wl_demo_a]; [wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ===================================================================== *)
(*  S6  A SESSION'S INPUT: A SEQUENCE OF LINES, EACH ITS OWN             *)
(* ===================================================================== *)

(* What a console session types is not one line repeated: it is a SEQUENCE
   of lines, each with its own words.  [wl_lines] is that input, and the
   laws below are what a discipline spends instead of dividing the wire by
   a fixed line length -- which is only meaningful when every round is the
   same size. *)
Definition wl_lines (wss : list (list (list (bv 8)))) : list (bv 8) :=
  concat (wl_line <$> wss).

Definition wl_seq_wf (wss : list (list (list (bv 8)))) : Prop :=
  Forall wl_wf wss.

Lemma wl_lines_nil : wl_lines [] = [].
Proof. reflexivity. Qed.

Lemma wl_lines_cons (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  wl_lines (ws :: r) = wl_line ws ++ wl_lines r.
Proof. reflexivity. Qed.

Lemma wl_lines_app (u v : list (list (list (bv 8)))) :
  wl_lines (u ++ v) = wl_lines u ++ wl_lines v.
Proof. by rewrite /wl_lines fmap_app concat_app. Qed.

Lemma wl_seq_wf_cons (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  wl_seq_wf (ws :: r) -> wl_wf ws /\ wl_seq_wf r.
Proof. rewrite /wl_seq_wf. apply Forall_cons_1. Qed.

(* every line carries its newline, so a nonempty sequence is nonempty *)
Lemma wl_lines_pos (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  0 < length (wl_lines (ws :: r)).
Proof.
  rewrite wl_lines_cons length_app. pose proof (wl_line_pos ws). lia.
Qed.

(* THE LAW THAT REPLACES THE DIVISION.  With one fixed line, which round a
   wire position falls in is [position / line length].  With a line per
   round that quotient is meaningless -- and it does not need replacing by
   another formula, because the ROUNDS THEMSELVES are already determined:
   a session whose input is a prefix of another's typed a prefix of the
   same lines.  So the round decomposition is read off the wire, never
   computed from a length. *)
Lemma wl_lines_prefix_det (wss1 wss2 : list (list (list (bv 8)))) :
  wl_seq_wf wss1 -> wl_seq_wf wss2 ->
  wl_lines wss1 `prefix_of` wl_lines wss2 -> wss1 `prefix_of` wss2.
Proof.
  revert wss2. induction wss1 as [| w1 r1 IH]; intros wss2 H1 H2 Hp.
  - apply prefix_nil.
  - destruct wss2 as [| w2 r2].
    + exfalso. rewrite wl_lines_nil in Hp.
      pose proof (prefix_length _ _ Hp) as Hl.
      pose proof (wl_lines_pos w1 r1) as Hpos.
      change (length (@nil (bv 8))) with 0%nat in Hl. lia.
    + destruct (wl_seq_wf_cons w1 r1 H1) as [Hw1 Hr1].
      destruct (wl_seq_wf_cons w2 r2 H2) as [Hw2 Hr2].
      rewrite !wl_lines_cons in Hp.
      destruct (wl_line_prefix_det w1 w2 (wl_lines r1) (wl_lines r2)
                  Hw1 Hw2 Hp) as [-> Hrest].
      apply prefix_cons, (IH r2 Hr1 Hr2 Hrest).
Qed.

Lemma wl_lines_inj (wss1 wss2 : list (list (list (bv 8)))) :
  wl_seq_wf wss1 -> wl_seq_wf wss2 ->
  wl_lines wss1 = wl_lines wss2 -> wss1 = wss2.
Proof.
  intros H1 H2 Heq.
  apply (anti_symm prefix);
    [ apply (wl_lines_prefix_det _ _ H1 H2); by rewrite Heq
    | apply (wl_lines_prefix_det _ _ H2 H1); by rewrite Heq ].
Qed.

(* ===================================================================== *)
(*  S7  THE PARSE: WHAT AN ERA'S INPUT SAYS                               *)
(*                                                                        *)
(*  S6 reads a sequence of lines FORWARDS -- given the words, it builds   *)
(*  the wire.  A session claim needs the other direction: the era's input *)
(*  [I : list (bv 8)] is whatever the console has echoed SO FAR, and it   *)
(*  ends wherever the user has got to -- mid-line as often as not.  So    *)
(*  the input is READ, not constructed: [wl_cut] splits it at its         *)
(*  newlines into the COMPLETE bodies (newline stripped) and the REST     *)
(*  after the last newline, and [wl_words] splits a body at its blanks.   *)
(*                                                                        *)
(*  WHY A PARSER AND NOT A LENGTH.  With one fixed line, the round a wire *)
(*  position falls in is that position divided by the line length; with a *)
(*  line per round that quotient is meaningless.  Every such division is  *)
(*  replaced here by [nlines I], [rest_of I = []] and [nstarted I] -- and *)
(*  what makes that sound rather than merely different is the DETERMINACY *)
(*  at the end of this section: the cut of a prefix is a prefix of the    *)
(*  cut, and a raw line followed by a remainder determines both halves.   *)
(*  Nothing below computes a position from a length.                      *)
(*                                                                        *)
(*  THE CUT IS STRUCTURAL FROM THE LEFT, because that is the direction    *)
(*  the recursion over the wire runs; but the laws a caller spends are    *)
(*  the SNOC laws, since one byte arrives at a time.  Those are proved    *)
(*  once here out of [wl_cut_join] and [wl_cut_of_join], so no proof      *)
(*  above this file inducts on the fixpoint.                              *)
(* ===================================================================== *)

(* ---- the join of raw bodies, each closed by the newline --------------- *)

Definition wl_join (bs : list (list (bv 8))) : list (bv 8) :=
  concat ((fun l => l ++ [wl_nl]) <$> bs).

Lemma wl_join_nil : wl_join [] = [].
Proof. reflexivity. Qed.

Lemma wl_join_cons (l : list (bv 8)) (bs : list (list (bv 8))) :
  wl_join (l :: bs) = l ++ wl_nl :: wl_join bs.
Proof.
  change (wl_join (l :: bs)) with ((l ++ [wl_nl]) ++ wl_join bs).
  by rewrite -app_assoc.
Qed.

Lemma wl_join_app (u v : list (list (bv 8))) :
  wl_join (u ++ v) = wl_join u ++ wl_join v.
Proof. by rewrite /wl_join fmap_app concat_app. Qed.

Lemma wl_join_snoc (bs : list (list (bv 8))) (l : list (bv 8)) :
  wl_join (bs ++ [l]) = wl_join bs ++ l ++ [wl_nl].
Proof. by rewrite wl_join_app wl_join_cons wl_join_nil. Qed.

(* the shape every cut law below is stated against: one body, the newline
   that closes it, and everything after *)
Lemma wl_join_cons_app (l : list (bv 8)) (bs : list (list (bv 8)))
    (r : list (bv 8)) :
  wl_join (l :: bs) ++ r = l ++ wl_nl :: (wl_join bs ++ r).
Proof. by rewrite wl_join_cons -!app_assoc. Qed.

(* ---- small list facts, named so no proof below has to hunt for them --- *)

(* a case split that leaves the scrutinee's equation as an ordinary
   hypothesis and touches nothing else -- [destruct t eqn:H] on a compound
   [t] rewrites the induction hypothesis too *)
Lemma wl_list_cases {A} (u : list A) :
  u = [] \/ exists (x : A) (r : list A), u = x :: r.
Proof. destruct u as [| x r]; [by left | right; by exists x, r]. Qed.

Lemma wl_app_inv_head {A} (u v w : list A) : u ++ v = u ++ w -> v = w.
Proof.
  induction u as [| a u' IH]; intro H; [exact H |].
  cbn in H. injection H as H. exact (IH H).
Qed.

Lemma wl_prefix_app_cancel {A} (u v w : list A) :
  u ++ v `prefix_of` u ++ w -> v `prefix_of` w.
Proof.
  intros [k Hk]. rewrite -app_assoc in Hk.
  exists k. exact (wl_app_inv_head u w (v ++ k) Hk).
Qed.

(* the one reassociation the prefix witnesses below need *)
Lemma wl_reshape {A} (u v m x d : list A) (n : A) :
  (u ++ ((v ++ m) ++ n :: x)) ++ d = (u ++ v) ++ (m ++ n :: (x ++ d)).
Proof. by rewrite -!app_assoc. Qed.

Lemma wl_nonl_cons (b : bv 8) (l : list (bv 8)) :
  wl_nl ∉ b :: l -> b <> wl_nl /\ wl_nl ∉ l.
Proof.
  intro H. apply not_elem_of_cons in H as [Hb Hl].
  split; [| exact Hl]. intro Heq. apply Hb. by rewrite Heq.
Qed.

Lemma wl_nonl_cons_2 (b : bv 8) (l : list (bv 8)) :
  b <> wl_nl -> wl_nl ∉ l -> wl_nl ∉ b :: l.
Proof.
  intros Hb Hl. apply not_elem_of_cons.
  split; [| exact Hl]. intro Heq. apply Hb. by rewrite Heq.
Qed.

Lemma wl_nonl_app (u v : list (bv 8)) :
  wl_nl ∉ u -> wl_nl ∉ v -> wl_nl ∉ u ++ v.
Proof.
  intros Hu Hv Hin.
  apply elem_of_app in Hin as [H | H]; [exact (Hu H) | exact (Hv H)].
Qed.

Lemma wl_nonl_Forall (l : list (bv 8)) :
  wl_nl ∉ l -> Forall (fun b => b <> wl_nl) l.
Proof.
  intro H. apply Forall_forall. intros x Hx Heq.
  rewrite Heq in Hx. exact (H Hx).
Qed.

(* a body carries no newline, which is why the split lands at the line's
   end and nowhere else *)
Lemma wl_nonl_of_body_bytes (l : list (bv 8)) :
  Forall wl_body_byte l -> wl_nl ∉ l.
Proof.
  intros Hl Hin. apply elem_of_list_lookup_1 in Hin as [i Hi].
  exact (wl_body_byte_not_nl (Forall_lookup_1 _ _ _ _ Hl Hi)).
Qed.

Lemma wl_body_nonl (ws : list (list (bv 8))) :
  wl_wf ws -> wl_nl ∉ wl_body ws.
Proof. intro H. exact (wl_nonl_of_body_bytes _ (wl_body_bytes ws H)). Qed.

Lemma wl_body_fmap_nonl (wss : list (list (list (bv 8)))) :
  Forall wl_wf wss -> Forall (fun l => wl_nl ∉ l) (wl_body <$> wss).
Proof.
  induction wss as [| ws rr IH]; intro Hwf; [constructor |].
  destruct (Forall_cons_1 _ _ _ Hwf) as [Hws Hrr].
  rewrite fmap_cons.
  constructor; [exact (wl_body_nonl ws Hws) | exact (IH Hrr)].
Qed.

(* ---- THE CUT --------------------------------------------------------- *)

(* Split an input at its newlines into the COMPLETE bodies (newline
   stripped, in order) and the REST after the last newline.  Structural
   from the left: a leading newline closes an EMPTY body; any other byte
   prepends onto the first body if there is a complete line, and onto the
   rest if there is not. *)
Fixpoint wl_cut (I : list (bv 8)) : list (list (bv 8)) * list (bv 8) :=
  match I with
  | [] => ([], [])
  | b :: I' =>
      let p := wl_cut I' in
      if decide (b = wl_nl) then ([] :: p.1, p.2)
      else match p.1 with
           | [] => ([], b :: p.2)
           | l :: ls => ((b :: l) :: ls, p.2)
           end
  end.

Definition bodies_of (I : list (bv 8)) : list (list (bv 8)) := (wl_cut I).1.
Definition rest_of   (I : list (bv 8)) : list (bv 8)        := (wl_cut I).2.
Definition nlines    (I : list (bv 8)) : nat := length (bodies_of I).
Definition nstarted  (I : list (bv 8)) : nat :=
  nlines I + (if decide (rest_of I = []) then 0%nat else 1%nat).

Lemma wl_cut_nil : wl_cut [] = ([], []).
Proof. reflexivity. Qed.

Lemma bodies_of_nil : bodies_of [] = [].
Proof. reflexivity. Qed.

Lemma rest_of_nil : rest_of [] = [].
Proof. reflexivity. Qed.

(* the three cons steps, spelled out once so nothing below unfolds the
   fixpoint again *)
Lemma wl_cut_cons_nl (I : list (bv 8)) :
  wl_cut (wl_nl :: I) = ([] :: bodies_of I, rest_of I).
Proof.
  rewrite /bodies_of /rest_of. cbn [wl_cut].
  case_decide as Hc; [reflexivity |]. exfalso. by apply Hc.
Qed.

Lemma wl_cut_cons_other_nil (b : bv 8) (I : list (bv 8)) :
  b <> wl_nl -> bodies_of I = [] -> wl_cut (b :: I) = ([], b :: rest_of I).
Proof.
  rewrite /bodies_of /rest_of. intros Hb Hl. cbn [wl_cut].
  case_decide as Hc; [exfalso; exact (Hb Hc) |].
  rewrite Hl. reflexivity.
Qed.

Lemma wl_cut_cons_other_cons (b : bv 8) (I : list (bv 8))
    (l : list (bv 8)) (ls : list (list (bv 8))) :
  b <> wl_nl -> bodies_of I = l :: ls ->
  wl_cut (b :: I) = ((b :: l) :: ls, rest_of I).
Proof.
  rewrite /bodies_of /rest_of. intros Hb Hl. cbn [wl_cut].
  case_decide as Hc; [exfalso; exact (Hb Hc) |].
  rewrite Hl. reflexivity.
Qed.

Lemma bodies_of_cons_nl (I : list (bv 8)) :
  bodies_of (wl_nl :: I) = [] :: bodies_of I.
Proof. by rewrite /bodies_of wl_cut_cons_nl. Qed.

Lemma rest_of_cons_nl (I : list (bv 8)) :
  rest_of (wl_nl :: I) = rest_of I.
Proof. by rewrite /rest_of wl_cut_cons_nl. Qed.

Lemma bodies_of_cons_other_nil (b : bv 8) (I : list (bv 8)) :
  b <> wl_nl -> bodies_of I = [] -> bodies_of (b :: I) = [].
Proof.
  intros Hb Hl. by rewrite /bodies_of (wl_cut_cons_other_nil b I Hb Hl).
Qed.

Lemma rest_of_cons_other_nil (b : bv 8) (I : list (bv 8)) :
  b <> wl_nl -> bodies_of I = [] -> rest_of (b :: I) = b :: rest_of I.
Proof.
  intros Hb Hl. by rewrite /rest_of (wl_cut_cons_other_nil b I Hb Hl).
Qed.

Lemma bodies_of_cons_other_cons (b : bv 8) (I : list (bv 8))
    (l : list (bv 8)) (ls : list (list (bv 8))) :
  b <> wl_nl -> bodies_of I = l :: ls -> bodies_of (b :: I) = (b :: l) :: ls.
Proof.
  intros Hb Hl.
  by rewrite /bodies_of (wl_cut_cons_other_cons b I l ls Hb Hl).
Qed.

Lemma rest_of_cons_other_cons (b : bv 8) (I : list (bv 8))
    (l : list (bv 8)) (ls : list (list (bv 8))) :
  b <> wl_nl -> bodies_of I = l :: ls -> rest_of (b :: I) = rest_of I.
Proof.
  intros Hb Hl.
  by rewrite /rest_of (wl_cut_cons_other_cons b I l ls Hb Hl).
Qed.

(* THE CUT LOSES NOTHING: the input IS the join of its bodies followed by
   its rest.  Every law after this one is an instance of this equation
   together with [wl_cut_of_join]. *)
Lemma wl_cut_join (I : list (bv 8)) : I = wl_join (bodies_of I) ++ rest_of I.
Proof.
  induction I as [| b I' IH].
  - by rewrite bodies_of_nil rest_of_nil wl_join_nil.
  - destruct (decide (b = wl_nl)) as [-> | Hb].
    + rewrite bodies_of_cons_nl rest_of_cons_nl
        (wl_join_cons_app [] (bodies_of I') (rest_of I')) app_nil_l.
      exact (f_equal (cons wl_nl) IH).
    + destruct (wl_list_cases (bodies_of I')) as [HB | (l & ls & HB)].
      * rewrite (bodies_of_cons_other_nil b I' Hb HB)
                (rest_of_cons_other_nil b I' Hb HB) wl_join_nil app_nil_l.
        rewrite HB wl_join_nil app_nil_l in IH.
        exact (f_equal (cons b) IH).
      * rewrite (bodies_of_cons_other_cons b I' l ls Hb HB)
                (rest_of_cons_other_cons b I' l ls Hb HB)
                (wl_join_cons_app (b :: l) ls (rest_of I')).
        rewrite HB (wl_join_cons_app l ls (rest_of I')) in IH.
        exact (f_equal (cons b) IH).
Qed.

(* ...and every piece it produces is newline-free, which is what makes the
   cut the INVERSE of the join and not merely a left inverse *)
Lemma wl_cut_bodies_nonl (I : list (bv 8)) :
  Forall (fun l => wl_nl ∉ l) (bodies_of I).
Proof.
  induction I as [| b I' IH].
  - rewrite bodies_of_nil. constructor.
  - destruct (decide (b = wl_nl)) as [-> | Hb].
    + rewrite bodies_of_cons_nl.
      constructor; [apply not_elem_of_nil | exact IH].
    + destruct (wl_list_cases (bodies_of I')) as [HB | (l & ls & HB)].
      * rewrite (bodies_of_cons_other_nil b I' Hb HB). constructor.
      * rewrite (bodies_of_cons_other_cons b I' l ls Hb HB).
        rewrite HB in IH.
        destruct (Forall_cons_1 _ _ _ IH) as [Hl Hls].
        constructor; [exact (wl_nonl_cons_2 b l Hb Hl) | exact Hls].
Qed.

Lemma wl_cut_rest_nonl (I : list (bv 8)) : wl_nl ∉ rest_of I.
Proof.
  induction I as [| b I' IH].
  - rewrite rest_of_nil. apply not_elem_of_nil.
  - destruct (decide (b = wl_nl)) as [-> | Hb].
    + rewrite rest_of_cons_nl. exact IH.
    + destruct (wl_list_cases (bodies_of I')) as [HB | (l & ls & HB)].
      * rewrite (rest_of_cons_other_nil b I' Hb HB).
        exact (wl_nonl_cons_2 b (rest_of I') Hb IH).
      * rewrite (rest_of_cons_other_cons b I' l ls Hb HB). exact IH.
Qed.

(* ---- the cut of a join, and the snoc laws that follow ----------------- *)

Lemma wl_cut_nonl (r : list (bv 8)) : wl_nl ∉ r -> wl_cut r = ([], r).
Proof.
  induction r as [| b r' IH]; intro Hr; [reflexivity |].
  destruct (wl_nonl_cons b r' Hr) as [Hb Hr'].
  pose proof (IH Hr') as HJ.
  assert (Hbod : bodies_of r' = []) by (rewrite /bodies_of HJ; reflexivity).
  assert (Hrst : rest_of r' = r') by (rewrite /rest_of HJ; reflexivity).
  by rewrite (wl_cut_cons_other_nil b r' Hb Hbod) Hrst.
Qed.

Lemma wl_cut_app_line (l I : list (bv 8)) :
  wl_nl ∉ l -> wl_cut (l ++ [wl_nl] ++ I) = (l :: bodies_of I, rest_of I).
Proof.
  revert I. induction l as [| b l' IH]; intros I Hl.
  - exact (wl_cut_cons_nl I).
  - destruct (wl_nonl_cons b l' Hl) as [Hb Hl'].
    pose proof (IH I Hl') as HJ.
    assert (Hbod : bodies_of (l' ++ [wl_nl] ++ I) = l' :: bodies_of I)
      by (rewrite /bodies_of HJ; reflexivity).
    assert (Hrst : rest_of (l' ++ [wl_nl] ++ I) = rest_of I)
      by (rewrite /rest_of HJ; reflexivity).
    change ((b :: l') ++ [wl_nl] ++ I) with (b :: (l' ++ [wl_nl] ++ I)).
    by rewrite (wl_cut_cons_other_cons b (l' ++ [wl_nl] ++ I) l'
                  (bodies_of I) Hb Hbod) Hrst.
Qed.

(* the same with the newline spelled as a cons, so a rewrite against a
   join lands without relying on conversion inside the pattern *)
Lemma wl_cut_app_line_cons (l I : list (bv 8)) :
  wl_nl ∉ l -> wl_cut (l ++ wl_nl :: I) = (l :: bodies_of I, rest_of I).
Proof. exact (wl_cut_app_line l I). Qed.

(* THE CUT INVERTS THE JOIN.  This is the law the discipline spends: an
   input that IS a sequence of newline-free bodies followed by a
   newline-free remainder parses back to exactly those. *)
Lemma wl_cut_of_join (bs : list (list (bv 8))) (r : list (bv 8)) :
  Forall (fun l => wl_nl ∉ l) bs -> wl_nl ∉ r ->
  wl_cut (wl_join bs ++ r) = (bs, r).
Proof.
  induction bs as [| l bs' IH]; intros Hbs Hr.
  - rewrite wl_join_nil app_nil_l. exact (wl_cut_nonl r Hr).
  - destruct (Forall_cons_1 _ _ _ Hbs) as [Hl Hbs'].
    pose proof (IH Hbs' Hr) as HJ.
    rewrite (wl_join_cons_app l bs' r)
            (wl_cut_app_line_cons l (wl_join bs' ++ r) Hl).
    by rewrite /bodies_of /rest_of HJ.
Qed.

Lemma wl_cut_app_nonl (I r : list (bv 8)) :
  wl_nl ∉ r -> wl_cut (I ++ r) = (bodies_of I, rest_of I ++ r).
Proof.
  intro Hr.
  assert (Heq : I ++ r = wl_join (bodies_of I) ++ (rest_of I ++ r))
    by (rewrite app_assoc -(wl_cut_join I); reflexivity).
  rewrite Heq. apply wl_cut_of_join; [exact (wl_cut_bodies_nonl I) |].
  exact (wl_nonl_app (rest_of I) r (wl_cut_rest_nonl I) Hr).
Qed.

Lemma wl_cut_snoc_nl (I : list (bv 8)) :
  wl_cut (I ++ [wl_nl]) = (bodies_of I ++ [rest_of I], []).
Proof.
  assert (Heq : I ++ [wl_nl] = wl_join (bodies_of I ++ [rest_of I]) ++ []).
  { rewrite wl_join_snoc app_nil_r app_assoc -(wl_cut_join I). reflexivity. }
  rewrite Heq. apply wl_cut_of_join; [| apply not_elem_of_nil].
  apply Forall_app. split; [exact (wl_cut_bodies_nonl I) |].
  constructor; [exact (wl_cut_rest_nonl I) | constructor].
Qed.

Lemma wl_cut_snoc_other (I : list (bv 8)) (b : bv 8) :
  b <> wl_nl -> wl_cut (I ++ [b]) = (bodies_of I, rest_of I ++ [b]).
Proof.
  intro Hb. apply wl_cut_app_nonl.
  exact (wl_nonl_cons_2 b [] Hb (not_elem_of_nil wl_nl)).
Qed.

Lemma bodies_of_snoc_nl (I : list (bv 8)) :
  bodies_of (I ++ [wl_nl]) = bodies_of I ++ [rest_of I].
Proof. by rewrite /bodies_of wl_cut_snoc_nl. Qed.

Lemma rest_of_snoc_nl (I : list (bv 8)) : rest_of (I ++ [wl_nl]) = [].
Proof. by rewrite /rest_of wl_cut_snoc_nl. Qed.

Lemma bodies_of_snoc_other (I : list (bv 8)) (b : bv 8) :
  b <> wl_nl -> bodies_of (I ++ [b]) = bodies_of I.
Proof. intro Hb. by rewrite /bodies_of (wl_cut_snoc_other I b Hb). Qed.

Lemma rest_of_snoc_other (I : list (bv 8)) (b : bv 8) :
  b <> wl_nl -> rest_of (I ++ [b]) = rest_of I ++ [b].
Proof. intro Hb. by rewrite /rest_of (wl_cut_snoc_other I b Hb). Qed.

(* ONE NEWLINE IS ONE ROUND.  This pair is what every division of the wire
   by a fixed line length becomes. *)
Lemma nlines_snoc_nl (I : list (bv 8)) : nlines (I ++ [wl_nl]) = S (nlines I).
Proof.
  rewrite /nlines bodies_of_snoc_nl length_app.
  change (length [rest_of I]) with 1%nat. lia.
Qed.

Lemma nlines_snoc_other (I : list (bv 8)) (b : bv 8) :
  b <> wl_nl -> nlines (I ++ [b]) = nlines I.
Proof. intro Hb. by rewrite /nlines (bodies_of_snoc_other I b Hb). Qed.

(* ---- the cut against S6's sequence of lines --------------------------- *)

Lemma wl_lines_join (wss : list (list (list (bv 8)))) :
  wl_join (wl_body <$> wss) = wl_lines wss.
Proof.
  induction wss as [| ws r IH]; [reflexivity |].
  rewrite fmap_cons wl_join_cons wl_lines_cons /wl_line -app_assoc IH.
  reflexivity.
Qed.

Lemma wl_cut_lines (wss : list (list (list (bv 8)))) (r : list (bv 8)) :
  Forall wl_wf wss -> wl_nl ∉ r ->
  wl_cut (wl_lines wss ++ r) = (wl_body <$> wss, r).
Proof.
  intros Hwf Hr. rewrite -wl_lines_join.
  exact (wl_cut_of_join (wl_body <$> wss) r (wl_body_fmap_nonl wss Hwf) Hr).
Qed.

(* ---- the cut is monotone in the input --------------------------------- *)

Lemma bodies_of_app (I k : list (bv 8)) :
  bodies_of I `prefix_of` bodies_of (I ++ k).
Proof.
  revert I. induction k as [| b k' IH]; intro I.
  - exists []. by rewrite !app_nil_r.
  - assert (Hs : I ++ b :: k' = (I ++ [b]) ++ k')
      by (rewrite -app_assoc; reflexivity).
    rewrite Hs. destruct (IH (I ++ [b])) as [m Hm].
    destruct (decide (b = wl_nl)) as [-> | Hb].
    + rewrite bodies_of_snoc_nl in Hm.
      exists ([rest_of I] ++ m). by rewrite Hm app_assoc.
    + rewrite (bodies_of_snoc_other I b Hb) in Hm. by exists m.
Qed.

Lemma bodies_of_prefix (I I' : list (bv 8)) :
  I `prefix_of` I' -> bodies_of I `prefix_of` bodies_of I'.
Proof. intros [k ->]. apply bodies_of_app. Qed.

Lemma nlines_app_le (I k : list (bv 8)) : nlines I <= nlines (I ++ k).
Proof. rewrite /nlines. apply prefix_length, bodies_of_app. Qed.

Lemma nlines_app_nl_lt (I k : list (bv 8)) :
  wl_nl ∈ k -> nlines I < nlines (I ++ k).
Proof.
  intro Hin. apply elem_of_list_split in Hin as (k1 & k2 & ->).
  assert (Hs : I ++ k1 ++ wl_nl :: k2 = ((I ++ k1) ++ [wl_nl]) ++ k2)
    by (rewrite -!app_assoc; reflexivity).
  rewrite Hs.
  pose proof (nlines_app_le ((I ++ k1) ++ [wl_nl]) k2) as H1.
  rewrite nlines_snoc_nl in H1.
  pose proof (nlines_app_le I k1) as H2. lia.
Qed.

Lemma rest_of_prefix (I I' : list (bv 8)) :
  I `prefix_of` I' -> nlines I = nlines I' -> rest_of I `prefix_of` rest_of I'.
Proof.
  intros [k ->] Heq.
  destruct (decide (wl_nl ∈ k)) as [Hin | Hni].
  - exfalso. pose proof (nlines_app_nl_lt I k Hin). lia.
  - rewrite /rest_of (wl_cut_app_nonl I k Hni). by exists k.
Qed.

(* the rest is empty exactly when the input ends at a newline -- the
   round-is-complete test, stated without arithmetic *)
Lemma rest_of_last_nl (I : list (bv 8)) :
  last I = Some wl_nl -> rest_of I = [].
Proof.
  induction I as [| b J IH] using rev_ind; intro Hl.
  - rewrite last_nil in Hl. discriminate.
  - rewrite last_snoc in Hl. injection Hl as Heq. subst b.
    exact (rest_of_snoc_nl J).
Qed.

Lemma rest_of_end (I : list (bv 8)) :
  rest_of I = [] -> I = [] \/ last I = Some wl_nl.
Proof.
  induction I as [| b J IH] using rev_ind; intro H; [by left |].
  right. rewrite last_snoc.
  destruct (decide (b = wl_nl)) as [-> | Hb]; [reflexivity |].
  exfalso. rewrite (rest_of_snoc_other J b Hb) in H.
  destruct (rest_of J) as [| a u]; discriminate.
Qed.

(* ---- S7.1  THE COMPLETE PART OF AN INPUT ----------------------------- *)

(* [done_of I] is the input TRUNCATED TO ITS COMPLETE LINES: the join of
   its bodies, each closed by the newline that closed it, with the partial
   line the user is in the middle of dropped.  It is equally the first
   [length I - length (rest_of I)] bytes of [I] ([done_of_app_rest] and
   [length_done_of]); the join is the definition because every law below
   is one rewrite of [wl_cut_of_join].

   WHAT IT IS FOR.  A discipline that pins the wire at every byte must
   name the whole input; one that pins it only at a line boundary names
   this.  So the echo application's D1 reads [done_of], and the partial
   line contributes nothing to the transcript it demands. *)
Definition done_of (I : list (bv 8)) : list (bv 8) := wl_join (bodies_of I).

Lemma done_of_nil : done_of [] = [].
Proof. by rewrite /done_of bodies_of_nil wl_join_nil. Qed.

(* the cut's two halves, with the complete one named *)
Lemma done_of_app_rest (I : list (bv 8)) : done_of I ++ rest_of I = I.
Proof. symmetry. exact (wl_cut_join I). Qed.

Lemma done_of_prefix (I : list (bv 8)) : done_of I `prefix_of` I.
Proof. exists (rest_of I). symmetry. exact (done_of_app_rest I). Qed.

Lemma length_done_of (I : list (bv 8)) :
  length (done_of I) = (length I - length (rest_of I))%nat.
Proof.
  rewrite -{2}(done_of_app_rest I) length_app. lia.
Qed.

(* the truncation IS complete: it parses to the same bodies and nothing is
   left over *)
Lemma wl_cut_done_of (I : list (bv 8)) : wl_cut (done_of I) = (bodies_of I, []).
Proof.
  rewrite /done_of -(app_nil_r (wl_join (bodies_of I))).
  apply wl_cut_of_join; [exact (wl_cut_bodies_nonl I) | apply not_elem_of_nil].
Qed.

Lemma bodies_of_done (I : list (bv 8)) : bodies_of (done_of I) = bodies_of I.
Proof. by rewrite /bodies_of wl_cut_done_of. Qed.

Lemma rest_of_done (I : list (bv 8)) : rest_of (done_of I) = [].
Proof. by rewrite /rest_of wl_cut_done_of. Qed.

Lemma nlines_done (I : list (bv 8)) : nlines (done_of I) = nlines I.
Proof. by rewrite /nlines bodies_of_done. Qed.

Lemma done_of_idemp (I : list (bv 8)) : done_of (done_of I) = done_of I.
Proof. by rewrite {1}/done_of bodies_of_done. Qed.

(* an input whose last byte is a newline is already complete *)
Lemma done_of_rest_nil (I : list (bv 8)) : rest_of I = [] -> done_of I = I.
Proof. intro Hr. by rewrite -{2}(done_of_app_rest I) Hr app_nil_r. Qed.

(* ...THE TWO SNOC STEPS.  The newline promotes the whole input; any other
   byte joins the partial line and changes nothing. *)
Lemma done_of_snoc_nl (I : list (bv 8)) : done_of (I ++ [wl_nl]) = I ++ [wl_nl].
Proof. apply done_of_rest_nil, rest_of_snoc_nl. Qed.

Lemma done_of_snoc_other (I : list (bv 8)) (b : bv 8) :
  b <> wl_nl -> done_of (I ++ [b]) = done_of I.
Proof. intro Hb. by rewrite /done_of (bodies_of_snoc_other I b Hb). Qed.

(* ...and it is monotone, which is what carries a discipline from a prefix
   of the input to the input *)
Lemma done_of_mono (I I' : list (bv 8)) :
  I `prefix_of` I' -> done_of I `prefix_of` done_of I'.
Proof.
  intro Hp. destruct (bodies_of_prefix I I' Hp) as [bs Hbs].
  exists (wl_join bs). by rewrite /done_of Hbs wl_join_app.
Qed.

(* ===================================================================== *)
(*  S7.2  THE WORDS OF A BODY                                             *)
(*                                                                        *)
(*  Same shape as the cut with [wl_sp] for [wl_nl], except that there is   *)
(*  no closing blank: a trailing word is a word.  The parser is TOTAL --   *)
(*  it parses a malformed body too, and what rejects one is [wl_wf] or     *)
(*  [wl_body (wl_words l) <> l], never the parser.  Two blanks in a row    *)
(*  parse to an EMPTY word, which [wl_word] refuses; a trailing blank      *)
(*  parses to the words before it, whose body is then shorter than the     *)
(*  input.                                                                 *)
(* ===================================================================== *)

Fixpoint wl_words (l : list (bv 8)) : list (list (bv 8)) :=
  match l with
  | [] => []
  | b :: l' =>
      let ws := wl_words l' in
      if decide (b = wl_sp) then [] :: ws
      else match ws with
           | [] => [[b]]
           | w :: r => (b :: w) :: r
           end
  end.

Definition last_ws (I : list (bv 8)) : list (list (bv 8)) :=
  wl_words (default [] (last (bodies_of I))).

Lemma wl_words_nil : wl_words [] = [].
Proof. reflexivity. Qed.

Lemma wl_words_cons_sp (l : list (bv 8)) :
  wl_words (wl_sp :: l) = [] :: wl_words l.
Proof.
  cbn [wl_words]. case_decide as Hc; [reflexivity |]. exfalso. by apply Hc.
Qed.

Lemma wl_words_cons_other_nil (b : bv 8) (l : list (bv 8)) :
  b <> wl_sp -> wl_words l = [] -> wl_words (b :: l) = [[b]].
Proof.
  intros Hb Hl. cbn [wl_words].
  case_decide as Hc; [exfalso; exact (Hb Hc) |]. by rewrite Hl.
Qed.

Lemma wl_words_cons_other_cons (b : bv 8) (l : list (bv 8))
    (w : list (bv 8)) (r : list (list (bv 8))) :
  b <> wl_sp -> wl_words l = w :: r -> wl_words (b :: l) = (b :: w) :: r.
Proof.
  intros Hb Hl. cbn [wl_words].
  case_decide as Hc; [exfalso; exact (Hb Hc) |]. by rewrite Hl.
Qed.

Lemma wl_alnum_ne_sp (b : bv 8) : wl_alnum b -> b <> wl_sp.
Proof. intros Hb Heq. rewrite Heq in Hb. exact (wl_alnum_not_sp Hb). Qed.

(* a word's bytes never break a word, so prepending one onto a parse that
   already has a first word only grows that word *)
Lemma wl_words_prepend (w : list (bv 8)) :
  forall (l w0 : list (bv 8)) (r : list (list (bv 8))),
    Forall wl_alnum w -> wl_words l = w0 :: r ->
    wl_words (w ++ l) = (w ++ w0) :: r.
Proof.
  induction w as [| b w' IH]; intros l w0 r Hw Hl; [exact Hl |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  change ((b :: w') ++ l) with (b :: (w' ++ l)).
  by rewrite (wl_words_cons_other_cons b (w' ++ l) (w' ++ w0) r
                (wl_alnum_ne_sp b Hb) (IH l w0 r Hw' Hl)).
Qed.

Lemma wl_words_word (w : list (bv 8)) :
  Forall wl_alnum w -> w <> [] -> wl_words w = [w].
Proof.
  induction w as [| b w' IH]; intros Hw Hne; [by destruct (Hne eq_refl) |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  destruct w' as [| b1 w1].
  - exact (wl_words_cons_other_nil b [] (wl_alnum_ne_sp b Hb) wl_words_nil).
  - assert (Hne1 : b1 :: w1 <> []) by discriminate.
    by rewrite (wl_words_cons_other_cons b (b1 :: w1) (b1 :: w1) []
                  (wl_alnum_ne_sp b Hb) (IH Hw' Hne1)).
Qed.

(* THE WORD PARSER'S SPEC: on a well-formed body it inverts [wl_body].
   Everything a round reads off the input goes through this. *)
Lemma wl_words_body (ws : list (list (bv 8))) :
  wl_wf ws -> wl_words (wl_body ws) = ws.
Proof.
  induction ws as [| w r IH]; intro Hwf; [reflexivity |].
  destruct (wl_wf_cons w r Hwf) as [[Hne Ha] Hr].
  rewrite wl_body_cons.
  destruct r as [| w1 r1].
  - cbn [wl_tail]. rewrite app_nil_r. exact (wl_words_word w Ha Hne).
  - rewrite wl_tail_cons.
    assert (Hsp : wl_words (wl_sp :: wl_body (w1 :: r1)) = [] :: (w1 :: r1))
      by (rewrite wl_words_cons_sp (IH Hr); reflexivity).
    rewrite (wl_words_prepend w (wl_sp :: wl_body (w1 :: r1)) [] (w1 :: r1)
               Ha Hsp).
    by rewrite app_nil_r.
Qed.

(* ...AND THE BYTES A WELL-FORMED WORD LIST CAME FROM (the PROGRAM
   STREAM).  [wl_words_body] inverts [wl_body] on a well-formed word list;
   this is the fact ABOUT THE INPUT that does not need the round trip: if
   every word the parser found is alphanumeric then every byte it read was
   alphanumeric or a blank, because a byte is either a blank or inside the
   word it opened.  It is what refutes a REDIRECT body at an echo line --
   the '>' is neither -- without knowing that the body rebuilds itself. *)
Lemma wl_words_nil_inv (l : list (bv 8)) : wl_words l = [] -> l = [].
Proof.
  destruct l as [| b l']; [reflexivity |].
  destruct (decide (b = wl_sp)) as [-> | Hb].
  - rewrite wl_words_cons_sp. discriminate.
  - destruct (wl_words l') as [| w r] eqn:Hws.
    + rewrite (wl_words_cons_other_nil b l' Hb Hws). discriminate.
    + rewrite (wl_words_cons_other_cons b l' w r Hb Hws). discriminate.
Qed.

Lemma wl_words_alnum_body (l : list (bv 8)) :
  Forall (Forall wl_alnum) (wl_words l) -> Forall wl_body_byte l.
Proof.
  induction l as [| b l' IH]; intro H; [constructor |].
  destruct (decide (b = wl_sp)) as [-> | Hb].
  - rewrite wl_words_cons_sp in H.
    destruct (Forall_cons_1 _ _ _ H) as [_ H'].
    constructor; [ by right | exact (IH H') ].
  - destruct (wl_words l') as [| w r] eqn:Hws.
    + rewrite (wl_words_cons_other_nil b l' Hb Hws) in H.
      destruct (Forall_cons_1 _ _ _ H) as [Hbw _].
      destruct (Forall_cons_1 _ _ _ Hbw) as [Hba _].
      rewrite (wl_words_nil_inv l' Hws).
      constructor; [ by left | constructor ].
    + rewrite (wl_words_cons_other_cons b l' w r Hb Hws) in H.
      destruct (Forall_cons_1 _ _ _ H) as [Hbw Hr].
      destruct (Forall_cons_1 _ _ _ Hbw) as [Hba Hw].
      constructor; [ by left | apply IH; rewrite ?Hws; by constructor ].
Qed.

Lemma wl_wf_alnum (ws : list (list (bv 8))) :
  wl_wf ws -> Forall (Forall wl_alnum) ws.
Proof.
  rewrite /wl_wf. intro H.
  induction H as [| w r Hw _ IH]; constructor;
    [ exact (proj2 Hw) | exact IH ].
Qed.

(* THE INPUT'S LAST BODY, at the index [FileHooks.fline] reads it at
   (the PROGRAM STREAM).  [last_ws] says [default [] (last ...)]; an era
   that types its own lines indexes the same body positionally, and these
   are the same body. *)
Lemma last_default_lookup_total (bs : list (list (bv 8))) :
  default [] (last bs) = bs !!! (length bs - 1)%nat.
Proof.
  induction bs as [| b bs' IH] using rev_ind; [reflexivity |].
  rewrite last_snoc length_app /=.
  replace (length bs' + 1 - 1)%nat with (length bs') by lia.
  rewrite lookup_total_app_r; [| lia].
  by rewrite Nat.sub_diag.
Qed.

Lemma last_ws_lastbody (I : list (bv 8)) :
  last_ws I = wl_words (bodies_of I !!! (nlines I - 1)%nat).
Proof. by rewrite /last_ws /nlines last_default_lookup_total. Qed.

Lemma lastbody_snoc_nl (I : list (bv 8)) :
  bodies_of (I ++ [wl_nl]) !!! (nlines (I ++ [wl_nl]) - 1)%nat = rest_of I.
Proof.
  rewrite /nlines. rewrite <- last_default_lookup_total.
  rewrite bodies_of_snoc_nl. rewrite last_snoc. reflexivity.
Qed.

(* the words the round that just closed typed *)
Lemma last_ws_snoc_nl (I : list (bv 8)) :
  last_ws (I ++ [wl_nl]) = wl_words (rest_of I).
Proof. by rewrite /last_ws bodies_of_snoc_nl last_snoc. Qed.

(* ===================================================================== *)
(*  S7.3  DETERMINACY: THE LAW THAT REPLACES THE DIVISION                 *)
(*                                                                        *)
(*  With one fixed line, which round a wire position falls in is a         *)
(*  quotient.  Here it is read off the parse instead, and what makes that  *)
(*  sound is that the parse of a PREFIX is a prefix of the parse: two      *)
(*  inputs whose wires are nested are themselves nested, body for body,    *)
(*  with the shorter one's remainder sitting inside the longer one's next   *)
(*  body.  [wl_cut_prefix_of] is the converse, which is how an input       *)
(*  prefix is REBUILT from its cut.                                        *)
(* ===================================================================== *)

Lemma wl_nl_head_not_nonl (t : list (bv 8)) (b : bv 8) :
  head (wl_nl :: t) = Some b -> ~ (b <> wl_nl).
Proof. intros [= <-] H. by apply H. Qed.

(* a raw line and its remainder determine each other -- [wl_split_pred]
   at [P := fun b => b <> wl_nl] *)
Lemma wl_raw_line_det (l l' t t' : list (bv 8)) :
  wl_nl ∉ l -> wl_nl ∉ l' ->
  l ++ wl_nl :: t = l' ++ wl_nl :: t' -> l = l' /\ t = t'.
Proof.
  intros Hl Hl' Heq.
  destruct (wl_split_pred (fun b => b <> wl_nl)
              l (wl_nl :: t) l' (wl_nl :: t')
              (wl_nonl_Forall l Hl) (wl_nonl_Forall l' Hl')
              (wl_nl_head_not_nonl t) (wl_nl_head_not_nonl t') Heq)
    as [Hb Ht].
  split; [exact Hb | by injection Ht].
Qed.

Lemma wl_raw_line_prefix_det (l l' t t' : list (bv 8)) :
  wl_nl ∉ l -> wl_nl ∉ l' ->
  l ++ wl_nl :: t `prefix_of` l' ++ wl_nl :: t' ->
  l = l' /\ t `prefix_of` t'.
Proof.
  intros Hl Hl' [k Hk]. rewrite -app_assoc in Hk.
  destruct (wl_raw_line_det l l' (t ++ k) t' Hl Hl' (eq_sym Hk)) as [-> Ht].
  split; [reflexivity | by exists k].
Qed.

(* a newline-free remainder cannot cover a whole line *)
Lemma wl_raw_line_not_prefix_nonl (l t r : list (bv 8)) :
  wl_nl ∉ r -> l ++ wl_nl :: t `prefix_of` r -> False.
Proof.
  intros Hr [k Hk]. rewrite Hk in Hr. apply Hr.
  apply elem_of_app. left. apply elem_of_app. right. apply elem_of_list_here.
Qed.

(* ...so a newline-free prefix of a line stops inside the body *)
Lemma wl_prefix_nonl_of_line (r l t : list (bv 8)) :
  wl_nl ∉ r -> r `prefix_of` l ++ wl_nl :: t -> r `prefix_of` l.
Proof.
  revert r. induction l as [| a l' IH]; intros r Hr Hp.
  - rewrite app_nil_l in Hp.
    destruct r as [| b r']; [apply prefix_nil |].
    exfalso. apply Hr.
    assert (Hba : b = wl_nl) by (apply prefix_cons_inv_1 in Hp; exact Hp).
    rewrite Hba. apply elem_of_list_here.
  - change ((a :: l') ++ wl_nl :: t) with (a :: (l' ++ wl_nl :: t)) in Hp.
    destruct r as [| b r']; [apply prefix_nil |].
    assert (Hba : b = a) by (apply prefix_cons_inv_1 in Hp; exact Hp).
    assert (Hrest : r' `prefix_of` l' ++ wl_nl :: t)
      by (apply prefix_cons_inv_2 in Hp; exact Hp).
    destruct (wl_nonl_cons b r' Hr) as [_ Hr'].
    subst b. apply prefix_cons, (IH r' Hr' Hrest).
Qed.

(* THE DETERMINACY, at the join: nested wires are nested body for body,
   and the shorter remainder lands where the parse says it does. *)
Lemma wl_join_prefix_det (bs1 bs2 : list (list (bv 8)))
    (r1 r2 : list (bv 8)) :
  Forall (fun l => wl_nl ∉ l) bs1 -> Forall (fun l => wl_nl ∉ l) bs2 ->
  wl_nl ∉ r1 -> wl_nl ∉ r2 ->
  wl_join bs1 ++ r1 `prefix_of` wl_join bs2 ++ r2 ->
  bs1 `prefix_of` bs2
  /\ (length bs1 = length bs2 -> r1 `prefix_of` r2)
  /\ (length bs1 < length bs2 -> r1 `prefix_of` bs2 !!! length bs1).
Proof.
  intros Hb1 Hb2 Hr1 Hr2 Hp.
  pose proof (wl_cut_of_join bs1 r1 Hb1 Hr1) as Hc1.
  pose proof (wl_cut_of_join bs2 r2 Hb2 Hr2) as Hc2.
  assert (Hbo1 : bodies_of (wl_join bs1 ++ r1) = bs1)
    by (rewrite /bodies_of Hc1; reflexivity).
  assert (Hbo2 : bodies_of (wl_join bs2 ++ r2) = bs2)
    by (rewrite /bodies_of Hc2; reflexivity).
  assert (Hre1 : rest_of (wl_join bs1 ++ r1) = r1)
    by (rewrite /rest_of Hc1; reflexivity).
  assert (Hre2 : rest_of (wl_join bs2 ++ r2) = r2)
    by (rewrite /rest_of Hc2; reflexivity).
  assert (Hpb : bs1 `prefix_of` bs2).
  { pose proof (bodies_of_prefix _ _ Hp) as H. by rewrite Hbo1 Hbo2 in H. }
  split; [exact Hpb |]. split.
  - intro Hlen.
    assert (Hn : nlines (wl_join bs1 ++ r1) = nlines (wl_join bs2 ++ r2))
      by (rewrite /nlines Hbo1 Hbo2; exact Hlen).
    pose proof (rest_of_prefix _ _ Hp Hn) as H. by rewrite Hre1 Hre2 in H.
  - intro Hlt. destruct Hpb as [ls Hls]. destruct ls as [| l ls'].
    { exfalso. rewrite app_nil_r in Hls. rewrite Hls in Hlt. lia. }
    assert (Hidx : bs2 !!! length bs1 = l).
    { rewrite Hls list_lookup_total_alt
        (lookup_app_r bs1 (l :: ls') (length bs1) ltac:(lia)) Nat.sub_diag.
      reflexivity. }
    rewrite Hidx.
    assert (Hsp : wl_join bs2 ++ r2
                  = wl_join bs1 ++ (l ++ wl_nl :: (wl_join ls' ++ r2))).
    { rewrite Hls wl_join_app -app_assoc (wl_join_cons_app l ls' r2).
      reflexivity. }
    rewrite Hsp in Hp.
    exact (wl_prefix_nonl_of_line r1 l (wl_join ls' ++ r2) Hr1
             (wl_prefix_app_cancel _ _ _ Hp)).
Qed.

(* ...AND ITS CONVERSE: the three clauses below are exactly what
   [wl_join_prefix_det] hands back, so the two together say that the cut
   and the input's prefix order determine each other.  The input prefix is
   rebuilt from the cut via [wl_cut_join]. *)
Lemma wl_cut_prefix_of (I I' : list (bv 8)) :
  bodies_of I `prefix_of` bodies_of I' ->
  (nlines I = nlines I' -> rest_of I `prefix_of` rest_of I') ->
  (nlines I < nlines I' -> rest_of I `prefix_of` bodies_of I' !!! nlines I) ->
  I `prefix_of` I'.
Proof.
  intros [ls Hls] Heq Hlt. destruct ls as [| l ls'].
  - rewrite app_nil_r in Hls.
    assert (Hn : nlines I = nlines I')
      by (rewrite /nlines Hls; reflexivity).
    destruct (Heq Hn) as [m Hm].
    assert (HI' : I' = (wl_join (bodies_of I) ++ rest_of I) ++ m).
    { transitivity (wl_join (bodies_of I') ++ rest_of I');
        [exact (wl_cut_join I') |].
      rewrite Hls Hm. exact (app_assoc _ _ _). }
    exists m. rewrite (wl_cut_join I). exact HI'.
  - assert (Hn : nlines I < nlines I').
    { rewrite /nlines Hls length_app.
      change (length (l :: ls')) with (S (length ls')). lia. }
    assert (Hidx : bodies_of I' !!! nlines I = l).
    { rewrite /nlines Hls list_lookup_total_alt
        (lookup_app_r (bodies_of I) (l :: ls') (length (bodies_of I))
           ltac:(lia)) Nat.sub_diag.
      reflexivity. }
    destruct (Hlt Hn) as [m Hm]. rewrite Hidx in Hm.
    assert (HI' : I' = (wl_join (bodies_of I) ++ rest_of I)
                        ++ (m ++ wl_nl :: (wl_join ls' ++ rest_of I'))).
    { transitivity (wl_join (bodies_of I') ++ rest_of I');
        [exact (wl_cut_join I') |].
      rewrite Hls wl_join_app wl_join_cons Hm.
      exact (wl_reshape _ _ _ _ _ _). }
    exists (m ++ wl_nl :: (wl_join ls' ++ rest_of I')).
    rewrite (wl_cut_join I). exact HI'.
Qed.

(* ---- decidability: the parser IS the witness, so nothing searches ----- *)

Global Instance wl_body_byte_dec b : Decision (wl_body_byte b).
Proof. rewrite /wl_body_byte. apply _. Defined.

Global Instance wl_body_bytes_dec l : Decision (Forall wl_body_byte l).
Proof. apply _. Defined.

(* ===================================================================== *)
(*  ANTI-VACUITY: the parse of a real input, by computation.  Two         *)
(*  complete lines -- one of a single two-letter word, one of two         *)
(*  one-letter words -- and a third line the user has only started.       *)
(* ===================================================================== *)

Definition wl_demo_in : list (bv 8) :=
  [wl_demo_a; wl_demo_b; wl_nl;
   wl_demo_a; wl_sp; wl_demo_b; wl_nl;
   wl_demo_b].

Lemma wl_demo_bodies :
  bodies_of wl_demo_in
  = [[wl_demo_a; wl_demo_b]; [wl_demo_a; wl_sp; wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_rest : rest_of wl_demo_in = [wl_demo_b].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_words :
  wl_words [wl_demo_a; wl_sp; wl_demo_b] = [[wl_demo_a]; [wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ===================================================================== *)
(*  S9  THE FILE-NAME WORD (cut W4; design of record:                     *)
(*  claude-notes/design/filenames.md section 0, law L1).                  *)
(*                                                                        *)
(*  A user file's name is a word over ONE more byte than a command word:  *)
(*  the alphanumerics and the dot.  The dot is neither a blank nor one of *)
(*  sh's metacharacters, so everything the word parser and sh's lexer     *)
(*  know of a [wl_word] they know of an [fn_word]: [wl_words] reads it    *)
(*  back whole, and [UkShWords] lexes it as one token.  What the dot must *)
(*  NOT do is widen what an ECHO word or a GREP pattern may be -- those   *)
(*  stay [wl_word], and the dot reaches a line only at a file-name       *)
(*  position ([FileDisc.parse_line], [PipesDisc.prod_parse]).  [fn_wf]    *)
(*  is the argv of an exec, whose words may be either.                    *)
(* ===================================================================== *)

Definition fn_dot : bv 8 := Z_to_bv 8 46%Z.

Lemma fn_dot_val : bv_unsigned fn_dot = 46%Z.
Proof. by vm_compute. Qed.

Definition fn_byte (b : bv 8) : Prop := wl_alnum b \/ b = fn_dot.

Global Instance fn_byte_dec b : Decision (fn_byte b).
Proof. rewrite /fn_byte. apply _. Defined.

Definition fn_word (w : list (bv 8)) : Prop := w <> [] /\ Forall fn_byte w.

Global Instance fn_word_dec w : Decision (fn_word w).
Proof. rewrite /fn_word. apply _. Defined.

Definition fn_wf (ws : list (list (bv 8))) : Prop := Forall fn_word ws.

Global Instance fn_wf_dec ws : Decision (fn_wf ws).
Proof. rewrite /fn_wf. apply _. Defined.

Lemma fn_byte_val (b : bv 8) :
  fn_byte b ->
  bv_unsigned b = 46%Z
  \/ (48 <= bv_unsigned b <= 57)%Z \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intros [Ha | ->]; [right; exact Ha | left; exact fn_dot_val].
Qed.

Lemma fn_byte_of_alnum (b : bv 8) : wl_alnum b -> fn_byte b.
Proof. by left. Qed.

Lemma fn_byte_ne_sp (b : bv 8) : fn_byte b -> b <> wl_sp.
Proof.
  intros Hb ->. apply fn_byte_val in Hb. rewrite wl_sp_val in Hb. lia.
Qed.

Lemma fn_byte_ne_nl (b : bv 8) : fn_byte b -> b <> wl_nl.
Proof.
  intros Hb ->. apply fn_byte_val in Hb. rewrite wl_nl_val in Hb. lia.
Qed.

Lemma wl_word_fn (w : list (bv 8)) : wl_word w -> fn_word w.
Proof.
  intros [Hne Hw]. split; [exact Hne |].
  eapply Forall_impl; [exact Hw | exact fn_byte_of_alnum].
Qed.

Lemma wl_wf_fn (ws : list (list (bv 8))) : wl_wf ws -> fn_wf ws.
Proof.
  intros H. eapply Forall_impl; [exact H | exact wl_word_fn].
Qed.

Lemma fn_wf_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  fn_wf (w :: r) -> fn_word w /\ fn_wf r.
Proof. rewrite /fn_wf. apply Forall_cons_1. Qed.

Lemma fn_word_pos (w : list (bv 8)) : fn_word w -> 0 < length w.
Proof. intros [Hne _]. destruct w as [| b w']; [done | cbn; lia]. Qed.

(* the word parser on a word of name bytes: the same three steps as
   [wl_words_prepend] / [wl_words_word] / [wl_words_body], since all
   they read of a byte is that it is not the blank *)
Lemma wl_words_prepend_fn (w : list (bv 8)) :
  forall (l w0 : list (bv 8)) (r : list (list (bv 8))),
    Forall fn_byte w -> wl_words l = w0 :: r ->
    wl_words (w ++ l) = (w ++ w0) :: r.
Proof.
  induction w as [| b w' IH]; intros l w0 r Hw Hl; [exact Hl |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  change ((b :: w') ++ l) with (b :: (w' ++ l)).
  by rewrite (wl_words_cons_other_cons b (w' ++ l) (w' ++ w0) r
                (fn_byte_ne_sp b Hb) (IH l w0 r Hw' Hl)).
Qed.

Lemma wl_words_word_fn (w : list (bv 8)) : fn_word w -> wl_words w = [w].
Proof.
  intros [Hne Hw].
  induction w as [| b w' IH]; [by destruct (Hne eq_refl) |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  destruct w' as [| b1 w1].
  - exact (wl_words_cons_other_nil b [] (fn_byte_ne_sp b Hb) wl_words_nil).
  - assert (Hne1 : b1 :: w1 <> []) by discriminate.
    by rewrite (wl_words_cons_other_cons b (b1 :: w1) (b1 :: w1) []
                  (fn_byte_ne_sp b Hb) (IH Hne1 Hw')).
Qed.

Lemma wl_words_body_fn (ws : list (list (bv 8))) :
  fn_wf ws -> wl_words (wl_body ws) = ws.
Proof.
  induction ws as [| w r IH]; intro Hwf; [reflexivity |].
  destruct (fn_wf_cons w r Hwf) as [Hword Hr].
  rewrite wl_body_cons.
  destruct r as [| w1 r1].
  - cbn [wl_tail]. rewrite app_nil_r. exact (wl_words_word_fn w Hword).
  - rewrite wl_tail_cons.
    assert (Hsp : wl_words (wl_sp :: wl_body (w1 :: r1)) = [] :: (w1 :: r1))
      by (rewrite wl_words_cons_sp (IH Hr); reflexivity).
    rewrite (wl_words_prepend_fn w (wl_sp :: wl_body (w1 :: r1)) [] (w1 :: r1)
               (proj2 Hword) Hsp).
    by rewrite app_nil_r.
Qed.

(* every byte of a body of name words: a name byte or the blank *)
Lemma wl_body_bytes_fn (ws : list (list (bv 8))) :
  fn_wf ws -> Forall (fun b => fn_byte b \/ b = wl_sp) (wl_body ws).
Proof.
  assert (Ht : forall r, fn_wf r ->
            Forall (fun b => fn_byte b \/ b = wl_sp) (wl_tail r)).
  { induction r as [| w r IH]; intro Hwf; cbn [wl_tail]; [constructor |].
    destruct (fn_wf_cons w r Hwf) as [[_ Hw] Hr].
    constructor; [by right |].
    apply Forall_app. split; [| exact (IH Hr)].
    eapply Forall_impl; [exact Hw | intros b Hb; by left]. }
  intro Hwf. destruct ws as [| w r]; cbn [wl_body]; [constructor |].
  destruct (fn_wf_cons w r Hwf) as [[_ Hw] Hr].
  apply Forall_app. split; [| exact (Ht r Hr)].
  eapply Forall_impl; [exact Hw | intros b Hb; by left].
Qed.

(* ...and the whole line's, numerically: [wl_line_byte_val] with the dot *)
Lemma wl_line_byte_val_fn (ws : list (list (bv 8))) (b : bv 8) :
  fn_wf ws -> b ∈ wl_line ws ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z \/ bv_unsigned b = 46%Z
  \/ (48 <= bv_unsigned b <= 57)%Z \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intros Hwf Hin. rewrite /wl_line in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - apply elem_of_list_lookup_1 in Hin as [i Hi].
    destruct (Forall_lookup_1 _ _ _ _ (wl_body_bytes_fn ws Hwf) Hi) as [Hb | ->].
    + apply fn_byte_val in Hb. tauto.
    + rewrite wl_sp_val. tauto.
  - apply elem_of_list_singleton in Hin as ->. rewrite wl_nl_val. tauto.
Qed.
