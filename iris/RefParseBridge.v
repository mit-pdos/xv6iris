(* ===================================================================== *)
(* RefParseBridge.v -- THE LANDED TOKEN MODELS ARE THE REFERENCE PARSER'S *)
(* INSTANCES (design/user-once.md SS2, worklist A1).                       *)
(*                                                                        *)
(* The three parser tiers each speak a pure model of THEIR line:          *)
(*                                                                        *)
(*   symbol-free   [UkShParse.ushp_no_symbols] + [ushp_tokens]            *)
(*   redirect      [UkShParseSym.ushs_redir]   + [ushs_toks] at the '>'   *)
(*   pipe          [UkShPipeLex.ushq_pipe]     + [ushs_toks] at the '|'   *)
(*                                                                        *)
(* and each walk is stated at its model.  This file proves that every one *)
(* of those models is [RefParse.ref_parsecmd len f = Some t] at the tree   *)
(* the walk answers -- so a walk re-stated at the reference (A2) recovers *)
(* the landed statement as a corollary, and a line shape is one equation  *)
(* about the reference on the line predicate the child laws speak         *)
(* ([UkSh.ush_line_is], [UkShRedirLine.ushs_line_is],                     *)
(* [UkShPipeLex.ushq_line_is]).                                           *)
(*                                                                        *)
(* Sits above the three model files and [UkShWords]/[UShLexRedir] (whose  *)
(* word-list tokenization theorems the line-shape facts reuse).  Pure: no *)
(* Iris proposition anywhere in it.                                       *)
(*                                                                        *)
(* THE ONE PREMISE EVERY BRIDGE CARRIES: the line's body bytes are         *)
(* non-NUL ([ref_nonnul]).  The walks have it from [ustr]; the line        *)
(* predicates imply it (every byte is alphanumeric, a blank, a symbol or   *)
(* the newline), and the line-shape facts discharge it.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.
Require Import LineWords.
Require Import UkShParse.
Require Import RefParse.
Require Import UkShParseSym.
Require Import UkShRedirLine.
Require Import UkShWords.
Require Import UShLexRedir.
Require Import UkShPipeLex.
Require Import RefParseSym.
Require UkSh.
Import UkShParse.
Local Open Scope nat_scope.


(* ===================================================================== *)
(* §0 THE CURSOR LEMMAS: what one step of the reference computes           *)
(* ===================================================================== *)

Lemma rb_bar_is_ushq : ushq_bar = rb_bar.
Proof using. reflexivity. Qed.

(* ---- the argument loop -------------------------------------------------- *)

(* at the end of the line the loop stops with what it has *)
Lemma ref_args_nul (len : nat) (f : nat -> bv 8) (n i : nat)
    (toks : list (nat * nat)) (rs : list rredir) :
  0 < n -> ref_skip len f i = len -> ref_args len f n i toks rs = Some (toks, rs, len).
Proof using.
  intros Hn Hs. destruct n as [| n ]; [ lia | ]. cbn [ref_args].
  rewrite (ref_peek_end _ _ _ _ Hs ref_symtoks_stop). cbn beta iota.
  rewrite (ref_gettoken_nul len f len (ref_skip_at_len len f)). cbn beta iota.
  rewrite (bool_decide_eq_true_2 _ eq_refl). reflexivity.
Qed.

(* one turn of the loop on a word: the word is appended and parseredirs
   runs at the cursor after it *)
Lemma ref_args_step (len : nat) (f : nat -> bv 8) (n i s n0 : nat)
    (acc : list (nat * nat)) (rs : list rredir) :
  ref_nonnul len f -> i <= len -> ref_skip len f i = s -> s < len ->
  ushp_is_sym (f s) = false -> ushp_toklen (len - s) s f = n0 ->
  length acc < 9 ->
  ref_args len f (S n) i acc rs
  = match ref_redirs len f n (ref_skip len f (s + n0)) rs with
    | Some (rs', s2) => ref_args len f n s2 (acc ++ [(s, s + n0)]) rs'
    | None => None
    end.
Proof using.
  intros Hnn Hi Hs Hlt Hsym Hn0 Hacc. cbn [ref_args].
  rewrite (ref_peek_miss len f i [rb_bar; rb_rpar; rb_amp; rb_semi]);
    [ | rewrite Hs; apply ref_at_notin; [ intros _; exact Hsym | exact ref_symtoks_stop ] ].
  rewrite Hs. cbn beta iota.
  assert (Hss : ref_skip len f s = s) by (rewrite <- Hs at 1; rewrite (ref_skip_idem _ _ _ Hi); exact Hs).
  rewrite (ref_gettoken_word len f s s Hnn Hss Hlt Hsym). cbn beta iota zeta.
  unfold ref_tokend. rewrite Hn0.
  rewrite (bool_decide_eq_false_2 _ rt_word_ne_0), (bool_decide_eq_true_2 _ eq_refl).
  cbn [negb].
  rewrite (bool_decide_eq_false_2 (10 <= length (acc ++ [(s, s + n0)]))
             ltac:(rewrite ushp_len_app1; lia)).
  reflexivity.
Qed.

(* ---- the & loop at the end of the line ---------------------------------- *)

Lemma ref_backs_len (len : nat) (f : nat -> bv 8) (n : nat) (t : ushp_cmd) :
  0 < n -> ref_backs len f n len t = Some (t, len).
Proof using.
  intro Hn. destruct n as [| n ]; [ lia | ]. cbn [ref_backs].
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_amp). reflexivity.
Qed.

(* ===================================================================== *)
(* §1 FUEL: more is never different                                       *)
(* ===================================================================== *)

Lemma ref_redirs_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat)
    (acc : list rredir) (r : list rredir * nat) :
  n <= n' -> ref_redirs len f n i acc = Some r -> ref_redirs len f n' i acc = Some r.
Proof using.
  revert n' i acc. induction n as [| n IH ]; intros n' i acc Hle H; [ discriminate H | ].
  destruct n' as [| n' ]; [ lia | ]. cbn [ref_redirs] in H |- *.
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ].
  destruct hit; [ | exact H ].
  destruct (ref_gettoken len f s) as [[[ tok q0 ] eq0 ] s1 ].
  destruct (ref_gettoken len f s1) as [[[ t2 q ] eq ] s2 ].
  destruct (bool_decide (t2 = rt_word)); [ | discriminate H ].
  destruct (rredir_of tok q eq); [ | discriminate H ].
  apply IH; [ lia | exact H ].
Qed.

Lemma ref_args_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat)
    (toks : list (nat * nat)) (rs : list rredir) (r : list (nat * nat) * list rredir * nat) :
  n <= n' -> ref_args len f n i toks rs = Some r -> ref_args len f n' i toks rs = Some r.
Proof using.
  revert n' i toks rs. induction n as [| n IH ]; intros n' i toks rs Hle H; [ discriminate H | ].
  destruct n' as [| n' ]; [ lia | ]. cbn [ref_args] in H |- *.
  destruct (ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi]) as [ stop s ].
  destruct stop; [ exact H | ].
  destruct (ref_gettoken len f s) as [[[ tok q ] eq ] s1 ].
  destruct (bool_decide (tok = 0%Z)); [ exact H | ].
  destruct (negb (bool_decide (tok = rt_word))); [ discriminate H | ].
  cbv zeta in H |- *.
  destruct (bool_decide (10 <= length (toks ++ [(q, eq)]))); [ discriminate H | ].
  destruct (ref_redirs len f n s1 rs) as [[ rs' s2 ] | ] eqn:E; [ | discriminate H ].
  rewrite (ref_redirs_fuel len f n n' s1 rs _ ltac:(lia) E).
  apply IH; [ lia | exact H ].
Qed.

Lemma ref_parseexec_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat) (r : ushp_cmd * nat) :
  n <= n' -> ref_parseexec len f n i = Some r -> ref_parseexec len f n' i = Some r.
Proof using.
  intros Hle H. unfold ref_parseexec in H |- *.
  destruct (ref_peek len f i [rb_lpar]) as [ blk s ].
  destruct blk; [ discriminate H | ].
  destruct (ref_redirs len f n s []) as [[ rs s1 ] | ] eqn:E; [ | discriminate H ].
  rewrite (ref_redirs_fuel len f n n' s [] _ Hle E).
  destruct (ref_args len f n s1 [] rs) as [[[ toks rs' ] s2 ] | ] eqn:E2; [ | discriminate H ].
  rewrite (ref_args_fuel len f n n' s1 [] rs _ Hle E2). exact H.
Qed.

Lemma ref_parsepipe_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat) (r : ushp_cmd * nat) :
  n <= n' -> ref_parsepipe len f n i = Some r -> ref_parsepipe len f n' i = Some r.
Proof using.
  revert n' i r. induction n as [| n IH ]; intros n' i r Hle H; [ discriminate H | ].
  destruct n' as [| n' ]; [ lia | ]. cbn [ref_parsepipe] in H |- *.
  destruct (ref_parseexec len f n i) as [[ t s ] | ] eqn:E; [ | discriminate H ].
  rewrite (ref_parseexec_fuel len f n n' i _ ltac:(lia) E).
  destruct (ref_peek len f s [rb_bar]) as [ bar s1 ].
  destruct bar; [ | exact H ].
  destruct (ref_gettoken len f s1) as [[[ tok q ] eq ] s2 ].
  destruct (ref_parsepipe len f n s2) as [[ t' s3 ] | ] eqn:E2; [ | discriminate H ].
  rewrite (IH n' s2 _ ltac:(lia) E2). exact H.
Qed.

Lemma ref_backs_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat) (t : ushp_cmd)
    (r : ushp_cmd * nat) :
  n <= n' -> ref_backs len f n i t = Some r -> ref_backs len f n' i t = Some r.
Proof using.
  revert n' i t. induction n as [| n IH ]; intros n' i t Hle H; [ discriminate H | ].
  destruct n' as [| n' ]; [ lia | ]. cbn [ref_backs] in H |- *.
  destruct (ref_peek len f i [rb_amp]) as [ amp s ].
  destruct amp; [ | exact H ].
  destruct (ref_gettoken len f s) as [[[ tok q ] eq ] s1 ].
  apply IH; [ lia | exact H ].
Qed.

(* (this needed [ref_backs] to fail at fuel 0, as every other loop does: the
   line  a & & & &  at fuels 4 and 5 answered two different [Some]s before) *)
Lemma ref_parseline_fuel (len : nat) (f : nat -> bv 8) (n n' i : nat) (r : ushp_cmd * nat) :
  n <= n' -> ref_parseline len f n i = Some r -> ref_parseline len f n' i = Some r.
Proof using.
  revert n' i r. induction n as [| n IH ]; intros n' i r Hle H; [ discriminate H | ].
  destruct n' as [| n' ]; [ lia | ]. cbn [ref_parseline] in H |- *.
  destruct (ref_parsepipe len f n i) as [[ t s ] | ] eqn:E; [ | discriminate H ].
  rewrite (ref_parsepipe_fuel len f n n' i _ ltac:(lia) E).
  destruct (ref_backs len f n s t) as [[ t1 s1 ] | ] eqn:E1; [ | discriminate H ].
  rewrite (ref_backs_fuel len f n n' s t _ ltac:(lia) E1).
  destruct (ref_peek len f s1 [rb_semi]) as [ semi s2 ].
  destruct semi; [ | exact H ].
  destruct (ref_gettoken len f s2) as [[[ tok q ] eq ] s3 ].
  destruct (ref_parseline len f n s3) as [[ t' s4 ] | ] eqn:E2; [ | discriminate H ].
  rewrite (IH n' s3 _ ltac:(lia) E2). exact H.
Qed.

(* ===================================================================== *)
(* §2 THE SYMBOL-FREE LINE: [ushp_tokens] under [ushp_no_symbols]          *)
(* ===================================================================== *)

(* every token is at least one byte, so a token list fits in the line *)
Lemma ushp_tokens_len_le (len : nat) (f : nat -> bv 8) (off : nat) (toks : list (nat * nat)) :
  ushp_tokens len f off toks -> off + length toks <= len.
Proof using.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; cbn [length]; lia.
Qed.

Lemma ushs_toks_len_le (len : nat) (f : nat -> bv 8) (stop off : nat) (toks : list (nat * nat)) :
  ushs_toks len f stop off toks -> off + length toks <= stop.
Proof using.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; cbn [length]; lia.
Qed.

(* the token model read back from the skipped cursor -- the converse of
   [ushp_tokens_skip] *)
Lemma ushp_tokens_unskip (len : nat) (f : nat -> bv 8) (off : nat) (toks : list (nat * nat)) :
  off <= len -> ushp_tokens len f (ref_skip len f off) toks -> ushp_tokens len f off toks.
Proof using.
  intros Hoff H.
  assert (Hk0 : ushp_skipws (len - ref_skip len f off) (ref_skip len f off) f = 0)
    by exact (ushp_skipws_idem len off f Hoff).
  destruct toks as [| tk rest ].
  - pose proof (ushp_tokens_nil_inv _ _ _ H) as Hnil. rewrite Hk0 in Hnil.
    apply UshpTokNil. unfold ref_skip in Hnil. lia.
  - destruct (ushp_tokens_cons_inv' len (ref_skip len f off) (ref_skip len f off)
                (ushp_toklen (len - ref_skip len f off) (ref_skip len f off) f) f tk rest
                ltac:(rewrite Hk0; lia) eq_refl H) as (Hq & -> & Hrest).
    assert (C := UshpTokCons len f off rest). cbv zeta in C.
    unfold ref_skip in Hq, Hrest |- *. exact (C Hq Hrest).
Qed.

(* THE LOOP, at a cursor above which the line is symbol-free: it consumes
   exactly the tokens [ushp_tokens] names and stops at the end.  Stated at
   [ushq_nosym_from] so that the pipe line's right command is an instance. *)
Lemma ref_args_of_tokens_from (len : nat) (f : nat -> bv 8) (off : nat)
    (toks acc : list (nat * nat)) (rs : list rredir) (n : nat) :
  ref_nonnul len f -> ushq_nosym_from len f off ->
  off <= len ->
  ushp_tokens len f off toks ->
  length acc + length toks < 10 ->
  length toks < n ->
  ref_args len f n off acc rs = Some (acc ++ toks, rs, len).
Proof using.
  revert off acc n. induction toks as [| tk rest IH ]; intros off acc n Hnn Hns Hoff Htoks Hlen Hn.
  - rewrite app_nil_r. apply ref_args_nul; [ lia | ].
    unfold ref_skip. exact (ushp_tokens_nil_inv _ _ _ Htoks).
  - destruct n as [| n ]; [ cbn in Hn; lia | ].
    destruct (ushp_tokens_cons_inv' len off (ref_skip len f off)
                (ushp_toklen (len - ref_skip len f off) (ref_skip len f off) f) f tk rest
                eq_refl eq_refl Htoks) as (Hq & -> & Hrest).
    set (s := ref_skip len f off) in *.
    set (n0 := ushp_toklen (len - s) s f) in *.
    assert (Hslt : s < len) by exact (ref_toklen_pos_lt len f s Hq).
    assert (Hsn : s + n0 <= len) by (pose proof (ushp_toklen_le (len - s) s f); lia).
    assert (Hsym : ushp_is_sym (f s) = false) by (apply Hns; pose proof (ref_skip_ge len f off); lia).
    cbn [length] in Hlen, Hn.
    rewrite (ref_args_step len f n off s n0 acc rs Hnn Hoff eq_refl Hslt Hsym eq_refl ltac:(lia)).
    set (s1 := ref_skip len f (s + n0)).
    assert (Hs1 : s1 <= len) by exact (ref_skip_le len f (s + n0) Hsn).
    assert (Hs1ge : s + n0 <= s1) by exact (ref_skip_ge len f (s + n0)).
    assert (Hs1i : ref_skip len f s1 = s1) by exact (ref_skip_idem len f (s + n0) Hsn).
    rewrite (ref_redirs_miss len f n s1 rs ltac:(lia)).
    2:{ rewrite Hs1i. apply ref_at_notin; [ | exact ref_symtoks_redir ].
        intro Hlt. apply Hns. pose proof (ref_skip_ge len f off). lia. }
    rewrite Hs1i. cbn beta iota.
    rewrite (IH s1 (acc ++ [(s, s + n0)]) n Hnn
               (ushq_nosym_from_mono len f off s1 ltac:(pose proof (ref_skip_ge len f off); lia) Hns)
               Hs1 (ushp_tokens_skip len f (s + n0) rest Hsn Hrest)
               ltac:(rewrite ushp_len_app1; lia) ltac:(lia)).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma ref_args_of_tokens (len : nat) (f : nat -> bv 8) (off : nat)
    (toks acc : list (nat * nat)) (rs : list rredir) (n : nat) :
  ref_nonnul len f -> ushp_no_symbols len f ->
  off <= len ->
  ushp_tokens len f off toks ->
  length acc + length toks < 10 ->
  length toks < n ->
  ref_args len f n off acc rs = Some (acc ++ toks, rs, len).
Proof using.
  intros Hnn Hns. apply ref_args_of_tokens_from; [ exact Hnn | ].
  intros j Hj. exact (Hns j ltac:(lia)).
Qed.

(* parseexec at a cursor above which the line is symbol-free: the EXEC
   node of the tokens, cursor at the end *)
Lemma ref_parseexec_exec (len : nat) (f : nat -> bv 8) (n i : nat) (toks : list (nat * nat)) :
  ref_nonnul len f -> ushq_nosym_from len f i -> i <= len ->
  ushp_tokens len f i toks -> length toks < 10 -> length toks < n ->
  ref_parseexec len f n i = Some (UshpExec toks, len).
Proof using.
  intros Hnn Hns Hi Htoks Hlen Hn. unfold ref_parseexec.
  pose proof (ref_skip_ge len f i) as Hge. pose proof (ref_skip_le len f i Hi) as Hle.
  assert (Hns' : forall j, ref_skip len f i <= j < len -> ushp_is_sym (f j) = false)
    by (intros j Hj; apply Hns; lia).
  rewrite (ref_peek_miss len f i [rb_lpar]);
    [ | apply ref_at_notin; [ intro Hlt; apply Hns'; lia | exact ref_symtoks_lpar ] ].
  cbn beta iota.
  rewrite (ref_redirs_miss len f n (ref_skip len f i) [] ltac:(lia)).
  2:{ rewrite (ref_skip_idem len f i Hi). apply ref_at_notin; [ intro Hlt; apply Hns'; lia | exact ref_symtoks_redir ]. }
  rewrite (ref_skip_idem len f i Hi). cbn beta iota.
  rewrite (ref_args_of_tokens_from len f (ref_skip len f i) toks [] [] n Hnn
             (ushq_nosym_from_mono len f i _ Hge Hns) Hle
             (ushp_tokens_skip len f i toks Hi Htoks) ltac:(cbn [length]; lia) Hn).
  reflexivity.
Qed.

(* the three outer functions on a command that ends at the end of the line:
   no '|', no '&', no ';' is found there *)
Lemma ref_parsepipe_end (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) :
  ref_parseexec len f n i = Some (t, len) -> ref_parsepipe len f (S n) i = Some (t, len).
Proof using.
  intro H. cbn [ref_parsepipe]. rewrite H.
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_bar). reflexivity.
Qed.

Lemma ref_parseline_end (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) :
  0 < n -> ref_parsepipe len f n i = Some (t, len) -> ref_parseline len f (S n) i = Some (t, len).
Proof using.
  intros Hn H. cbn [ref_parseline]. rewrite H, (ref_backs_len _ _ _ _ Hn).
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_semi). reflexivity.
Qed.

Lemma ref_parsecmd_of_line (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ref_parseline len f (ref_fuel len) 0 = Some (t, len) -> ref_parsecmd len f = Some t.
Proof using.
  intro H. unfold ref_parsecmd. rewrite H.
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_nil).
  rewrite (bool_decide_eq_true_2 _ eq_refl). reflexivity.
Qed.

Lemma ref_fuel_SS (len : nat) : ref_fuel len = S (S (4 * len + 6)).
Proof using. unfold ref_fuel. lia. Qed.

Theorem ref_parsecmd_nosym (len : nat) (f : nat -> bv 8) (toks : list (nat * nat)) :
  ref_nonnul len f -> ushp_no_symbols len f ->
  ushp_tokens len f 0 toks -> length toks < 10 ->
  ref_parsecmd len f = Some (UshpExec toks).
Proof using.
  intros Hnn Hns Htoks Hlen. apply ref_parsecmd_of_line. rewrite ref_fuel_SS.
  apply ref_parseline_end; [ lia | ]. apply ref_parsepipe_end.
  pose proof (ushp_tokens_len_le _ _ _ _ Htoks).
  apply ref_parseexec_exec; [ exact Hnn | apply ushq_nosym_from_0; exact Hns | lia | exact Htoks | exact Hlen | lia ].
Qed.

(* ---- and back: what the loop answers on a symbol-free suffix ----------- *)

Lemma ref_args_nosym_inv (len : nat) (f : nat -> bv 8) (n i : nat)
    (acc toks : list (nat * nat)) (rs rs' : list rredir) (s : nat) :
  ref_nonnul len f -> ushq_nosym_from len f i -> i <= len -> length acc < 10 ->
  ref_args len f n i acc rs = Some (toks, rs', s) ->
  rs' = rs /\ s = len /\ length toks < 10
  /\ exists tl, toks = acc ++ tl /\ ushp_tokens len f i tl.
Proof using.
  revert i acc. induction n as [| n IH ]; intros i acc Hnn Hns Hi Hacc H; [ discriminate H | ].
  pose proof (ref_skip_ge len f i) as Hge. pose proof (ref_skip_le len f i Hi) as Hle.
  assert (Hns' : forall j, ref_skip len f i <= j < len -> ushp_is_sym (f j) = false)
    by (intros j Hj; apply Hns; lia).
  cbn [ref_args] in H.
  rewrite (ref_peek_miss len f i [rb_bar; rb_rpar; rb_amp; rb_semi]) in H;
    [ | apply ref_at_notin; [ intro Hlt; apply Hns'; lia | exact ref_symtoks_stop ] ].
  cbn beta iota in H.
  destruct (Nat.eq_dec (ref_skip len f i) len) as [ Hend | Hend ].
  - rewrite Hend, (ref_gettoken_nul len f len (ref_skip_at_len len f)) in H. cbn beta iota in H.
    rewrite (bool_decide_eq_true_2 _ eq_refl) in H. injection H as <- <- <-.
    split; [ reflexivity | ]. split; [ reflexivity | ]. split; [ exact Hacc | ].
    exists []. rewrite app_nil_r. split; [ reflexivity | ].
    apply UshpTokNil. unfold ref_skip in Hend. exact Hend.
  - set (s0 := ref_skip len f i) in *.
    assert (Hlt : s0 < len) by lia.
    assert (Hsym : ushp_is_sym (f s0) = false) by (apply Hns'; lia).
    assert (Hws : ushp_is_ws (f s0) = false) by exact (ref_skip_nows len f i Hi Hlt).
    assert (Hss : ref_skip len f s0 = s0) by exact (ref_skip_idem len f i Hi).
    rewrite (ref_gettoken_word len f s0 s0 Hnn Hss Hlt Hsym) in H. cbn beta iota zeta in H.
    rewrite (bool_decide_eq_false_2 _ rt_word_ne_0), (bool_decide_eq_true_2 _ eq_refl) in H.
    cbn [negb] in H.
    set (n0 := ushp_toklen (len - s0) s0 f) in *.
    assert (Hn0 : ref_tokend len f s0 = s0 + n0) by reflexivity.
    rewrite Hn0 in H.
    destruct (bool_decide (10 <= length (acc ++ [(s0, s0 + n0)]))) eqn:E10; [ discriminate H | ].
    apply bool_decide_eq_false_1 in E10.
    destruct n as [| n ]; [ cbn [ref_redirs] in H; discriminate H | ].
    assert (Hsn : s0 + n0 <= len) by (pose proof (ushp_toklen_le (len - s0) s0 f); lia).
    set (s1 := ref_skip len f (s0 + n0)) in *.
    assert (Hs1 : s1 <= len) by exact (ref_skip_le len f (s0 + n0) Hsn).
    assert (Hs1ge : s0 + n0 <= s1) by exact (ref_skip_ge len f (s0 + n0)).
    assert (Hs1i : ref_skip len f s1 = s1) by exact (ref_skip_idem len f (s0 + n0) Hsn).
    rewrite (ref_redirs_miss len f (S n) s1 rs ltac:(lia)) in H.
    2:{ rewrite Hs1i. apply ref_at_notin; [ intro Hlt'; apply Hns'; lia | exact ref_symtoks_redir ]. }
    rewrite Hs1i in H. cbn beta iota in H.
    destruct (IH s1 (acc ++ [(s0, s0 + n0)]) Hnn
                (ushq_nosym_from_mono len f i s1 ltac:(lia) Hns) Hs1 ltac:(lia) H)
      as (Hrs & Hs & Hlen & tl & Htoks & Htl).
    split; [ exact Hrs | ]. split; [ exact Hs | ]. split; [ exact Hlen | ].
    exists ((s0, s0 + n0) :: tl). split; [ rewrite Htoks, <- app_assoc; reflexivity | ].
    assert (Hpos : 0 < n0) by exact (ref_toklen_pos_of len f s0 Hlt Hws Hsym).
    assert (C := UshpTokCons len f i tl). cbv zeta in C.
    pose proof (ushp_tokens_unskip len f (s0 + n0) tl Hsn Htl) as Htl'.
    unfold s1, s0, ref_skip in *. exact (C Hpos Htl').
Qed.

Lemma ref_parseexec_nosym_inv (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (s : nat) :
  ref_nonnul len f -> ushq_nosym_from len f i -> i <= len ->
  ref_parseexec len f n i = Some (t, s) ->
  s = len /\ exists toks, t = UshpExec toks /\ ushp_tokens len f i toks /\ length toks < 10.
Proof using.
  intros Hnn Hns Hi H. unfold ref_parseexec in H.
  pose proof (ref_skip_ge len f i) as Hge. pose proof (ref_skip_le len f i Hi) as Hle.
  assert (Hns' : forall j, ref_skip len f i <= j < len -> ushp_is_sym (f j) = false)
    by (intros j Hj; apply Hns; lia).
  rewrite (ref_peek_miss len f i [rb_lpar]) in H;
    [ | apply ref_at_notin; [ intro Hlt; apply Hns'; lia | exact ref_symtoks_lpar ] ].
  cbn beta iota in H.
  destruct n as [| n ]; [ cbn [ref_redirs] in H; discriminate H | ].
  rewrite (ref_redirs_miss len f (S n) (ref_skip len f i) [] ltac:(lia)) in H.
  2:{ rewrite (ref_skip_idem len f i Hi). apply ref_at_notin; [ intro Hlt; apply Hns'; lia | exact ref_symtoks_redir ]. }
  rewrite (ref_skip_idem len f i Hi) in H. cbn beta iota in H.
  destruct (ref_args len f (S n) (ref_skip len f i) [] []) as [[[ toks rs' ] s2 ] | ] eqn:E;
    [ | discriminate H ].
  injection H as <- <-.
  destruct (ref_args_nosym_inv len f (S n) (ref_skip len f i) [] toks [] rs' s2 Hnn
              (ushq_nosym_from_mono len f i _ Hge Hns) Hle ltac:(cbn; lia) E)
    as (-> & -> & Hlen & tl & -> & Htl).
  split; [ reflexivity | ]. exists tl. cbn [app ref_wrap fold_left].
  split; [ reflexivity | ]. split; [ exact (ushp_tokens_unskip len f i tl Hi Htl) | exact Hlen ].
Qed.

Lemma ref_parsepipe_nosym_inv (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (s : nat) :
  ref_nonnul len f -> ushq_nosym_from len f i -> i <= len ->
  ref_parsepipe len f n i = Some (t, s) ->
  s = len /\ exists toks, t = UshpExec toks /\ ushp_tokens len f i toks /\ length toks < 10.
Proof using.
  intros Hnn Hns Hi H. destruct n as [| n ]; [ discriminate H | ]. cbn [ref_parsepipe] in H.
  destruct (ref_parseexec len f n i) as [[ t1 s1 ] | ] eqn:E; [ | discriminate H ].
  destruct (ref_parseexec_nosym_inv len f n i t1 s1 Hnn Hns Hi E) as (-> & toks & -> & Htoks & Hlen).
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_bar) in H.
  cbn beta iota in H. injection H as <- <-.
  split; [ reflexivity | ]. exists toks. auto.
Qed.

Lemma ref_parseline_nosym_inv (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (s : nat) :
  ref_nonnul len f -> ushq_nosym_from len f i -> i <= len ->
  ref_parseline len f n i = Some (t, s) ->
  s = len /\ exists toks, t = UshpExec toks /\ ushp_tokens len f i toks /\ length toks < 10.
Proof using.
  intros Hnn Hns Hi H. destruct n as [| n ]; [ discriminate H | ]. cbn [ref_parseline] in H.
  destruct n as [| n ]; [ cbn [ref_parsepipe] in H; discriminate H | ].
  destruct (ref_parsepipe len f (S n) i) as [[ t1 s1 ] | ] eqn:E; [ | discriminate H ].
  destruct (ref_parsepipe_nosym_inv len f (S n) i t1 s1 Hnn Hns Hi E) as (-> & toks & -> & Htoks & Hlen).
  rewrite (ref_backs_len len f (S n) (UshpExec toks) ltac:(lia)) in H.
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_semi) in H.
  cbn beta iota in H. injection H as <- <-.
  split; [ reflexivity | ]. exists toks. auto.
Qed.

(* ...and back: what the reference answers on a symbol-free line IS an
   EXEC node at [ushp_tokens] (so nothing is lost in the re-statement) *)
Theorem ref_parsecmd_nosym_inv (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ref_nonnul len f -> ushp_no_symbols len f ->
  ref_parsecmd len f = Some t ->
  exists toks, t = UshpExec toks /\ ushp_tokens len f 0 toks /\ length toks < 10.
Proof using.
  intros Hnn Hns H. unfold ref_parsecmd in H.
  destruct (ref_parseline len f (ref_fuel len) 0) as [[ t' s' ] | ] eqn:E; [ | discriminate H ].
  destruct (ref_parseline_nosym_inv len f (ref_fuel len) 0 t' s' Hnn
              (proj2 (ushq_nosym_from_0 len f) Hns) ltac:(lia) E)
    as (-> & toks & -> & Htoks & Hlen).
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_nil) in H.
  cbn beta iota in H. rewrite (bool_decide_eq_true_2 _ eq_refl) in H. injection H as <-.
  exists toks. auto.
Qed.

(* ===================================================================== *)
(* §3 THE REDIRECT LINE: [ushs_redir] + [ushs_toks] at the '>'              *)
(* ===================================================================== *)

(* at or below the one symbol, a symbol byte IS that symbol *)
Lemma ushs_one_le_sym (len : nat) (f : nat -> bv 8) (p j : nat) :
  ushs_one len f (Some p) -> j <= p -> ushp_is_sym (f j) = true -> f j = rb_gt.
Proof using.
  intros Hone Hj Hs. destruct (ushs_one_some_at _ _ _ Hone) as [ Hp Hgt ].
  destruct Hone as [ H1 _ ]. injection (H1 j ltac:(lia) Hs) as <-.
  rewrite Hgt. exact rb_gt_is_ushs.
Qed.

Lemma ref_at_notin_gt (len : nat) (f : nat -> bv 8) (p s : nat) (toks : list (bv 8)) :
  ushs_one len f (Some p) -> s <= p -> ref_symtoks toks -> rb_gt ∉ toks ->
  ref_at len f s ∉ toks.
Proof using.
  intros Hone Hs Hsym Hgt Hin. destruct (ushs_one_some_at _ _ _ Hone) as [ Hp _ ].
  rewrite (ref_at_lt len f s ltac:(lia)) in Hin.
  apply elem_of_list_lookup_1 in Hin as [ k Hk ].
  pose proof (Forall_lookup_1 _ _ _ _ Hsym Hk) as Hb.
  rewrite (ushs_one_le_sym len f p s Hone Hs Hb) in Hk.
  exact (Hgt (elem_of_list_lookup_2 _ _ _ Hk)).
Qed.

(* on the redirect line the argument loop does NOT stop at the '>': '>' is
   not in parseexec's stop set, so the [parseredirs] that follows the LAST
   argument consumes `> file' and the loop then finds the line exhausted.
   The redirect is appended to the ones consumed so far. *)
Lemma ref_args_of_toks_redir (len : nat) (f : nat -> bv 8) (off p e : nat)
    (toks acc : list (nat * nat)) (rs : list rredir) (n : nat) :
  ref_nonnul len f ->
  ushs_redir len f p e ->
  off <= p ->
  ushs_toks len f p off toks ->
  0 < length toks ->
  length acc + length toks < 10 ->
  length toks + 1 < n ->
  ref_args len f n off acc rs
  = Some (acc ++ toks,
          rs ++ [{| rr_q := S (S p); rr_eq := e; rr_mode := rr_mode_gt; rr_fd := 1 |}],
          len).
Proof using.
  revert off acc rs n.
  induction toks as [| tk rest IH ]; intros off acc rs n Hnn Hr Hoff Htoks Hpos Hlen Hn;
    [ cbn in Hpos; lia | ].
  pose proof (ushs_redir_lt _ _ _ _ Hr) as Hp.
  pose proof (ushs_one_nosym_below _ _ _ (ushs_redir_one _ _ _ _ Hr)) as Hbelow.
  destruct n as [| n ]; [ cbn in Hn; lia | ].
  destruct (ushs_toks_cons_inv' len p off (ref_skip len f off)
              (ushp_toklen (len - ref_skip len f off) (ref_skip len f off) f) f tk rest
              eq_refl eq_refl Htoks) as (Hq & -> & Hrest).
  set (s := ref_skip len f off) in *.
  set (n0 := ushp_toklen (len - s) s f) in *.
  assert (Hslt : s < len) by exact (ref_toklen_pos_lt len f s Hq).
  assert (Hsn : s + n0 <= len) by (pose proof (ushp_toklen_le (len - s) s f); lia).
  assert (Hsnp : s + n0 <= p) by exact (ushs_toks_le _ _ _ _ _ Hrest).
  assert (Hsym : ushp_is_sym (f s) = false) by (apply Hbelow; lia).
  cbn [length] in Hlen, Hn.
  rewrite (ref_args_step len f n off s n0 acc rs Hnn ltac:(lia) eq_refl Hslt Hsym eq_refl ltac:(lia)).
  set (s1 := ref_skip len f (s + n0)).
  assert (Hs1 : s1 <= len) by exact (ref_skip_le len f (s + n0) Hsn).
  assert (Hs1ge : s + n0 <= s1) by exact (ref_skip_ge len f (s + n0)).
  assert (Hs1i : ref_skip len f s1 = s1) by exact (ref_skip_idem len f (s + n0) Hsn).
  pose proof (ushs_toks_skip len p f (s + n0) rest Hsn Hrest) as Hrest1.
  fold s1 in Hrest1.
  assert (Hs1p : s1 <= p) by exact (ushs_toks_le _ _ _ _ _ Hrest1).
  destruct rest as [| tk' rest' ].
  - (* the last token: parseredirs finds the '>' *)
    assert (Hs1eq : s1 = p).
    { assert (Hnil : s1 + ushp_skipws (len - s1) s1 f = p)
        by exact (ushs_toks_nil_inv _ _ _ _ Hrest1).
      assert (Hk : ushp_skipws (len - s1) s1 f = 0) by exact (ushp_skipws_idem len (s + n0) f Hsn).
      lia. }
    rewrite (ref_redirs_gt len f p e n s1 rs Hnn Hr ltac:(rewrite Hs1i; exact Hs1eq) ltac:(lia)).
    rewrite (ref_args_nul len f n len _ _ ltac:(lia) (ref_skip_at_len len f)). reflexivity.
  - (* more tokens: the byte after the blanks is a word byte *)
    destruct (ushs_toks_cons_inv' len p s1 (ref_skip len f s1)
                (ushp_toklen (len - ref_skip len f s1) (ref_skip len f s1) f) f tk' rest'
                eq_refl eq_refl Hrest1) as (Hq' & _ & Hrest').
    rewrite Hs1i in Hq', Hrest'.
    assert (Hs1lt : s1 < p) by (pose proof (ushs_toks_le _ _ _ _ _ Hrest'); lia).
    rewrite (ref_redirs_miss len f n s1 rs ltac:(lia)).
    2:{ rewrite Hs1i. apply ref_at_notin; [ intros _; apply Hbelow; lia | exact ref_symtoks_redir ]. }
    rewrite Hs1i. cbn beta iota.
    rewrite (IH s1 (acc ++ [(s, s + n0)]) rs n Hnn Hr Hs1p Hrest1 ltac:(cbn [length]; lia)
               ltac:(rewrite ushp_len_app1; cbn [length] in *; lia) ltac:(cbn [length] in *; lia)).
    rewrite <- app_assoc. reflexivity.
Qed.

(* parseexec on the redirect line: a leading redirect (no tokens) is
   consumed by the parseredirs BEFORE the loop; otherwise by the one after
   the last token.  Either way the same REDIR node, at the end of the line. *)
Lemma ref_parseexec_redir (len : nat) (f : nat -> bv 8) (n off p e : nat)
    (toks : list (nat * nat)) :
  ref_nonnul len f -> ushs_redir len f p e -> off <= p ->
  ushs_toks len f p off toks -> length toks < 10 -> length toks + 2 < n ->
  ref_parseexec len f n off = Some (UshpRedir (UshpExec toks) (S (S p)) e rr_mode_gt 1, len).
Proof using.
  intros Hnn Hr Hoff Htoks Hlen Hn. unfold ref_parseexec.
  pose proof (ushs_redir_lt _ _ _ _ Hr) as Hp.
  pose proof (ushs_redir_one _ _ _ _ Hr) as Hone.
  pose proof (ushs_one_nosym_below _ _ _ Hone) as Hbelow.
  assert (Hoffl : off <= len) by lia.
  pose proof (ushs_toks_skip len p f off toks Hoffl Htoks) as Htoks0.
  set (s0 := ref_skip len f off) in *.
  assert (Hs0p : s0 <= p) by exact (ushs_toks_le _ _ _ _ _ Htoks0).
  assert (Hs0i : ref_skip len f s0 = s0) by exact (ref_skip_idem len f off Hoffl).
  rewrite (ref_peek_miss len f off [rb_lpar]);
    [ | apply (ref_at_notin_gt len f p); [ exact Hone | exact Hs0p | exact ref_symtoks_lpar | exact rb_gt_notin_lpar ] ].
  fold s0. cbn beta iota.
  destruct toks as [| tk rest ].
  - (* no token: the leading parseredirs takes the redirect *)
    assert (Hs0eq : s0 = p).
    { assert (Hnil : s0 + ushp_skipws (len - s0) s0 f = p)
        by exact (ushs_toks_nil_inv _ _ _ _ Htoks0).
      assert (Hk : ushp_skipws (len - s0) s0 f = 0) by exact (ushp_skipws_idem len off f Hoffl).
      lia. }
    rewrite (ref_redirs_gt len f p e n s0 [] Hnn Hr ltac:(rewrite Hs0i; exact Hs0eq) ltac:(lia)).
    rewrite (ref_args_nul len f n len _ _ ltac:(lia) (ref_skip_at_len len f)). reflexivity.
  - destruct (ushs_toks_cons_inv' len p s0 (ref_skip len f s0)
                (ushp_toklen (len - ref_skip len f s0) (ref_skip len f s0) f) f tk rest
                eq_refl eq_refl Htoks0) as (Hq & _ & Hrest).
    rewrite Hs0i in Hq, Hrest.
    assert (Hs0lt : s0 < p) by (pose proof (ushs_toks_le _ _ _ _ _ Hrest); lia).
    rewrite (ref_redirs_miss len f n s0 [] ltac:(lia)).
    2:{ rewrite Hs0i. apply ref_at_notin; [ intros _; apply Hbelow; lia | exact ref_symtoks_redir ]. }
    rewrite Hs0i. cbn beta iota.
    rewrite (ref_args_of_toks_redir len f s0 p e (tk :: rest) [] [] n Hnn Hr Hs0p Htoks0
               ltac:(cbn [length]; lia) ltac:(cbn [length] in *; lia) ltac:(lia)).
    reflexivity.
Qed.

Theorem ref_parsecmd_redir (len : nat) (f : nat -> bv 8) (p e : nat)
    (toks : list (nat * nat)) :
  ref_nonnul len f ->
  ushs_redir len f p e ->
  ushs_toks len f p 0 toks -> length toks < 10 ->
  ref_parsecmd len f = Some (UshpRedir (UshpExec toks) (S (S p)) e rr_mode_gt 1).
Proof using.
  intros Hnn Hr Htoks Hlen. apply ref_parsecmd_of_line. rewrite ref_fuel_SS.
  apply ref_parseline_end; [ lia | ]. apply ref_parsepipe_end.
  pose proof (ushs_toks_len_le _ _ _ _ _ Htoks). pose proof (ushs_redir_lt _ _ _ _ Hr).
  apply ref_parseexec_redir; [ exact Hnn | exact Hr | lia | exact Htoks | exact Hlen | lia ].
Qed.

(* ===================================================================== *)
(* §4 THE PIPE LINE: [ushq_pipe] + [ushs_toks] at the '|'                   *)
(* ===================================================================== *)

Lemma ushq_one_le_sym (len : nat) (f : nat -> bv 8) (p j : nat) :
  ushq_one len f (Some p) -> j <= p -> ushp_is_sym (f j) = true -> f j = rb_bar.
Proof using.
  intros Hone Hj Hs. destruct (ushq_one_some_at _ _ _ Hone) as [ Hp Hbar ].
  destruct Hone as [ H1 _ ]. injection (H1 j ltac:(lia) Hs) as <-.
  rewrite Hbar. exact rb_bar_is_ushq.
Qed.

Lemma ref_at_notin_bar (len : nat) (f : nat -> bv 8) (p s : nat) (toks : list (bv 8)) :
  ushq_one len f (Some p) -> s <= p -> ref_symtoks toks -> rb_bar ∉ toks ->
  ref_at len f s ∉ toks.
Proof using.
  intros Hone Hs Hsym Hbar Hin. destruct (ushq_one_some_at _ _ _ Hone) as [ Hp _ ].
  rewrite (ref_at_lt len f s ltac:(lia)) in Hin.
  apply elem_of_list_lookup_1 in Hin as [ k Hk ].
  pose proof (Forall_lookup_1 _ _ _ _ Hsym Hk) as Hb.
  rewrite (ushq_one_le_sym len f p s Hone Hs Hb) in Hk.
  exact (Hbar (elem_of_list_lookup_2 _ _ _ Hk)).
Qed.

(* on the pipe line the loop DOES stop at the '|', which is in the stop set
   and not in [parseredirs]'s, having consumed the tokens before it *)
Lemma ref_args_of_toks_at (len : nat) (f : nat -> bv 8) (off p : nat)
    (toks acc : list (nat * nat)) (rs : list rredir) (n : nat) :
  ref_nonnul len f ->
  ushq_one len f (Some p) ->
  off <= p ->
  ushs_toks len f p off toks ->
  length acc + length toks < 10 ->
  length toks < n ->
  ref_args len f n off acc rs = Some (acc ++ toks, rs, p).
Proof using.
  revert off acc n.
  induction toks as [| tk rest IH ]; intros off acc n Hnn Hone Hoff Htoks Hlen Hn.
  - destruct (ushq_one_some_at _ _ _ Hone) as [ Hp Hbar ]. rewrite rb_bar_is_ushq in Hbar.
    destruct n as [| n ]; [ lia | ]. cbn [ref_args].
    pose proof (ushs_toks_nil_inv _ _ _ _ Htoks) as Hnil.
    assert (Hs : ref_skip len f off = p) by (unfold ref_skip; exact Hnil).
    rewrite (ref_peek_hit len f off [rb_bar; rb_rpar; rb_amp; rb_semi]);
      [ | rewrite Hs, (ref_at_lt _ _ _ Hp); exact (Hnn p Hp)
        | rewrite Hs, (ref_at_lt _ _ _ Hp), Hbar; exact rb_bar_in_stop ].
    rewrite Hs, app_nil_r. reflexivity.
  - destruct n as [| n ]; [ cbn in Hn; lia | ].
    destruct (ushq_one_some_at _ _ _ Hone) as [ Hp _ ].
    pose proof (ushq_one_nosym_below _ _ _ Hone) as Hbelow.
    destruct (ushs_toks_cons_inv' len p off (ref_skip len f off)
                (ushp_toklen (len - ref_skip len f off) (ref_skip len f off) f) f tk rest
                eq_refl eq_refl Htoks) as (Hq & -> & Hrest).
    set (s := ref_skip len f off) in *.
    set (n0 := ushp_toklen (len - s) s f) in *.
    assert (Hslt : s < len) by exact (ref_toklen_pos_lt len f s Hq).
    assert (Hsn : s + n0 <= len) by (pose proof (ushp_toklen_le (len - s) s f); lia).
    assert (Hsnp : s + n0 <= p) by exact (ushs_toks_le _ _ _ _ _ Hrest).
    assert (Hsym : ushp_is_sym (f s) = false) by (apply Hbelow; lia).
    cbn [length] in Hlen, Hn.
    rewrite (ref_args_step len f n off s n0 acc rs Hnn ltac:(lia) eq_refl Hslt Hsym eq_refl ltac:(lia)).
    set (s1 := ref_skip len f (s + n0)).
    assert (Hs1 : s1 <= len) by exact (ref_skip_le len f (s + n0) Hsn).
    assert (Hs1i : ref_skip len f s1 = s1) by exact (ref_skip_idem len f (s + n0) Hsn).
    pose proof (ushs_toks_skip len p f (s + n0) rest Hsn Hrest) as Hrest1.
    fold s1 in Hrest1.
    assert (Hs1p : s1 <= p) by exact (ushs_toks_le _ _ _ _ _ Hrest1).
    rewrite (ref_redirs_miss len f n s1 rs ltac:(lia)).
    2:{ rewrite Hs1i. apply (ref_at_notin_bar len f p); [ exact Hone | exact Hs1p | exact ref_symtoks_redir | exact rb_bar_notin_redir ]. }
    rewrite Hs1i. cbn beta iota.
    rewrite (IH s1 (acc ++ [(s, s + n0)]) n Hnn Hone Hs1p Hrest1
               ltac:(rewrite ushp_len_app1; lia) ltac:(lia)).
    rewrite <- app_assoc. reflexivity.
Qed.

(* the left command: an EXEC node, cursor at the '|' *)
Lemma ref_parseexec_left (len : nat) (f : nat -> bv 8) (n off p : nat) (toks : list (nat * nat)) :
  ref_nonnul len f -> ushq_one len f (Some p) -> off <= p ->
  ushs_toks len f p off toks -> length toks < 10 -> length toks < n ->
  ref_parseexec len f n off = Some (UshpExec toks, p).
Proof using.
  intros Hnn Hone Hoff Htoks Hlen Hn. unfold ref_parseexec.
  destruct (ushq_one_some_at _ _ _ Hone) as [ Hp _ ].
  assert (Hoffl : off <= len) by lia.
  pose proof (ushs_toks_skip len p f off toks Hoffl Htoks) as Htoks0.
  set (s0 := ref_skip len f off) in *.
  assert (Hs0p : s0 <= p) by exact (ushs_toks_le _ _ _ _ _ Htoks0).
  assert (Hs0i : ref_skip len f s0 = s0) by exact (ref_skip_idem len f off Hoffl).
  rewrite (ref_peek_miss len f off [rb_lpar]);
    [ | apply (ref_at_notin_bar len f p); [ exact Hone | exact Hs0p | exact ref_symtoks_lpar | exact rb_bar_notin_lpar ] ].
  fold s0. cbn beta iota.
  rewrite (ref_redirs_miss len f n s0 [] ltac:(lia)).
  2:{ rewrite Hs0i. apply (ref_at_notin_bar len f p); [ exact Hone | exact Hs0p | exact ref_symtoks_redir | exact rb_bar_notin_redir ]. }
  rewrite Hs0i. cbn beta iota.
  rewrite (ref_args_of_toks_at len f s0 p toks [] [] n Hnn Hone Hs0p Htoks0 ltac:(cbn [length]; lia) Hn).
  reflexivity.
Qed.

(* the right command's one token, as [ushp_tokens] at its cursor *)
Lemma ushq_pipe_right_tokens (len : nat) (f : nat -> bv 8) (p e : nat) :
  ushq_pipe len f p e -> ushp_tokens len f (S (S p)) [(S (S p), e)].
Proof using.
  intro Hq.
  assert (Hlo : S (S p) < e) by (destruct Hq as (_ & _ & _ & _ & H1 & _); lia).
  assert (He : e < len) by (destruct Hq as (_ & _ & _ & _ & _ & H2 & _); lia).
  destruct (ushq_pipe_right_byte len f p e (S (S p)) Hq (conj (Nat.le_refl _) Hlo)) as [ Hws _ ].
  replace e with (S (S p) + (e - S (S p))) at 1 by lia.
  apply ushp_tokens_cons'.
  - exact (ushp_skipws_stop _ _ _ Hws).
  - exact (ushq_toklen_right len f p e Hq).
  - lia.
  - replace (S (S p) + (e - S (S p))) with e by lia.
    apply UshpTokNil. rewrite (ushq_skipws_tail len f p e Hq). lia.
Qed.

Lemma ref_parseexec_right (len : nat) (f : nat -> bv 8) (n p e : nat) :
  ref_nonnul len f -> ushq_pipe len f p e -> 1 < n ->
  ref_parseexec len f n (S (S p)) = Some (UshpExec [(S (S p), e)], len).
Proof using.
  intros Hnn Hq Hn. pose proof (ushq_pipe_right_lt _ _ _ _ Hq).
  apply ref_parseexec_exec; [ exact Hnn | exact (ushq_pipe_nosym_from _ _ _ _ Hq) | lia
                            | exact (ushq_pipe_right_tokens _ _ _ _ Hq) | cbn; lia | cbn; lia ].
Qed.

(* parsepipe on the pipe line: the left EXEC, the '|' consumed, the right EXEC *)
Lemma ref_parsepipe_pipe (len : nat) (f : nat -> bv 8) (n p e : nat) (toks : list (nat * nat)) :
  ref_nonnul len f -> ushq_pipe len f p e ->
  ushs_toks len f p 0 toks -> length toks < 10 -> length toks < n -> 2 < n ->
  ref_parsepipe len f (S n) 0 = Some (UshpPipe (UshpExec toks) (UshpExec [(S (S p), e)]), len).
Proof using.
  intros Hnn Hq Htoks Hlen Hn Hn2.
  pose proof (ushq_pipe_one _ _ _ _ Hq) as Hone.
  pose proof (ushq_pipe_lt _ _ _ _ Hq) as Hp.
  pose proof (ushq_pipe_bar _ _ _ _ Hq) as Hbar. rewrite rb_bar_is_ushq in Hbar.
  assert (Hpp : ref_skip len f p = p).
  { unfold ref_skip. rewrite (ushq_skipws_at_bar len f p e _ Hq). lia. }
  cbn [ref_parsepipe].
  rewrite (ref_parseexec_left len f n 0 p toks Hnn Hone ltac:(lia) Htoks Hlen Hn).
  rewrite (ref_peek_hit len f p [rb_bar]);
    [ | rewrite Hpp, (ref_at_lt _ _ _ Hp); exact (Hnn p Hp)
      | rewrite Hpp, (ref_at_lt _ _ _ Hp), Hbar; exact rb_bar_in_bar ].
  rewrite Hpp. cbn beta iota.
  rewrite (ref_gettoken_sym len f p p Hnn Hpp Hp);
    [ | rewrite Hbar; exact ushq_bar_sym
      | rewrite Hbar, <- rb_gt_is_ushs; exact ushq_bar_not_gt ].
  cbn beta iota.
  assert (Hskip : ref_skip len f (S p) = S (S p)).
  { unfold ref_skip. rewrite (ushq_skipws_after_bar len f p e Hq). lia. }
  rewrite Hskip.
  destruct n as [| n ]; [ lia | ].
  rewrite (ref_parsepipe_end len f n (S (S p)) _ (ref_parseexec_right len f n p e Hnn Hq ltac:(lia))).
  reflexivity.
Qed.

Theorem ref_parsecmd_pipe (len : nat) (f : nat -> bv 8) (p e : nat)
    (toks : list (nat * nat)) :
  ref_nonnul len f ->
  ushq_pipe len f p e ->
  ushs_toks len f p 0 toks -> length toks < 10 ->
  ref_parsecmd len f = Some (UshpPipe (UshpExec toks) (UshpExec [(S (S p), e)])).
Proof using.
  intros Hnn Hq Htoks Hlen. apply ref_parsecmd_of_line. rewrite ref_fuel_SS.
  apply ref_parseline_end; [ lia | ].
  pose proof (ushs_toks_len_le _ _ _ _ _ Htoks). pose proof (ushq_pipe_lt _ _ _ _ Hq).
  apply ref_parsepipe_pipe; [ exact Hnn | exact Hq | exact Htoks | exact Hlen | lia | lia ].
Qed.

(* ===================================================================== *)
(* §5 THE LINE SHAPES, on the predicates the child laws speak              *)
(* ===================================================================== *)

(* the byte classes a line carries, none of them NUL *)
Lemma ref_alnum_nonnul (b : bv 8) : wl_alnum b -> b <> ubyte0.
Proof using.
  intros Ha E. apply (f_equal bv_unsigned) in E. rewrite ubyte0_val in E.
  unfold wl_alnum in Ha. lia.
Qed.

Lemma ref_body_byte_nonnul (b : bv 8) : wl_body_byte b -> b <> ubyte0.
Proof using.
  intros [ Ha | -> ]; [ exact (ref_alnum_nonnul b Ha) | ].
  intro E. apply (f_equal bv_unsigned) in E. rewrite ubyte0_val, wl_sp_val in E. lia.
Qed.

Lemma ref_sp_nonnul : wl_sp <> ubyte0.
Proof using. apply ref_body_byte_nonnul. right. reflexivity. Qed.

Lemma ref_nl_nonnul : wl_nl <> ubyte0.
Proof using.
  intro E. apply (f_equal bv_unsigned) in E. rewrite ubyte0_val, wl_nl_val in E. lia.
Qed.

Lemma ref_lookup_total_Forall {P : bv 8 -> Prop} (l : list (bv 8)) (j : nat) :
  Forall P l -> j < length l -> P (l !!! j).
Proof using.
  intros HF Hj. exact (Forall_lookup_1 _ _ _ _ HF (list_lookup_lookup_total_lt l j Hj)).
Qed.

(* the bytes of a well-formed line are never NUL *)
Lemma ref_nonnul_line_is (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_is ws f k len -> ref_nonnul len (fun j => f (k + j)).
Proof using.
  intros (Hok & Hlen & Hbytes) j Hj. cbn beta. rewrite (Hbytes j Hj).
  assert (Hjl : j < length (wl_line ws)) by lia.
  pose proof (wl_line_byte_val ws (wl_line ws !!! j) (EchoDisc.line_ok_wf ws Hok)
                (elem_of_list_lookup_2 _ _ _ (list_lookup_lookup_total_lt (wl_line ws) j Hjl))) as Hv.
  intro E. apply (f_equal bv_unsigned) in E. rewrite ubyte0_val in E. lia.
Qed.

Lemma ref_nonnul_redir_line_is (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len -> ref_nonnul len (fun j => f (k + j)).
Proof using.
  intros (Hok & Hfile & Hlen & Hbody & Hsp1 & Hgt & Hsp2 & Hfb & Hnl) j Hj. cbn beta.
  set (p0 := length (wl_body ws)) in *.
  destruct (lt_dec j p0) as [ Hlt | Hge ].
  { rewrite (Hbody j Hlt). apply ref_body_byte_nonnul.
    exact (ref_lookup_total_Forall _ _ (wl_body_bytes ws (EchoDisc.line_ok_wf ws Hok)) Hlt). }
  destruct (Nat.eq_dec j p0) as [ -> | Hne0 ].
  { rewrite Hsp1. exact ref_sp_nonnul. }
  destruct (Nat.eq_dec j (p0 + 1)) as [ -> | Hne1 ].
  { replace (k + (p0 + 1)) with (k + p0 + 1) by lia. rewrite Hgt. exact ushs_gt_not_nul. }
  destruct (Nat.eq_dec j (p0 + 2)) as [ -> | Hne2 ].
  { replace (k + (p0 + 2)) with (k + p0 + 2) by lia. rewrite Hsp2. exact ref_sp_nonnul. }
  destruct (lt_dec j (p0 + 3 + length file)) as [ Hf | Hnf ].
  { replace (k + j) with (k + p0 + 3 + (j - (p0 + 3))) by lia.
    rewrite (Hfb (j - (p0 + 3)) ltac:(lia)). apply ref_alnum_nonnul.
    destruct Hfile as [ _ Hfile ]. exact (ref_lookup_total_Forall file (j - (p0 + 3)) Hfile ltac:(lia)). }
  replace (k + j) with (k + p0 + 3 + length file) by lia. rewrite Hnl. exact ref_nl_nonnul.
Qed.

Lemma ref_nonnul_pipe_line_is (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len -> ref_nonnul len (fun j => f (k + j)).
Proof using.
  intros (Hok & Hright & Hlen & Hbody & Hsp1 & Hbar & Hsp2 & Hrb & Hnl) j Hj. cbn beta.
  set (p0 := length (wl_body ws)) in *.
  destruct (lt_dec j p0) as [ Hlt | Hge ].
  { rewrite (Hbody j Hlt). apply ref_body_byte_nonnul.
    exact (ref_lookup_total_Forall _ _ (wl_body_bytes ws (EchoDisc.line_ok_wf ws Hok)) Hlt). }
  destruct (Nat.eq_dec j p0) as [ -> | Hne0 ].
  { rewrite Hsp1. exact ref_sp_nonnul. }
  destruct (Nat.eq_dec j (p0 + 1)) as [ -> | Hne1 ].
  { replace (k + (p0 + 1)) with (k + p0 + 1) by lia. rewrite Hbar. exact ushq_bar_not_nul. }
  destruct (Nat.eq_dec j (p0 + 2)) as [ -> | Hne2 ].
  { replace (k + (p0 + 2)) with (k + p0 + 2) by lia. rewrite Hsp2. exact ref_sp_nonnul. }
  destruct (lt_dec j (p0 + 3 + length right)) as [ Hf | Hnf ].
  { replace (k + j) with (k + p0 + 3 + (j - (p0 + 3))) by lia.
    rewrite (Hrb (j - (p0 + 3)) ltac:(lia)). apply ref_alnum_nonnul.
    destruct Hright as [ _ Hright ]. exact (ref_lookup_total_Forall right (j - (p0 + 3)) Hright ltac:(lia)). }
  replace (k + j) with (k + p0 + 3 + length right) by lia. rewrite Hnl. exact ref_nl_nonnul.
Qed.

(* echo w1 ... wn *)
Theorem ref_parsecmd_line_is (ws : list (list (bv 8))) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_is ws f k len ->
  ref_parsecmd len (fun j => f (k + j)) = Some (UshpExec (wl_toks ws)).
Proof using.
  intro Hl. pose proof (ref_nonnul_line_is ws f k len Hl) as Hnn.
  pose proof (ushs_line_is_nosym ws f k len Hl) as Hns.
  destruct Hl as (Hok & Hlen & Hbytes).
  apply ref_parsecmd_nosym; [ exact Hnn | exact Hns | | ].
  - exact (wl_tokens ws (fun j => f (k + j)) len (EchoDisc.line_ok_wf ws Hok) Hlen Hbytes).
  - rewrite wl_toks_length. exact (EchoDisc.line_ok_lt10 ws Hok).
Qed.

(* echo w1 ... wn > file *)
Theorem ref_parsecmd_redir_line_is (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len ->
  ref_parsecmd len (fun j => f (k + j))
  = Some (UshpRedir (UshpExec (wl_toks ws))
            (length (wl_body ws) + 3) (length (wl_body ws) + 3 + length file)
            rr_mode_gt 1).
Proof using.
  intro Hl. pose proof (ref_nonnul_redir_line_is ws file f k len Hl) as Hnn.
  pose proof (ushs_line_is_redir ws file f k len Hl) as Hr.
  pose proof (ushs_line_is_toks ws file f k len Hl) as Htoks.
  destruct Hl as (Hok & _).
  rewrite (ref_parsecmd_redir len (fun j => f (k + j)) _ _ (wl_toks ws) Hnn Hr Htoks
             ltac:(rewrite wl_toks_length; exact (EchoDisc.line_ok_lt10 ws Hok))).
  do 3 f_equal. lia.
Qed.

(* echo w1 ... wn | right *)
Theorem ref_parsecmd_pipe_line_is (ws : list (list (bv 8))) (right : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushq_line_is ws right f k len ->
  ref_parsecmd len (fun j => f (k + j))
  = Some (UshpPipe (UshpExec (wl_toks ws))
            (UshpExec [(length (wl_body ws) + 3, length (wl_body ws) + 3 + length right)])).
Proof using.
  intro Hl. pose proof (ref_nonnul_pipe_line_is ws right f k len Hl) as Hnn.
  pose proof (ushq_line_is_pipe ws right f k len Hl) as Hq.
  pose proof (ushq_line_is_toks_l ws right f k len Hl) as Htoks.
  destruct Hl as (Hok & _).
  rewrite (ref_parsecmd_pipe len (fun j => f (k + j)) _ _ (wl_toks ws) Hnn Hq Htoks
             ltac:(rewrite wl_toks_length; exact (EchoDisc.line_ok_lt10 ws Hok))).
  do 5 f_equal. lia.
Qed.

(* and all three are in the catalog's scope *)
Lemma ushp_cat_line_shapes (toks toks' : list (nat * nat)) (q e : nat) :
  ushp_cat (UshpExec toks)
  /\ ushp_cat (UshpRedir (UshpExec toks) q e rr_mode_gt 1)
  /\ ushp_cat (UshpPipe (UshpExec toks) (UshpExec toks')).
Proof using. cbn. auto. Qed.

(* the NUL cut of each shape is the landed one: the tokens' ends, plus the
   file name's end at the redirect, plus the right command's at the pipe *)
Lemma ref_nulcut_shapes (toks : list (nat * nat)) (q e : nat) (r : nat * nat) :
  ref_nulcut (UshpExec toks) = map snd toks
  /\ ref_nulcut (UshpRedir (UshpExec toks) q e rr_mode_gt 1) = map snd toks ++ [e]
  /\ ref_nulcut (UshpPipe (UshpExec toks) (UshpExec [r])) = map snd toks ++ [snd r].
Proof using. cbn. auto. Qed.
