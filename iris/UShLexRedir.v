(* ===================================================================== *)
(* UShLexRedir.v -- THE REDIRECT LINE LEXES, lane SH-LEX-REDIR            *)
(* (design/app-file.md SS5.1; SKELETON's obligation 13, [UShRound.Hlexr]) *)
(*                                                                        *)
(* [UkShLoop.ush_line_lexable_redir] is a [Prop] nothing proved and        *)
(* nothing threaded.  This file proves it, and does it the way the         *)
(* symbol-free twin is proved: the DEFINITION stays at the lowest file     *)
(* that sees both halves ([UkShLoop]), and the PROOF lives above           *)
(* [UkShWords], because what makes a line lex is the general word-list     *)
(* tokenization and that file is the one that has it.  Read the three      *)
(* sections against their echo counterparts:                               *)
(*                                                                        *)
(*   S1 is [UkShWords.wl_tokens_tail] / [wl_tokens] with the line's        *)
(*     closing byte a PARAMETER and the scan's fuel allowed to run past    *)
(*     it.  echo's line is closed by the newline AT THE END OF THE BUFFER; *)
(*     the redirect line's argument list is closed by the blank before the *)
(*     '>', with four more bytes behind it.  Neither the skip nor the      *)
(*     token measure can tell the two apart -- both stop dead on the byte  *)
(*     that closes them -- so ONE induction covers both, and the landed    *)
(*     [ushp_tokens] statements are its instance at [stop = len].          *)
(*   S2 is [UkShEcho.ush_line_toks_holds]'s twin: the redirect line's      *)
(*     tokens NAMED ([LineWords.wl_toks ws], the same list echo's line     *)
(*     has, because the argument region IS echo's line without its         *)
(*     newline), and the count, which is what a supplier really owes.      *)
(*     [ush_line_lexable_redir_holds] is then [UShRest.                     *)
(*     ush_line_lexable_holds]'s twin -- the existential form.             *)
(*   S3 is the bridge FROM THE TYPED LINE: the file application's tag      *)
(*     ([FileOut.ftag]) gives [FileDisc.disc_f], whose content at one line *)
(*     is [FileDisc.parse_line J = Some l]; at [l = LEchoF ws nm] that body *)
(*     IS [wl_body ws ++ suf_gt nm] ([FileDisc.line_body_parse]), which is *)
(*     the redirect line positionally.  [sh_redir_line_lexable] is that    *)
(*     chain in one step: from the line sh READ to the four parser         *)
(*     premises of [UkShRedirSeam.wp_kshm_child_alloc_redir].             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShWords.
Require Import UkShRedirLine.
Require Import UkShLoop.
Require Import UNameBytes.   (* the suffix around a name of any length *)


(* ===================================================================== *)
(* §1 THE TOKENIZATION, AT A TERMINATOR                                   *)
(* ===================================================================== *)

(* [UkShParseSym.UshsTokCons] with the two scanned lengths NAMED, so a call
   site supplies them rather than leaving them to unification.  It is
   [UkShWords.wl_tok_step] at the terminator form. *)
Lemma ushs_tok_step (len stop i k n : nat) (f : nat -> bv 8)
    (toks : list (nat * nat)) :
  ushp_skipws (len - i)%nat i f = k ->
  ushp_toklen (len - (i + k))%nat (i + k)%nat f = n ->
  (0 < n)%nat ->
  ushs_toks len f stop (i + k + n)%nat toks ->
  ushs_toks len f stop i ((i + k, i + k + n)%nat :: toks).
Proof using.
  intros Hk Hn Hpos Ht.
  pose proof (UshsTokCons len f stop i toks) as C. cbv zeta in C.
  rewrite Hk in C. rewrite Hn in C. exact (C Hpos Ht).
Qed.

(* the byte a tail opens with is a blank -- a space if the tail has a word
   in it, the line's own closer if it does not.  [UkShWords.
   wl_tail_head_ws] is this at [c := wl_nl]. *)
Lemma ushs_tail_head_ws (r : list (list (bv 8))) (c : bv 8) :
  ushp_is_ws c = true ->
  ushp_is_ws ((wl_tail r ++ [c]) !!! 0%nat) = true.
Proof using.
  intro Hc. destruct r as [| w0 r0]; [ exact Hc | exact wl_sp_ws ].
Qed.

(* the two readings of a three-part line the inductions below spend, with
   the association fixed once.  [LineWords.wl_lta_app_l] / [_app_r] are
   them at two parts. *)
Lemma ushs_lta3_l (u v m : list (bv 8)) (j : nat) :
  (j < length u)%nat -> ((u ++ v) ++ m) !!! j = u !!! j.
Proof using.
  intro Hj. rewrite <- app_assoc. exact (wl_lta_app_l u (v ++ m) j Hj).
Qed.

Lemma ushs_lta3_r (u v m : list (bv 8)) (j : nat) :
  ((u ++ v) ++ m) !!! (length u + j)%nat = (v ++ m) !!! j.
Proof using.
  rewrite <- app_assoc. exact (wl_lta_app_r u (v ++ m) j).
Qed.

(* THE INDUCTION.  [p] points AT the blank that opens the tail, [stop] at
   the byte one past the line's closer, and [len] may be anything at or
   past [stop] provided the byte AT [stop] is not a blank (else the skip
   would run on into it).  [UkShWords.wl_tokens_tail] is this at
   [c := wl_nl] and [stop = len]. *)
Lemma ushs_toks_tail (ws : list (list (bv 8))) :
  fn_wf ws ->
  forall (f : nat -> bv 8) (c : bv 8) (p len stop : nat),
    ushp_is_ws c = true ->
    stop = (p + length (wl_tail ws) + 1)%nat ->
    (stop <= len)%nat ->
    (stop = len \/ ushp_is_ws (f stop) = false) ->
    (forall j : nat, (j < length (wl_tail ws) + 1)%nat ->
       f (p + j)%nat = (wl_tail ws ++ [c]) !!! j) ->
    ushs_toks len f stop p (wl_toks_at (S p) ws).
Proof using.
  induction ws as [| w r IH]; intros Hwf f c p len stop Hc Hstop Hle Hend Hf.
  - (* nothing left but the closer *)
    cbn [wl_tail length] in Hstop.
    cbn [wl_toks_at]. apply UshsTokNil.
    assert (Hp : ushp_is_ws (f p) = true).
    { replace p with (p + 0)%nat at 1 by lia.
      rewrite (Hf 0%nat ltac:(cbn; lia)). exact (ushs_tail_head_ws [] c Hc). }
    assert (Hsk : ushp_skipws (len - p)%nat p f = 1%nat).
    { apply (ushs_skipws_exact (len - p)%nat p 1%nat f).
      - lia.
      - intros j Hj. replace j with p by lia. exact Hp.
      - destruct Hend as [ He | He ]; [ left; lia | ].
        right. replace (p + 1)%nat with stop by lia. exact He. }
    lia.
  - destruct (fn_wf_cons w r Hwf) as [ Hword Hr ].
    pose proof (fn_word_pos w Hword) as Hwpos.
    pose proof (wl_word_plain w Hword) as Hwpl.
    assert (Hlenw : length (wl_tail (w :: r))
                    = (1 + length w + length (wl_tail r))%nat).
    { cbn [wl_tail length]. rewrite length_app. lia. }
    (* the tail's bytes, spelled out: ' ' at 0, [w] at 1..|w|, then the
       REST of the tail (or the closer) from 1+|w| on *)
    assert (Hsp : f p = wl_sp).
    { replace p with (p + 0)%nat at 1 by lia.
      rewrite (Hf 0%nat ltac:(lia)). reflexivity. }
    assert (Hw : forall j : nat, (j < length w)%nat ->
              f (p + 1 + j)%nat = w !!! j).
    { intros j Hj. replace (p + 1 + j)%nat with (p + S j)%nat by lia.
      rewrite (Hf (S j) ltac:(lia)).
      exact (ushs_lta3_l w (wl_tail r) [c] j Hj). }
    assert (Hrest : forall j : nat, (j < length (wl_tail r) + 1)%nat ->
              f (p + 1 + length w + j)%nat = (wl_tail r ++ [c]) !!! j).
    { intros j Hj.
      replace (p + 1 + length w + j)%nat with (p + S (length w + j))%nat by lia.
      rewrite (Hf (S (length w + j))%nat ltac:(lia)).
      exact (ushs_lta3_r w (wl_tail r) [c] j). }
    (* ---- the skip: exactly the one separator ---- *)
    assert (Hskip : ushp_skipws (len - p)%nat p f = 1%nat).
    { apply wl_skipws_one; [ rewrite Hsp; exact wl_sp_ws | | lia ].
      replace (S p) with (p + 1 + 0)%nat by lia.
      rewrite (Hw 0%nat Hwpos). exact (wl_word_head w Hword). }
    (* ---- the token: exactly the word ---- *)
    assert (Htok : ushp_toklen (len - (p + 1))%nat (p + 1)%nat f = length w).
    { apply (wl_toklen_run (length w) (len - (p + 1))%nat (p + 1)%nat f).
      - intros j Hj. rewrite (Hw j Hj).
        rewrite list_lookup_total_alt.
        destruct (lookup_lt_is_Some_2 w j Hj) as [ b Hb ]. rewrite Hb.
        cbn [default from_option].
        exact (Forall_lookup_1 _ _ _ _ Hwpl Hb).
      - lia.
      - left.
        replace (p + 1 + length w)%nat with (p + 1 + length w + 0)%nat by lia.
        rewrite (Hrest 0%nat ltac:(lia)). exact (ushs_tail_head_ws r c Hc). }
    cbn [wl_toks_at].
    replace (S p, (S p + length w)%nat) with ((p + 1)%nat, (p + 1 + length w)%nat)
      by (f_equal; lia).
    apply (ushs_tok_step len stop p 1%nat (length w) f);
      [ exact Hskip | exact Htok | exact Hwpos | ].
    replace (S (S p + length w)%nat) with (S (p + 1 + length w)%nat) by lia.
    apply (IH Hr f c (p + 1 + length w)%nat len stop Hc); [ lia | lia | | ].
    + destruct Hend as [ He | He ]; [ left; exact He | right; exact He ].
    + intros j Hj. exact (Hrest j Hj).
Qed.

(* ...AND THE LINE.  The first word has no separator before it, so it is
   one [UshsTokCons] at [k = 0] outside the induction.  [UkShWords.
   wl_tokens] is this at [c := wl_nl] and [stop = len]. *)
Lemma ushs_toks_line (ws : list (list (bv 8))) (f : nat -> bv 8) (c : bv 8)
    (len stop : nat) :
  fn_wf ws ->
  ushp_is_ws c = true ->
  stop = (length (wl_body ws) + 1)%nat ->
  (stop <= len)%nat ->
  (stop = len \/ ushp_is_ws (f stop) = false) ->
  (forall j : nat, (j < stop)%nat -> f j = (wl_body ws ++ [c]) !!! j) ->
  ushs_toks len f stop 0%nat (wl_toks ws).
Proof using.
  intros Hwf Hc Hstop Hle Hend Hf. unfold wl_toks.
  destruct ws as [| w r].
  - cbn [wl_body length] in Hstop.
    cbn [wl_toks_at]. apply UshsTokNil.
    assert (Hp : ushp_is_ws (f 0%nat) = true).
    { rewrite (Hf 0%nat ltac:(lia)). exact Hc. }
    assert (Hsk : ushp_skipws (len - 0)%nat 0%nat f = 1%nat).
    { apply (ushs_skipws_exact (len - 0)%nat 0%nat 1%nat f).
      - lia.
      - intros j Hj. replace j with 0%nat by lia. exact Hp.
      - destruct Hend as [ He | He ]; [ left; lia | ].
        right. replace (0 + 1)%nat with stop by lia. exact He. }
    lia.
  - destruct (fn_wf_cons w r Hwf) as [ Hword Hr ].
    pose proof (fn_word_pos w Hword) as Hwpos.
    pose proof (wl_word_plain w Hword) as Hwpl.
    assert (Hlenb : length (wl_body (w :: r))
                    = (length w + length (wl_tail r))%nat)
      by (rewrite wl_body_cons; rewrite length_app; lia).
    assert (Hw : forall j : nat, (j < length w)%nat -> f j = w !!! j).
    { intros j Hj. rewrite (Hf j ltac:(lia)).
      exact (ushs_lta3_l w (wl_tail r) [c] j Hj). }
    assert (Hrest : forall j : nat, (j < length (wl_tail r) + 1)%nat ->
              f (length w + j)%nat = (wl_tail r ++ [c]) !!! j).
    { intros j Hj. rewrite (Hf (length w + j)%nat ltac:(lia)).
      exact (ushs_lta3_r w (wl_tail r) [c] j). }
    (* ---- no skip at all: the line opens on the command name ---- *)
    assert (Hskip : ushp_skipws (len - 0)%nat 0%nat f = 0%nat).
    { apply wl_skipws_none. rewrite (Hw 0%nat Hwpos).
      exact (wl_word_head w Hword). }
    assert (Htok : ushp_toklen (len - (0 + 0))%nat (0 + 0)%nat f = length w).
    { apply (wl_toklen_run (length w) (len - (0 + 0))%nat (0 + 0)%nat f).
      - intros j Hj. rewrite Nat.add_0_l. rewrite (Hw j Hj).
        rewrite list_lookup_total_alt.
        destruct (lookup_lt_is_Some_2 w j Hj) as [ b Hb ]. rewrite Hb.
        cbn [default from_option].
        exact (Forall_lookup_1 _ _ _ _ Hwpl Hb).
      - lia.
      - left. rewrite Nat.add_0_l.
        replace (length w) with (length w + 0)%nat by lia.
        rewrite (Hrest 0%nat ltac:(lia)). exact (ushs_tail_head_ws r c Hc). }
    cbn [wl_toks_at].
    replace (0%nat, (0 + length w)%nat) with ((0 + 0)%nat, (0 + 0 + length w)%nat)
      by (f_equal; lia).
    apply (ushs_tok_step len stop 0%nat 0%nat (length w) f);
      [ exact Hskip | exact Htok | exact Hwpos | ].
    replace (0 + 0 + length w)%nat with (length w) by lia.
    replace (S (0 + length w)%nat) with (S (length w)) by lia.
    apply (ushs_toks_tail r Hr f c (length w) len stop Hc); [ lia | lia | | ].
    + destruct Hend as [ He | He ]; [ left; exact He | right; exact He ].
    + intros j Hj. exact (Hrest j Hj).
Qed.


(* ===================================================================== *)
(* §2 THE REDIRECT LINE'S TOKENS, NAMED -- [UkShEcho.ush_line_toks]'s TWIN *)
(* ===================================================================== *)

(* THE ARGUMENT LIST IS ECHO'S OWN.  [ushs_line_is ws file f k len] holds
   [wl_body ws] at [k] and then ' ' '>' ' ' <file> '\n'; below the '>' the
   buffer is echo's line with its newline replaced by the blank that
   separates the command from the redirect, so the tokens are [wl_toks ws]
   -- the SAME list [UkShEcho.echo_toks] names -- and the scan stops at the
   '>' because a '>' is not a blank. *)
Lemma ushs_line_is_toks (ws : list (list (bv 8))) (file : list (bv 8))
    (f : nat -> bv 8) (k len : nat) :
  ushs_line_is ws file f k len ->
  ushs_toks len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat 0%nat (wl_toks ws).
Proof using.
  intro Hl. pose proof Hl as HL.
  destruct HL as (Hok & Hfile & Hlen & Hbody & Hsp1 & Hgt & Hsp2 & Hfb & Hnl).
  assert (Hfpos : (0 < length file)%nat)
    by (destruct Hfile as [ Hne _ ]; destruct file; [ done | cbn; lia ]).
  apply (ushs_toks_line ws (fun j : nat => f (k + j)%nat) wl_sp len
           (length (wl_body ws) + 1)%nat).
  - exact (wl_wf_fn ws (line_ok_wf ws Hok)).
  - exact wl_sp_ws.
  - reflexivity.
  - lia.
  - right. cbn beta.
    replace (k + (length (wl_body ws) + 1))%nat
      with (k + length (wl_body ws) + 1)%nat by lia.
    rewrite Hgt. exact ushs_gt_not_ws.
  - intros j Hj. cbn beta.
    destruct (Nat.eq_dec j (length (wl_body ws))) as [ -> | Hne ].
    + rewrite Hsp1.
      pose proof (wl_lta_app_r (wl_body ws) [wl_sp] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. rewrite Hr. reflexivity.
    + rewrite (Hbody j ltac:(lia)). symmetry.
      exact (wl_lta_app_l (wl_body ws) [wl_sp] j ltac:(lia)).
Qed.

(* [UkShEcho.ush_line_toks]'s twin, at the redirect line: the two conjuncts
   of [UkShLoop.ush_line_lexable_redir] with the token list NAMED, and the
   count, which is what [UkShRedirSeam.wp_kshm_child_alloc_redir] asks for
   and the existential form cannot give. *)
Definition ush_line_toks_redir : Prop :=
  forall (ws : list (list (bv 8))) (file : list (bv 8)) (f : nat -> bv 8)
         (k len : nat),
    ushs_line_is ws file f k len ->
    ushs_redir len (fun j : nat => f (k + j)%nat)
      (length (wl_body ws) + 1)%nat
      (length (wl_body ws) + 3 + length file)%nat
    /\ ushs_toks len (fun j : nat => f (k + j)%nat)
         (length (wl_body ws) + 1)%nat 0%nat (wl_toks ws)
    /\ (0 < length (wl_toks ws))%nat
    /\ (length (wl_toks ws) < 10)%nat.

Lemma ush_line_toks_holds_redir : ush_line_toks_redir.
Proof using.
  intros ws file f k len Hl. pose proof Hl as HL.
  destruct HL as (Hok & _).
  split_and!.
  - exact (UkShLoop.ush_line_lexable_redir_shape ws file f k len Hl).
  - exact (ushs_line_is_toks ws file f k len Hl).
  - rewrite wl_toks_length. exact (line_ok_pos ws Hok).
  - rewrite wl_toks_length. exact (line_ok_lt10 ws Hok).
Qed.

(* ...and the existential form, which is SKELETON's obligation 13.
   [UShRest.ush_line_lexable_holds] is the symbol-free twin of this line. *)
Lemma ush_line_lexable_redir_holds : UkShLoop.ush_line_lexable_redir.
Proof using.
  intros ws file f k len Hl.
  destruct (ush_line_toks_holds_redir ws file f k len Hl)
    as (Hr & Ht & Hpos & Hlt).
  split; [ exact Hr | ].
  exists (wl_toks ws). exact (conj Ht (conj Hpos Hlt)).
Qed.


(* ===================================================================== *)
(* §3 FROM THE TYPED LINE: WHAT [UShRound.Hlexr] IS DISCHARGED FROM        *)
(* ===================================================================== *)

(* THE BRIDGE, at ANY name of the class (cut W3).  The premises are the
   ones [UkSh.ush_gets_done_line] takes -- the body the read delivered,
   the buffer holding it at [k] and the newline the loop stored past it --
   with [EchoDisc.body_ok J] replaced by the file discipline's own reading
   of the same body, [FileDisc.parse_line J = Some (LEchoF ws nm)]; the
   name is a word of name bytes by L1 ([FileDisc.uname_lex], cut W4). *)
Lemma sh_redir_line_of_typed (J : list (bv 8)) (ws : list (list (bv 8)))
    (nm : list (bv 8)) (f : nat -> bv 8) (k len : nat) :
  parse_line J = Some (LEchoF ws nm) ->
  len = S (length J) ->
  (forall j : nat, (j < length J)%nat -> f (k + j)%nat = J !!! j) ->
  f (k + length J)%nat = wl_nl ->
  ushs_line_is ws nm f k len.
Proof using.
  intros Hp Hlen Hf Hnl.
  pose proof (line_body_parse J (LEchoF ws nm) Hp) as HJ.
  cbn [line_body] in HJ.
  pose proof (parse_line_ok J (LEchoF ws nm) Hp) as [ Hok [ Hu _ ] ].
  pose proof (uname_lex nm Hu) as Hw.
  assert (HlenJ : length J = (length (wl_body ws) + (3 + length nm))%nat)
    by (rewrite HJ, length_app, suf_gt_len; reflexivity).
  (* every byte of the suffix, off the body's own layout *)
  assert (Hsuf : forall i : nat, (i < 3 + length nm)%nat ->
            f (k + (length (wl_body ws) + i))%nat = suf_gt nm !!! i).
  { intros i Hi. rewrite (Hf (length (wl_body ws) + i)%nat ltac:(lia)). rewrite HJ.
    exact (wl_lta_app_r (wl_body ws) (suf_gt nm) i). }
  unfold ushs_line_is. split_and!.
  - exact Hok.
  - exact Hw.
  - rewrite Hlen, HlenJ. lia.
  - intros j Hj. rewrite (Hf j ltac:(lia)). rewrite HJ.
    exact (wl_lta_app_l (wl_body ws) (suf_gt nm) j Hj).
  - pose proof (Hsuf 0%nat ltac:(lia)) as H0.
    rewrite Nat.add_0_r in H0. rewrite H0. exact (suf_gt_0 nm).
  - pose proof (Hsuf 1%nat ltac:(lia)) as H1.
    replace (k + length (wl_body ws) + 1)%nat
      with (k + (length (wl_body ws) + 1))%nat by lia.
    rewrite H1. exact (suf_gt_1 nm).
  - pose proof (Hsuf 2%nat ltac:(lia)) as H2.
    replace (k + length (wl_body ws) + 2)%nat
      with (k + (length (wl_body ws) + 2))%nat by lia.
    rewrite H2. exact (suf_gt_2 nm).
  - intros j Hj.
    pose proof (Hsuf (3 + j)%nat ltac:(lia)) as H3.
    replace (k + length (wl_body ws) + 3 + j)%nat
      with (k + (length (wl_body ws) + (3 + j)))%nat by lia.
    rewrite H3. exact (suf_gt_name nm j).
  - replace (k + length (wl_body ws) + 3 + length nm)%nat with (k + length J)%nat
      by lia.
    exact Hnl.
Qed.

(* ...AND THE OBLIGATION, END TO END.  This is the lemma the round applies
   at the child: from the line sh READ -- typed, so its body parses -- come
   the four PURE premises of [UkShRedirSeam.wp_kshm_child_alloc_redir]
   ([ushs_redir], [ushs_toks], [0 < length args], [length args < 10]) at
   [args := wl_toks ws], [gp := |wl_body ws| + 1] and
   [fe := |wl_body ws| + 3 + |nm|], at a name of any length. *)
Lemma sh_redir_line_lexable (J : list (bv 8)) (ws : list (list (bv 8)))
    (nm : list (bv 8)) (f : nat -> bv 8) (k len : nat) :
  parse_line J = Some (LEchoF ws nm) ->
  len = S (length J) ->
  (forall j : nat, (j < length J)%nat -> f (k + j)%nat = J !!! j) ->
  f (k + length J)%nat = wl_nl ->
  ushs_redir len (fun j : nat => f (k + j)%nat)
    (length (wl_body ws) + 1)%nat
    (length (wl_body ws) + 3 + length nm)%nat
  /\ ushs_toks len (fun j : nat => f (k + j)%nat)
       (length (wl_body ws) + 1)%nat 0%nat (wl_toks ws)
  /\ (0 < length (wl_toks ws))%nat
  /\ (length (wl_toks ws) < 10)%nat.
Proof using.
  intros Hp Hlen Hf Hnl.
  exact (ush_line_toks_holds_redir ws nm f k len
           (sh_redir_line_of_typed J ws nm f k len Hp Hlen Hf Hnl)).
Qed.


(* ===================================================================== *)
(* §4 A DEMO: THE MODEL'S OWN LINE                                        *)
(*                                                                        *)
(* [UkShWords] §6 is the mould.  This is not decoration: [ushs_line_is]    *)
(* and [parse_line _ = Some (LEchoF _ _)] are PREMISES of everything above, *)
(* so a lane that never instantiates them cannot tell a threaded premise   *)
(* from an unsatisfiable one (durable-notes, Vacuity).  [FileDisc.fd_ws]   *)
(* is the model's own [echo hello world], [FileDisc.fd_b0] the body        *)
(* [FileDisc.parse_line] answers [LEchoF fd_ws fd_nm] on (the name        *)
(* `a.txt`), and the tokens below                                          *)
(* are the three the child's argv is built from.                           *)
(* ===================================================================== *)

Definition fd_demo_f : nat -> bv 8 := fun j : nat => (fd_b0 ++ [wl_nl]) !!! j.

Lemma fd_demo_parse : parse_line fd_b0 = Some (LEchoF fd_ws fd_nm).
Proof using.
  apply (parse_line_body (LEchoF fd_ws fd_nm)); [ exact (uline_nopipe_echof fd_ws fd_nm) |].
  apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

Lemma fd_demo_toks : wl_toks fd_ws = [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat].
Proof using. vm_compute; reflexivity. Qed.

Lemma fd_demo_lexes :
  ushs_redir (S (length fd_b0)) (fun j : nat => fd_demo_f (0 + j)%nat)
    (length (wl_body fd_ws) + 1)%nat
    (length (wl_body fd_ws) + 3 + length fd_nm)%nat
  /\ ushs_toks (S (length fd_b0)) (fun j : nat => fd_demo_f (0 + j)%nat)
       (length (wl_body fd_ws) + 1)%nat 0%nat
       [(0, 4)%nat; (5, 10)%nat; (11, 16)%nat].
Proof using.
  assert (Hb : forall j : nat, (j < length fd_b0)%nat ->
            fd_demo_f (0 + j)%nat = fd_b0 !!! j)
    by (intros j Hj; exact (wl_lta_app_l fd_b0 [wl_nl] j Hj)).
  assert (Hnl : fd_demo_f (0 + length fd_b0)%nat = wl_nl).
  { pose proof (wl_lta_app_r fd_b0 [wl_nl] 0%nat) as Hr.
    rewrite Nat.add_0_r in Hr. exact Hr. }
  destruct (sh_redir_line_lexable fd_b0 fd_ws fd_nm fd_demo_f 0%nat
              (S (length fd_b0)) fd_demo_parse eq_refl Hb Hnl)
    as (Hr & Ht & _ & _).
  rewrite fd_demo_toks in Ht. exact (conj Hr Ht).
Qed.
