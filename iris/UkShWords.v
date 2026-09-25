(* ===================================================================== *)
(* UkShWords.v -- WHAT SH'S LEXER MAKES OF A LINE OF WORDS.               *)
(*                                                                        *)
(* [LineWords.v] spells a console line as words joined by single spaces    *)
(* and closed by a newline.  This file is what sh does with such a line,   *)
(* for an ARBITRARY word list:                                             *)
(*                                                                        *)
(*   [wl_no_symbols]  the line carries no shell metacharacter, so          *)
(*                    [gettoken] never leaves its default arm;             *)
(*   [wl_tokens]      [UkShParse.ushp_tokens] holds at [LineWords.wl_toks] *)
(*                    -- one [UshpTokCons] per word and [UshpTokNil] on    *)
(*                    the trailing newline;                                *)
(*   [wl_nulfold_at]  [nulterminate]'s cut ([UkShParseCmd.ushp_nulfold])   *)
(*                    leaves every word's own bytes alone and plants the   *)
(*                    terminator at each word's END -- so the argv strings *)
(*                    are the line's bytes and their NULs are the cut's.   *)
(*                                                                        *)
(* The tokenization induction runs on [wl_tail], whose offset always       *)
(* points AT a blank -- which is where [UshpTokCons] leaves the scan -- so *)
(* the first word is the only case outside it.                             *)
(*                                                                        *)
(* WHAT IT DOES NOT SAY.  Nothing here bounds the number of words (sh's    *)
(* [MAXARGS]) or the line's length (the console buffer, [getcmd]'s 100     *)
(* bytes, exec's stack page).  Those are the CALLER's side conditions;     *)
(* this file is about the lexer alone.                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import UmodeAbi.        (* [ubyte0] -- the terminator the cut plants *)
Require Import LineWords.       (* the line, the words, where they sit      *)
Require Import UkShParse.       (* the lexer: [ushp_skipws] / [ushp_toklen] /
                                   [ushp_tokens] / [ushp_no_symbols]        *)
Require Import UkShParseCmd.    (* the cut: [ushp_setb] / [ushp_nulfold]    *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  S1  THE TWO BLANKS, AS THE LEXER SEES THEM                            *)
(* ===================================================================== *)

Lemma wl_sp_ws : ushp_is_ws wl_sp = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wl_nl_ws : ushp_is_ws wl_nl = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wl_sp_nsym : ushp_is_sym wl_sp = false.
Proof. vm_compute. reflexivity. Qed.
Lemma wl_nl_nsym : ushp_is_sym wl_nl = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*  S2  THE LEXER'S CONDITION, FROM THE DISCIPLINE'S                     *)
(*                                                                        *)
(*  [LineWords.fn_wf] says a word is nonempty and made of alphanumerics   *)
(*  and the dot (an argv may carry a file name, cut W4).  What the lexer   *)
(*  needs is weaker and negative -- no byte of a word is one of sh's five  *)
(*  whitespace bytes or seven metacharacters -- and it is a consequence,  *)
(*  proved once here.  Nothing below states its own notion of a           *)
(*  well-formed word.                                                      *)
(* ===================================================================== *)

Definition wl_plain (b : bv 8) : Prop :=
  ushp_is_ws b = false /\ ushp_is_sym b = false.

(* the two tables, read numerically -- so that refuting a byte is [lia] *)
Lemma ushp_is_ws_val (b : bv 8) :
  ushp_is_ws b = true ->
  bv_unsigned b = 32%Z \/ bv_unsigned b = 9%Z \/ bv_unsigned b = 13%Z
  \/ bv_unsigned b = 10%Z \/ bv_unsigned b = 11%Z.
Proof.
  rewrite /ushp_is_ws /ushp_ws_bytes. intro H.
  apply bool_decide_eq_true_1 in H.
  apply elem_of_list_fmap in H as (z & -> & Hz).
  apply elem_of_cons in Hz as [-> | Hz]; [left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz]; [right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz]; [right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; right; by vm_compute |].
  by apply elem_of_nil in Hz.
Qed.

Lemma ushp_is_sym_val (b : bv 8) :
  ushp_is_sym b = true ->
  bv_unsigned b = 60%Z \/ bv_unsigned b = 124%Z \/ bv_unsigned b = 62%Z
  \/ bv_unsigned b = 38%Z \/ bv_unsigned b = 59%Z \/ bv_unsigned b = 40%Z
  \/ bv_unsigned b = 41%Z.
Proof.
  rewrite /ushp_is_sym /ushp_sym_bytes. intro H.
  apply bool_decide_eq_true_1 in H.
  apply elem_of_list_fmap in H as (z & -> & Hz).
  apply elem_of_cons in Hz as [-> | Hz]; [left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz]; [right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz]; [right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; right; right; left; by vm_compute |].
  apply elem_of_cons in Hz as [-> | Hz];
    [right; right; right; right; right; right; by vm_compute |].
  by apply elem_of_nil in Hz.
Qed.

Lemma wl_alnum_plain (b : bv 8) : wl_alnum b -> wl_plain b.
Proof.
  rewrite /wl_alnum /wl_plain. intro Ha. split.
  - destruct (ushp_is_ws b) eqn:Hw; [| reflexivity].
    exfalso. pose proof (ushp_is_ws_val b Hw). lia.
  - destruct (ushp_is_sym b) eqn:Hs; [| reflexivity].
    exfalso. pose proof (ushp_is_sym_val b Hs). lia.
Qed.

(* ...and the dot a file name carries (cut W4): 46 is neither *)
Lemma fn_byte_plain (b : bv 8) : fn_byte b -> wl_plain b.
Proof.
  intros [Ha | ->]; [exact (wl_alnum_plain b Ha) |].
  rewrite /wl_plain. split.
  - destruct (ushp_is_ws fn_dot) eqn:Hw; [| reflexivity].
    exfalso. pose proof (ushp_is_ws_val fn_dot Hw). rewrite fn_dot_val in H. lia.
  - destruct (ushp_is_sym fn_dot) eqn:Hs; [| reflexivity].
    exfalso. pose proof (ushp_is_sym_val fn_dot Hs). rewrite fn_dot_val in H. lia.
Qed.

(* A WORD OF NAME BYTES ([LineWords.fn_word]) -- every command word, and
   a file name of the class -- is plain *)
Lemma wl_word_plain (w : list (bv 8)) : fn_word w -> Forall wl_plain w.
Proof.
  intros [_ Hw]. induction w as [| b w' IH]; [constructor |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  constructor; [exact (fn_byte_plain b Hb) | exact (IH Hw')].
Qed.

Lemma wl_word_head (w : list (bv 8)) :
  fn_word w -> ushp_is_ws (w !!! 0) = false.
Proof.
  intro Hword. pose proof (wl_word_plain w Hword) as Hpl.
  destruct Hword as [Hne _]. destruct w as [| b w']; [done |].
  change ((b :: w') !!! 0) with b.
  by destruct (Forall_cons_1 _ _ _ Hpl) as [[? _] _].
Qed.

Lemma wl_nsym_of_plain (w : list (bv 8)) :
  Forall wl_plain w -> Forall (fun b => ushp_is_sym b = false) w.
Proof.
  induction w as [| b w' IH]; intro Hpl; [constructor |].
  destruct (Forall_cons_1 _ _ _ Hpl) as [[_ Hs] Hr].
  constructor; [exact Hs | exact (IH Hr)].
Qed.

(* ===================================================================== *)
(*  S3  THE TWO SCANS, AT A WORD                                          *)
(* ===================================================================== *)

(* [ushp_skipws] stops dead on a non-blank, at any fuel *)
Lemma wl_skipws_none (f : nat -> bv 8) (n i : nat) :
  ushp_is_ws (f i) = false -> ushp_skipws n i f = 0.
Proof. intro H. destruct n as [| n']; cbn; [reflexivity |]. by rewrite H. Qed.

(* ...and eats exactly one blank when the byte after it is not one *)
Lemma wl_skipws_one (f : nat -> bv 8) (n i : nat) :
  ushp_is_ws (f i) = true -> ushp_is_ws (f (S i)) = false ->
  0 < n -> ushp_skipws n i f = 1.
Proof.
  intros H0 H1 Hn. destruct n as [| n']; [lia |]. cbn. rewrite H0.
  by rewrite (wl_skipws_none f n' (S i) H1).
Qed.

(* [ushp_toklen] measures a run of plain bytes closed by a blank or a
   metacharacter, provided the fuel reaches that closer *)
Lemma wl_toklen_run (m : nat) :
  forall (n i : nat) (f : nat -> bv 8),
    (forall k : nat, k < m -> wl_plain (f (i + k))) ->
    m < n ->
    (ushp_is_ws (f (i + m)) = true \/ ushp_is_sym (f (i + m)) = true) ->
    ushp_toklen n i f = m.
Proof.
  induction m as [| m IH]; intros n i f Hpl Hn Hstop.
  - destruct n as [| n']; [lia |]. cbn. rewrite Nat.add_0_r in Hstop.
    destruct Hstop as [H | H]; rewrite H; [reflexivity |].
    by rewrite orb_true_r.
  - destruct n as [| n']; [lia |]. cbn.
    destruct (Hpl 0 ltac:(lia)) as [Hw Hs].
    rewrite Nat.add_0_r in Hw, Hs. rewrite Hw Hs. cbn [orb].
    f_equal. apply (IH n' (S i) f).
    + intros k Hk. replace (S i + k) with (i + S k) by lia.
      exact (Hpl (S k) ltac:(lia)).
    + lia.
    + replace (S i + m) with (i + S m) by lia. exact Hstop.
Qed.

(* [UkShParse.UshpTokCons] with the two scanned lengths NAMED, so a call
   site supplies them rather than leaving them to unification. *)
Lemma wl_tok_step (len i k n : nat) (f : nat -> bv 8)
    (toks : list (nat * nat)) :
  ushp_skipws (len - i) i f = k ->
  ushp_toklen (len - (i + k)) (i + k) f = n ->
  0 < n ->
  ushp_tokens len f (i + k + n) toks ->
  ushp_tokens len f i ((i + k, i + k + n) :: toks).
Proof.
  intros Hk Hn Hpos Ht.
  pose proof (UshpTokCons len f i toks) as C. cbv zeta in C.
  rewrite Hk Hn in C. exact (C Hpos Ht).
Qed.

(* ---- the scans read only inside the window they are given ------------ *)
(* [ushp_skipws] / [ushp_toklen] read [f] only inside their window, and
   [ushp_tokens]' two constructors read it only through them -- so
   pointwise equality below [len] carries a tokenization across.  A caller
   needs this because [wl_tokens] below is stated at the line read as a
   LIST while sh's command loop hands its body the line as [fun j =>
   f (k + j)]: the two are the same tokenization, not two computations.
   Three plain inductions; nothing about any particular line. *)
Lemma ushp_skipws_ext (n : nat) :
  forall (i : nat) (f f' : nat -> bv 8),
    (forall j : nat, i <= j < i + n -> f j = f' j) ->
    ushp_skipws n i f = ushp_skipws n i f'.
Proof.
  induction n as [| n IH]; intros i f f' H; cbn; [reflexivity |].
  rewrite (H i ltac:(lia)).
  destruct (ushp_is_ws (f' i)); [| reflexivity].
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma ushp_toklen_ext (n : nat) :
  forall (i : nat) (f f' : nat -> bv 8),
    (forall j : nat, i <= j < i + n -> f j = f' j) ->
    ushp_toklen n i f = ushp_toklen n i f'.
Proof.
  induction n as [| n IH]; intros i f f' H; cbn; [reflexivity |].
  rewrite (H i ltac:(lia)).
  destruct (ushp_is_ws (f' i) || ushp_is_sym (f' i)); [reflexivity |].
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

Lemma ushp_no_symbols_ext (len : nat) (f f' : nat -> bv 8) :
  (forall j : nat, j < len -> f j = f' j) ->
  ushp_no_symbols len f -> ushp_no_symbols len f'.
Proof. intros H Hns j Hj. rewrite <- (H j Hj). exact (Hns j Hj). Qed.

Lemma ushp_tokens_ext (len : nat) (f f' : nat -> bv 8) :
  (forall j : nat, j < len -> f j = f' j) ->
  forall (i : nat) (toks : list (nat * nat)),
    ushp_tokens len f i toks -> ushp_tokens len f' i toks.
Proof.
  intros Hff i toks Ht.
  assert (Hsk : forall a : nat,
            ushp_skipws (len - a) a f' = ushp_skipws (len - a) a f).
  { intro a. apply ushp_skipws_ext. intros j Hj. symmetry. apply Hff. lia. }
  assert (Htl : forall b : nat,
            ushp_toklen (len - b) b f' = ushp_toklen (len - b) b f).
  { intro b. apply ushp_toklen_ext. intros j Hj. symmetry. apply Hff. lia. }
  induction Ht as [off Hnil | off toks0 k0 n0 Hpos Hrec IH].
  - apply UshpTokNil. rewrite (Hsk off). exact Hnil.
  - apply (wl_tok_step len off k0 n0 f').
    + exact (Hsk off).
    + exact (Htl (off + k0)).
    + exact Hpos.
    + exact IH.
Qed.

(* ===================================================================== *)
(*  S4  NO METACHARACTER                                                  *)
(* ===================================================================== *)

Lemma wl_tail_nsym (ws : list (list (bv 8))) :
  fn_wf ws -> Forall (fun b => ushp_is_sym b = false) (wl_tail ws).
Proof.
  induction ws as [| w r IH]; intro Hwf; cbn [wl_tail]; [constructor |].
  destruct (fn_wf_cons w r Hwf) as [Hword Hr].
  constructor; [exact wl_sp_nsym |].
  apply Forall_app.
  split; [exact (wl_nsym_of_plain w (wl_word_plain w Hword)) | exact (IH Hr)].
Qed.

Lemma wl_line_nsym (ws : list (list (bv 8))) :
  fn_wf ws -> Forall (fun b => ushp_is_sym b = false) (wl_line ws).
Proof.
  intro Hwf. rewrite /wl_line. apply Forall_app. split.
  - destruct ws as [| w r]; cbn [wl_body]; [constructor |].
    destruct (fn_wf_cons w r Hwf) as [Hword Hr].
    apply Forall_app.
    split; [exact (wl_nsym_of_plain w (wl_word_plain w Hword))
           | exact (wl_tail_nsym r Hr)].
  - constructor; [exact wl_nl_nsym | constructor].
Qed.

Lemma wl_no_symbols (ws : list (list (bv 8))) (f : nat -> bv 8) (len : nat) :
  fn_wf ws ->
  len = length (wl_line ws) ->
  (forall j : nat, j < len -> f j = wl_line ws !!! j) ->
  ushp_no_symbols len f.
Proof.
  intros Hwf Hlen Hf j Hj. rewrite (Hf j Hj).
  rewrite list_lookup_total_alt.
  rewrite Hlen in Hj.
  destruct (lookup_lt_is_Some_2 (wl_line ws) j Hj) as [b Hb].
  rewrite Hb. cbn [default from_option].
  exact (Forall_lookup_1 _ _ _ _ (wl_line_nsym ws Hwf) Hb).
Qed.

(* ===================================================================== *)
(*  S5  THE TOKENIZATION                                                  *)
(* ===================================================================== *)

(* the byte a tail opens with is a blank -- a space if the tail has a word
   in it, the closing newline if it does not.  This is what closes the
   [ushp_toklen] scan of the word before it. *)
Lemma wl_tail_head_ws (r : list (list (bv 8))) :
  ushp_is_ws ((wl_tail r ++ [wl_nl]) !!! 0) = true.
Proof.
  destruct r as [| w0 r0]; cbn [wl_tail app].
  - exact wl_nl_ws.
  - exact wl_sp_ws.
Qed.

(* THE INDUCTION.  [p] points AT the blank that opens the tail, which is
   where [UshpTokCons] leaves the scan, and the tokens the relation names
   start one past it. *)
Lemma wl_tokens_tail (ws : list (list (bv 8))) :
  fn_wf ws ->
  forall (f : nat -> bv 8) (p len : nat),
    len = p + length (wl_tail ws) + 1 ->
    (forall j : nat, j < length (wl_tail ws) + 1 ->
       f (p + j) = (wl_tail ws ++ [wl_nl]) !!! j) ->
    ushp_tokens len f p (wl_toks_at (S p) ws).
Proof.
  induction ws as [| w r IH]; intros Hwf f p len Hlen Hf.
  - (* nothing left but the newline *)
    cbn [wl_tail length] in Hlen. subst len.
    cbn [wl_toks_at]. apply UshpTokNil.
    assert (Hp : ushp_is_ws (f p) = true).
    { replace p with (p + 0) at 1 by lia.
      rewrite (Hf 0 ltac:(cbn; lia)). exact (wl_tail_head_ws []). }
    replace (p + 0 + 1 - p) with 1 by lia.
    cbn [ushp_skipws]. rewrite Hp. lia.
  - destruct (fn_wf_cons w r Hwf) as [Hword Hr].
    pose proof (fn_word_pos w Hword) as Hwpos.
    pose proof (wl_word_plain w Hword) as Hwpl.
    (* the tail's bytes, spelled out: ' ' at 0, [w] at 1..|w|, then the
       REST of the tail (or the closing newline) from 1+|w| on *)
    assert (Hlenw : length (wl_tail (w :: r))
                    = 1 + length w + length (wl_tail r)).
    { cbn [wl_tail length]. rewrite length_app. lia. }
    assert (Hsp : f p = wl_sp).
    { replace p with (p + 0) at 1 by lia.
      rewrite (Hf 0 ltac:(lia)). reflexivity. }
    assert (Hw : forall k : nat, k < length w -> f (p + 1 + k) = w !!! k).
    { intros k Hk. replace (p + 1 + k) with (p + S k) by lia.
      rewrite (Hf (S k) ltac:(lia)).
      cbn [wl_tail app]. rewrite -app_assoc wl_lta_cons_S.
      exact (wl_lta_app_l w _ k Hk). }
    assert (Hrest : forall j : nat, j < length (wl_tail r) + 1 ->
              f (p + 1 + length w + j) = (wl_tail r ++ [wl_nl]) !!! j).
    { intros j Hj.
      replace (p + 1 + length w + j) with (p + S (length w + j)) by lia.
      rewrite (Hf (S (length w + j)) ltac:(lia)).
      cbn [wl_tail app]. rewrite -app_assoc wl_lta_cons_S.
      exact (wl_lta_app_r w (wl_tail r ++ [wl_nl]) j). }
    rewrite Hlenw in Hlen.
    (* ---- the skip: exactly the one separator ---- *)
    assert (Hskip : ushp_skipws (len - p) p f = 1).
    { apply wl_skipws_one; [ rewrite Hsp; exact wl_sp_ws | | lia ].
      replace (S p) with (p + 1 + 0) by lia.
      rewrite (Hw 0 Hwpos). exact (wl_word_head w Hword). }
    (* ---- the token: exactly the word ---- *)
    assert (Htok : ushp_toklen (len - (p + 1)) (p + 1) f = length w).
    { apply (wl_toklen_run (length w) (len - (p + 1)) (p + 1) f).
      - intros k Hk. rewrite (Hw k Hk).
        rewrite list_lookup_total_alt.
        destruct (lookup_lt_is_Some_2 w k Hk) as [b Hb]. rewrite Hb.
        cbn [default from_option].
        exact (Forall_lookup_1 _ _ _ _ Hwpl Hb).
      - lia.
      - left. replace (p + 1 + length w) with (p + 1 + length w + 0) by lia.
        rewrite (Hrest 0 ltac:(lia)). exact (wl_tail_head_ws r). }
    cbn [wl_toks_at].
    replace (S p, S p + length w) with (p + 1, p + 1 + length w)
      by (f_equal; lia).
    apply (wl_tok_step len p 1 (length w) f);
      [ exact Hskip | exact Htok | exact Hwpos | ].
    replace (S (S p + length w)) with (S (p + 1 + length w)) by lia.
    apply (IH Hr f (p + 1 + length w) len); [lia |].
    intros j Hj. exact (Hrest j Hj).
Qed.

(* ...AND THE LINE.  The first word has no separator before it, so it is
   one [UshpTokCons] at [k = 0] outside the induction. *)
Lemma wl_tokens (ws : list (list (bv 8))) (f : nat -> bv 8) (len : nat) :
  fn_wf ws ->
  len = length (wl_line ws) ->
  (forall j : nat, j < len -> f j = wl_line ws !!! j) ->
  ushp_tokens len f 0 (wl_toks ws).
Proof.
  intros Hwf Hlen Hf. rewrite /wl_toks.
  destruct ws as [| w r].
  - rewrite wl_line_length in Hlen. cbn [wl_body length] in Hlen.
    cbn [wl_toks_at]. apply UshpTokNil.
    assert (Hp : ushp_is_ws (f 0) = true).
    { rewrite (Hf 0 ltac:(lia)) wl_line_nil. exact wl_nl_ws. }
    assert (Hs : ushp_skipws (len - 0) 0 f = 1).
    { replace (len - 0) with 1 by lia. cbn [ushp_skipws]. by rewrite Hp. }
    lia.
  - destruct (fn_wf_cons w r Hwf) as [Hword Hr].
    pose proof (fn_word_pos w Hword) as Hwpos.
    pose proof (wl_word_plain w Hword) as Hwpl.
    assert (Hlen' : len = length w + (length (wl_tail r) + 1)).
    { rewrite Hlen wl_line_cons length_app length_app. cbn [length]. lia. }
    assert (Hw : forall k : nat, k < length w -> f k = w !!! k).
    { intros k Hk. rewrite (Hf k ltac:(lia)) wl_line_cons.
      exact (wl_lta_app_l w _ k Hk). }
    assert (Hrest : forall j : nat, j < length (wl_tail r) + 1 ->
              f (length w + j) = (wl_tail r ++ [wl_nl]) !!! j).
    { intros j Hj. rewrite (Hf (length w + j) ltac:(lia)) wl_line_cons.
      exact (wl_lta_app_r w (wl_tail r ++ [wl_nl]) j). }
    (* ---- no skip at all: the line opens on the command name ---- *)
    assert (Hskip : ushp_skipws (len - 0) 0 f = 0).
    { apply wl_skipws_none. rewrite (Hw 0 Hwpos).
      exact (wl_word_head w Hword). }
    assert (Htok : ushp_toklen (len - (0 + 0)) (0 + 0) f = length w).
    { apply (wl_toklen_run (length w) (len - (0 + 0)) (0 + 0) f).
      - intros k Hk. rewrite Nat.add_0_l (Hw k Hk).
        rewrite list_lookup_total_alt.
        destruct (lookup_lt_is_Some_2 w k Hk) as [b Hb]. rewrite Hb.
        cbn [default from_option].
        exact (Forall_lookup_1 _ _ _ _ Hwpl Hb).
      - lia.
      - left. rewrite Nat.add_0_l.
        replace (length w) with (length w + 0) by lia.
        rewrite (Hrest 0 ltac:(lia)). exact (wl_tail_head_ws r). }
    cbn [wl_toks_at].
    replace (0, 0 + length w) with (0 + 0, 0 + 0 + length w)
      by (f_equal; lia).
    apply (wl_tok_step len 0 0 (length w) f);
      [ exact Hskip | exact Htok | exact Hwpos | ].
    replace (0 + 0 + length w) with (length w) by lia.
    replace (S (0 + length w)) with (S (length w)) by lia.
    apply (wl_tokens_tail r Hr f (length w) len); [lia |].
    intros j Hj. exact (Hrest j Hj).
Qed.

(* ===================================================================== *)
(*  S6  THE CUT                                                           *)
(*                                                                        *)
(*  [ushp_nulfold] writes [ubyte0] at each token's END and touches nothing *)
(*  else, so its value at an index is decided by whether some token ends   *)
(*  there.  [wl_ends_at] is that test, and [wl_nulfold_spec] is the whole  *)
(*  of the cut -- everything below it is arithmetic on [wl_off].           *)
(* ===================================================================== *)

Definition wl_ends_at (toks : list (nat * nat)) (x : nat) : bool :=
  existsb (fun tk => Nat.eqb (snd tk) x) toks.

Lemma wl_nulfold_spec (toks : list (nat * nat)) :
  forall (g : nat -> bv 8) (x : nat),
    ushp_nulfold toks g x = if wl_ends_at toks x then ubyte0 else g x.
Proof.
  induction toks as [| tk toks IH]; intros g x; [reflexivity |].
  cbn [ushp_nulfold]. rewrite (IH (ushp_setb g (snd tk) ubyte0) x).
  rewrite /wl_ends_at. cbn [existsb].
  destruct (existsb (fun t => Nat.eqb (snd t) x) toks) eqn:He.
  - by rewrite orb_true_r.
  - rewrite orb_false_r /ushp_setb.
    destruct (Nat.eqb (snd tk) x) eqn:Hk.
    + apply Nat.eqb_eq in Hk. subst x. by rewrite Nat.eqb_refl.
    + apply Nat.eqb_neq in Hk.
      by rewrite (proj2 (Nat.eqb_neq x (snd tk)) ltac:(lia)).
Qed.

Lemma wl_nulfold_other (toks : list (nat * nat)) (g : nat -> bv 8) (x : nat) :
  wl_ends_at toks x = false -> ushp_nulfold toks g x = g x.
Proof. intro H. by rewrite (wl_nulfold_spec toks g x) H. Qed.

Lemma wl_nulfold_hit (toks : list (nat * nat)) (g : nat -> bv 8) (x : nat) :
  wl_ends_at toks x = true -> ushp_nulfold toks g x = ubyte0.
Proof. intro H. by rewrite (wl_nulfold_spec toks g x) H. Qed.

(* nothing laid out from [p] ends before [p] *)
Lemma wl_ends_at_below (ws : list (list (bv 8))) (p x : nat) :
  x < p -> wl_ends_at (wl_toks_at p ws) x = false.
Proof.
  intro Hx. rewrite /wl_ends_at.
  apply not_true_is_false. intro He.
  apply existsb_exists in He as [tk [Htk Heq]].
  apply Nat.eqb_eq in Heq.
  apply elem_of_list_In in Htk.
  destruct (wl_toks_at_ge ws p tk Htk) as [_ Hge]. lia.
Qed.

(* THE CUT, AT A WORD.  Inside word [i] the byte is the line's own; at its
   END it is the terminator [nulterminate] planted.  One induction, whose
   whole content is that every LATER token lies past this word and the one
   EARLIER write this step makes lies before the next word. *)
Lemma wl_nulfold_at (ws : list (list (bv 8))) :
  forall (off : nat) (g : nat -> bv 8) (i : nat) (w : list (bv 8)) (j : nat),
    ws !! i = Some w -> j <= length w ->
    ushp_nulfold (wl_toks_at off ws) g (wl_off off ws i + j)
    = (if Nat.eqb j (length w) then ubyte0 else g (wl_off off ws i + j)).
Proof.
  induction ws as [| w0 r IH]; intros off g i w j Hi Hj; [by destruct i |].
  cbn [wl_toks_at ushp_nulfold].
  destruct i as [| i']; cbn [wl_off].
  - (* this word is the first: every later token is past its end *)
    cbn in Hi. injection Hi as Heq. subst w0.
    rewrite (wl_nulfold_other _ _ _
               (wl_ends_at_below r (S (off + length w)) (off + j)
                  ltac:(lia))).
    rewrite /ushp_setb.
    destruct (Nat.eqb j (length w)) eqn:Hje.
    + apply Nat.eqb_eq in Hje. subst j. by rewrite Nat.eqb_refl.
    + apply Nat.eqb_neq in Hje.
      by rewrite (proj2 (Nat.eqb_neq (off + j) (off + length w))
                    ltac:(lia)).
  - (* ...or it is later, and the write this step makes is before it *)
    rewrite (IH (S (off + length w0)) (ushp_setb g (off + length w0) ubyte0)
               i' w j Hi Hj).
    pose proof (wl_off_ge r (S (off + length w0)) i') as Hge.
    destruct (Nat.eqb j (length w)); [reflexivity |].
    rewrite /ushp_setb.
    by rewrite (proj2 (Nat.eqb_neq (wl_off (S (off + length w0)) r i' + j)
                         (off + length w0)) ltac:(lia)).
Qed.

(* ---- ...AT THE LINE THE COMMAND LOOP HANDS THE PARSER ----------------- *)
(* [UkShParseCmd.ushp_ext] is the line as a byte RUN -- its own bytes below
   [len] and the terminator past it -- and what [nulterminate] cuts is that
   run.  Every index a word names is inside the window, so the extension is
   transparent at all of them: these two are the form a caller consumes. *)

Lemma wl_cut_in (ws : list (list (bv 8))) (g : nat -> bv 8)
    (len i : nat) (w : list (bv 8)) (j : nat) :
  ws !! i = Some w -> j < length w -> wl_off 0 ws i + j < len ->
  ushp_nulfold (wl_toks ws) (ushp_ext len g) (wl_off 0 ws i + j)
  = g (wl_off 0 ws i + j).
Proof.
  intros Hi Hj Hlt.
  rewrite /wl_toks (wl_nulfold_at ws 0 (ushp_ext len g) i w j Hi ltac:(lia)).
  rewrite (proj2 (Nat.eqb_neq j (length w)) ltac:(lia)).
  rewrite /ushp_ext. by rewrite (bool_decide_eq_true_2 _ Hlt).
Qed.

Lemma wl_cut_end (ws : list (list (bv 8))) (g : nat -> bv 8)
    (len i : nat) (w : list (bv 8)) :
  ws !! i = Some w ->
  ushp_nulfold (wl_toks ws) (ushp_ext len g) (wl_off 0 ws i + length w)
  = ubyte0.
Proof.
  intro Hi. rewrite /wl_toks.
  rewrite (wl_nulfold_at ws 0 (ushp_ext len g) i w (length w) Hi ltac:(lia)).
  by rewrite Nat.eqb_refl.
Qed.

(* ===================================================================== *)
(*  S7  ANTI-VACUITY                                                      *)
(*                                                                        *)
(*  Not merely true of nothing: a line of two words lexes into two tokens, *)
(*  at the offsets the join puts them at.  Everything here is closed, so   *)
(*  [vm_compute] answers it.                                              *)
(* ===================================================================== *)

Definition wl_demo : list (list (bv 8)) :=
  [ (fun z => Z_to_bv 8 z) <$> [104%Z; 105%Z]              (* "hi"  *)
  ; (fun z => Z_to_bv 8 z) <$> [121%Z; 111%Z; 117%Z] ].    (* "you" *)

Lemma wl_demo_wf : wl_wf wl_demo.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_toks : wl_toks wl_demo = [(0, 2); (3, 6)].
Proof. vm_compute. reflexivity. Qed.

Lemma wl_demo_line_length : length (wl_line wl_demo) = 7.
Proof. vm_compute. reflexivity. Qed.

Lemma wl_demo_lexes :
  ushp_no_symbols (length (wl_line wl_demo))
    (fun j => wl_line wl_demo !!! j)
  /\ ushp_tokens (length (wl_line wl_demo))
       (fun j => wl_line wl_demo !!! j) 0 [(0, 2); (3, 6)].
Proof.
  split.
  - exact (wl_no_symbols wl_demo _ _ (wl_wf_fn _ wl_demo_wf) eq_refl (fun j _ => eq_refl)).
  - rewrite -wl_demo_toks.
    exact (wl_tokens wl_demo _ _ (wl_wf_fn _ wl_demo_wf) eq_refl (fun j _ => eq_refl)).
Qed.
