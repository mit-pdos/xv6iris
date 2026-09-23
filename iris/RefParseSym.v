(* ===================================================================== *)
(* RefParseSym.v -- THE REFERENCE PARSER MEETS THE LANDED TOKEN MODELS     *)
(* (design/user-once.md SS2, worklist A2a).  Pure.                         *)
(*                                                                        *)
(* [RefParse.ref_gettoken] and [RefParse.ref_peek] are sh's gettoken and   *)
(* peek as computations on the line; [UkShParseSym.ushs_gettok_res] /     *)
(* [_end] / [_fin] are what the landed walks answer.  This file is the     *)
(* equation between the two, stated once, so that ONE gettoken walk       *)
(* (UkShGettoken.wp_ref_gettoken) is stated at the reference and the      *)
(* landed statements are its corollaries:                                 *)
(*                                                                        *)
(*   ref_gettoken len f off = (ushs_gettok_res .. k, k, ushs_gettok_end .. k, *)
(*                             ushs_gettok_fin .. k)   at k = off + skipws  *)
(*                                                                        *)
(* under [ref_sym_scope] (the walked arms of the switch) and             *)
(* [ref_nonnul] (the line's body bytes are not NUL -- the first pure       *)
(* conjunct of [UserHeap.ustr], so a walk reads it off the resource and   *)
(* never takes it as a premise).  The peek bridge is the same fact for    *)
(* [ref_peek] against strchr's pure model [ushp_find]: the table's byte   *)
(* function and the reference's byte LIST are related by                 *)
(* [tl = tf <$> seq 0 tlen].                                              *)
(*                                                                        *)
(* Sits right after UkShParseSym in the build so both the symbol tiers    *)
(* and the general walk can name it.  The cursor lemmas of SS0 were       *)
(* RefParseBridge's SS0 (one step of the reference, what it computes);    *)
(* they moved here because this file is below that one, and             *)
(* RefParseBridge imports this file.  [ref_sym_scope]'s instances: the    *)
(* symbol-free line ([RefParse.ref_sym_scope_nosym]), the redirect tier   *)
(* ([ushs_gt_ok_scope], below) and the pipe tier                          *)
(* ([UkShPipeLex.ushq_sym_ok_scope], above this file, where its premise   *)
(* is defined).                                                           *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import UmodeAbi.
Require Import UkShParse.
Require Import RefParse.
Require Import UkShParseSym.
Local Open Scope nat_scope.

(* the body bytes of the line are not NUL: [UserHeap.ustr]'s first pure
   conjunct, and what makes [ref_at len f i = ubyte0] mean [len <= i] *)
Definition ref_nonnul (len : nat) (f : nat -> bv 8) : Prop :=
  forall j : nat, j < len -> f j <> ubyte0.


(* ===================================================================== *)
(* §0 THE CURSOR LEMMAS: what one step of the reference computes           *)
(* ===================================================================== *)

Lemma ubyte0_val : bv_unsigned ubyte0 = 0%Z.
Proof using. vm_compute. reflexivity. Qed.

Lemma rb_gt_is_ushs : ushs_gt = rb_gt.
Proof using. reflexivity. Qed.


Lemma rt_word_ne_0 : rt_word <> 0%Z.
Proof using. unfold rt_word. lia. Qed.

Lemma ref_at_lt (len : nat) (f : nat -> bv 8) (i : nat) :
  i < len -> ref_at len f i = f i.
Proof using. intro H. unfold ref_at. rewrite (bool_decide_eq_true_2 _ H). reflexivity. Qed.

Lemma ref_at_ge (len : nat) (f : nat -> bv 8) (i : nat) :
  len <= i -> ref_at len f i = ubyte0.
Proof using.
  intro H. unfold ref_at. rewrite (bool_decide_eq_false_2 (i < len) ltac:(lia)). reflexivity.
Qed.

Lemma ref_skip_ge (len : nat) (f : nat -> bv 8) (i : nat) : i <= ref_skip len f i.
Proof using. unfold ref_skip. lia. Qed.

Lemma ref_skip_le (len : nat) (f : nat -> bv 8) (i : nat) :
  i <= len -> ref_skip len f i <= len.
Proof using. intro H. unfold ref_skip. pose proof (ushp_skipws_le (len - i) i f). lia. Qed.

Lemma ref_skip_idem (len : nat) (f : nat -> bv 8) (i : nat) :
  i <= len -> ref_skip len f (ref_skip len f i) = ref_skip len f i.
Proof using.
  intro H. unfold ref_skip. rewrite (ushp_skipws_idem len i f H). lia.
Qed.

Lemma ref_skip_at_len (len : nat) (f : nat -> bv 8) : ref_skip len f len = len.
Proof using. unfold ref_skip. rewrite Nat.sub_diag. cbn [ushp_skipws]. lia. Qed.

Lemma ref_skip_stop (len : nat) (f : nat -> bv 8) (i : nat) :
  ushp_is_ws (f i) = false -> ref_skip len f i = i.
Proof using. intro H. unfold ref_skip. rewrite (ushp_skipws_stop _ _ _ H). lia. Qed.

(* the blank scan stops on a non-blank byte or at the end *)
Lemma ref_skip_nows (len : nat) (f : nat -> bv 8) (i : nat) :
  i <= len -> ref_skip len f i < len -> ushp_is_ws (f (ref_skip len f i)) = false.
Proof using.
  intros Hi Hlt. unfold ref_skip in *. apply ushp_skipws_end. lia.
Qed.

(* a token of positive length starts on a byte that is neither blank nor
   symbol, so the cursor there is strictly inside the line *)
Lemma ref_toklen_pos_lt (len : nat) (f : nat -> bv 8) (s : nat) :
  0 < ushp_toklen (len - s) s f -> s < len.
Proof using. intro H. pose proof (ushp_toklen_le (len - s) s f). lia. Qed.

Lemma ref_toklen_pos_of (len : nat) (f : nat -> bv 8) (s : nat) :
  s < len -> ushp_is_ws (f s) = false -> ushp_is_sym (f s) = false ->
  0 < ushp_toklen (len - s) s f.
Proof using.
  intros Hlt Hws Hsym. destruct (len - s) as [| m ] eqn:E; [ lia | ].
  rewrite (ushp_toklen_step m s f ltac:(rewrite Hws, Hsym; reflexivity)). lia.
Qed.

(* ---- the peek sets are symbol bytes ---------------------------------- *)

Definition ref_symtoks (toks : list (bv 8)) : Prop :=
  Forall (fun b => ushp_is_sym b = true) toks.

Lemma ref_symtoks_redir : ref_symtoks [rb_lt; rb_gt].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_stop : ref_symtoks [rb_bar; rb_rpar; rb_amp; rb_semi].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_lpar : ref_symtoks [rb_lpar].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_bar : ref_symtoks [rb_bar].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_amp : ref_symtoks [rb_amp].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_semi : ref_symtoks [rb_semi].
Proof using. repeat (constructor; [ vm_compute; reflexivity | ]); constructor. Qed.
Lemma ref_symtoks_nil : ref_symtoks [].
Proof using. constructor. Qed.

Lemma rb_gt_notin_lpar : rb_gt ∉ [rb_lpar].
Proof using. apply (bool_decide_eq_false_1 (rb_gt ∈ [rb_lpar])). vm_compute. reflexivity. Qed.
Lemma rb_bar_notin_lpar : rb_bar ∉ [rb_lpar].
Proof using. apply (bool_decide_eq_false_1 (rb_bar ∈ [rb_lpar])). vm_compute. reflexivity. Qed.
Lemma rb_bar_notin_redir : rb_bar ∉ [rb_lt; rb_gt].
Proof using. apply (bool_decide_eq_false_1 (rb_bar ∈ [rb_lt; rb_gt])). vm_compute. reflexivity. Qed.
Lemma rb_gt_in_redir : rb_gt ∈ [rb_lt; rb_gt].
Proof using. apply (bool_decide_eq_true_1 (rb_gt ∈ [rb_lt; rb_gt])). vm_compute. reflexivity. Qed.
Lemma rb_bar_in_stop : rb_bar ∈ [rb_bar; rb_rpar; rb_amp; rb_semi].
Proof using. apply (bool_decide_eq_true_1 (rb_bar ∈ [rb_bar; rb_rpar; rb_amp; rb_semi])). vm_compute. reflexivity. Qed.
Lemma rb_bar_in_bar : rb_bar ∈ [rb_bar].
Proof using. apply (bool_decide_eq_true_1 (rb_bar ∈ [rb_bar])). vm_compute. reflexivity. Qed.
Lemma ushp_is_sym_nul : ushp_is_sym ubyte0 = false.
Proof using. vm_compute. reflexivity. Qed.
Lemma ushp_is_sym_gt : ushp_is_sym rb_gt = true.
Proof using. vm_compute. reflexivity. Qed.

(* the byte under the cursor is in no symbol set when it is not a symbol
   (or is the NUL past the end) *)
Lemma ref_at_notin (len : nat) (f : nat -> bv 8) (s : nat) (toks : list (bv 8)) :
  (s < len -> ushp_is_sym (f s) = false) -> ref_symtoks toks ->
  ref_at len f s ∉ toks.
Proof using.
  intros Hns Hsym Hin. unfold ref_symtoks in Hsym.
  apply elem_of_list_lookup_1 in Hin as [ k Hk ].
  pose proof (Forall_lookup_1 _ _ _ _ Hsym Hk) as Hb.
  unfold ref_at in Hb. destruct (bool_decide (s < len)) eqn:E.
  - apply bool_decide_eq_true_1 in E. rewrite (Hns E) in Hb. discriminate.
  - rewrite ushp_is_sym_nul in Hb. discriminate.
Qed.

(* ---- peek -------------------------------------------------------------- *)

Lemma ref_peek_miss (len : nat) (f : nat -> bv 8) (i : nat) (toks : list (bv 8)) :
  ref_at len f (ref_skip len f i) ∉ toks ->
  ref_peek len f i toks = (false, ref_skip len f i).
Proof using.
  intro H. unfold ref_peek. rewrite (bool_decide_eq_false_2 _ H), andb_false_r. reflexivity.
Qed.

Lemma ref_peek_hit (len : nat) (f : nat -> bv 8) (i : nat) (toks : list (bv 8)) :
  ref_at len f (ref_skip len f i) <> ubyte0 ->
  ref_at len f (ref_skip len f i) ∈ toks ->
  ref_peek len f i toks = (true, ref_skip len f i).
Proof using.
  intros Hnn Hin. unfold ref_peek.
  rewrite (bool_decide_eq_false_2 _ Hnn), (bool_decide_eq_true_2 _ Hin). reflexivity.
Qed.

(* peek at the end of the line misses every set and stays there *)
Lemma ref_peek_end (len : nat) (f : nat -> bv 8) (i : nat) (toks : list (bv 8)) :
  ref_skip len f i = len -> ref_symtoks toks -> ref_peek len f i toks = (false, len).
Proof using.
  intros Hs Hsym. rewrite <- Hs at 2. apply ref_peek_miss. rewrite Hs.
  apply ref_at_notin; [ lia | exact Hsym ].
Qed.

(* ---- gettoken ---------------------------------------------------------- *)

(* at the end of the line: code 0, cursor stays *)
Lemma ref_gettoken_nul (len : nat) (f : nat -> bv 8) (i : nat) :
  ref_skip len f i = len -> ref_gettoken len f i = (0%Z, len, len, len).
Proof using.
  intro Hs. unfold ref_gettoken. rewrite Hs, (ref_at_ge len f len ltac:(lia)).
  rewrite (bool_decide_eq_true_2 _ eq_refl). cbn beta iota. rewrite ref_skip_at_len. reflexivity.
Qed.

(* on a non-symbol byte: the default arm, a word that runs [ushp_toklen] *)
Lemma ref_gettoken_word (len : nat) (f : nat -> bv 8) (i s : nat) :
  ref_nonnul len f -> ref_skip len f i = s -> s < len -> ushp_is_sym (f s) = false ->
  ref_gettoken len f i
  = (rt_word, s, ref_tokend len f s, ref_skip len f (ref_tokend len f s)).
Proof using.
  intros Hnn Hs Hlt Hsym. unfold ref_gettoken. rewrite Hs, (ref_at_lt len f s Hlt).
  rewrite (bool_decide_eq_false_2 _ (Hnn s Hlt)).
  rewrite (bool_decide_eq_false_2 (f s = rb_gt)
             ltac:(intro E; rewrite E, ushp_is_sym_gt in Hsym; discriminate)).
  rewrite Hsym. reflexivity.
Qed.

(* on a symbol byte other than '>': the byte itself, one step *)
Lemma ref_gettoken_sym (len : nat) (f : nat -> bv 8) (i s : nat) :
  ref_nonnul len f -> ref_skip len f i = s -> s < len ->
  ushp_is_sym (f s) = true -> f s <> rb_gt ->
  ref_gettoken len f i = (bv_unsigned (f s), s, S s, ref_skip len f (S s)).
Proof using.
  intros Hnn Hs Hlt Hsym Hgt. unfold ref_gettoken. rewrite Hs, (ref_at_lt len f s Hlt).
  rewrite (bool_decide_eq_false_2 _ (Hnn s Hlt)), (bool_decide_eq_false_2 _ Hgt), Hsym.
  reflexivity.
Qed.

(* on a '>' not followed by another: the '>' code, one step *)
Lemma ref_gettoken_gt (len : nat) (f : nat -> bv 8) (i s : nat) :
  ref_nonnul len f -> ref_skip len f i = s -> s < len ->
  f s = rb_gt -> ref_at len f (S s) <> rb_gt ->
  ref_gettoken len f i = (bv_unsigned rb_gt, s, S s, ref_skip len f (S s)).
Proof using.
  intros Hnn Hs Hlt Hgt Hnext. unfold ref_gettoken. rewrite Hs, (ref_at_lt len f s Hlt).
  rewrite (bool_decide_eq_false_2 _ (Hnn s Hlt)), Hgt.
  rewrite (bool_decide_eq_true_2 _ eq_refl), (bool_decide_eq_false_2 _ Hnext).
  reflexivity.
Qed.


(* ===================================================================== *)
(* §1 THE SYMBOL SCOPE'S REDIRECT INSTANCE                                *)
(* ===================================================================== *)

(* '>' only, never last, never doubled -- the right disjunct, every time *)
Lemma ushs_gt_ok_scope (len : nat) (f : nat -> bv 8) :
  ushs_gt_ok len f -> ref_sym_scope len f.
Proof using.
  intros Hgt j Hj Hs. right. exact (Hgt j Hj Hs).
Qed.

Lemma rb_bar_ne_gt : rb_bar <> rb_gt.
Proof using. vm_compute. discriminate. Qed.


(* ===================================================================== *)
(* §2 gettoken: THE REFERENCE IS THE LANDED ANSWER                        *)
(* ===================================================================== *)

(* the four arms the scope allows, as [ushs_gettok_*] spell them: the
   cursor after the blank scan is [k]; NUL at [k = len]; a '|' or a single
   '>' answers the byte and steps once; anything else is a word *)
Lemma ref_gettoken_ushs (len : nat) (f : nat -> bv 8) (off : nat) :
  ref_sym_scope len f -> ref_nonnul len f -> off <= len ->
  ref_gettoken len f off
  = (ushs_gettok_res len f (off + ushp_skipws (len - off) off f),
     off + ushp_skipws (len - off) off f,
     ushs_gettok_end len f (off + ushp_skipws (len - off) off f),
     ushs_gettok_fin len f (off + ushp_skipws (len - off) off f)).
Proof using.
  intros Hscope Hnn Hoff.
  set (k := off + ushp_skipws (len - off) off f).
  assert (Hk : ref_skip len f off = k) by reflexivity.
  assert (Hkle : k <= len)
    by (unfold k; pose proof (ushp_skipws_le (len - off) off f); lia).
  destruct (lt_dec k len) as [ Hlt | Hge ].
  - destruct (ushp_is_sym (f k)) eqn:Esym.
    + destruct (Hscope k Hlt Esym) as [ Hbar | (Hgt & Hk1 & Hnext) ].
      * rewrite (ref_gettoken_sym len f off k Hnn Hk Hlt Esym
                   ltac:(rewrite Hbar; exact rb_bar_ne_gt)).
        unfold ushs_gettok_fin, ushs_gettok_end, ushs_gettok_res, ref_skip.
        rewrite (bool_decide_eq_true_2 _ Hlt), Esym. reflexivity.
      * rewrite (ref_gettoken_gt len f off k Hnn Hk Hlt Hgt
                   ltac:(rewrite (ref_at_lt len f (S k) Hk1); exact Hnext)).
        unfold ushs_gettok_fin, ushs_gettok_end, ushs_gettok_res, ref_skip.
        rewrite (bool_decide_eq_true_2 _ Hlt), Esym, Hgt. reflexivity.
    + rewrite (ref_gettoken_word len f off k Hnn Hk Hlt Esym).
      unfold ushs_gettok_fin, ushs_gettok_end, ushs_gettok_res,
        ref_tokend, ref_skip.
      rewrite (bool_decide_eq_true_2 _ Hlt), Esym. reflexivity.
  - assert (Hkeq : k = len) by lia.
    rewrite (ref_gettoken_nul len f off (eq_trans Hk Hkeq)).
    rewrite Hkeq, ushs_gettok_res_end, ushs_gettok_end_stop,
      ushs_gettok_fin_stop.
    reflexivity.
Qed.


(* ===================================================================== *)
(* §3 peek: THE REFERENCE AGAINST strchr's PURE MODEL                     *)
(* ===================================================================== *)

(* the table as peek's walk sees it ([tlen] bytes at [tf]) and as the
   reference sees it (a list): membership is a [ushp_find] hit *)
Lemma ushp_find_elem (tlen : nat) (tf : nat -> bv 8) (b : bv 8) :
  (exists j : nat, ushp_find tlen 0 tf b = Some j) <-> b ∈ (tf <$> seq 0 tlen).
Proof using.
  split.
  - intros [ j Hj ].
    pose proof (ushp_find_some_val tlen 0 j tf b Hj) as Hb.
    pose proof (ushp_find_ge tlen 0 tf b j Hj) as Hrng.
    apply elem_of_list_fmap. exists j. split; [ exact (eq_sym Hb) | ].
    apply elem_of_seq. lia.
  - intro Hin. apply elem_of_list_fmap in Hin as (j & Hb & Hj).
    apply elem_of_seq in Hj.
    exact (ushp_find_some_of tlen 0 j tf b ltac:(lia) (eq_sym Hb)).
Qed.

(* [ref_peek] at a non-NUL line: the byte at the skipped cursor is inside
   the line and found in the table *)
Lemma ref_peek_find (len : nat) (f : nat -> bv 8) (off tlen : nat)
    (tf : nat -> bv 8) (tl : list (bv 8)) :
  ref_nonnul len f -> off <= len -> tl = tf <$> seq 0 tlen ->
  ref_peek len f off tl
  = (bool_decide (off + ushp_skipws (len - off) off f < len)
     && match ushp_find tlen 0 tf (f (off + ushp_skipws (len - off) off f)) with
        | Some _ => true | None => false end,
     off + ushp_skipws (len - off) off f).
Proof using.
  intros Hnn Hoff Htl. subst tl.
  set (k := off + ushp_skipws (len - off) off f).
  assert (Hk : ref_skip len f off = k) by reflexivity.
  assert (Hkle : k <= len)
    by (unfold k; pose proof (ushp_skipws_le (len - off) off f); lia).
  unfold ref_peek. rewrite Hk.
  destruct (lt_dec k len) as [ Hlt | Hge ].
  - rewrite (ref_at_lt len f k Hlt), (bool_decide_eq_true_2 _ Hlt).
    rewrite (bool_decide_eq_false_2 _ (Hnn k Hlt)). cbn [negb andb].
    f_equal.
    destruct (ushp_find tlen 0 tf (f k)) as [ j | ] eqn:Ef.
    + apply bool_decide_eq_true_2.
      apply ushp_find_elem. exists j. exact Ef.
    + apply bool_decide_eq_false_2. intro Hin.
      apply ushp_find_elem in Hin as [ j Hj ]. rewrite Ef in Hj. discriminate.
  - rewrite (ref_at_ge len f k ltac:(lia)), (bool_decide_eq_false_2 (k < len) Hge).
    rewrite (bool_decide_eq_true_2 (ubyte0 = ubyte0) eq_refl). reflexivity.
Qed.
