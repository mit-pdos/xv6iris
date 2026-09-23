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
(* SS5 (A2c) is parseexec's: the argument loop's inversion [ref_args_inv] *)
(* and prefix law, the wrap's inversions, and the redirect line's          *)
(* [ref_parseexec_redir] moved down from RefParseBridge.                   *)
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

(* ===================================================================== *)
(* §4 parseredirs: WHAT ONE TURN OF THE REFERENCE LOOP IS                  *)
(* ===================================================================== *)

(* The lemmas the general parseredirs walk (UkShRedirs.wp_ref_parseredirs)
   reads its case split off: the accumulator is a prefix the loop never
   looks at; a [Some ([], fin)] answer is a peek that missed at [fin]; a
   [Some (r :: rs, fin)] answer under the symbol scope is a peek that hit
   a '>', the '>' token, a word for the file name, and the loop again at
   the word's end.  The three bridge lemmas at the bottom were
   RefParseBridge's; they moved here because the walk sits below that
   file.  The three of them come first: the inversions use [rredir_of_gt]. *)

(* ---- parseredirs ------------------------------------------------------- *)

(* no '<' or '>' under the cursor: no redirect, cursor at the skipped
   position *)
Lemma ref_redirs_miss (len : nat) (f : nat -> bv 8) (n i : nat) (acc : list rredir) :
  0 < n -> ref_at len f (ref_skip len f i) ∉ [rb_lt; rb_gt] ->
  ref_redirs len f n i acc = Some (acc, ref_skip len f i).
Proof using.
  intros Hn Hnotin. destruct n as [| n ]; [ lia | ]. cbn [ref_redirs].
  rewrite (ref_peek_miss _ _ _ _ Hnotin). reflexivity.
Qed.

Lemma rredir_of_gt (q eq : nat) :
  rredir_of (bv_unsigned rb_gt) q eq
  = Some {| rr_q := q; rr_eq := eq; rr_mode := rr_mode_gt; rr_fd := 1 |}.
Proof using. vm_compute. reflexivity. Qed.

(* the canonical redirect under the cursor: `> file' is consumed, the
   redirect appended, and the line is exhausted *)
Lemma ref_redirs_gt (len : nat) (f : nat -> bv 8) (p e n i : nat) (acc : list rredir) :
  ref_nonnul len f -> ushs_redir len f p e -> ref_skip len f i = p -> 1 < n ->
  ref_redirs len f n i acc
  = Some (acc ++ [{| rr_q := S (S p); rr_eq := e; rr_mode := rr_mode_gt; rr_fd := 1 |}], len).
Proof using.
  intros Hnn Hr Hs Hn. destruct n as [| [| n ]]; [ lia | lia | ].
  pose proof (ushs_redir_lt _ _ _ _ Hr) as Hp.
  pose proof (ushs_redir_sp_lt _ _ _ _ Hr) as Hsp.
  pose proof (ushs_redir_gt _ _ _ _ Hr) as Hgt. rewrite rb_gt_is_ushs in Hgt.
  assert (Hssp : S (S p) < len) by (destruct Hr as (_ & _ & _ & _ & H1 & H2 & _ & _); lia).
  assert (He : e < len) by (destruct Hr as (_ & _ & _ & _ & _ & H2 & _ & _); lia).
  assert (Hlo : S (S p) < e) by (destruct Hr as (_ & _ & _ & _ & H1 & _); lia).
  destruct (ushs_redir_file_byte len f p e (S (S p)) Hr (conj (Nat.le_refl _) Hlo)) as [ Hfw Hfs ].
  cbn [ref_redirs].
  rewrite (ref_peek_hit len f i [rb_lt; rb_gt]);
    [ | rewrite Hs, (ref_at_lt _ _ _ Hp); exact (Hnn p Hp)
      | rewrite Hs, (ref_at_lt _ _ _ Hp), Hgt; exact rb_gt_in_redir ].
  rewrite Hs. cbn beta iota.
  (* the '>' *)
  rewrite (ref_gettoken_gt len f p p Hnn (ref_skip_stop _ _ _ ltac:(rewrite Hgt; exact ushs_gt_not_ws)) Hp Hgt);
    [ | rewrite (ref_at_lt _ _ _ Hsp), <- rb_gt_is_ushs; exact (ushs_redir_next _ _ _ _ Hr) ].
  cbn beta iota.
  assert (Hskip1 : ref_skip len f (S p) = S (S p)).
  { unfold ref_skip. rewrite (ushs_skipws_after_gt _ _ _ _ Hr). lia. }
  rewrite Hskip1.
  (* the file name *)
  rewrite (ref_gettoken_word len f (S (S p)) (S (S p)) Hnn (ref_skip_stop _ _ _ Hfw) Hssp Hfs).
  cbn beta iota.
  assert (Hend : ref_tokend len f (S (S p)) = e).
  { unfold ref_tokend. rewrite (ushs_toklen_file _ _ _ _ Hr). lia. }
  rewrite Hend.
  assert (Hskip2 : ref_skip len f e = len).
  { unfold ref_skip. rewrite (ushs_skipws_tail _ _ _ _ Hr). lia. }
  rewrite Hskip2, (bool_decide_eq_true_2 _ eq_refl), rredir_of_gt.
  (* the fuel [S (S n)] unfolded both turns: the second peek is at the end *)
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_redir). reflexivity.
Qed.

Lemma rb_gt_ne_nul : rb_gt <> ubyte0.
Proof using. vm_compute. discriminate. Qed.
Lemma rb_bar_ne_lt : rb_bar <> rb_lt.
Proof using. vm_compute. discriminate. Qed.
Lemma ushp_is_sym_lt : ushp_is_sym rb_lt = true.
Proof using. vm_compute. reflexivity. Qed.

(* the accumulator is only ever appended to *)
Lemma ref_redirs_acc (len : nat) (f : nat -> bv 8) (n i : nat) (acc : list rredir) :
  ref_redirs len f n i acc
  = match ref_redirs len f n i [] with
    | Some (rs, s) => Some (acc ++ rs, s)
    | None => None
    end.
Proof using.
  revert i acc. induction n as [| n IH ]; intros i acc; [ reflexivity | ].
  cbn [ref_redirs].
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ].
  destruct hit; [ | rewrite app_nil_r; reflexivity ].
  destruct (ref_gettoken len f s) as [[[ tok q0 ] e0 ] s1 ].
  destruct (ref_gettoken len f s1) as [[[ t2 q ] e ] s2 ].
  destruct (bool_decide (t2 = rt_word)); [ | reflexivity ].
  destruct (rredir_of tok q e) as [ r | ]; [ | reflexivity ].
  rewrite (IH s2 (acc ++ [r])).
  rewrite (IH s2 (@nil rredir ++ [r])).
  destruct (ref_redirs len f n s2 []) as [[ rs s' ] | ]; [ | reflexivity ].
  cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.

(* the two answers of peek, read back *)
Lemma ref_peek_hit_inv (len : nat) (f : nat -> bv 8) (i s : nat) (toks : list (bv 8)) :
  ref_peek len f i toks = (true, s) ->
  s = ref_skip len f i /\ ref_at len f s <> ubyte0 /\ ref_at len f s ∈ toks.
Proof using.
  unfold ref_peek. intro H. injection H as Hb Hs. subst s.
  apply andb_true_iff in Hb as [ Hnn Hin ].
  apply negb_true_iff, bool_decide_eq_false_1 in Hnn.
  apply bool_decide_eq_true_1 in Hin.
  auto.
Qed.

Lemma ref_peek_miss_inv (len : nat) (f : nat -> bv 8) (i s : nat) (toks : list (bv 8)) :
  ref_peek len f i toks = (false, s) -> s = ref_skip len f i.
Proof using. unfold ref_peek. intro H. injection H as _ Hs. exact (eq_sym Hs). Qed.

(* gettoken leaves the cursor inside the line *)
Lemma ref_gettoken_fin_le (len : nat) (f : nat -> bv 8) (i : nat) (ret : Z) (q e fin : nat) :
  i <= len -> ref_gettoken len f i = (ret, q, e, fin) -> fin <= len.
Proof using.
  intros Hi H. unfold ref_gettoken in H.
  set (s := ref_skip len f i) in H.
  assert (Hs : s <= len) by exact (ref_skip_le len f i Hi).
  destruct (bool_decide (ref_at len f s = ubyte0)) eqn:E0.
  { injection H as _ _ _ <-. exact (ref_skip_le len f s Hs). }
  apply bool_decide_eq_false_1 in E0.
  assert (Hlt : s < len).
  { destruct (lt_dec s len) as [ | Hge ]; [ assumption | ].
    exfalso. apply E0. exact (ref_at_ge len f s ltac:(lia)). }
  destruct (bool_decide (ref_at len f s = rb_gt)) eqn:E1.
  - destruct (bool_decide (ref_at len f (S s) = rb_gt)) eqn:E2.
    + injection H as _ _ _ <-.
      apply bool_decide_eq_true_1 in E2.
      assert (HSs : S s < len).
      { destruct (lt_dec (S s) len) as [ | Hge ]; [ assumption | ].
        exfalso. rewrite (ref_at_ge len f (S s) ltac:(lia)) in E2.
        exact (rb_gt_ne_nul (eq_sym E2)). }
      apply ref_skip_le. lia.
    + injection H as _ _ _ <-. apply ref_skip_le. lia.
  - destruct (ushp_is_sym (ref_at len f s)).
    + injection H as _ _ _ <-. apply ref_skip_le. lia.
    + injection H as _ _ _ <-. apply ref_skip_le.
      unfold ref_tokend. pose proof (ushp_toklen_le (len - s) s f). lia.
Qed.

(* a peek that hit the redirect table under the scope hit a single '>' *)
Lemma ref_redir_hit_gt (len : nat) (f : nat -> bv 8) (s : nat) :
  ref_sym_scope len f -> ref_at len f s <> ubyte0 -> ref_at len f s ∈ [rb_lt; rb_gt] ->
  s < len /\ f s = rb_gt /\ S s < len /\ f (S s) <> rb_gt.
Proof using.
  intros Hsc Hnn Hin.
  assert (Hlt : s < len).
  { destruct (lt_dec s len) as [ | Hge ]; [ assumption | ].
    exfalso. apply Hnn. exact (ref_at_ge len f s ltac:(lia)). }
  rewrite (ref_at_lt len f s Hlt) in Hin.
  assert (Hsym : ushp_is_sym (f s) = true).
  { apply elem_of_cons in Hin as [ -> | Hin ]; [ exact ushp_is_sym_lt | ].
    apply elem_of_cons in Hin as [ -> | Hin ]; [ exact ushp_is_sym_gt | ].
    exfalso. exact (not_elem_of_nil _ Hin). }
  destruct (Hsc s Hlt Hsym) as [ Hbar | (Hgt & Hk1 & Hnext) ].
  - exfalso. rewrite Hbar in Hin.
    apply elem_of_cons in Hin as [ E | Hin ]; [ exact (rb_bar_ne_lt E) | ].
    apply elem_of_cons in Hin as [ E | Hin ]; [ exact (rb_bar_ne_gt E) | ].
    exact (not_elem_of_nil _ Hin).
  - auto.
Qed.

(* ZERO turns: the first peek missed, and the cursor is where it stopped *)
Lemma ref_redirs_nil_inv (len : nat) (f : nat -> bv 8) (n i fin : nat) :
  ref_redirs len f n i [] = Some ([], fin) -> ref_peek len f i [rb_lt; rb_gt] = (false, fin).
Proof using.
  destruct n as [| n ]; [ discriminate | ]. cbn [ref_redirs].
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ].
  destruct hit; [ | intro H; injection H as <-; reflexivity ].
  destruct (ref_gettoken len f s) as [[[ tok q0 ] e0 ] s1 ].
  destruct (ref_gettoken len f s1) as [[[ t2 q ] e ] s2 ].
  destruct (bool_decide (t2 = rt_word)); [ | discriminate ].
  destruct (rredir_of tok q e) as [ r | ]; [ | discriminate ].
  rewrite ref_redirs_acc.
  destruct (ref_redirs len f n s2 []) as [[ rs s' ] | ]; [ | discriminate ].
  intro H. injection H as H _. cbn [app] in H. discriminate H.
Qed.

(* ONE turn: the peek hit a single '>' at [s], the '>' token steps to [s1],
   the file name is the word [[q, e)] ending at [s2], the redirect is the
   '>' one, and the loop goes on at [s2] with one unit of fuel less *)
Lemma ref_redirs_cons_inv (len : nat) (f : nat -> bv 8) (n i : nat)
    (r : rredir) (rs : list rredir) (fin : nat) :
  ref_sym_scope len f -> ref_nonnul len f -> i <= len ->
  ref_redirs len f (S n) i [] = Some (r :: rs, fin) ->
  exists s s1 q e s2 : nat,
    ref_peek len f i [rb_lt; rb_gt] = (true, s) /\ s <= len
    /\ ref_gettoken len f s = (bv_unsigned rb_gt, s, S s, s1) /\ s1 <= len
    /\ ref_gettoken len f s1 = (rt_word, q, e, s2) /\ s2 <= len
    /\ r = {| rr_q := q; rr_eq := e; rr_mode := rr_mode_gt; rr_fd := 1 |}
    /\ ref_redirs len f n s2 [] = Some (rs, fin).
Proof using.
  intros Hsc Hnonul Hi H. cbn [ref_redirs] in H.
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ] eqn:Epk.
  destruct hit; [ | injection H as H _; discriminate H ].
  destruct (ref_peek_hit_inv len f i s [rb_lt; rb_gt] Epk) as (Hs & Hnn & Hin).
  destruct (ref_redir_hit_gt len f s Hsc Hnn Hin) as (Hlt & Hgt & HSs & Hnext).
  assert (Hskip : ref_skip len f s = s) by (rewrite Hs; exact (ref_skip_idem len f i Hi)).
  assert (Hnext' : ref_at len f (S s) <> rb_gt) by (rewrite (ref_at_lt len f (S s) HSs); exact Hnext).
  pose proof (ref_gettoken_gt len f s s Hnonul Hskip Hlt Hgt Hnext') as E1.
  rewrite E1 in H. cbn beta iota in H.
  destruct (ref_gettoken len f (ref_skip len f (S s))) as [[[ t2 q ] e ] s2 ] eqn:E2.
  destruct (bool_decide (t2 = rt_word)) eqn:Et2; [ | discriminate H ].
  apply bool_decide_eq_true_1 in Et2. subst t2.
  rewrite rredir_of_gt, ref_redirs_acc in H.
  destruct (ref_redirs len f n s2 []) as [[ rs0 s' ] | ] eqn:Er; [ | discriminate H ].
  cbn [app] in H. injection H as <- <- <-.
  assert (Hs1 : ref_skip len f (S s) <= len) by (apply ref_skip_le; lia).
  exists s, (ref_skip len f (S s)), q, e, s2.
  refine (conj eq_refl (conj _ (conj E1 (conj Hs1 (conj E2 (conj _ (conj eq_refl Er))))))).
  - lia.
  - exact (ref_gettoken_fin_le len f _ _ _ _ _ Hs1 E2).
Qed.

Lemma ref_redirs_of_peek_miss (len : nat) (f : nat -> bv 8) (n i s : nat) (acc : list rredir) :
  ref_peek len f i [rb_lt; rb_gt] = (false, s) -> ref_redirs len f (S n) i acc = Some (acc, s).
Proof using. intro H. cbn [ref_redirs]. rewrite H. reflexivity. Qed.



(* ===================================================================== *)
(* §5 parseexec: THE ARGUMENT LOOP AND THE WRAP                            *)
(* ===================================================================== *)

(* The lemmas the general argument-loop walk (UkShArgs.wp_ref_pex_loop)
   and the general parseexec walk (UkShArgs.wp_ref_parseexec) read their
   case splits off.  [ref_args_nul] / [ref_args_step] and the redirect
   line's [ref_args_of_toks_redir] / [ref_parseexec_redir] (with their two
   helpers) were RefParseBridge's; they moved here because those walks sit
   below that file. *)

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


(* parseredirs leaves the cursor inside the line *)
Lemma ref_redirs_fin_le (len : nat) (f : nat -> bv 8) (n i : nat)
    (acc rs : list rredir) (fin : nat) :
  i <= len -> ref_redirs len f n i acc = Some (rs, fin) -> fin <= len.
Proof using.
  revert i acc. induction n as [| n IH ]; intros i acc Hi H; [ discriminate H | ].
  cbn [ref_redirs] in H.
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ] eqn:Epk.
  destruct hit.
  - apply ref_peek_hit_inv in Epk as (Hs & _ & _).
    assert (Hsle : s <= len) by (rewrite Hs; exact (ref_skip_le len f i Hi)).
    destruct (ref_gettoken len f s) as [[[ tok q0 ] e0 ] s1 ] eqn:E1.
    assert (Hs1 : s1 <= len) by exact (ref_gettoken_fin_le len f s tok q0 e0 s1 Hsle E1).
    destruct (ref_gettoken len f s1) as [[[ t2 q ] e ] s2 ] eqn:E2.
    assert (Hs2 : s2 <= len) by exact (ref_gettoken_fin_le len f s1 t2 q e s2 Hs1 E2).
    destruct (bool_decide (t2 = rt_word)); [ | discriminate H ].
    destruct (rredir_of tok q e); [ | discriminate H ].
    exact (IH s2 _ Hs2 H).
  - apply ref_peek_miss_inv in Epk. injection H as _ Hfin. subst fin. rewrite Epk.
    exact (ref_skip_le len f i Hi).
Qed.

(* the argument loop only ever appends to its redirect accumulator *)
Lemma ref_args_prefix (len : nat) (f : nat -> bv 8) (n i : nat)
    (toks0 toks : list (nat * nat)) (rs0 rs : list rredir) (fin : nat) :
  ref_args len f n i toks0 rs0 = Some (toks, rs, fin) ->
  exists rs' : list rredir, rs = rs0 ++ rs'.
Proof using.
  revert i toks0 rs0. induction n as [| n IH ]; intros i toks0 rs0 H; [ discriminate H | ].
  cbn [ref_args] in H.
  destruct (ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi]) as [ stop s ].
  destruct stop.
  { injection H as _ Hrs _. subst rs. exists []. rewrite app_nil_r. reflexivity. }
  destruct (ref_gettoken len f s) as [[[ tok q ] e ] s1 ].
  destruct (bool_decide (tok = 0%Z)).
  { injection H as _ Hrs _. subst rs. exists []. rewrite app_nil_r. reflexivity. }
  destruct (negb (bool_decide (tok = rt_word))); [ discriminate H | ].
  cbv zeta in H.
  destruct (bool_decide (10 <= length (toks0 ++ [(q, e)]))); [ discriminate H | ].
  rewrite ref_redirs_acc in H.
  destruct (ref_redirs len f n s1 []) as [[ rs1 s2 ] | ]; [ | discriminate H ].
  destruct (IH s2 _ _ H) as [ rs' -> ].
  exists (rs1 ++ rs'). rewrite app_assoc. reflexivity.
Qed.

(* what one round of the loop did, read off its answer: the stop set was
   hit at the skipped cursor; or gettoken answered NUL there; or a word
   was consumed, parseredirs ran after it, and the loop went on with one
   unit of fuel less.  Any other token code makes the reference answer
   [None], so the syntax panic never has to be walked. *)
Lemma ref_args_inv (len : nat) (f : nat -> bv 8) (n i : nat)
    (toks0 toks : list (nat * nat)) (rs0 rs : list rredir) (fin : nat) :
  i <= len ->
  ref_args len f (S n) i toks0 rs0 = Some (toks, rs, fin) ->
  (ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi] = (true, fin)
   /\ toks = toks0 /\ rs = rs0)
  \/ (exists s q e : nat,
        ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi] = (false, s) /\ s <= len
        /\ ref_gettoken len f s = (0%Z, q, e, fin)
        /\ toks = toks0 /\ rs = rs0)
  \/ (exists s q e s1 s2 : nat, exists rs1 : list rredir,
        ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi] = (false, s) /\ s <= len
        /\ ref_gettoken len f s = (rt_word, q, e, s1) /\ s1 <= len
        /\ length toks0 < 9
        /\ ref_redirs len f n s1 [] = Some (rs1, s2) /\ s2 <= len
        /\ ref_args len f n s2 (toks0 ++ [(q, e)]) (rs0 ++ rs1) = Some (toks, rs, fin)).
Proof using.
  intros Hi H. cbn [ref_args] in H.
  destruct (ref_peek len f i [rb_bar; rb_rpar; rb_amp; rb_semi]) as [ stop s ] eqn:Epk.
  destruct stop.
  { left. injection H as H1 H2 H3. subst. exact (conj eq_refl (conj eq_refl eq_refl)). }
  right.
  assert (Hs : s <= len)
    by (rewrite (ref_peek_miss_inv _ _ _ _ _ Epk); exact (ref_skip_le len f i Hi)).
  destruct (ref_gettoken len f s) as [[[ tok q ] e ] s1 ] eqn:Eg.
  destruct (bool_decide (tok = 0%Z)) eqn:E0.
  { left. apply bool_decide_eq_true_1 in E0. subst tok.
    injection H as H1 H2 H3. subst. exists s, q, e.
    exact (conj eq_refl (conj Hs (conj Eg (conj eq_refl eq_refl)))). }
  right.
  destruct (negb (bool_decide (tok = rt_word))) eqn:Ew; [ discriminate H | ].
  apply negb_false_iff, bool_decide_eq_true_1 in Ew. subst tok.
  cbv zeta in H.
  destruct (bool_decide (10 <= length (toks0 ++ [(q, e)]))) eqn:E10; [ discriminate H | ].
  apply bool_decide_eq_false_1 in E10. rewrite ushp_len_app1 in E10.
  rewrite ref_redirs_acc in H.
  destruct (ref_redirs len f n s1 []) as [[ rs1 s2 ] | ] eqn:Er; [ | discriminate H ].
  assert (Hs1 : s1 <= len) by exact (ref_gettoken_fin_le len f s _ _ _ _ Hs Eg).
  exists s, q, e, s1, s2, rs1.
  refine (conj eq_refl (conj Hs (conj Eg (conj Hs1 (conj _ (conj Er (conj _ H))))))).
  - lia.
  - exact (ref_redirs_fin_le len f n s1 [] rs1 s2 Hs1 Er).
Qed.

(* ---- the wrap ---------------------------------------------------------- *)

Lemma ref_wrap_snoc (c : ushp_cmd) (rs : list rredir) (r : rredir) :
  ref_wrap c (rs ++ [r])
  = UshpRedir (ref_wrap c rs) (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r).
Proof using. unfold ref_wrap. rewrite fold_left_app. reflexivity. Qed.

Lemma ref_wrap_app (c : ushp_cmd) (rs rs' : list rredir) :
  ref_wrap c (rs ++ rs') = ref_wrap (ref_wrap c rs) rs'.
Proof using. unfold ref_wrap. apply fold_left_app. Qed.

(* an EXEC node came from no redirect at all *)
Lemma ref_wrap_exec_inv (toks toks' : list (nat * nat)) (rs : list rredir) :
  ref_wrap (UshpExec toks) rs = UshpExec toks' -> rs = [] /\ toks = toks'.
Proof using.
  induction rs as [| r rs _ ] using rev_ind; intro H.
  - injection H as <-. auto.
  - rewrite ref_wrap_snoc in H. discriminate H.
Qed.

(* a REDIR over an EXEC came from exactly one redirect *)
Lemma ref_wrap_redir_exec_inv (toks toks' : list (nat * nat)) (rs : list rredir)
    (q e : nat) (mode fd : Z) :
  ref_wrap (UshpExec toks) rs = UshpRedir (UshpExec toks') q e mode fd ->
  toks = toks' /\ rs = [{| rr_q := q; rr_eq := e; rr_mode := mode; rr_fd := fd |}].
Proof using.
  induction rs as [| r rs _ ] using rev_ind; intro H.
  - discriminate H.
  - rewrite ref_wrap_snoc in H. injection H as H1 H2 H3 H4 H5.
    destruct (ref_wrap_exec_inv toks toks' rs H1) as [ -> -> ].
    split; [ reflexivity | ]. destruct r. cbn in H2, H3, H4, H5. subst. reflexivity.
Qed.

(* one malloc per node: the wrap adds one per redirect *)
Lemma ushp_nodes_wrap (c : ushp_cmd) (rs : list rredir) :
  ushp_nodes (ref_wrap c rs) = ushp_nodes c + length rs.
Proof using.
  revert c. induction rs as [| r rs IH ]; intro c; cbn [ref_wrap fold_left length].
  - lia.
  - unfold ref_wrap in IH. rewrite IH. cbn [ushp_nodes]. lia.
Qed.

(* ---- the top constructor of a wrapped command (A2e) --------------------- *)

(* whether the answer is topped by a REDIR node: the redirect turn's eight
   stack words are needed exactly when it is, so the parseexec budget is
   guarded by this and not by the redirect list, which the caller does not
   see until the answer arrives *)
Definition ref_has_redir (t : ushp_cmd) : bool :=
  match t with
  | UshpRedir _ _ _ _ _ => true
  | _ => false
  end.

(* a wrap either adds nothing or leaves a REDIR on top *)
Lemma ref_wrap_redir_or (c : ushp_cmd) (rs : list rredir) :
  ref_wrap c rs = c
  \/ exists (c' : ushp_cmd) (q e : nat) (mode fd : Z), ref_wrap c rs = UshpRedir c' q e mode fd.
Proof using.
  revert c. induction rs as [| r rs IH ]; intro c.
  - left. reflexivity.
  - right.
    change (ref_wrap c (r :: rs))
      with (ref_wrap (UshpRedir c (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)) rs).
    destruct (IH (UshpRedir c (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)))
      as [ E | (c' & q & e & mode & fd & E) ].
    + exists c, (rr_q r), (rr_eq r), (rr_mode r), (rr_fd r). exact E.
    + exists c', q, e, mode, fd. exact E.
Qed.

Lemma ref_has_redir_wrap (c : ushp_cmd) (rs : list rredir) :
  rs <> [] -> ref_has_redir (ref_wrap c rs) = true.
Proof using.
  intro Hne. destruct rs as [| r rs ]; [ exact (False_ind _ (Hne eq_refl)) | ].
  change (ref_wrap c (r :: rs))
    with (ref_wrap (UshpRedir c (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)) rs).
  destruct (ref_wrap_redir_or (UshpRedir c (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)) rs)
    as [ E | (c' & q & e & mode & fd & E) ]; rewrite E; reflexivity.
Qed.

(* the two halves of the redirect list parseexec consumes, each non-empty
   only if the whole is *)
Lemma app_ne_l {A : Type} (l1 l2 : list A) : l1 <> [] -> l1 ++ l2 <> [].
Proof using. intros H E. apply H. destruct l1; [ reflexivity | discriminate E ]. Qed.

Lemma app_ne_r {A : Type} (l1 l2 : list A) : l2 <> [] -> l1 ++ l2 <> [].
Proof using. intros H E. apply H. destruct l1; [ exact E | discriminate E ]. Qed.

(* ---- the redirect line ------------------------------------------------- *)

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


(* ===================================================================== *)
(* §6 THE TOP OF THE PARSER: parsepipe, parseline, parsecmd, nulterminate  *)
(* (design/user-once.md SS2, worklist A2d).  What the general walk        *)
(* UkShParser reads off the reference, and what the redirect tier's       *)
(* corollaries (UkShRedirCm / UkShRedirPc, below RefParseBridge) need:    *)
(* the end-of-line tail facts moved down from RefParseBridge SS0-SS3, the  *)
(* two peeks parseline makes under the scope, and the BOUNDS of the tree   *)
(* the reference answers, which nulterminate's byte stores index by.       *)
(* ===================================================================== *)

(* ---- the & loop at the end of the line (from RefParseBridge SS0) -------- *)

Lemma ref_backs_len (len : nat) (f : nat -> bv 8) (n : nat) (t : ushp_cmd) :
  0 < n -> ref_backs len f n len t = Some (t, len).
Proof using.
  intro Hn. destruct n as [| n ]; [ lia | ]. cbn [ref_backs].
  rewrite (ref_peek_end _ _ _ _ (ref_skip_at_len len f) ref_symtoks_amp). reflexivity.
Qed.

(* every token is at least one byte, so a token list fits before its stop
   (from RefParseBridge SS2) *)
Lemma ushs_toks_len_le (len : nat) (f : nat -> bv 8) (stop off : nat) (toks : list (nat * nat)) :
  ushs_toks len f stop off toks -> off + length toks <= stop.
Proof using.
  induction 1 as [ off Hnil | off toks k n Hn Htoks IH ]; cbn [length]; lia.
Qed.

(* the three outer functions on a command that ends at the end of the line:
   no '|', no '&', no ';' is found there (from RefParseBridge SS2) *)
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

(* the redirect line, parsed to the top (from RefParseBridge SS3) *)
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

(* ---- the two symbol bytes parseline peeks for are OUT OF THE SCOPE ------ *)

Lemma ushp_is_sym_amp : ushp_is_sym rb_amp = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma ushp_is_sym_semi : ushp_is_sym rb_semi = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma rb_amp_ne_bar : rb_amp <> rb_bar.
Proof using. vm_compute. discriminate. Qed.
Lemma rb_amp_ne_gt : rb_amp <> rb_gt.
Proof using. vm_compute. discriminate. Qed.
Lemma rb_semi_ne_bar : rb_semi <> rb_bar.
Proof using. vm_compute. discriminate. Qed.
Lemma rb_semi_ne_gt : rb_semi <> rb_gt.
Proof using. vm_compute. discriminate. Qed.

(* a peek table of symbol bytes none of which the scope admits *)
Definition ref_out_scope (toks : list (bv 8)) : Prop :=
  Forall (fun b => ushp_is_sym b = true /\ b <> rb_bar /\ b <> rb_gt) toks.

Lemma ref_out_scope_amp : ref_out_scope [rb_amp].
Proof using.
  apply Forall_singleton. exact (conj ushp_is_sym_amp (conj rb_amp_ne_bar rb_amp_ne_gt)).
Qed.
Lemma ref_out_scope_semi : ref_out_scope [rb_semi].
Proof using.
  apply Forall_singleton. exact (conj ushp_is_sym_semi (conj rb_semi_ne_bar rb_semi_ne_gt)).
Qed.
Lemma ref_out_scope_nil : ref_out_scope [].
Proof using. constructor. Qed.

(* ...so under the scope such a peek MISSES, and the cursor is the skip *)
Lemma ref_peek_scope_miss (len : nat) (f : nat -> bv 8) (i : nat) (toks : list (bv 8)) :
  ref_sym_scope len f -> ref_out_scope toks ->
  ref_peek len f i toks = (false, ref_skip len f i).
Proof using.
  intros Hsc Hout. apply ref_peek_miss. intro Hin.
  set (s := ref_skip len f i) in *.
  destruct (elem_of_list_lookup_1 _ _ Hin) as [ k Hk ].
  destruct (Forall_lookup_1 _ _ _ _ Hout Hk) as (Hsym & Hnb & Hng).
  destruct (lt_dec s len) as [ Hlt | Hge ].
  - rewrite (ref_at_lt len f s Hlt) in Hsym, Hnb, Hng.
    destruct (Hsc s Hlt Hsym) as [ E | (E & _) ]; [ exact (Hnb E) | exact (Hng E) ].
  - rewrite (ref_at_ge len f s ltac:(lia)) in Hsym.
    rewrite ushp_is_sym_nul in Hsym. discriminate Hsym.
Qed.

(* the backgrounding loop never turns under the scope *)
Lemma ref_backs_scope (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) :
  ref_sym_scope len f -> 0 < n ->
  ref_backs len f n i t = Some (t, ref_skip len f i).
Proof using.
  intros Hsc Hn. destruct n as [| n ]; [ lia | ]. cbn [ref_backs].
  rewrite (ref_peek_scope_miss len f i [rb_amp] Hsc ref_out_scope_amp). reflexivity.
Qed.

(* ---- THE BOUNDS: every index the reference records is inside the line -- *)

(* a token's two indices, a redirect's two *)
Definition ref_tok_le (len : nat) (tk : nat * nat) : Prop :=
  fst tk <= len /\ snd tk <= len.
Definition ref_rr_le (len : nat) (r : rredir) : Prop :=
  rr_q r <= len /\ rr_eq r <= len.

(* ...and over the whole tree, with MAXARGS at every exec node: exactly
   what nulterminate's stores need before they may index the line (a
   redirect's file-name START is not stored, so it is not bounded here) *)
Fixpoint ushp_bounded (len : nat) (t : ushp_cmd) : Prop :=
  match t with
  | UshpExec toks => length toks < 10 /\ Forall (ref_tok_le len) toks
  | UshpRedir c _ e _ _ => ushp_bounded len c /\ e <= len
  | UshpPipe l r => ushp_bounded len l /\ ushp_bounded len r
  | UshpList l r => ushp_bounded len l /\ ushp_bounded len r
  | UshpBack c => ushp_bounded len c
  end.

(* gettoken's two out-indices and its cursor are inside the line *)
Lemma ref_gettoken_bounds (len : nat) (f : nat -> bv 8) (i : nat) (ret : Z) (q e fin : nat) :
  i <= len -> ref_gettoken len f i = (ret, q, e, fin) -> q <= len /\ e <= len /\ fin <= len.
Proof using.
  intros Hi H. pose proof (ref_gettoken_fin_le len f i ret q e fin Hi H) as Hfin.
  unfold ref_gettoken in H.
  set (s := ref_skip len f i) in H.
  assert (Hs : s <= len) by exact (ref_skip_le len f i Hi).
  destruct (bool_decide (ref_at len f s = ubyte0)) eqn:E0.
  { injection H as _ <- <- _. exact (conj Hs (conj Hs Hfin)). }
  apply bool_decide_eq_false_1 in E0.
  assert (Hlt : s < len).
  { destruct (lt_dec s len) as [ | Hge ]; [ assumption | ].
    exfalso. apply E0. exact (ref_at_ge len f s ltac:(lia)). }
  destruct (bool_decide (ref_at len f s = rb_gt)) eqn:E1.
  - destruct (bool_decide (ref_at len f (S s) = rb_gt)) eqn:E2.
    + injection H as _ <- <- _.
      apply bool_decide_eq_true_1 in E2.
      assert (HSs : S s < len).
      { destruct (lt_dec (S s) len) as [ | Hge ]; [ assumption | ].
        exfalso. rewrite (ref_at_ge len f (S s) ltac:(lia)) in E2.
        exact (rb_gt_ne_nul (eq_sym E2)). }
      split; [ lia | split; [ lia | exact Hfin ] ].
    + injection H as _ <- <- _. split; [ lia | split; [ lia | exact Hfin ] ].
  - destruct (ushp_is_sym (ref_at len f s)).
    + injection H as _ <- <- _. split; [ lia | split; [ lia | exact Hfin ] ].
    + injection H as _ <- <- _. unfold ref_tokend.
      pose proof (ushp_toklen_le (len - s) s f).
      split; [ lia | split; [ lia | exact Hfin ] ].
Qed.

Lemma ref_redirs_bounds (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (acc rs : list rredir) (fin : nat),
    i <= len -> Forall (ref_rr_le len) acc ->
    ref_redirs len f n i acc = Some (rs, fin) ->
    Forall (ref_rr_le len) rs /\ fin <= len.
Proof using.
  induction n as [| n IH ]; intros i acc rs fin Hi Hacc H; [ discriminate H | ].
  cbn [ref_redirs] in H.
  destruct (ref_peek len f i [rb_lt; rb_gt]) as [ hit s ] eqn:Epk.
  destruct hit.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es & _ & _).
    assert (Hs : s <= len) by (rewrite Es; exact (ref_skip_le len f i Hi)).
    destruct (ref_gettoken len f s) as [[[ tok q0 ] e0 ] s1 ] eqn:E1.
    destruct (ref_gettoken len f s1) as [[[ t2 q ] e ] s2 ] eqn:E2.
    destruct (bool_decide (t2 = rt_word)); [ | discriminate H ].
    assert (Hs1 : s1 <= len) by exact (ref_gettoken_fin_le len f s _ _ _ _ Hs E1).
    destruct (ref_gettoken_bounds len f s1 _ _ _ _ Hs1 E2) as (Hq & He & Hs2).
    destruct (rredir_of tok q e) as [ r | ] eqn:Er; [ | discriminate H ].
    apply (IH s2 (acc ++ [r]) rs fin Hs2); [ | exact H ].
    apply Forall_app_2; [ exact Hacc | ].
    apply Forall_singleton.
    unfold rredir_of in Er.
    destruct (bool_decide (tok = bv_unsigned rb_lt));
      [ injection Er as <-; exact (conj Hq He) | ].
    destruct (bool_decide (tok = bv_unsigned rb_gt));
      [ injection Er as <-; exact (conj Hq He) | ].
    destruct (bool_decide (tok = rt_app));
      [ injection Er as <-; exact (conj Hq He) | discriminate Er ].
  - injection H as <- <-. split; [ exact Hacc | ].
    rewrite (ref_peek_miss_inv _ _ _ _ _ Epk). exact (ref_skip_le len f i Hi).
Qed.

Lemma ref_args_bounds (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (toks0 toks : list (nat * nat)) (rs0 rs : list rredir) (fin : nat),
    i <= len -> length toks0 < 10 ->
    Forall (ref_tok_le len) toks0 -> Forall (ref_rr_le len) rs0 ->
    ref_args len f n i toks0 rs0 = Some (toks, rs, fin) ->
    length toks < 10 /\ Forall (ref_tok_le len) toks /\ Forall (ref_rr_le len) rs /\ fin <= len.
Proof using.
  induction n as [| n IH ]; intros i toks0 toks rs0 rs fin Hi Hlen Htoks Hrs H;
    [ discriminate H | ].
  destruct (ref_args_inv len f n i toks0 toks rs0 rs fin Hi H)
    as [ (Epk & -> & ->)
       | [ (s & q & e & Epk & Hs & Eg & -> & ->)
         | (s & q & e & s1 & s2 & rs1 & Epk & Hs & Eg & Hs1 & Hl9 & Er & Hs2 & Hrec) ] ].
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (-> & _ & _).
    split_and!; [ exact Hlen | exact Htoks | exact Hrs | exact (ref_skip_le len f i Hi) ].
  - split_and!; [ exact Hlen | exact Htoks | exact Hrs
                | exact (ref_gettoken_fin_le len f s _ _ _ _ Hs Eg) ].
  - destruct (ref_gettoken_bounds len f s _ _ _ _ Hs Eg) as (Hq & He & _).
    destruct (ref_redirs_bounds len f n s1 [] rs1 s2 Hs1 (List.Forall_nil _) Er) as (Hrs1 & _).
    apply (IH s2 (toks0 ++ [(q, e)]) toks (rs0 ++ rs1) rs fin Hs2).
    + rewrite length_app. cbn [length]. lia.
    + apply Forall_app_2; [ exact Htoks | apply Forall_singleton; exact (conj Hq He) ].
    + apply Forall_app_2; [ exact Hrs | exact Hrs1 ].
    + exact Hrec.
Qed.

Lemma ref_wrap_cons (c : ushp_cmd) (r : rredir) (rs : list rredir) :
  ref_wrap c (r :: rs) = ref_wrap (UshpRedir c (rr_q r) (rr_eq r) (rr_mode r) (rr_fd r)) rs.
Proof using. reflexivity. Qed.

Lemma ushp_bounded_wrap (len : nat) (c : ushp_cmd) (rs : list rredir) :
  ushp_bounded len c -> Forall (ref_rr_le len) rs -> ushp_bounded len (ref_wrap c rs).
Proof using.
  revert c. induction rs as [| r rs IH ]; intros c Hc Hrs; [ exact Hc | ].
  rewrite ref_wrap_cons.
  apply Forall_cons_1 in Hrs as [ Hr Hrs ].
  apply IH; [ | exact Hrs ]. destruct Hr as [ _ He ].
  exact (conj Hc He).
Qed.

Lemma ref_parseexec_bounded (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (fin : nat) :
  i <= len -> ref_parseexec len f n i = Some (t, fin) -> ushp_bounded len t /\ fin <= len.
Proof using.
  intros Hi H. unfold ref_parseexec in H.
  destruct (ref_peek len f i [rb_lpar]) as [ blk s ] eqn:Epk. destruct blk; [ discriminate H | ].
  assert (Hs : s <= len)
    by (rewrite (ref_peek_miss_inv _ _ _ _ _ Epk); exact (ref_skip_le len f i Hi)).
  destruct (ref_redirs len f n s []) as [[ rs1 s1 ] | ] eqn:Er; [ | discriminate H ].
  destruct (ref_redirs_bounds len f n s [] rs1 s1 Hs (List.Forall_nil _) Er) as (Hrs1 & Hs1).
  destruct (ref_args len f n s1 [] rs1) as [[[ toks rs ] s2 ] | ] eqn:Ea; [ | discriminate H ].
  injection H as <- <-.
  destruct (ref_args_bounds len f n s1 [] toks rs1 rs s2 Hs1 ltac:(cbn [length]; lia)
              (List.Forall_nil _) Hrs1 Ea) as (Hl & Htoks & Hrs & Hs2).
  split; [ | exact Hs2 ].
  apply ushp_bounded_wrap; [ exact (conj Hl Htoks) | exact Hrs ].
Qed.

Lemma ref_parsepipe_bounded (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (t : ushp_cmd) (fin : nat),
    i <= len -> ref_parsepipe len f n i = Some (t, fin) -> ushp_bounded len t /\ fin <= len.
Proof using.
  induction n as [| n IH ]; intros i t fin Hi H; [ discriminate H | ].
  cbn [ref_parsepipe] in H.
  destruct (ref_parseexec len f n i) as [[ t1 s ] | ] eqn:Ex; [ | discriminate H ].
  destruct (ref_parseexec_bounded len f n i t1 s Hi Ex) as (Ht1 & Hs).
  destruct (ref_peek len f s [rb_bar]) as [ bar s1 ] eqn:Epk.
  destruct bar.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es1 & _ & _).
    assert (Hs1 : s1 <= len) by (rewrite Es1; exact (ref_skip_le len f s Hs)).
    destruct (ref_gettoken len f s1) as [[[ tok q ] e ] s2 ] eqn:Eg.
    assert (Hs2 : s2 <= len) by exact (ref_gettoken_fin_le len f s1 _ _ _ _ Hs1 Eg).
    destruct (ref_parsepipe len f n s2) as [[ r s3 ] | ] eqn:Er; [ | discriminate H ].
    injection H as <- <-.
    destruct (IH s2 r s3 Hs2 Er) as (Hr & Hs3).
    split; [ exact (conj Ht1 Hr) | exact Hs3 ].
  - injection H as <- <-. split; [ exact Ht1 | ].
    rewrite (ref_peek_miss_inv _ _ _ _ _ Epk). exact (ref_skip_le len f s Hs).
Qed.

Lemma ref_backs_bounded (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (t t' : ushp_cmd) (fin : nat),
    i <= len -> ushp_bounded len t -> ref_backs len f n i t = Some (t', fin) ->
    ushp_bounded len t' /\ fin <= len.
Proof using.
  induction n as [| n IH ]; intros i t t' fin Hi Ht H; [ discriminate H | ].
  cbn [ref_backs] in H.
  destruct (ref_peek len f i [rb_amp]) as [ amp s ] eqn:Epk.
  destruct amp.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es & _ & _).
    assert (Hs : s <= len) by (rewrite Es; exact (ref_skip_le len f i Hi)).
    destruct (ref_gettoken len f s) as [[[ tok q ] e ] s1 ] eqn:Eg.
    exact (IH s1 (UshpBack t) t' fin (ref_gettoken_fin_le len f s _ _ _ _ Hs Eg) Ht H).
  - injection H as <- <-. split; [ exact Ht | ].
    rewrite (ref_peek_miss_inv _ _ _ _ _ Epk). exact (ref_skip_le len f i Hi).
Qed.

Lemma ref_parseline_bounded (len : nat) (f : nat -> bv 8) (n : nat) :
  forall (i : nat) (t : ushp_cmd) (fin : nat),
    i <= len -> ref_parseline len f n i = Some (t, fin) -> ushp_bounded len t /\ fin <= len.
Proof using.
  induction n as [| n IH ]; intros i t fin Hi H; [ discriminate H | ].
  cbn [ref_parseline] in H.
  destruct (ref_parsepipe len f n i) as [[ t1 s ] | ] eqn:Ep; [ | discriminate H ].
  destruct (ref_parsepipe_bounded len f n i t1 s Hi Ep) as (Ht1 & Hs).
  destruct (ref_backs len f n s t1) as [[ t2 s1 ] | ] eqn:Eb; [ | discriminate H ].
  destruct (ref_backs_bounded len f n s t1 t2 s1 Hs Ht1 Eb) as (Ht2 & Hs1).
  destruct (ref_peek len f s1 [rb_semi]) as [ semi s2 ] eqn:Epk.
  destruct semi.
  - destruct (ref_peek_hit_inv _ _ _ _ _ Epk) as (Es2 & _ & _).
    assert (Hs2 : s2 <= len) by (rewrite Es2; exact (ref_skip_le len f s1 Hs1)).
    destruct (ref_gettoken len f s2) as [[[ tok q ] e ] s3 ] eqn:Eg.
    assert (Hs3 : s3 <= len) by exact (ref_gettoken_fin_le len f s2 _ _ _ _ Hs2 Eg).
    destruct (ref_parseline len f n s3) as [[ r s4 ] | ] eqn:Er; [ | discriminate H ].
    injection H as <- <-.
    destruct (IH s3 r s4 Hs3 Er) as (Hr & Hs4).
    split; [ exact (conj Ht2 Hr) | exact Hs4 ].
  - injection H as <- <-. split; [ exact Ht2 | ].
    rewrite (ref_peek_miss_inv _ _ _ _ _ Epk). exact (ref_skip_le len f s1 Hs1).
Qed.

Theorem ref_parsecmd_bounded (len : nat) (f : nat -> bv 8) (t : ushp_cmd) :
  ref_parsecmd len f = Some t -> ushp_bounded len t.
Proof using.
  intro H. unfold ref_parsecmd in H.
  destruct (ref_parseline len f (ref_fuel len) 0) as [[ t1 s ] | ] eqn:Ep; [ | discriminate H ].
  destruct (ref_parseline_bounded len f (ref_fuel len) 0 t1 s ltac:(lia) Ep) as (Ht1 & _).
  destruct (ref_peek len f s []) as [ b s1 ].
  destruct (bool_decide (s1 = len)); [ | discriminate H ].
  injection H as <-. exact Ht1.
Qed.

(* ---- THE WALKED CONSTRUCTORS: nulterminate's three rows ---------------- *)

(* EXEC, REDIR at any mode, PIPE: the rows nulterminate's jump table is
   walked at.  Weaker than [ushp_cat] -- the REDIR row does not read the
   mode word -- so the landed redirect row at an arbitrary mode is an
   instance. *)
Fixpoint ushp_walked (t : ushp_cmd) : Prop :=
  match t with
  | UshpExec _ => True
  | UshpRedir c _ _ _ _ => ushp_walked c
  | UshpPipe l r => ushp_walked l /\ ushp_walked r
  | UshpList _ _ => False
  | UshpBack _ => False
  end.

Lemma ushp_cat_walked (t : ushp_cmd) : ushp_cat t -> ushp_walked t.
Proof using. induction t; cbn [ushp_cat ushp_walked]; tauto. Qed.

(* the cut indices of a wrapped exec node, and the node count of the
   three shapes, for the corollaries *)
Lemma ref_nulcut_wrap (c : ushp_cmd) (rs : list rredir) :
  ref_nulcut (ref_wrap c rs) = ref_nulcut c ++ map rr_eq rs.
Proof using.
  revert c. induction rs as [| r rs IH ]; intro c; cbn [map].
  - cbn [ref_wrap fold_left]. rewrite app_nil_r. reflexivity.
  - rewrite ref_wrap_cons, IH. cbn [ref_nulcut]. rewrite <- app_assoc. reflexivity.
Qed.

(* ---- parseexec's answer, and one step of the two fuelled recursions ---- *)
(* (moved down from UkShParser at A2e) *)

(* parseexec's answer is always a wrapped exec node *)
Lemma ref_parseexec_wrap_inv (len : nat) (f : nat -> bv 8) (n i : nat) (t : ushp_cmd) (fin : nat) :
  ref_parseexec len f n i = Some (t, fin) ->
  exists (toks : list (nat * nat)) (rs : list rredir), t = ref_wrap (UshpExec toks) rs.
Proof using.
  intro H. unfold ref_parseexec in H.
  destruct (ref_peek len f i [rb_lpar]) as [ blk s ]. destruct blk; [ discriminate H | ].
  destruct (ref_redirs len f n s []) as [[ rs1 s1 ] | ]; [ | discriminate H ].
  destruct (ref_args len f n s1 [] rs1) as [[[ toks rs ] s2 ] | ]; [ | discriminate H ].
  injection H as <- _. exists toks, rs. reflexivity.
Qed.

(* one step of the two fuelled recursions, as a rewrite: [cbn] on a
   constructor fuel unfolds the INNER call too *)
Lemma ref_parsepipe_S (len : nat) (f : nat -> bv 8) (n i : nat) :
  ref_parsepipe len f (S n) i =
  match ref_parseexec len f n i with
  | Some (t, s) =>
      let '(bar, s1) := ref_peek len f s [rb_bar] in
      if bar then
        let '(_, _, _, s2) := ref_gettoken len f s1 in
        match ref_parsepipe len f n s2 with
        | Some (r, s3) => Some (UshpPipe t r, s3)
        | None => None
        end
      else Some (t, s1)
  | None => None
  end.
Proof using. reflexivity. Qed.

Lemma ref_parseline_S (len : nat) (f : nat -> bv 8) (n i : nat) :
  ref_parseline len f (S n) i =
  match ref_parsepipe len f n i with
  | Some (t, s) =>
      match ref_backs len f n s t with
      | Some (t1, s1) =>
          let '(semi, s2) := ref_peek len f s1 [rb_semi] in
          if semi then
            let '(_, _, _, s3) := ref_gettoken len f s2 in
            match ref_parseline len f n s3 with
            | Some (r, s4) => Some (UshpList t1 r, s4)
            | None => None
            end
          else Some (t1, s2)
      | None => None
      end
  | None => None
  end.
Proof using. reflexivity. Qed.
