(* ===================================================================== *)
(*  PipesCut.v -- THE N-STAGE PIPELINE LINE, READ BY THE PARSER (cut C8). *)
(*                                                                       *)
(*  [echo ws | cat | ... | cat] with [n >= 1] cats, as the loop's typed   *)
(*  line fact [UkSh.ush_line_at (FileDisc.LPipe (PrEcho ws) n)] says:    *)
(*    - it is the pipeline lexer's line ([UkShPipesLex.ushq_lines_is] at  *)
(*      [n] words [cat]), so [ushq_lines_bars] lexes it stage by stage;   *)
(*    - the parser's cut ([UkShPipesCmd.ushq_nulfolds] over every stage's *)
(*      tokens) holds echo's argv at the left stage and [cat]'s at every  *)
(*      right one -- the two readings [UShPipesNode]'s stages take.       *)
(*  Pure.                                                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions ssreflect.
Require Import LineWords.
Require Import EchoDisc.
Require FileDisc.
Require Import UkShParse.
Require UkShParseCmd.
Require UkShMain.
Require Import UkShWords.
Require Import UkShPipeLex.
Require Import UkShPipesLex.
Require Import UkShPipesCmd.
Require UkShEcho.
Require UkShCat.
Require UkSh.
Local Open Scope nat_scope.

(* ---- the bytes of a list at an offset ---- *)
Definition bat (g : nat -> bv 8) (c : nat) (bs : list (bv 8)) : Prop :=
  forall j : nat, j < length bs -> g (c + j) = bs !!! j.

Lemma bat_app (g : nat -> bv 8) (c : nat) (a b : list (bv 8)) :
  bat g c (a ++ b) -> bat g c a /\ bat g (c + length a) b.
Proof using.
  intros H. split.
  - intros j Hj. rewrite (H j); [| rewrite length_app; lia].
    exact (wl_lta_app_l a b j Hj).
  - intros j Hj.
    replace (c + length a + j) with (c + (length a + j)) by lia.
    rewrite (H (length a + j)); [| rewrite length_app; lia].
    exact (wl_lta_app_r a b j).
Qed.

(* ---- the suffix ---- *)
Lemma suf_barcat_split :
  FileDisc.suf_barcat = [wl_sp; ushq_bar; wl_sp] ++ ushq_cat.
Proof using. reflexivity. Qed.

Lemma suf_barcats_length (n : nat) : length (FileDisc.suf_barcats n) = 6 * n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite FileDisc.suf_barcats_S length_app IH.
  rewrite (_ : length FileDisc.suf_barcat = 6); [lia | reflexivity].
Qed.

(* at either producer (cut C9f2): [p]'s words are [prod_words p], its
   body [wl_body (prod_words p)] *)
Lemma line_bytes_pipe_split_p (p : FileDisc.producer) (n : nat) :
  FileDisc.line_bytes (FileDisc.LPipe p (S n))
  = wl_body (FileDisc.prod_words p) ++ [wl_sp; ushq_bar; wl_sp]
    ++ (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]).
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite FileDisc.suf_barcats_S suf_barcat_split -!app_assoc. reflexivity.
Qed.

Lemma line_bytes_pipe_length_p (p : FileDisc.producer) (n : nat) :
  length (FileDisc.line_bytes (FileDisc.LPipe p n))
  = length (wl_body (FileDisc.prod_words p)) + 6 * n + 1.
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite !length_app suf_barcats_length. cbn [length]. unfold FileDisc.prod_body. lia.
Qed.

Lemma line_bytes_pipe_split (ws : list (list (bv 8))) (n : nat) :
  FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (S n))
  = wl_body ws ++ [wl_sp; ushq_bar; wl_sp] ++ (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]).
Proof using. exact (line_bytes_pipe_split_p (FileDisc.PrEcho ws) n). Qed.

Lemma line_bytes_pipe_length (ws : list (list (bv 8))) (n : nat) :
  length (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) n))
  = length (wl_body ws) + 6 * n + 1.
Proof using. exact (line_bytes_pipe_length_p (FileDisc.PrEcho ws) n). Qed.

(* the lexer's word condition at an admissible producer *)
Lemma prod_ws_ok (p : FileDisc.producer) :
  FileDisc.prod_ok p -> ushq_ws_ok (FileDisc.prod_words p).
Proof using.
  intros Hp. split_and!.
  - exact (FileDisc.prod_wf p Hp).
  - pose proof (FileDisc.prod_words_ge2 p Hp). lia.
  - destruct p as [ws | f]; cbn [FileDisc.prod_ok FileDisc.prod_words length] in *;
      [exact (line_ok_lt10 ws Hp) | lia].
Qed.

(* ---- the tail after the first bar: one [cat] per stage ---- *)
Lemma tail_cats (g : nat -> bv 8) (len : nat) :
  forall n c : nat,
    bat g c (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]) ->
    len = c + (6 * n + 4) ->
    ushq_tail_is g c len (replicate (S n) ushq_cat).
Proof using.
  induction n as [| n IH]; intros c Hb Hlen.
  - cbn [replicate]. apply ushq_tail_is_one.
    rewrite (_ : FileDisc.suf_barcats 0 = []) in Hb; [| reflexivity].
    apply bat_app in Hb as [Hc Hr].
    split; [exact ushq_cat_word |]. split; [exact Hc |].
    rewrite ushq_cat_len in Hr |- *. split; [lia |].
    pose proof (Hr 0 ltac:(cbn; lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
  - rewrite FileDisc.suf_barcats_S suf_barcat_split -!app_assoc in Hb.
    apply bat_app in Hb as [Hc Hr]. apply bat_app in Hr as [Hs Hr].
    rewrite (_ : replicate (S (S n)) ushq_cat
                 = ushq_cat :: ushq_cat :: replicate n ushq_cat); [| reflexivity].
    apply ushq_tail_is_two.
    split; [exact ushq_cat_word |]. split; [exact Hc |].
    rewrite ushq_cat_len in Hs, Hr |- *.
    split; [pose proof (Hs 0 ltac:(cbn; lia)) as H0; rewrite Nat.add_0_r in H0; exact H0 |].
    split; [exact (Hs 1 ltac:(cbn; lia)) |].
    split; [exact (Hs 2 ltac:(cbn; lia)) |].
    apply (IH (c + 3 + 3)); [exact Hr | lia].
Qed.

(* ---- THE LINE IS THE LEXER'S ---- *)
Lemma lines_of_pipe_p (p : FileDisc.producer) (n : nat) (f : nat -> bv 8) (len : nat) :
  FileDisc.prod_ok p -> 1 <= n ->
  bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p n)) ->
  len = length (FileDisc.line_bytes (FileDisc.LPipe p n)) ->
  ushq_lines_is (FileDisc.prod_words p) (replicate n ushq_cat) f 0 len.
Proof using.
  intros Hok Hn Hb Hlen.
  rewrite line_bytes_pipe_length_p in Hlen.
  destruct n as [| n]; [lia |].
  rewrite line_bytes_pipe_split_p in Hb.
  apply bat_app in Hb as [Hbody Hr]. apply bat_app in Hr as [Hs Hr].
  set (ws := FileDisc.prod_words p) in *.
  unfold ushq_lines_is. cbv zeta.
  split; [exact (prod_ws_ok p Hok) |].
  split; [exact Hbody |].
  split; [pose proof (Hs 0 ltac:(cbn; lia)) as H0; rewrite Nat.add_0_r in H0; exact H0 |].
  split; [exact (Hs 1 ltac:(cbn; lia)) |].
  split; [exact (Hs 2 ltac:(cbn; lia)) |].
  apply (tail_cats (fun j : nat => f (0 + j)) len n (length (wl_body ws) + 3)).
  - exact Hr.
  - lia.
Qed.

Lemma lines_of_pipe (ws : list (list (bv 8))) (n : nat) (f : nat -> bv 8) (len : nat) :
  line_ok ws -> 1 <= n ->
  bat f 0 (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) n)) ->
  len = length (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) n)) ->
  ushq_lines_is ws (replicate n ushq_cat) f 0 len.
Proof using. exact (lines_of_pipe_p (FileDisc.PrEcho ws) n f len). Qed.

(* ---- the [cat] words' bytes, stage by stage ---- *)
Lemma bat_cat_at (g : nat -> bv 8) :
  forall (i n c : nat),
    i <= n ->
    bat g c (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]) ->
    bat g (c + 6 * i) ushq_cat.
Proof using.
  induction i as [| i IH]; intros n c Hi Hb.
  - rewrite Nat.add_0_r. exact (proj1 (bat_app _ _ _ _ Hb)).
  - destruct n as [| n]; [lia |].
    rewrite FileDisc.suf_barcats_S suf_barcat_split -!app_assoc in Hb.
    apply bat_app in Hb as [_ Hr]. apply bat_app in Hr as [_ Hr].
    rewrite ushq_cat_len in Hr. cbn [length] in Hr.
    replace (c + 6 * S i) with (c + 3 + 3 + 6 * i) by lia.
    exact (IH n (c + 3 + 3) ltac:(lia) Hr).
Qed.

(* ---- THE LOOP'S TYPED LINE, as the round's line predicate ---- *)
Definition pipes_lp (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) : Prop :=
  exists (ws : list (list (bv 8))) (n : nat),
    wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) n)
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) n) gf k len.

Lemma pipes_lp_of_at (ws : list (list (bv 8))) (n : nat) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) n) f k len ->
  pipes_lp (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) n)) (fun j : nat => f (k + j)) 0 len.
Proof using.
  intros (Hok & Hlen & Hby). exists ws, n. split; [reflexivity |].
  split; [exact Hok |]. split; [exact Hlen |].
  intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

Lemma line_ok_body_pos (ws : list (list (bv 8))) :
  line_ok ws -> 0 < length (wl_body ws).
Proof using.
  intros Hok. pose proof (line_ok_wf _ Hok) as Hwf.
  pose proof Hok as Hok2. destruct Hok2 as (_ & _ & Hge2 & _ & _).
  destruct ws as [| w rest].
  - exfalso. cbn [length] in Hge2. clear -Hge2. lia.
  - destruct (wl_wf_cons w rest Hwf) as [Hw _].
    rewrite wl_body_cons length_app.
    pose proof (wl_word_pos w Hw). lia.
Qed.

(* below the first bar the pipeline line's bytes ARE the echo line's *)
Lemma pipe_bytes_lo_p (p : FileDisc.producer) (n j : nat) :
  j < length (wl_body (FileDisc.prod_words p)) ->
  FileDisc.line_bytes (FileDisc.LPipe p n) !!! j = wl_line (FileDisc.prod_words p) !!! j.
Proof using.
  intros Hj. rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  unfold FileDisc.prod_body.
  rewrite -app_assoc (wl_lta_app_l (wl_body (FileDisc.prod_words p)) _ j Hj).
  rewrite /wl_line (wl_lta_app_l (wl_body (FileDisc.prod_words p)) [wl_nl] j Hj). reflexivity.
Qed.

Lemma pipe_bytes_lo (ws : list (list (bv 8))) (n j : nat) :
  j < length (wl_body ws) ->
  FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) n) !!! j = wl_line ws !!! j.
Proof using. exact (pipe_bytes_lo_p (FileDisc.PrEcho ws) n j). Qed.

Lemma pipes_lp0 (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lp wsf gf k len -> bv_unsigned (gf k) = 101%Z.
Proof using.
  intros (ws & n & _ & Hok & Hlen & Hby).
  destruct Hok as (Hok & _ & _).
  pose proof (line_ok_body_pos ws Hok) as Hbody.
  assert (Hlpos : 0 < len)
    by (rewrite Hlen line_bytes_pipe_length; lia).
  pose proof (Hby 0 Hlpos) as H0. rewrite Nat.add_0_r in H0.
  rewrite H0 (pipe_bytes_lo ws n 0 Hbody).
  exact (line_ok_head_byte0 ws Hok).
Qed.

(* THE [cat f] PIPELINE'S LINE PREDICATE (cut C9f2): the loop's typed
   line [cat f | cat | ... | cat] at the one user file *)
Definition pipes_lpc (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) : Prop :=
  exists n : nat,
    wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF FileDisc.fname_f) n)
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF FileDisc.fname_f) n) gf k len.

Lemma pipes_lpc_of_at (n : nat) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF FileDisc.fname_f) n) f k len ->
  pipes_lpc (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF FileDisc.fname_f) n))
    (fun j : nat => f (k + j)) 0 len.
Proof using.
  intros (Hok & Hlen & Hby). exists n. split; [reflexivity |].
  split; [exact Hok |]. split; [exact Hlen |].
  intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

(* its first two bytes are [c] and [a], so the loop's [cd] test falls out
   at the second, as [cat f]'s does *)
Lemma pipes_lpc_bytes (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lpc wsf gf k len ->
  bv_unsigned (gf k) = 99%Z /\ bv_unsigned (gf (k + 1)) = 97%Z /\ 2 <= len.
Proof using.
  intros (n & _ & _ & Hlen & Hby).
  assert (Hb : length (wl_body (FileDisc.prod_words (FileDisc.PrCatF FileDisc.fname_f))) = 5)
    by (vm_compute; reflexivity).
  rewrite line_bytes_pipe_length_p Hb in Hlen.
  split_and!; [| | lia].
  - rewrite -(Nat.add_0_r k) (Hby 0 ltac:(lia)) (pipe_bytes_lo_p (FileDisc.PrCatF FileDisc.fname_f) n 0 ltac:(lia)).
    by vm_compute.
  - rewrite (Hby 1 ltac:(lia)) (pipe_bytes_lo_p (FileDisc.PrCatF FileDisc.fname_f) n 1 ltac:(lia)).
    by vm_compute.
Qed.

(* ===================================================================== *)
(*  THE CUT                                                              *)
(* ===================================================================== *)
Lemma rtoks_cats_lookup (n c i : nat) :
  i < n ->
  ushq_rtoks c (replicate n ushq_cat) !! i = Some [(c + 6 * i, c + 6 * i + 3)].
Proof using.
  revert c i. induction n as [| n IH]; intros c i Hi; [lia |].
  cbn [replicate ushq_rtoks]. rewrite ushq_cat_len.
  destruct i as [| i].
  - cbn. repeat f_equal; lia.
  - cbn [lookup list_lookup]. rewrite (IH (c + 3 + 3) i ltac:(lia)).
    do 3 f_equal; lia.
Qed.

Lemma rtoks_cats_length (n c : nat) :
  length (ushq_rtoks c (replicate n ushq_cat)) = n.
Proof using.
  revert c. induction n as [| n IH]; intros c; [reflexivity |].
  cbn [replicate ushq_rtoks length]. by rewrite IH.
Qed.

Lemma rtoks_cats_in (n c : nat) (tk : nat * nat) :
  tk ∈ concat (ushq_rtoks c (replicate n ushq_cat)) ->
  exists i, i < n /\ tk = (c + 6 * i, c + 6 * i + 3).
Proof using.
  revert c. induction n as [| n IH]; intros c Htk.
  - cbn in Htk. by apply elem_of_nil in Htk.
  - cbn [replicate ushq_rtoks concat] in Htk. rewrite ushq_cat_len in Htk.
    apply elem_of_app in Htk as [Htk | Htk].
    + apply elem_of_list_singleton in Htk as ->. exists 0. split; [lia |].
      f_equal; lia.
    + destruct (IH (c + 3 + 3) Htk) as (i & Hi & ->). exists (S i).
      split; [lia |]. f_equal; lia.
Qed.

Lemma rtoks_cats_concat_lookup (n c i : nat) :
  i < n ->
  concat (ushq_rtoks c (replicate n ushq_cat)) !! i = Some (c + 6 * i, c + 6 * i + 3).
Proof using.
  revert c i. induction n as [| n IH]; intros c i Hi; [lia |].
  cbn [replicate ushq_rtoks concat]. rewrite ushq_cat_len.
  destruct i as [| i].
  - cbn. repeat f_equal; lia.
  - cbn [app lookup list_lookup]. rewrite (IH (c + 3 + 3) i ltac:(lia)).
    do 2 f_equal; lia.
Qed.

(* every token of echo's words ends inside its body *)
Lemma wl_toks_end_le (ws : list (list (bv 8))) (tk : nat * nat) :
  tk ∈ wl_toks ws -> snd tk <= length (wl_body ws).
Proof using.
  intros Htk. apply elem_of_list_lookup_1 in Htk as [i Hi].
  assert (Hlt : i < length ws)
    by (rewrite -(wl_toks_length ws); exact (lookup_lt_Some _ _ _ Hi)).
  destruct (lookup_lt_is_Some_2 ws i Hlt) as [w Hw].
  rewrite /wl_toks (wl_toks_at_lookup ws 0 i w Hw) in Hi.
  injection Hi as <-. cbn [snd].
  pose proof (wl_off_le_body ws 0 i w (length w) Hw ltac:(lia)). lia.
Qed.

(* THE CUT of the line, at the parser's stages *)
Definition pcut (ws : list (list (bv 8))) (n len : nat) (f : nat -> bv 8) : nat -> bv 8 :=
  ushq_nulfolds (wl_toks ws)
    (ushq_rtoks (length (wl_body ws) + 3) (replicate n ushq_cat))
    (UkShParseCmd.ushp_ext len f).

Lemma pcut_flat (ws : list (list (bv 8))) (n len : nat) (f : nat -> bv 8) :
  pcut ws n len f
  = UkShParseCmd.ushp_nulfold
      (concat (ushq_rtoks (length (wl_body ws) + 3) (replicate n ushq_cat)))
      (UkShParseCmd.ushp_nulfold (wl_toks ws) (UkShParseCmd.ushp_ext len f)).
Proof using.
  rewrite /pcut ushq_nulfolds_flat ushq_nulfold_app. reflexivity.
Qed.

(* below the first bar the right stages' tokens are not there *)
Lemma pcut_low (ws : list (list (bv 8))) (n len : nat) (f : nat -> bv 8) (x : nat) :
  x <= length (wl_body ws) ->
  pcut ws n len f x
  = UkShParseCmd.ushp_nulfold (wl_toks ws) (UkShParseCmd.ushp_ext len f) x.
Proof using.
  intros Hx. rewrite pcut_flat.
  apply UkShMain.ushp_nulfold_miss.
  intros i tk Hi. apply elem_of_list_lookup_2 in Hi.
  destruct (rtoks_cats_in n _ tk Hi) as (i' & _ & ->). cbn [snd]. lia.
Qed.

(* ...AND ECHO'S ARGV IS THERE *)
Lemma pcut_echo_bytes_p (p : FileDisc.producer) (n : nat) (f : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe p n) f 0 len ->
  UkShEcho.echo_argv_bytes (FileDisc.prod_words p) (pcut (FileDisc.prod_words p) n len f).
Proof using.
  intros (Hok & Hlen & Hby).
  destruct Hok as (Hok & Hn & _).
  assert (Hblen : length (wl_body (FileDisc.prod_words p)) < len)
    by (rewrite Hlen line_bytes_pipe_length_p; lia).
  assert (Hlo : forall j : nat, j < length (wl_body (FileDisc.prod_words p)) -> f j = wl_line (FileDisc.prod_words p) !!! j).
  { intros j Hj. pose proof (Hby j ltac:(lia)) as Hfj.
    rewrite Nat.add_0_l in Hfj. rewrite Hfj. exact (pipe_bytes_lo_p p n j Hj). }
  split.
  - intros i j Hi Hj.
    destruct (lookup_lt_is_Some_2 (FileDisc.prod_words p) i Hi) as [w Hw].
    assert (Hwi : (FileDisc.prod_words p) !!! i = w)
      by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_alen Hwi in Hj.
    rewrite /UkShEcho.echo_off.
    pose proof (wl_off_le_body (FileDisc.prod_words p) 0 i w (length w) Hw ltac:(lia)) as Hle.
    rewrite (pcut_low (FileDisc.prod_words p) n len f (wl_off 0 (FileDisc.prod_words p) i + j) ltac:(lia)).
    rewrite (wl_cut_in (FileDisc.prod_words p) f len i w j Hw Hj ltac:(lia)).
    exact (Hlo (wl_off 0 (FileDisc.prod_words p) i + j) ltac:(lia)).
  - intros i Hi.
    destruct (lookup_lt_is_Some_2 (FileDisc.prod_words p) i Hi) as [w Hw].
    assert (Hwi : (FileDisc.prod_words p) !!! i = w)
      by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_off /UkShEcho.echo_alen Hwi.
    pose proof (wl_off_le_body (FileDisc.prod_words p) 0 i w (length w) Hw ltac:(lia)) as Hle.
    rewrite (pcut_low (FileDisc.prod_words p) n len f (wl_off 0 (FileDisc.prod_words p) i + length w) ltac:(lia)).
    exact (wl_cut_end (FileDisc.prod_words p) f len i w Hw).
Qed.

Lemma pcut_echo_bytes (ws : list (list (bv 8))) (n : nat) (f : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) n) f 0 len ->
  UkShEcho.echo_argv_bytes ws (pcut ws n len f).
Proof using. exact (pcut_echo_bytes_p (FileDisc.PrEcho ws) n f len). Qed.

(* ...AND EVERY [cat]'s *)
Lemma pcut_cat_bytes_p (p : FileDisc.producer) (n : nat) (f : nat -> bv 8) (len i : nat) :
  UkSh.ush_line_at (FileDisc.LPipe p n) f 0 len -> i < n ->
  UkShCat.cat_argv_bytes (length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i)
    (length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i + 3) (pcut (FileDisc.prod_words p) n len f).
Proof using.
  intros (Hok & Hlen & Hby) Hi.
  destruct n as [| n]; [lia |].
  assert (Hlen' : len = length (wl_body (FileDisc.prod_words p)) + 6 * S n + 1)
    by (rewrite Hlen line_bytes_pipe_length_p; reflexivity).
  assert (Hb : bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p (S n)))).
  { intros j Hj. apply Hby. rewrite Hlen. exact Hj. }
  rewrite line_bytes_pipe_split_p in Hb.
  apply bat_app in Hb as [_ Hr]. apply bat_app in Hr as [_ Hr].
  cbn [length] in Hr.
  pose proof (bat_cat_at f i n (0 + length (wl_body (FileDisc.prod_words p)) + 3) ltac:(lia) Hr) as Hc.
  split_and!.
  - rewrite UkShCat.cmd_cat_len. reflexivity.
  - intros j Hj. rewrite UkShCat.cmd_cat_len in Hj.
    rewrite pcut_flat.
    rewrite UkShMain.ushp_nulfold_miss.
    2:{ intros i' tk Hi'. apply elem_of_list_lookup_2 in Hi'.
        destruct (rtoks_cats_in (S n) _ tk Hi') as (i'' & _ & ->). cbn [snd]. lia. }
    rewrite UkShMain.ushp_nulfold_miss.
    2:{ intros i' tk Hi'. apply elem_of_list_lookup_2 in Hi'.
        pose proof (wl_toks_end_le (FileDisc.prod_words p) tk Hi'). lia. }
    rewrite /UkShParseCmd.ushp_ext bool_decide_eq_true_2; [| lia].
    pose proof (Hc j ltac:(rewrite ushq_cat_len; lia)) as Hcj.
    replace (0 + length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i + j)
      with (length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i + j) in Hcj by lia.
    exact Hcj.
  - rewrite pcut_flat.
    pose proof (rtoks_cats_concat_lookup (S n) (length (wl_body (FileDisc.prod_words p)) + 3) i Hi) as Hl.
    exact (UkShParseCmd.ushp_nulfold_hit _ _ i _ Hl).
Qed.

Lemma pcut_cat_bytes (ws : list (list (bv 8))) (n : nat) (f : nat -> bv 8) (len i : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) n) f 0 len -> i < n ->
  UkShCat.cat_argv_bytes (length (wl_body ws) + 3 + 6 * i)
    (length (wl_body ws) + 3 + 6 * i + 3) (pcut ws n len f).
Proof using. exact (pcut_cat_bytes_p (FileDisc.PrEcho ws) n f len i). Qed.

(* a lookup in a [map], as the option's *)
Lemma map_lookup_fmap {A B : Type} (f : A -> B) (l : list A) (k : nat) :
  map f l !! k = f <$> (l !! k).
Proof using.
  revert k. induction l as [| x l IH]; intros [| k]; [done | done | done |].
  exact (IH k).
Qed.
