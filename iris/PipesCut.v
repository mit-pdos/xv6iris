(* ===================================================================== *)
(*  PipesCut.v -- THE N-STAGE PIPELINE LINE, READ BY THE PARSER (cut C8). *)
(*                                                                       *)
(*  [echo ws | cat | ... | cat] with [n >= 1] cats, as the loop's typed   *)
(*  line fact [UkSh.ush_line_at (FileDisc.LPipe (PrEcho ws) (cats n))]   *)
(*  says (the stages all cats: the round's admission, cut G3):           *)
(*    - it is the pipeline lexer's line ([UkShPipesLex.ushq_lines_is] at  *)
(*      [n] words [cat]), so [ushq_lines_bars] lexes it stage by stage;   *)
(*    - the parser's cut ([UkShPipesCmd.ushq_nulfolds] over every stage's *)
(*      tokens) holds echo's argv at the left stage and [cat]'s at every  *)
(*      right one -- the two readings [UShPipesNode]'s stages take.       *)
(*  At ANY admissible stage list [fs] (cut G7, the last section): the     *)
(*  line is [UkShPipesLex.ushq_lines_ws] ([lines_of_pipe_fs]), and the    *)
(*  cut [pcut_fs] holds the producer's argv ([pcut_fs_echo_bytes]) and    *)
(*  every stage's words [filt_words F] at its offset ([pcut_fs_stage]);   *)
(*  [pipes_lpg] / [pipes_lpcg] are the loop's line predicates there.      *)
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
Require ExecWords UmodeAbi.
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
  FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats (S n)))
  = wl_body (FileDisc.prod_words p) ++ [wl_sp; ushq_bar; wl_sp]
    ++ (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]).
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite FileDisc.suf_filts_cats FileDisc.suf_barcats_S suf_barcat_split -!app_assoc. reflexivity.
Qed.

Lemma line_bytes_pipe_length_p (p : FileDisc.producer) (n : nat) :
  length (FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats n)))
  = length (wl_body (FileDisc.prod_words p)) + 6 * n + 1.
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite FileDisc.suf_filts_cats !length_app suf_barcats_length. cbn [length].
  unfold FileDisc.prod_body. lia.
Qed.

Lemma line_bytes_pipe_split (ws : list (list (bv 8))) (n : nat) :
  FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats (S n)))
  = wl_body ws ++ [wl_sp; ushq_bar; wl_sp] ++ (ushq_cat ++ FileDisc.suf_barcats n ++ [wl_nl]).
Proof using. exact (line_bytes_pipe_split_p (FileDisc.PrEcho ws) n). Qed.

Lemma line_bytes_pipe_length (ws : list (list (bv 8))) (n : nat) :
  length (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)))
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
  bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats n))) ->
  len = length (FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats n))) ->
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
  bat f 0 (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n))) ->
  len = length (FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n))) ->
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
    wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n))
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)) gf k len.

Lemma pipes_lp_of_at (ws : list (list (bv 8))) (n : nat) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)) f k len ->
  pipes_lp (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n))) (fun j : nat => f (k + j)) 0 len.
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
  FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats n)) !!! j = wl_line (FileDisc.prod_words p) !!! j.
Proof using.
  intros Hj. rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  unfold FileDisc.prod_body.
  rewrite -app_assoc (wl_lta_app_l (wl_body (FileDisc.prod_words p)) _ j Hj).
  rewrite /wl_line (wl_lta_app_l (wl_body (FileDisc.prod_words p)) [wl_nl] j Hj). reflexivity.
Qed.

Lemma pipe_bytes_lo (ws : list (list (bv 8))) (n j : nat) :
  j < length (wl_body ws) ->
  FileDisc.line_bytes (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)) !!! j = wl_line ws !!! j.
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

(* THE [cat N] PIPELINE'S LINE PREDICATE (cut C9f2; at any name of the
   class, cut W3): the loop's typed line [cat N | cat | ... | cat] *)
Definition pipes_lpc (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) : Prop :=
  exists (nm : list (bv 8)) (n : nat),
    FileDisc.uname nm
    /\ wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF nm) (FileDisc.cats n))
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF nm) (FileDisc.cats n)) gf k len.

Lemma pipes_lpc_of_at (nm : list (bv 8)) (n : nat) (f : nat -> bv 8) (k len : nat) :
  FileDisc.uname nm ->
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF nm) (FileDisc.cats n)) f k len ->
  pipes_lpc (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF nm) (FileDisc.cats n)))
    (fun j : nat => f (k + j)) 0 len.
Proof using.
  intros Hu (Hok & Hlen & Hby). exists nm, n. split; [exact Hu |]. split; [reflexivity |].
  split; [exact Hok |]. split; [exact Hlen |].
  intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

(* the producer [cat N]'s body, at a name of any length *)
Lemma catf_body_len (nm : list (bv 8)) :
  length (wl_body (FileDisc.prod_words (FileDisc.PrCatF nm))) = 4 + length nm.
Proof using.
  unfold FileDisc.prod_words, wl_body. cbn [wl_tail]. rewrite app_nil_r length_app.
  cbn [length]. change (length FileDisc.fd_w_cat) with 3. lia.
Qed.

(* its first two bytes are [c] and [a], so the loop's [cd] test falls out
   at the second, as [cat f]'s does *)
Lemma pipes_lpc_bytes (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lpc wsf gf k len ->
  bv_unsigned (gf k) = 99%Z /\ bv_unsigned (gf (k + 1)) = 97%Z /\ 2 <= len.
Proof using.
  intros (nm & n & _ & _ & _ & Hlen & Hby).
  pose proof (catf_body_len nm) as Hb.
  rewrite line_bytes_pipe_length_p Hb in Hlen.
  split_and!; [| | lia].
  - rewrite -(Nat.add_0_r k) (Hby 0 ltac:(lia)) (pipe_bytes_lo_p (FileDisc.PrCatF nm) n 0 ltac:(lia)).
    by vm_compute.
  - rewrite (Hby 1 ltac:(lia)) (pipe_bytes_lo_p (FileDisc.PrCatF nm) n 1 ltac:(lia)).
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
  UkSh.ush_line_at (FileDisc.LPipe p (FileDisc.cats n)) f 0 len ->
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
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)) f 0 len ->
  UkShEcho.echo_argv_bytes ws (pcut ws n len f).
Proof using. exact (pcut_echo_bytes_p (FileDisc.PrEcho ws) n f len). Qed.

(* ...AND EVERY [cat]'s *)
Lemma pcut_cat_bytes_p (p : FileDisc.producer) (n : nat) (f : nat -> bv 8) (len i : nat) :
  UkSh.ush_line_at (FileDisc.LPipe p (FileDisc.cats n)) f 0 len -> i < n ->
  UkShCat.cat_argv_bytes (length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i)
    (length (wl_body (FileDisc.prod_words p)) + 3 + 6 * i + 3) (pcut (FileDisc.prod_words p) n len f).
Proof using.
  intros (Hok & Hlen & Hby) Hi.
  destruct n as [| n]; [lia |].
  assert (Hlen' : len = length (wl_body (FileDisc.prod_words p)) + 6 * S n + 1)
    by (rewrite Hlen line_bytes_pipe_length_p; reflexivity).
  assert (Hb : bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p (FileDisc.cats (S n))))).
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
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) (FileDisc.cats n)) f 0 len -> i < n ->
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

(* ===================================================================== *)
(*  A CAT STAGE's ARGV, READ AS ITS WORDS (cut G7): the one token [cat] at *)
(*  its line offset is the rebase of the word list [[cat]]'s token, and   *)
(*  its bytes are the words' argv at that offset                          *)
(* ===================================================================== *)
Lemma cat_rebase_toks (a : nat) :
  ushq_rebase a (wl_toks (FileDisc.filt_words FileDisc.FCat)) = UkShCat.cat_toks a (a + 3).
Proof using.
  replace (wl_toks (FileDisc.filt_words FileDisc.FCat)) with [(0, 3)] by (vm_compute; reflexivity).
  cbn. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma cat_words_exec_ok : ExecWords.exec_ok (FileDisc.filt_words FileDisc.FCat).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma cat_argv_bytes_echo (a b : nat) (g : nat -> bv 8) :
  UkShCat.cat_argv_bytes a b g ->
  UkShEcho.echo_argv_bytes (FileDisc.filt_words FileDisc.FCat) (fun j : nat => g (a + j)).
Proof using.
  intros Hab. pose proof (UkShCat.cat_argv_bytes_end a b g Hab) as Hb3.
  destruct Hab as (_ & Hin & Hnul). rewrite UkShCat.cmd_cat_len in Hin.
  assert (Hoff : UkShEcho.echo_off (FileDisc.filt_words FileDisc.FCat) 0 = 0) by apply UkShEcho.echo_off_0.
  assert (Halen : UkShEcho.echo_alen (FileDisc.filt_words FileDisc.FCat) 0 = 3) by reflexivity.
  split.
  - intros i j Hi Hj. cbn [FileDisc.filt_words length] in Hi. assert (i = 0) as -> by lia.
    rewrite Halen in Hj. rewrite Hoff. cbn [Nat.add].
    rewrite (Hin j Hj).
    do 3 (destruct j as [| j]; [vm_compute; reflexivity |]). lia.
  - intros i Hi. cbn [FileDisc.filt_words length] in Hi. assert (i = 0) as -> by lia.
    rewrite Hoff Halen. cbn [Nat.add]. rewrite <- Hb3. exact Hnul.
Qed.

(* ===================================================================== *)
(*  THE FILTER PIPELINE's LINE (cut G7, grep-pipes SS4): [p | F1 | .. |   *)
(*  Fn] at ANY admissible stage list, lexed stage by stage                *)
(*  ([UkShPipesLex.ushq_lines_ws]) and cut: each stage's argv is its      *)
(*  words ([FileDisc.filt_words]) at the stage's offset in the line.      *)
(* ===================================================================== *)

Lemma fd_bar_bar : FileDisc.fd_bar = ushq_bar.
Proof using. reflexivity. Qed.

Lemma fd_w_grep_word : wl_word FileDisc.fd_w_grep.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* a filter's words lex as a command's *)
Lemma filt_ws_ok (F : FileDisc.filt) : FileDisc.filt_ok F -> ushq_ws_ok (FileDisc.filt_words F).
Proof using.
  destruct F as [| w]; cbn [FileDisc.filt_ok FileDisc.filt_words]; intros HF.
  - split_and!; [exact (wl_wf_fn _ (FileDisc.filt_wf FileDisc.FCat HF)) | cbn; lia | cbn; lia].
  - split_and!; [exact (wl_wf_fn _ (FileDisc.filt_wf (FileDisc.FGrep w) HF)) | cbn; lia | cbn; lia].
Qed.

Lemma bat_cons3 (g : nat -> bv 8) (c : nat) (a b d : bv 8) (l : list (bv 8)) :
  bat g c (a :: b :: d :: l) -> g c = a /\ g (c + 1) = b /\ g (c + 2) = d /\ bat g (c + 3) l.
Proof using.
  intros H. split_and!.
  - pose proof (H 0 ltac:(cbn; lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
  - exact (H 1 ltac:(cbn; lia)).
  - exact (H 2 ltac:(cbn; lia)).
  - intros j Hj. replace (c + 3 + j) with (c + (3 + j)) by lia.
    rewrite (H (3 + j) ltac:(cbn; lia)). reflexivity.
Qed.

(* the line: the producer, then [ | F] per stage *)
Lemma line_bytes_pipe_split_fs (p : FileDisc.producer) (F : FileDisc.filt) (fs : list FileDisc.filt) :
  FileDisc.line_bytes (FileDisc.LPipe p (F :: fs))
  = wl_body (FileDisc.prod_words p) ++ [wl_sp; ushq_bar; wl_sp]
    ++ (wl_body (FileDisc.filt_words F) ++ FileDisc.suf_filts fs ++ [wl_nl]).
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite FileDisc.suf_filts_cons. unfold FileDisc.prod_body, FileDisc.suf_filt.
  rewrite -!app_assoc. reflexivity.
Qed.

Lemma line_bytes_pipe_length_fs (p : FileDisc.producer) (fs : list FileDisc.filt) :
  length (FileDisc.line_bytes (FileDisc.LPipe p fs))
  = length (wl_body (FileDisc.prod_words p)) + length (FileDisc.suf_filts fs) + 1.
Proof using.
  rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  rewrite !length_app. unfold FileDisc.prod_body. cbn [length]. lia.
Qed.

(* ---- the tail after the first bar: a word list per stage ---- *)
Lemma tail_filts (g : nat -> bv 8) (len : nat) :
  forall (fs : list FileDisc.filt) (F : FileDisc.filt) (c : nat),
    Forall FileDisc.filt_ok (F :: fs) ->
    bat g c (wl_body (FileDisc.filt_words F) ++ FileDisc.suf_filts fs ++ [wl_nl]) ->
    len = c + (length (wl_body (FileDisc.filt_words F)) + length (FileDisc.suf_filts fs) + 1) ->
    ushq_tail_ws g c len (map FileDisc.filt_words (F :: fs)).
Proof using.
  induction fs as [| F' fs IH]; intros F c HF Hb Hlen.
  - cbn [map ushq_tail_ws].
    apply Forall_cons_1 in HF as [HF _].
    apply bat_app in Hb as [Hbody Hr].
    split; [exact (filt_ws_ok F HF) |]. split; [exact Hbody |].
    change (FileDisc.suf_filts []) with (@nil (bv 8)) in Hlen, Hr. cbn [length app] in Hlen, Hr.
    split; [lia |].
    pose proof (Hr 0 ltac:(cbn; lia)) as H0. rewrite Nat.add_0_r in H0. exact H0.
  - cbn [map ushq_tail_ws].
    apply Forall_cons_1 in HF as [HF HF'].
    rewrite FileDisc.suf_filts_cons -app_assoc in Hb. unfold FileDisc.suf_filt in Hb.
    apply bat_app in Hb as [Hbody Hr]. cbn [app] in Hr.
    destruct (bat_cons3 _ _ _ _ _ _ Hr) as (Hsp1 & Hbar & Hsp2 & Hr').
    rewrite FileDisc.suf_filts_cons length_app in Hlen. unfold FileDisc.suf_filt in Hlen.
    cbn [length] in Hlen.
    split; [exact (filt_ws_ok F HF) |]. split; [exact Hbody |].
    split; [exact Hsp1 |]. split; [rewrite Hbar; exact fd_bar_bar |]. split; [exact Hsp2 |].
    apply (IH F' (c + length (wl_body (FileDisc.filt_words F)) + 3) HF' Hr'). lia.
Qed.

(* ---- THE LINE IS THE LEXER'S, at any stage list ---- *)
Lemma lines_of_pipe_fs (p : FileDisc.producer) (fs : list FileDisc.filt) (f : nat -> bv 8) (len : nat) :
  FileDisc.prod_ok p -> fs <> [] -> Forall FileDisc.filt_ok fs ->
  bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p fs)) ->
  len = length (FileDisc.line_bytes (FileDisc.LPipe p fs)) ->
  ushq_lines_ws (FileDisc.prod_words p) (map FileDisc.filt_words fs) f 0 len.
Proof using.
  intros Hok Hn HF Hb Hlen.
  destruct fs as [| F fs]; [done |].
  rewrite line_bytes_pipe_length_fs in Hlen.
  rewrite FileDisc.suf_filts_cons length_app in Hlen. unfold FileDisc.suf_filt in Hlen.
  cbn [length] in Hlen.
  rewrite line_bytes_pipe_split_fs in Hb.
  apply bat_app in Hb as [Hbody Hr]. apply bat_app in Hr as [Hs Hr].
  unfold ushq_lines_is, ushq_lines_ws. cbv zeta.
  split; [exact (prod_ws_ok p Hok) |].
  split; [exact Hbody |].
  split; [pose proof (Hs 0 ltac:(cbn; lia)) as H0; rewrite Nat.add_0_r in H0; exact H0 |].
  split; [exact (Hs 1 ltac:(cbn; lia)) |].
  split; [exact (Hs 2 ltac:(cbn; lia)) |].
  apply (tail_filts (fun j : nat => f (0 + j)) len fs F (length (wl_body (FileDisc.prod_words p)) + 3)).
  - exact HF.
  - intros j Hj. cbv beta. rewrite (Hr j Hj). reflexivity.
  - lia.
Qed.

(* ---- the stages' offsets and token lists ---- *)
Fixpoint ushq_soff (c : nat) (rs : list (list (list (bv 8)))) (k : nat) : nat :=
  match rs with
  | [] => c
  | r :: rs' => match k with O => c | S k' => ushq_soff (c + length (wl_body r) + 3) rs' k' end
  end.

Lemma ushq_soff_ge (rs : list (list (list (bv 8)))) :
  forall c k, c <= ushq_soff c rs k.
Proof using.
  induction rs as [| r rs IH]; intros c k; cbn [ushq_soff]; [lia |].
  destruct k as [| k]; [lia |]. pose proof (IH (c + length (wl_body r) + 3) k). lia.
Qed.

Lemma ushq_rtoks_ws_lookup (rs : list (list (list (bv 8)))) :
  forall c k r, rs !! k = Some r ->
    ushq_rtoks_ws c rs !! k = Some (ushq_rebase (ushq_soff c rs k) (wl_toks r)).
Proof using.
  induction rs as [| r0 rs IH]; intros c k r Hk; [by destruct k |].
  destruct k as [| k]; cbn in Hk |- *.
  - by injection Hk as <-.
  - exact (IH _ k r Hk).
Qed.

(* a word list's tokens at [off], and at a rebase *)
Lemma wl_toks_at_shift (r : list (list (bv 8))) :
  forall c off, wl_toks_at (c + off) r = ushq_rebase c (wl_toks_at off r).
Proof using.
  induction r as [| w r IH]; intros c off; [reflexivity |].
  cbn [wl_toks_at ushq_rebase map fst snd].
  replace (S (c + off + length w)) with (c + S (off + length w)) by lia.
  rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma wl_rebase_toks (r : list (list (bv 8))) (c : nat) :
  ushq_rebase c (wl_toks r) = wl_toks_at c r.
Proof using.
  unfold wl_toks. rewrite <- (Nat.add_0_r c) at 2. rewrite (wl_toks_at_shift r c 0). reflexivity.
Qed.

Lemma wl_off_shift (r : list (list (bv 8))) :
  forall c off i, wl_off (c + off) r i = c + wl_off off r i.
Proof using.
  induction r as [| w r IH]; intros c off i; cbn [wl_off]; [reflexivity |].
  destruct i as [| i]; [reflexivity |].
  replace (S (c + off + length w)) with (c + S (off + length w)) by lia. apply IH.
Qed.

Lemma wl_toks_at_bounds (r : list (list (bv 8))) :
  forall off tk, tk ∈ wl_toks_at off r -> off <= fst tk <= snd tk /\ snd tk <= off + length (wl_body r).
Proof using.
  induction r as [| w r IH]; intros off tk Htk; [by apply elem_of_nil in Htk |].
  cbn [wl_toks_at] in Htk. rewrite wl_body_cons length_app.
  apply elem_of_cons in Htk as [-> | Htk]; cbn [fst snd].
  - lia.
  - destruct r as [| w' r']; [by apply elem_of_nil in Htk |].
    pose proof (IH _ tk Htk) as Hb. rewrite wl_tail_cons. cbn [length]. lia.
Qed.

(* every token of the stages from [c] on starts at [c] or past it *)
Lemma ushq_rtoks_ws_ge (rs : list (list (list (bv 8)))) :
  forall c tk, tk ∈ concat (ushq_rtoks_ws c rs) -> c <= fst tk <= snd tk.
Proof using.
  induction rs as [| r rs IH]; intros c tk Htk; [by apply elem_of_nil in Htk |].
  cbn [ushq_rtoks_ws concat] in Htk. apply elem_of_app in Htk as [Htk | Htk].
  - rewrite wl_rebase_toks in Htk. pose proof (wl_toks_at_bounds r c tk Htk). lia.
  - pose proof (IH _ tk Htk). lia.
Qed.

(* THE FOLD AT A STAGE'S WORD: the stages' cuts leave a word's bytes and
   put the NUL at its end *)
Lemma nulfold_stage (rs : list (list (list (bv 8)))) :
  forall (c k : nat) (r : list (list (bv 8))) (g : nat -> bv 8) (i : nat) (w : list (bv 8)) (j : nat),
    rs !! k = Some r -> r !! i = Some w -> j <= length w ->
    UkShParseCmd.ushp_nulfold (concat (ushq_rtoks_ws c rs)) g (wl_off (ushq_soff c rs k) r i + j)
    = (if Nat.eqb j (length w) then UmodeAbi.ubyte0 else g (wl_off (ushq_soff c rs k) r i + j)).
Proof using.
  induction rs as [| r0 rs IH]; intros c k r g i w j Hk Hi Hj; [by destruct k |].
  cbn [ushq_rtoks_ws concat]. rewrite ushq_nulfold_app.
  destruct k as [| k]; cbn [ushq_soff] in *.
  - cbn in Hk. injection Hk as ->.
    pose proof (wl_off_le_body r c i w j Hi Hj) as Hle.
    rewrite UkShMain.ushp_nulfold_miss.
    2:{ intros i' tk Hi'. apply elem_of_list_lookup_2 in Hi'.
        pose proof (ushq_rtoks_ws_ge rs _ tk Hi'). lia. }
    rewrite wl_rebase_toks. exact (wl_nulfold_at r c g i w j Hi Hj).
  - cbn in Hk.
    pose proof (ushq_soff_ge rs (c + length (wl_body r0) + 3) k) as Hge.
    pose proof (wl_off_ge r (ushq_soff (c + length (wl_body r0) + 3) rs k) i) as Hge2.
    rewrite (IH _ k r _ i w j Hk Hi Hj).
    destruct (Nat.eqb j (length w)); [reflexivity |].
    apply UkShMain.ushp_nulfold_miss.
    intros i' tk Hi'. apply elem_of_list_lookup_2 in Hi'.
    rewrite wl_rebase_toks in Hi'. pose proof (wl_toks_at_bounds r0 c tk Hi'). lia.
Qed.

(* the stage [k]'s words and the line's bytes there *)
Lemma tail_ws_stage (g : nat -> bv 8) (len : nat) (rs : list (list (list (bv 8)))) :
  forall (c k : nat) (r : list (list (bv 8))),
    ushq_tail_ws g c len rs -> rs !! k = Some r ->
    ushq_ws_ok r
    /\ (forall j, j < length (wl_body r) -> g (ushq_soff c rs k + j) = wl_body r !!! j)
    /\ ushq_soff c rs k + length (wl_body r) + 1 <= len.
Proof using.
  induction rs as [| r0 rs IH]; intros c k r Ht Hk; [by destruct k |].
  destruct k as [| k]; cbn [ushq_soff].
  - cbn in Hk. injection Hk as <-.
    destruct Ht as (Hok & Hb & Hrest). split; [exact Hok |]. split; [exact Hb |].
    destruct rs as [| r2 rs].
    + destruct Hrest as [Hlen _]. lia.
    + destruct Hrest as (_ & _ & _ & Ht'). pose proof (ushq_tail_ws_lt g len _ _ Ht'). lia.
  - cbn in Hk. destruct rs as [| r2 rs]; [by destruct k |].
    destruct Ht as (_ & _ & _ & _ & _ & Ht'). exact (IH _ k r Ht' Hk).
Qed.

(* THE CUT of a filter pipeline's line, at the parser's stages *)
Definition pcut_fs (ws : list (list (bv 8))) (rs : list (list (list (bv 8)))) (len : nat)
    (f : nat -> bv 8) : nat -> bv 8 :=
  ushq_nulfolds (wl_toks ws) (ushq_rtoks_ws (length (wl_body ws) + 3) rs)
    (UkShParseCmd.ushp_ext len f).

(* ...and the producer's argv is there *)
Lemma pcut_fs_echo_bytes (p : FileDisc.producer) (fs : list FileDisc.filt) (f : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe p fs) f 0 len ->
  UkShEcho.echo_argv_bytes (FileDisc.prod_words p)
    (pcut_fs (FileDisc.prod_words p) (map FileDisc.filt_words fs) len f).
Proof using.
  intros (Hok & Hlen & Hby).
  destruct Hok as (Hok & Hn & _).
  assert (Hblen : length (wl_body (FileDisc.prod_words p)) < len)
    by (rewrite Hlen line_bytes_pipe_length_fs; lia).
  assert (Hlo : forall j : nat, j < length (wl_body (FileDisc.prod_words p)) -> f j = wl_line (FileDisc.prod_words p) !!! j).
  { intros j Hj. pose proof (Hby j ltac:(lia)) as Hfj.
    rewrite Nat.add_0_l in Hfj. rewrite Hfj.
    rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body]. unfold FileDisc.prod_body.
    rewrite -app_assoc (wl_lta_app_l (wl_body (FileDisc.prod_words p)) _ j Hj).
    rewrite /wl_line (wl_lta_app_l (wl_body (FileDisc.prod_words p)) [wl_nl] j Hj). reflexivity. }
  (* below the first bar the stages' cuts are not there *)
  assert (Hlow : forall x, x <= length (wl_body (FileDisc.prod_words p)) ->
            pcut_fs (FileDisc.prod_words p) (map FileDisc.filt_words fs) len f x
            = UkShParseCmd.ushp_nulfold (wl_toks (FileDisc.prod_words p)) (UkShParseCmd.ushp_ext len f) x).
  { intros x Hx. rewrite /pcut_fs ushq_nulfolds_flat ushq_nulfold_app.
    apply UkShMain.ushp_nulfold_miss.
    intros i tk Hi. apply elem_of_list_lookup_2 in Hi.
    pose proof (ushq_rtoks_ws_ge _ _ tk Hi). lia. }
  split.
  - intros i j Hi Hj.
    destruct (lookup_lt_is_Some_2 (FileDisc.prod_words p) i Hi) as [w Hw].
    assert (Hwi : (FileDisc.prod_words p) !!! i = w) by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_alen Hwi in Hj.
    rewrite /UkShEcho.echo_off.
    pose proof (wl_off_le_body (FileDisc.prod_words p) 0 i w (length w) Hw ltac:(lia)) as Hle.
    rewrite (Hlow (wl_off 0 (FileDisc.prod_words p) i + j) ltac:(lia)).
    rewrite (wl_cut_in (FileDisc.prod_words p) f len i w j Hw Hj ltac:(lia)).
    exact (Hlo (wl_off 0 (FileDisc.prod_words p) i + j) ltac:(lia)).
  - intros i Hi.
    destruct (lookup_lt_is_Some_2 (FileDisc.prod_words p) i Hi) as [w Hw].
    assert (Hwi : (FileDisc.prod_words p) !!! i = w) by (rewrite list_lookup_total_alt Hw; reflexivity).
    rewrite /UkShEcho.echo_off /UkShEcho.echo_alen Hwi.
    pose proof (wl_off_le_body (FileDisc.prod_words p) 0 i w (length w) Hw ltac:(lia)) as Hle.
    rewrite (Hlow (wl_off 0 (FileDisc.prod_words p) i + length w) ltac:(lia)).
    exact (wl_cut_end (FileDisc.prod_words p) f len i w Hw).
Qed.

(* ...AND STAGE [k]'s: its words at its offset [co], its token list the
   rebase of its words' there, and an exec'able word list *)
Lemma pcut_fs_stage (p : FileDisc.producer) (fs : list FileDisc.filt) (f : nat -> bv 8)
    (len k : nat) (F : FileDisc.filt) :
  UkSh.ush_line_at (FileDisc.LPipe p fs) f 0 len -> fs !! k = Some F ->
  let rs := map FileDisc.filt_words fs in
  let co := ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k in
  ushq_rtoks_ws (length (wl_body (FileDisc.prod_words p)) + 3) rs !! k
    = Some (ushq_rebase co (wl_toks (FileDisc.filt_words F)))
  /\ ExecWords.exec_ok (FileDisc.filt_words F)
  /\ UkShEcho.echo_argv_bytes (FileDisc.filt_words F)
       (fun j : nat => pcut_fs (FileDisc.prod_words p) rs len f (co + j)).
Proof using.
  intros Hlat Hk rs co. subst rs co.
  pose proof Hlat as (Hok & Hlen & Hby).
  pose proof Hok as (Hp & Hn & HF & Hlm).
  assert (Hr : map FileDisc.filt_words fs !! k = Some (FileDisc.filt_words F))
    by (rewrite list_lookup_fmap Hk; reflexivity).
  set (rs := map FileDisc.filt_words fs) in *.
  assert (Hbat : bat f 0 (FileDisc.line_bytes (FileDisc.LPipe p fs))).
  { intros j Hj. apply Hby. rewrite Hlen. exact Hj. }
  pose proof (lines_of_pipe_fs p fs f len Hp Hn HF Hbat Hlen) as Hlines.
  destruct Hlines as (_ & _ & _ & _ & _ & Htail).
  destruct (tail_ws_stage _ len rs _ k _ Htail Hr) as ((Hwf & Hpos & Hlt10) & Hb & Hend).
  assert (Hco : length (wl_body (FileDisc.prod_words p)) + 3 <= (ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k)) by apply ushq_soff_ge.
  split_and!.
  - exact (ushq_rtoks_ws_lookup rs _ k _ Hr).
  - split_and!; [exact Hwf | exact Hpos | exact Hlt10 |].
    rewrite Hlen in Hend. unfold wl_line. rewrite length_app. cbn [length]. lia.
  - (* the stage's bytes, and the NULs the cut put at its words' ends *)
    assert (Hval : forall i w j, FileDisc.filt_words F !! i = Some w -> j <= length w ->
              pcut_fs (FileDisc.prod_words p) rs len f ((ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) + (wl_off 0 (FileDisc.filt_words F) i + j))
              = if Nat.eqb j (length w) then UmodeAbi.ubyte0
                else f ((ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) + (wl_off 0 (FileDisc.filt_words F) i + j))).
    { intros i w j Hi Hj.
      rewrite /pcut_fs ushq_nulfolds_flat ushq_nulfold_app.
      replace ((ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) + (wl_off 0 (FileDisc.filt_words F) i + j))
        with (wl_off (ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) (FileDisc.filt_words F) i + j)
        by (rewrite <- (Nat.add_0_r (ushq_soff _ rs k)) at 1; rewrite (wl_off_shift _ _ 0 i); lia).
      rewrite (nulfold_stage rs _ k _ _ i w j Hr Hi Hj).
      destruct (Nat.eqb j (length w)) eqn:Hjw; [reflexivity |].
      pose proof (wl_off_ge (FileDisc.filt_words F) (ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) i) as Hge.
      rewrite UkShMain.ushp_nulfold_miss.
      2:{ intros i' tk Hi'. apply elem_of_list_lookup_2 in Hi'.
          pose proof (wl_toks_end_le (FileDisc.prod_words p) tk Hi'). lia. }
      rewrite /UkShParseCmd.ushp_ext bool_decide_eq_true_2; [reflexivity |].
      pose proof (wl_off_le_body _ (ushq_soff (length (wl_body (FileDisc.prod_words p)) + 3) rs k) i w j Hi Hj). lia. }
    split.
    + intros i j Hi Hj.
      destruct (lookup_lt_is_Some_2 _ i Hi) as [w Hw].
      assert (Hwi : FileDisc.filt_words F !!! i = w) by (rewrite list_lookup_total_alt Hw; reflexivity).
      rewrite /UkShEcho.echo_alen Hwi in Hj. rewrite /UkShEcho.echo_off.
      cbv beta. rewrite (Hval i w j Hw ltac:(lia)).
      rewrite (proj2 (Nat.eqb_neq j (length w)) ltac:(lia)).
      pose proof (wl_off_le_body _ 0 i w (length w) Hw ltac:(lia)) as Hle.
      pose proof (Hb (wl_off 0 (FileDisc.filt_words F) i + j) ltac:(lia)) as Hbj.
      cbv beta in Hbj. rewrite Nat.add_0_l in Hbj. rewrite Hbj.
      rewrite /wl_line (wl_lta_app_l (wl_body (FileDisc.filt_words F)) [wl_nl] (wl_off 0 (FileDisc.filt_words F) i + j) ltac:(lia)). reflexivity.
    + intros i Hi.
      destruct (lookup_lt_is_Some_2 _ i Hi) as [w Hw].
      assert (Hwi : FileDisc.filt_words F !!! i = w) by (rewrite list_lookup_total_alt Hw; reflexivity).
      rewrite /UkShEcho.echo_off /UkShEcho.echo_alen Hwi. cbv beta.
      rewrite (Hval i w (length w) Hw ltac:(lia)) Nat.eqb_refl. reflexivity.
Qed.

(* ---- THE LOOP'S TYPED LINE at any admissible stage list, as the round's
        line predicate (the landed [pipes_lp] / [pipes_lpc] are its all-cat
        members) ---- *)
Definition pipes_lpg (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) : Prop :=
  exists (ws : list (list (bv 8))) (fs : list FileDisc.filt),
    wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) fs)
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) fs) gf k len.

Definition pipes_lpcg (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) : Prop :=
  exists (nm : list (bv 8)) (fs : list FileDisc.filt),
    FileDisc.uname nm
    /\ wsf = FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF nm) fs)
    /\ UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF nm) fs) gf k len.

Lemma pipes_lp_g (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lp wsf gf k len -> pipes_lpg wsf gf k len.
Proof using. intros (ws & n & H). exists ws, (FileDisc.cats n). exact H. Qed.

Lemma pipes_lpc_g (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lpc wsf gf k len -> pipes_lpcg wsf gf k len.
Proof using. intros (nm & n & H). exists nm, (FileDisc.cats n). exact H. Qed.

(* below the first bar the line's bytes are the producer's, at any stage
   list *)
Lemma pipe_bytes_lo_fs (p : FileDisc.producer) (fs : list FileDisc.filt) (j : nat) :
  j < length (wl_body (FileDisc.prod_words p)) ->
  FileDisc.line_bytes (FileDisc.LPipe p fs) !!! j = wl_line (FileDisc.prod_words p) !!! j.
Proof using.
  intros Hj. rewrite FileDisc.line_bytes_body. cbn [FileDisc.line_body].
  unfold FileDisc.prod_body.
  rewrite -app_assoc (wl_lta_app_l (wl_body (FileDisc.prod_words p)) _ j Hj).
  rewrite /wl_line (wl_lta_app_l (wl_body (FileDisc.prod_words p)) [wl_nl] j Hj). reflexivity.
Qed.

Lemma pipes_lpg0 (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lpg wsf gf k len -> bv_unsigned (gf k) = 101%Z.
Proof using.
  intros (ws & fs & _ & Hok & Hlen & Hby).
  destruct Hok as (Hok & _ & _).
  pose proof (line_ok_body_pos ws Hok) as Hbody.
  assert (Hlpos : 0 < len) by (rewrite Hlen line_bytes_pipe_length_fs; lia).
  pose proof (Hby 0 Hlpos) as H0. rewrite Nat.add_0_r in H0.
  rewrite H0 (pipe_bytes_lo_fs (FileDisc.PrEcho ws) fs 0 Hbody).
  exact (line_ok_head_byte0 ws Hok).
Qed.

Lemma pipes_lpcg_bytes (wsf : list (list (bv 8))) (gf : nat -> bv 8) (k len : nat) :
  pipes_lpcg wsf gf k len ->
  bv_unsigned (gf k) = 99%Z /\ bv_unsigned (gf (k + 1)) = 97%Z /\ 2 <= len.
Proof using.
  intros (nm & fs & _ & _ & _ & Hlen & Hby).
  pose proof (catf_body_len nm) as Hb.
  rewrite line_bytes_pipe_length_fs Hb in Hlen.
  split_and!; [| | lia].
  - rewrite -(Nat.add_0_r k) (Hby 0 ltac:(lia))
      (pipe_bytes_lo_fs (FileDisc.PrCatF nm) fs 0 ltac:(lia)).
    by vm_compute.
  - rewrite (Hby 1 ltac:(lia)) (pipe_bytes_lo_fs (FileDisc.PrCatF nm) fs 1 ltac:(lia)).
    by vm_compute.
Qed.

Lemma pipes_lpg_of_at (ws : list (list (bv 8))) (fs : list FileDisc.filt) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrEcho ws) fs) f k len ->
  pipes_lpg (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrEcho ws) fs)) (fun j : nat => f (k + j)) 0 len.
Proof using.
  intros (Hok & Hlen & Hby). exists ws, fs. split; [reflexivity |].
  split; [exact Hok |]. split; [exact Hlen |].
  intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

Lemma pipes_lpcg_of_at (nm : list (bv 8)) (fs : list FileDisc.filt) (f : nat -> bv 8) (k len : nat) :
  FileDisc.uname nm ->
  UkSh.ush_line_at (FileDisc.LPipe (FileDisc.PrCatF nm) fs) f k len ->
  pipes_lpcg (FileDisc.uline_ws (FileDisc.LPipe (FileDisc.PrCatF nm) fs))
    (fun j : nat => f (k + j)) 0 len.
Proof using.
  intros Hu (Hok & Hlen & Hby). exists nm, fs. split; [exact Hu |]. split; [reflexivity |].
  split; [exact Hok |]. split; [exact Hlen |].
  intros j Hj. rewrite Nat.add_0_l. exact (Hby j Hj).
Qed.

(* a stage costs the line at least six bytes ([ | cat]), so at most
   sixteen stages fit it, at either producer and any filters *)
Lemma suf_filt_len_ge (F : FileDisc.filt) : 6 <= length (FileDisc.suf_filt F).
Proof using.
  destruct F as [| w]; [vm_compute; lia |].
  unfold FileDisc.suf_filt. cbn [FileDisc.filt_words length].
  rewrite wl_body_cons length_app.
  assert (Hg : length FileDisc.fd_w_grep = 4) by (vm_compute; reflexivity). lia.
Qed.

Lemma suf_filts_len_ge (fs : list FileDisc.filt) : 6 * length fs <= length (FileDisc.suf_filts fs).
Proof using.
  induction fs as [| F fs IH]; [cbn; lia |].
  rewrite FileDisc.suf_filts_cons length_app. pose proof (suf_filt_len_ge F). cbn [length]. lia.
Qed.

Lemma upls_fs_le (p : FileDisc.producer) (fs : list FileDisc.filt) :
  FileDisc.uline_ok (FileDisc.LPipe p fs) -> length fs <= 16.
Proof using.
  intros (_ & _ & _ & Hlm). rewrite line_bytes_pipe_length_fs in Hlm.
  pose proof (suf_filts_len_ge fs). unfold EchoDisc.line_max in Hlm. lia.
Qed.
