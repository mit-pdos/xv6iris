(* ===================================================================== *)
(*  PipesUline.v -- THE BRIDGE from the N-stage pipeline model's line     *)
(*  type [PipesDisc.pline'] to the shell loop's [FileDisc.uline] (cut C8).*)
(*                                                                       *)
(*  [UkSh.ush_line_at] -- the sh loop's line fact, which every era        *)
(*  shares -- reads three projections of a [FileDisc.uline]: the words,  *)
(*  the admissibility and the bytes.  The pipeline era's lines are        *)
(*  [LEcho ws] and [LPipe p n] (the producer [p] then [n] bare cats);    *)
(*  [uline_of_pl] is the injection (cut C9b: at every line, [cat f] as   *)
(*  a producer included), and the three projections agree with          *)
(*  [PipesDisc]'s own readings.  PURE.                                   *)
(*                                                                       *)
(*  AND THE CONVERSE the forked child needs: the loop's slot knows the    *)
(*  input's last body only by its WORDS and by [FileDisc.fline_ok] (some  *)
(*  admissible line's body), and the words of an N-stage pipeline         *)
(*  determine it ([fline_ok_pipes_words]) -- the bars are not words of a  *)
(*  command, so the command and the number of cats are the same.         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require FileDisc.
Require Import PipeDisc.
Require Import PipesDisc.
From stdpp Require Import list ssreflect.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  THE INJECTION                                                         *)
(* ===================================================================== *)
Definition uline_of_pl (l : pline') : FileDisc.uline :=
  match l with
  | LEcho' ws => FileDisc.LEcho ws
  | LPipes p n => FileDisc.LPipe p n
  end.

(* the era discipline [UkSh]'s [Dl] is instantiated at: the lines the
   application admits, and nothing else *)
Definition ush_line_pipes (lu : FileDisc.uline) : Prop :=
  exists l : pline', adm_echo l = true /\ lu = uline_of_pl l.

Lemma ush_line_pipes_cases (lu : FileDisc.uline) :
  ush_line_pipes lu ->
  (exists ws, lu = FileDisc.LEcho ws) \/ (exists ws n, lu = FileDisc.LPipe (PrEcho ws) n).
Proof using.
  intros (l & Ha & ->). destruct l as [ws | [ws | f] n]; cbn [uline_of_pl].
  - left. by exists ws.
  - right. by exists ws, n.
  - discriminate Ha.
Qed.

Lemma suf_pipecat_barcat : suf_pipecat = FileDisc.suf_barcat.
Proof using. by vm_compute. Qed.

Lemma suf_n_barcats (n : nat) : suf_n n = FileDisc.suf_barcats n.
Proof using.
  unfold suf_n, FileDisc.suf_barcats. rewrite suf_pipecat_barcat. reflexivity.
Qed.

(* (1) THE BODY and THE BYTES, at every line (cut C9b: the producer is
   the line's own, so [cat f | cat] is its own body) *)
Lemma line_body_of_pl_all (l : pline') :
  FileDisc.line_body (uline_of_pl l) = pl_body l.
Proof using.
  destruct l as [ws | p n]; [reflexivity |].
  cbn [uline_of_pl FileDisc.line_body pl_body]. by rewrite suf_n_barcats.
Qed.

Lemma line_body_of_pl (l : pline') :
  adm_echo l = true -> FileDisc.line_body (uline_of_pl l) = pl_body l.
Proof using. intros _. exact (line_body_of_pl_all l). Qed.

Lemma line_bytes_of_pl (l : pline') :
  adm_echo l = true -> FileDisc.line_bytes (uline_of_pl l) = pl_body l ++ [wl_nl].
Proof using.
  intros _. rewrite FileDisc.line_bytes_body (line_body_of_pl_all l). reflexivity.
Qed.

(* (2) ADMISSIBILITY, both ways *)
Lemma uline_ok_of_pl_all (l : pline') :
  pl_ok l -> FileDisc.uline_ok (uline_of_pl l).
Proof using.
  intros Hok. destruct l as [ws | p n]; [exact Hok |].
  destruct Hok as (Hp & Hn & Hlen).
  cbn [uline_of_pl FileDisc.uline_ok]. split; [exact Hp |]. split; [exact Hn |].
  rewrite FileDisc.line_bytes_body (line_body_of_pl_all (LPipes p n)) length_app.
  cbn [length]. lia.
Qed.

Lemma uline_ok_of_pl (l : pline') :
  adm_echo l = true -> pl_ok l -> FileDisc.uline_ok (uline_of_pl l).
Proof using. intros _ Hok. exact (uline_ok_of_pl_all l Hok). Qed.

Lemma pl_ok_of_uline (p : producer) (n : nat) :
  FileDisc.uline_ok (FileDisc.LPipe p n) -> pl_ok (LPipes p n).
Proof using.
  intros (Hp & Hn & Hlen). split; [exact Hp |]. split; [exact Hn |].
  rewrite -(line_body_of_pl_all (LPipes p n)).
  cbn [uline_of_pl]. rewrite FileDisc.line_bytes_body length_app in Hlen.
  cbn [length] in Hlen. lia.
Qed.

(* (3) THE WORDS: the whole body's parse *)
Lemma uline_ws_of_pl_all (l : pline') :
  pl_ok l -> FileDisc.uline_ws (uline_of_pl l) = wl_words (pl_body l).
Proof using.
  intros Hok. destruct l as [ws | p n].
  - cbn [uline_of_pl FileDisc.uline_ws pl_body].
    symmetry. exact (wl_words_body ws (line_ok_wf _ Hok)).
  - destruct Hok as (Hp & _ & _).
    rewrite -(line_body_of_pl_all (LPipes p n)).
    symmetry. exact (FileDisc.uline_ws_pipe p n Hp).
Qed.

Lemma uline_ws_of_pl (l : pline') :
  adm_echo l = true -> pl_ok l ->
  FileDisc.uline_ws (uline_of_pl l) = wl_words (pl_body l).
Proof using. intros _ Hok. exact (uline_ws_of_pl_all l Hok). Qed.

(* ===================================================================== *)
(*  THE WORDS OF A PIPELINE DETERMINE IT                                  *)
(* ===================================================================== *)

Lemma alnum_word_ne_bar (w : list (bv 8)) : Forall wl_alnum w -> w <> FileDisc.fd_w_bar.
Proof using.
  intros Hw ->. rewrite FileDisc.fd_w_bar_eq in Hw.
  apply Forall_cons_1 in Hw as [Hb _]. revert Hb.
  rewrite /wl_alnum. vm_compute. intros [H | [H | H]];
    destruct H as [H1 H2]; first [ by apply H1 | by apply H2 ].
Qed.

Lemma line_ok_no_bar (ws : list (list (bv 8))) :
  line_ok ws -> Forall (fun w => w <> FileDisc.fd_w_bar) ws.
Proof using.
  intros Hok. pose proof (wl_wf_alnum _ (line_ok_wf _ Hok)) as Ha.
  eapply Forall_impl; [exact Ha |]. intros w Hw. exact (alnum_word_ne_bar w Hw).
Qed.

(* ...nor has a [cat f] producer: [cat] and a word *)
Lemma prod_no_bar (p : producer) :
  prod_ok p -> Forall (fun w => w <> FileDisc.fd_w_bar) (prod_words p).
Proof using.
  intros Hok. pose proof (wl_wf_alnum _ (prod_wf p Hok)) as Ha.
  eapply Forall_impl; [exact Ha |]. intros w Hw. exact (alnum_word_ne_bar w Hw).
Qed.

Lemma w_barcats_head (n : nat) (w : list (bv 8)) (r : list (list (bv 8))) :
  FileDisc.w_barcats n = w :: r -> w = FileDisc.fd_w_bar.
Proof using.
  destruct n as [| m]; [discriminate |]. rewrite FileDisc.w_barcats_S. cbn [app].
  by intros [= <- _].
Qed.

Lemma w_barcats_inj (n n' : nat) :
  FileDisc.w_barcats n = FileDisc.w_barcats n' -> n = n'.
Proof using.
  intros H. apply (f_equal length) in H. rewrite !FileDisc.w_barcats_length in H. lia.
Qed.

Lemma barcats_split (ws ws' : list (list (bv 8))) (n n' : nat) :
  Forall (fun w => w <> FileDisc.fd_w_bar) ws ->
  Forall (fun w => w <> FileDisc.fd_w_bar) ws' ->
  ws ++ FileDisc.w_barcats n = ws' ++ FileDisc.w_barcats n' ->
  ws = ws' /\ n = n'.
Proof using.
  revert ws'. induction ws as [| x r IH]; intros ws' Hnb Hnb' Heq.
  - destruct ws' as [| y r'].
    + split; [reflexivity | exact (w_barcats_inj n n' Heq)].
    + exfalso. cbn [app] in Heq.
      apply Forall_cons_1 in Hnb' as [Hy _].
      exact (Hy (w_barcats_head n y (r' ++ FileDisc.w_barcats n') Heq)).
  - destruct ws' as [| y r'].
    + exfalso. cbn [app] in Heq.
      apply Forall_cons_1 in Hnb as [Hx _].
      exact (Hx (w_barcats_head n' x (r ++ FileDisc.w_barcats n) (eq_sym Heq))).
    + cbn [app] in Heq. injection Heq as <- Heq.
      apply Forall_cons_1 in Hnb as [_ Hnb]. apply Forall_cons_1 in Hnb' as [_ Hnb'].
      destruct (IH r' Hnb Hnb' Heq) as [-> ->]. by split.
Qed.

(* the producers' words determine them *)
Lemma prod_words_inj (p q : producer) :
  prod_ok p -> prod_ok q -> prod_words p = prod_words q -> p = q.
Proof using.
  intros Hp Hq Hw. destruct p as [ws | f], q as [ws' | f']; cbn [prod_words prod_ok] in *.
  - by subst.
  - exfalso. pose proof (line_ok_head ws Hp) as Hh. rewrite Hw in Hh.
    change (Some cmd_cat = Some cmd_echo) in Hh.
    exact (cmd_cat_ne_echo (inj Some _ _ Hh)).
  - exfalso. pose proof (line_ok_head ws' Hq) as Hh. rewrite -Hw in Hh.
    change (Some cmd_cat = Some cmd_echo) in Hh.
    exact (cmd_cat_ne_echo (inj Some _ _ Hh)).
  - injection Hw as ->. reflexivity.
Qed.

(* an admissible line whose words are an N-stage pipeline's IS that
   pipeline, at either producer *)
Lemma uline_pipes_words (l : FileDisc.uline) (p : producer) (n : nat) :
  FileDisc.uline_ok l -> prod_ok p -> 1 <= n ->
  wl_words (FileDisc.line_body l) = FileDisc.uline_ws (FileDisc.LPipe p n) ->
  l = FileDisc.LPipe p n.
Proof using.
  intros Hok Hp Hn Hw.
  destruct n as [| m]; [lia |].
  cbn [FileDisc.uline_ws] in Hw.
  destruct l as [ws' | ws' | | ws' n'].
  - (* LEcho: its words are alphanumeric, and the bar is not *)
    exfalso. cbn [FileDisc.line_body] in Hw.
    rewrite (wl_words_body ws' (line_ok_wf _ Hok)) in Hw.
    pose proof (line_ok_no_bar ws' Hok) as Hnb. rewrite Hw in Hnb.
    rewrite FileDisc.w_barcats_S in Hnb.
    apply Forall_app in Hnb as [_ Hnb]. apply Forall_cons_1 in Hnb as [Hbar _].
    exact (Hbar eq_refl).
  - (* LEchoF: the two suffixes line up and `>' is not the bar *)
    exfalso. destruct Hok as [Hok' _].
    rewrite (FileDisc.uline_ws_gtf ws' Hok') in Hw. cbn [FileDisc.uline_ws] in Hw.
    rewrite FileDisc.w_barcats_S_r in Hw.
    replace (ws' ++ [FileDisc.fd_w_gt; FileDisc.fname_f])
      with ((ws' ++ [FileDisc.fd_w_gt]) ++ [FileDisc.fname_f]) in Hw
      by (rewrite -app_assoc; reflexivity).
    replace (prod_words p ++ FileDisc.w_barcats m ++ [FileDisc.fd_w_bar; FileDisc.fd_w_cat])
      with (((prod_words p ++ FileDisc.w_barcats m) ++ [FileDisc.fd_w_bar]) ++ [FileDisc.fd_w_cat])
      in Hw by (rewrite -!app_assoc; reflexivity).
    apply app_inj_tail in Hw as [Hw _].
    apply app_inj_tail in Hw as [_ Hgt]. discriminate Hgt.
  - (* LCat: two words, while a pipeline has at least four *)
    exfalso. cbn [FileDisc.line_body] in Hw.
    apply (f_equal length) in Hw. rewrite length_app FileDisc.w_barcats_length in Hw.
    pose proof (FileDisc.prod_words_ge2 p Hp) as H2.
    revert Hw. vm_compute (length (wl_words FileDisc.cmd_cat_f)). lia.
  - (* LPipe: the words determine the producer and the cats *)
    destruct Hok as (Hok' & Hn' & _).
    rewrite (FileDisc.uline_ws_pipe ws' n' Hok') in Hw. cbn [FileDisc.uline_ws] in Hw.
    destruct (barcats_split (prod_words ws') (prod_words p) n' (S m) (prod_no_bar ws' Hok')
                (prod_no_bar p Hp) Hw) as [Hpw ->].
    by rewrite (prod_words_inj ws' p Hok' Hp Hpw).
Qed.

(* a body some admissible line has, whose words are an N-stage pipeline's,
   IS that pipeline's body *)
Lemma fline_ok_pipes_words_p (b : list (bv 8)) (p : producer) (n : nat) :
  FileDisc.fline_ok b -> prod_ok p -> 1 <= n ->
  wl_words b = FileDisc.uline_ws (FileDisc.LPipe p n) ->
  b = FileDisc.line_body (FileDisc.LPipe p n).
Proof using.
  intros (l & Hok & ->) Hp Hn Hw. by rewrite (uline_pipes_words l p n Hok Hp Hn Hw).
Qed.

Lemma fline_ok_pipes_words (b : list (bv 8)) (ws : list (list (bv 8))) (n : nat) :
  FileDisc.fline_ok b -> line_ok ws -> 1 <= n ->
  wl_words b = FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) n) ->
  b = FileDisc.line_body (FileDisc.LPipe (PrEcho ws) n).
Proof using. exact (fline_ok_pipes_words_p b (PrEcho ws) n). Qed.

(* ...AND THE MODEL READS IT AS THAT LINE *)
Lemma pl_of_pipe_body (ws : list (list (bv 8))) (n : nat) :
  pl_ok (LPipes (PrEcho ws) n) ->
  pl_of (FileDisc.line_body (FileDisc.LPipe (PrEcho ws) n)) = LPipes (PrEcho ws) n.
Proof using.
  intros Hok.
  rewrite (_ : FileDisc.LPipe (PrEcho ws) n = uline_of_pl (LPipes (PrEcho ws) n)); [| reflexivity].
  rewrite (line_body_of_pl (LPipes (PrEcho ws) n) eq_refl).
  exact (pl_of_body _ Hok).
Qed.

(* the admissibility of a pipeline line, read back from the loop's *)
Lemma pl_ok_of_uline_pipe (ws : list (list (bv 8))) (n : nat) :
  FileDisc.uline_ok (FileDisc.LPipe (PrEcho ws) n) -> pl_ok (LPipes (PrEcho ws) n).
Proof using. exact (pl_ok_of_uline (PrEcho ws) n). Qed.
