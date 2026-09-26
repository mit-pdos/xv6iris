(* ===================================================================== *)
(*  PipesUline.v -- THE BRIDGE from the N-stage pipeline model's line     *)
(*  type [PipesDisc.pline'] to the shell loop's [FileDisc.uline] (cut C8).*)
(*                                                                       *)
(*  [UkSh.ush_line_at] -- the sh loop's line fact, which every era        *)
(*  shares -- reads three projections of a [FileDisc.uline]: the words,  *)
(*  the admissibility and the bytes.  The pipeline era's lines are        *)
(*  [LEcho ws] and [LPipe p fs] (the producer [p] then its filter        *)
(*  stages [fs], cut G3);                                                 *)
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
  | LPipes p fs => FileDisc.LPipe p fs
  end.

(* the era discipline [UkSh]'s [Dl] is instantiated at: the lines the
   application admits, and nothing else *)
Definition ush_line_pipes (lu : FileDisc.uline) : Prop :=
  exists l : pline', adm_echo l = true /\ lu = uline_of_pl l.

Lemma ush_line_pipes_cases (lu : FileDisc.uline) :
  ush_line_pipes lu ->
  (exists ws, lu = FileDisc.LEcho ws) \/ (exists ws fs, lu = FileDisc.LPipe (PrEcho ws) fs).
Proof using.
  intros (l & Ha & ->). destruct l as [ws | [ws | f] fs]; cbn [uline_of_pl].
  - left. by exists ws.
  - right. by exists ws, fs.
  - discriminate Ha.
Qed.

Lemma suf_pipecat_barcat : suf_pipecat = FileDisc.suf_barcat.
Proof using. by vm_compute. Qed.

(* (1) THE BODY and THE BYTES, at every line (cut C9b: the producer is
   the line's own, so [cat f | cat] is its own body) *)
Lemma line_body_of_pl_all (l : pline') :
  FileDisc.line_body (uline_of_pl l) = pl_body l.
Proof using. destruct l as [ws | p fs]; reflexivity. Qed.

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
  intros Hok. destruct l as [ws | p fs]; [exact Hok |].
  destruct Hok as (Hp & Hn & HF & Hlen).
  cbn [uline_of_pl FileDisc.uline_ok]. split; [exact Hp |]. split; [exact Hn |].
  split; [exact HF |].
  rewrite FileDisc.line_bytes_body (line_body_of_pl_all (LPipes p fs)) length_app.
  cbn [length]. lia.
Qed.

Lemma uline_ok_of_pl (l : pline') :
  adm_echo l = true -> pl_ok l -> FileDisc.uline_ok (uline_of_pl l).
Proof using. intros _ Hok. exact (uline_ok_of_pl_all l Hok). Qed.

Lemma pl_ok_of_uline (p : producer) (fs : list filt) :
  FileDisc.uline_ok (FileDisc.LPipe p fs) -> pl_ok (LPipes p fs).
Proof using.
  intros (Hp & Hn & HF & Hlen). split; [exact Hp |]. split; [exact Hn |]. split; [exact HF |].
  rewrite -(line_body_of_pl_all (LPipes p fs)).
  cbn [uline_of_pl]. rewrite FileDisc.line_bytes_body length_app in Hlen.
  cbn [length] in Hlen. lia.
Qed.

(* (3) THE WORDS: the whole body's parse *)
Lemma uline_ws_of_pl_all (l : pline') :
  pl_ok l -> FileDisc.uline_ws (uline_of_pl l) = wl_words (pl_body l).
Proof using.
  intros Hok. destruct l as [ws | p fs].
  - cbn [uline_of_pl FileDisc.uline_ws pl_body].
    symmetry. exact (wl_words_body ws (line_ok_wf _ Hok)).
  - destruct Hok as (Hp & _ & HF & _).
    rewrite -(line_body_of_pl_all (LPipes p fs)).
    symmetry. exact (FileDisc.uline_ws_pipe p fs Hp HF).
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

(* ...and a word of name bytes (cut W4): the dot is not the bar either *)
Lemma fn_word_ne_bar (w : list (bv 8)) : fn_word w -> w <> FileDisc.fd_w_bar.
Proof using.
  intros [_ Hw] ->. rewrite FileDisc.fd_w_bar_eq in Hw.
  apply Forall_cons_1 in Hw as [Hb _]. apply fn_byte_val in Hb.
  assert (Hbar : bv_unsigned FileDisc.fd_bar = 124%Z) by (vm_compute; reflexivity).
  rewrite Hbar in Hb. lia.
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
  intros Hok. pose proof (prod_wf p Hok) as Ha.
  eapply Forall_impl; [exact Ha |]. intros w Hw. exact (fn_word_ne_bar w Hw).
Qed.

(* A WORD LIST WITH NO BAR, FOLLOWED BY NOTHING OR BY A BAR, splits
   there: the command's words end at the first bar *)
Lemma nobar_split (a a' X X' : list (list (bv 8))) :
  Forall (fun w => w <> FileDisc.fd_w_bar) a -> Forall (fun w => w <> FileDisc.fd_w_bar) a' ->
  head X = None \/ head X = Some FileDisc.fd_w_bar ->
  head X' = None \/ head X' = Some FileDisc.fd_w_bar ->
  a ++ X = a' ++ X' -> a = a' /\ X = X'.
Proof using.
  revert a'. induction a as [| x r IH]; intros a' Ha Ha' HX HX' Heq.
  - destruct a' as [| y r']; [split; [reflexivity | exact Heq] |].
    exfalso. cbn [app] in Heq. apply Forall_cons_1 in Ha' as [Hy _].
    destruct HX as [HX | HX]; rewrite Heq in HX; cbn [head] in HX; [discriminate HX |].
    injection HX as HX. exact (Hy HX).
  - destruct a' as [| y r'].
    + exfalso. cbn [app] in Heq. apply Forall_cons_1 in Ha as [Hx _].
      destruct HX' as [HX' | HX']; rewrite -Heq in HX'; cbn [head] in HX'; [discriminate HX' |].
      injection HX' as HX'. exact (Hx HX').
    + cbn [app] in Heq. injection Heq as <- Heq.
      apply Forall_cons_1 in Ha as [_ Ha]. apply Forall_cons_1 in Ha' as [_ Ha'].
      destruct (IH r' Ha Ha' HX HX' Heq) as [-> ->]. by split.
Qed.

Lemma filt_words_no_bar (F : filt) :
  filt_ok F -> Forall (fun w => w <> FileDisc.fd_w_bar) (filt_words F).
Proof using.
  intros HF. pose proof (wl_wf_alnum _ (FileDisc.filt_wf F HF)) as Ha.
  eapply Forall_impl; [exact Ha |]. intros w Hw. exact (alnum_word_ne_bar w Hw).
Qed.

Lemma w_filts_head (fs : list filt) :
  head (FileDisc.w_filts fs) = None \/ head (FileDisc.w_filts fs) = Some FileDisc.fd_w_bar.
Proof using. destruct fs as [| F fs]; [by left | by right]. Qed.

(* the stage words determine the stages *)
Lemma w_filts_inj (fs fs' : list filt) :
  Forall filt_ok fs -> Forall filt_ok fs' -> FileDisc.w_filts fs = FileDisc.w_filts fs' -> fs = fs'.
Proof using.
  revert fs'. induction fs as [| F fs IH]; intros fs' HF HF' Heq.
  - destruct fs' as [| F' fs']; [reflexivity | discriminate Heq].
  - destruct fs' as [| F' fs']; [discriminate Heq |].
    apply Forall_cons_1 in HF as [HF1 HF]. apply Forall_cons_1 in HF' as [HF1' HF'].
    rewrite !FileDisc.w_filts_cons in Heq. cbn [app] in Heq. injection Heq as Heq.
    destruct (nobar_split _ _ _ _ (filt_words_no_bar F HF1) (filt_words_no_bar F' HF1')
                (w_filts_head fs) (w_filts_head fs') Heq) as [Hw Hr].
    rewrite (IH fs' HF HF' Hr). f_equal.
    destruct F as [| w], F' as [| w']; cbn [filt_words] in Hw; try discriminate Hw.
    + reflexivity.
    + inversion Hw; subst; reflexivity.
Qed.

Lemma barcats_split (ws ws' : list (list (bv 8))) (fs fs' : list filt) :
  Forall (fun w => w <> FileDisc.fd_w_bar) ws ->
  Forall (fun w => w <> FileDisc.fd_w_bar) ws' ->
  Forall filt_ok fs -> Forall filt_ok fs' ->
  ws ++ FileDisc.w_filts fs = ws' ++ FileDisc.w_filts fs' ->
  ws = ws' /\ fs = fs'.
Proof using.
  intros Hnb Hnb' HF HF' Heq.
  destruct (nobar_split _ _ _ _ Hnb Hnb' (w_filts_head fs) (w_filts_head fs') Heq) as [-> Hw].
  split; [reflexivity | exact (w_filts_inj fs fs' HF HF' Hw)].
Qed.

(* a pipeline's words hold the bar *)
Lemma w_filts_bar (fs : list filt) : fs <> [] -> FileDisc.fd_w_bar ∈ FileDisc.w_filts fs.
Proof using.
  destruct fs as [| F fs]; [by intros H; destruct (H eq_refl) |]. intros _.
  rewrite FileDisc.w_filts_cons. apply elem_of_app. left. apply elem_of_list_here.
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
   pipeline, at either producer: an echo line, a redirect and [cat f]
   have no bar among their words, and a pipeline's words are split at its
   bars *)
Lemma uline_pipes_words (l : FileDisc.uline) (p : producer) (fs : list filt) :
  FileDisc.uline_ok l -> prod_ok p -> fs <> [] -> Forall filt_ok fs ->
  wl_words (FileDisc.line_body l) = FileDisc.uline_ws (FileDisc.LPipe p fs) ->
  l = FileDisc.LPipe p fs.
Proof using.
  intros Hok Hp Hn HF Hw.
  pose proof (w_filts_bar fs Hn) as Hbar.
  assert (Hin : FileDisc.fd_w_bar ∈ wl_words (FileDisc.line_body l)).
  { rewrite Hw. cbn [FileDisc.uline_ws]. apply elem_of_app. right. exact Hbar. }
  destruct l as [ws' | ws' N' | N' | ws' fs' | ws'].
  5: { (* LSecc: its words are file-name words, and the bar is not *)
       exfalso. rewrite (FileDisc.uline_ws_body _ Hok) in Hin. cbn [FileDisc.uline_ws] in Hin.
       assert (Hnb : ~ fn_word FileDisc.fd_w_bar)
         by (apply (bool_decide_unpack _); vm_compute; exact I).
       exact (Hnb (proj1 (Forall_forall _ _) (FileDisc.secc_ok_wf ws' Hok) _ Hin)). }
  - (* LEcho: its words are alphanumeric, and the bar is not *)
    exfalso. cbn [FileDisc.line_body] in Hin.
    rewrite (wl_words_body ws' (line_ok_wf _ Hok)) in Hin.
    exact (proj1 (Forall_forall _ _) (line_ok_no_bar ws' Hok) _ Hin eq_refl).
  - (* LEchoF: the command's words, `>' and [f] *)
    exfalso. destruct Hok as (Hok' & Hu' & _).
    rewrite (FileDisc.uline_ws_gtf ws' N' Hok' Hu') in Hin.
    cbn [FileDisc.uline_ws] in Hin.
    apply elem_of_app in Hin as [Hin | Hin].
    + exact (proj1 (Forall_forall _ _) (line_ok_no_bar ws' Hok') _ Hin eq_refl).
    + apply elem_of_cons in Hin as [Hin | Hin].
      * apply (f_equal (fun w : list (bv 8) => bv_unsigned (w !!! 0%nat))) in Hin.
        vm_compute in Hin. discriminate Hin.
      * apply elem_of_list_singleton in Hin.
        exact (fn_word_ne_bar N' (FileDisc.uname_lex N' Hu') (eq_sym Hin)).
  - (* LCat: [cat] and [N] *)
    exfalso. cbn [FileDisc.line_body] in Hin.
    rewrite (FileDisc.cat_words_N N' (FileDisc.uname_lex N' Hok)) in Hin.
    apply elem_of_cons in Hin as [Hin | Hin].
    + apply (f_equal (fun w : list (bv 8) => bv_unsigned (w !!! 0%nat))) in Hin.
        vm_compute in Hin. discriminate Hin.
    + apply elem_of_list_singleton in Hin.
      exact (fn_word_ne_bar N' (FileDisc.uname_lex N' Hok) (eq_sym Hin)).
  - (* LPipe: the words determine the producer and the stages *)
    destruct Hok as (Hok' & Hn' & HF' & _).
    rewrite (FileDisc.uline_ws_pipe ws' fs' Hok' HF') in Hw. cbn [FileDisc.uline_ws] in Hw.
    destruct (barcats_split (prod_words ws') (prod_words p) fs' fs (prod_no_bar ws' Hok')
                (prod_no_bar p Hp) HF' HF Hw) as [Hpw ->].
    by rewrite (prod_words_inj ws' p Hok' Hp Hpw).
Qed.

(* a body some admissible line has, whose words are an N-stage pipeline's,
   IS that pipeline's body *)
Lemma fline_ok_pipes_words_p (b : list (bv 8)) (p : producer) (fs : list filt) :
  FileDisc.fline_ok b -> prod_ok p -> fs <> [] -> Forall filt_ok fs ->
  wl_words b = FileDisc.uline_ws (FileDisc.LPipe p fs) ->
  b = FileDisc.line_body (FileDisc.LPipe p fs).
Proof using.
  intros (l & Hok & ->) Hp Hn HF Hw. by rewrite (uline_pipes_words l p fs Hok Hp Hn HF Hw).
Qed.

Lemma fline_ok_pipes_words (b : list (bv 8)) (ws : list (list (bv 8))) (fs : list filt) :
  FileDisc.fline_ok b -> line_ok ws -> fs <> [] -> Forall filt_ok fs ->
  wl_words b = FileDisc.uline_ws (FileDisc.LPipe (PrEcho ws) fs) ->
  b = FileDisc.line_body (FileDisc.LPipe (PrEcho ws) fs).
Proof using. exact (fline_ok_pipes_words_p b (PrEcho ws) fs). Qed.

(* ...AND THE MODEL READS IT AS THAT LINE *)
Lemma pl_of_pipe_body (ws : list (list (bv 8))) (fs : list filt) :
  pl_ok (LPipes (PrEcho ws) fs) ->
  pl_of (FileDisc.line_body (FileDisc.LPipe (PrEcho ws) fs)) = LPipes (PrEcho ws) fs.
Proof using.
  intros Hok.
  rewrite (_ : FileDisc.LPipe (PrEcho ws) fs = uline_of_pl (LPipes (PrEcho ws) fs)); [| reflexivity].
  rewrite (line_body_of_pl_all (LPipes (PrEcho ws) fs)).
  exact (pl_of_body _ Hok).
Qed.

(* the admissibility of a pipeline line, read back from the loop's *)
Lemma pl_ok_of_uline_pipe (ws : list (list (bv 8))) (fs : list filt) :
  FileDisc.uline_ok (FileDisc.LPipe (PrEcho ws) fs) -> pl_ok (LPipes (PrEcho ws) fs).
Proof using. exact (pl_ok_of_uline (PrEcho ws) fs). Qed.
