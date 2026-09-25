(* FileDisc.v -- THE FILE APPLICATION'S PURE MODEL: the lines the user may
   type ([echo w1 .. wn], [echo w1 .. wn > f], [cat f]), the file state each
   round leaves behind, and the console transcript the session calls for.
   Iris-free, over [EchoDisc]/[LineWords]/[FileState], so the claim can be
   read -- and refuted -- without opening the logic.

   Design of record: claude-notes/design/app-file.md section 1; the state
   vocabulary ([fstate], [echo_chunks], [sel_ok], [subseq]) is [FileState.v],
   which the claim reads too.

   WHAT THIS FILE IS.  [EchoDisc] models a session in which every round is
   one echo line and the only state is the console's.  Here a round is one
   of THREE line shapes and carries a second state -- the file [f] -- which
   SURVIVES the round, the era and the power cycle.  So the session
   function threads it: [sessf ps cs s0 I] is [EchoDisc.sess] with the
   per-round block computed at the state the previous rounds left
   ([fstate_upto]), and [file_phi] is the whole-history claim, one boot state
   per cycle, each admissible for what earlier cycles typed.

   THE OBSERVER STILL CANNOT SEE THE FILE, and does not need to.  Two
   resolutions that print the same bytes may leave different files
   ([RFOpenU] against [RFOpenM]), and two different files may print the
   same bytes ([RCRan] at an absent f against [RCNoOpen]).  So the
   determinacy theorem [sessf_prefix_det] -- the twin of
   [EchoOutPure.sess_prefix_det], which is what the stage spends --
   concludes an equality of BYTES and never of states or indices.  Its
   engine is one observation, not a table: EVERY alternative's own output
   is either sh's panic line "fork\n" or a '$'-free run followed by the
   prompt, and no content, no line and no diagnostic carries a '$'.  So two
   alternatives below one wire agree by [fd_dollar_split], whatever they
   are, and only the panic alternative -- which re-enters init's prologue
   instead of printing a prompt -- needs an argument of its own.

   WHERE THIS FILE DEPARTS FROM design section 1, each departure reported
   in claude-notes/projects/app-file.md under Findings:

   - [parse_line] inverts [line_body] (the body [LineWords.bodies_of]
     cuts), NOT [line_bytes] (which carries the closing newline the cut has
     already stripped): [parse_line (line_bytes l) = Some l] is false at
     every [l], e.g. [parse_line (line_bytes LCat) = parse_line (sb "cat
     f\n") = None].  [line_bytes l = line_body l ++ [wl_nl]] is kept.
   - the partial line of a disciplined input is [fbody_byte], which admits
     '>' beside [LineWords.wl_body_byte]'s alphanumerics and blank -- the
     user typing [echo hi > f] is mid-line at [echo hi >], and the old
     predicate refutes that byte.
   - [fsm]'s [RFOpenM] keeps design section 1's guard "only at an absent
     f": at a PRESENT f xv6's [sys_open] truncates only after [filealloc]
     has succeeded (kernel/sysfile.c), so at [Some bs] this alternative
     leaves the file alone and is [RFOpenU].
   - [good_out_f] takes no [Ls]: the admissible-boot condition is
     [file_phi]'s own conjunct and nothing in the per-cycle claim reads it.
   - [file_phi]'s "the first cycle boots absent" is stated as a GUARDED
     clause: [forall s, s0s !! 0 = Some s -> s = None].  The design's
     [s0s !! 0 = Some None] is refuted at the empty history, where
     [cycles_of [] = []] forces [length s0s = 0]. *)
From Stdlib Require Import ZArith Lia List String.
From Stdlib Require Import Sorted.        (* [StronglySorted], [sel_ok]'s order *)
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of] *)
Require Import LineWords.        (* the word line and the parser *)
Require Import EchoDisc.         (* the console discipline this one extends *)
Require Export LineBytes.        (* [nodollar], the byte facts every model reads *)
Require Import LineModel.        (* the line model this one instantiates *)
Require Export FileState.        (* [fstate], [echo_chunks], [sel_ok], [subseq] *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST AND PREFIX FACTS                                        *)
(* ====================================================================== *)

Lemma fd_app_inv_tail {A} (u v w : list A) : u ++ w = v ++ w -> u = v.
Proof. intro H. exact (app_inv_tail w u v H). Qed.


(* ====================================================================== *)
(*  1.  THE LINES THE USER MAY TYPE                                        *)
(* ====================================================================== *)

(* the ONE file name of the model -- generalising to a name is an index,
   not a redesign *)
Definition fname_f : list (bv 8) := sb "f"%string.

(* sh's lexer sees '>' as a symbol token; the redirect is CANONICAL -- one
   blank each side, at the end of the line -- which is the shape the sh
   walk (design section 5.1) is stated at *)
Definition suf_gtf : list (bv 8) := sb " > f"%string.
Definition cmd_cat_f : list (bv 8) := sb "cat f"%string.

(* ---- THE PIPELINE APPLICATION'S LINE (lane ULINE-LPIPE) --------------- *)
(* sh's lexer sees the bar as a symbol token; the pipeline is CANONICAL --
   one blank each side, and the right-hand command is the single word
   [cat] with no argument -- which is the shape the sh walk (app-pipe
   design section 5.1) is stated at.  These are [PipeDisc]'s [wl_bar] and
   [suf_pipecat] spelled again here, because [PipeDisc] reads this file
   and not the other way round; [PipeDisc.uline_of_pline] proves the two
   readings equal.

   WHY THE CONSTRUCTOR IS HERE AND NOT IN A SIBLING TYPE.
   [UkSh.ush_line_at] -- the sh loop's line fact, which every era shares --
   reads exactly three projections of [uline] ([uline_ok], [line_bytes]
   and, through [ush_rest_line_at], [uline_ws]), so an era whose lines are
   not [uline]s cannot use the loop at all.  [parse_line] is UNTOUCHED, so
   it never answers [LPipe] ([parse_line_not_pipe]), [lines_of]'s range is
   exactly the three it was, and every FILE statement quantified over
   [disc_input_f] means what it meant.  The price is the guard
   [uline_nopipe] on the three round-trip lemmas below, which say that the
   model's lines ARE the parser's range and are therefore false at a
   constructor outside it. *)
Definition fd_bar : bv 8 := Z_to_bv 8 124%Z.
Definition fd_w_gt : list (bv 8) := sb ">"%string.
Definition fd_w_bar : list (bv 8) := sb "|"%string.
Definition fd_w_cat : list (bv 8) := sb "cat"%string.
Definition suf_barcat : list (bv 8) := sb " | cat"%string.

(* ---- THE PRODUCER of a pipeline (cut C9b, moved down from [PipesDisc]):
   the first command, [echo w1 .. wk] (the words [ws], command name
   included) or [cat f].  It lives HERE because the shell loop's line type
   [uline] names it ([LPipe p n]), so that [cat f | cat] lexes exactly as
   sh reads it; [PipesDisc] re-exports these names. *)
Inductive producer :=
  | PrEcho (ws : list (list (bv 8)))
  | PrCatF (f : list (bv 8)).

Global Instance producer_eq_dec : EqDecision producer.
Proof using. solve_decision. Defined.

Definition prod_words (p : producer) : list (list (bv 8)) :=
  match p with PrEcho ws => ws | PrCatF f => [fd_w_cat; f] end.
Definition prod_body (p : producer) : list (bv 8) := wl_body (prod_words p).

(* an admissible producer: an admissible echo line, or [cat] of a word *)
Definition prod_ok (p : producer) : Prop :=
  match p with PrEcho ws => line_ok ws | PrCatF f => wl_word f end.

Global Instance prod_ok_dec p : Decision (prod_ok p).
Proof using. destruct p; unfold prod_ok; apply _. Defined.

Lemma fd_w_cat_word : wl_word fd_w_cat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma prod_wf (p : producer) : prod_ok p -> wl_wf (prod_words p).
Proof using.
  destruct p as [ws | f]; cbn [prod_ok prod_words]; intros H.
  - exact (line_ok_wf ws H).
  - unfold wl_wf. constructor; [exact fd_w_cat_word | constructor; [exact H | constructor]].
Qed.

Lemma prod_body_bytes p : prod_ok p -> Forall wl_body_byte (prod_body p).
Proof using. intros Hp. exact (wl_body_bytes _ (prod_wf p Hp)). Qed.

Lemma prod_words_ge2 p : prod_ok p -> (2 <= length (prod_words p))%nat.
Proof using. destruct p as [ws | f]; cbn [prod_ok prod_words length]; [exact (line_ok_ge2 ws) | lia]. Qed.

Lemma prod_words_ne p : prod_ok p -> prod_words p <> [].
Proof using. intros Hp He. pose proof (prod_words_ge2 p Hp) as H. rewrite He in H. cbn in H. lia. Qed.

(* ---- THE FILTER STAGES of a pipeline (cut G3; design
   claude-notes/design/grep-pipes.md section 2): every stage after the
   producer is [cat] or [grep w].  They live HERE beside [producer] for the
   same reason: the shell loop's line type names them ([LPipe p fs]). *)
Inductive filt :=
  | FCat
  | FGrep (pat : list (bv 8)).

Global Instance filt_eq_dec : EqDecision filt.
Proof using. solve_decision. Defined.

Definition fd_w_grep : list (bv 8) := sb "grep"%string.

(* the stage's words, command name included *)
Definition filt_words (F : filt) : list (list (bv 8)) :=
  match F with FCat => [fd_w_cat] | FGrep w => [fd_w_grep; w] end.

(* an admissible filter: [cat], or [grep] of one alphanumeric word *)
Definition filt_ok (F : filt) : Prop :=
  match F with FCat => True | FGrep w => wl_word w end.

Global Instance filt_ok_dec F : Decision (filt_ok F).
Proof using. destruct F; unfold filt_ok; apply _. Defined.

(* the writer-is-a-cat flag (a cat's halt prints, a grep's does not) *)
Definition filt_is_cat (F : filt) : bool :=
  match F with FCat => true | FGrep _ => false end.

(* [n] bare cats, and the all-cat test the admissions ask *)
Definition cats (n : nat) : list filt := replicate n FCat.
Definition all_cats (fs : list filt) : bool := forallb filt_is_cat fs.

Lemma cats_length (n : nat) : length (cats n) = n.
Proof using. apply length_replicate. Qed.

Lemma cats_S (n : nat) : cats (S n) = FCat :: cats n.
Proof using. reflexivity. Qed.

Lemma cats_ne (n : nat) : (1 <= n)%nat -> cats n <> [].
Proof using. destruct n as [| n]; [lia | discriminate]. Qed.

Lemma cats_inj (n m : nat) : cats n = cats m -> n = m.
Proof using. intros H. apply (f_equal length) in H. rewrite !cats_length in H. exact H. Qed.

Lemma all_cats_cats (n : nat) : all_cats (cats n) = true.
Proof using. induction n as [| n IH]; [reflexivity | exact IH]. Qed.

Lemma all_cats_cons (F : filt) (fs : list filt) :
  all_cats (F :: fs) = true <-> F = FCat /\ all_cats fs = true.
Proof using.
  unfold all_cats. destruct F; cbn [forallb filt_is_cat andb]; split.
  - intros H. split; [reflexivity | exact H].
  - intros [_ H]. exact H.
  - intros H. discriminate H.
  - intros [H _]. discriminate H.
Qed.

Lemma all_cats_eq (fs : list filt) : all_cats fs = true -> fs = cats (length fs).
Proof using.
  induction fs as [| F fs IH]; intros H; [reflexivity |].
  apply all_cats_cons in H as [-> H]. cbn [length]. rewrite cats_S -(IH H). reflexivity.
Qed.

Lemma fd_w_grep_word : wl_word fd_w_grep.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma filt_wf (F : filt) : filt_ok F -> wl_wf (filt_words F).
Proof using.
  destruct F as [| w]; cbn [filt_ok filt_words]; intros H.
  - constructor; [exact fd_w_cat_word | constructor].
  - constructor; [exact fd_w_grep_word | constructor; [exact H | constructor]].
Qed.

Lemma filt_words_ne (F : filt) : filt_words F <> [].
Proof using. by destruct F. Qed.

(* the suffix one stage adds: the canonical bar, then the stage's words *)
Definition suf_filt (F : filt) : list (bv 8) :=
  wl_sp :: fd_bar :: wl_sp :: wl_body (filt_words F).
Definition suf_filts (fs : list filt) : list (bv 8) := concat (map suf_filt fs).
Definition w_filts (fs : list filt) : list (list (bv 8)) :=
  concat (map (fun F => fd_w_bar :: filt_words F) fs).

Lemma suf_filts_cons (F : filt) (fs : list filt) :
  suf_filts (F :: fs) = suf_filt F ++ suf_filts fs.
Proof using. reflexivity. Qed.

Lemma w_filts_cons (F : filt) (fs : list filt) :
  w_filts (F :: fs) = (fd_w_bar :: filt_words F) ++ w_filts fs.
Proof using. reflexivity. Qed.

(* [n] times the suffix, and its [n] times two words (cut C8: the pipeline
   is its producer followed by [n] bare cats) *)
Definition suf_barcats (n : nat) : list (bv 8) := concat (replicate n suf_barcat).
Definition w_barcats (n : nat) : list (list (bv 8)) :=
  concat (replicate n [fd_w_bar; fd_w_cat]).

Inductive uline :=
  | LEcho (ws : list (list (bv 8)))
  | LEchoF (ws : list (list (bv 8)))
  | LCat
  | LPipe (p : producer) (fs : list filt).

Global Instance uline_eq_dec : EqDecision uline.
Proof using. solve_decision. Defined.
Global Instance uline_inhabited : Inhabited uline := populate (LEcho []).

(* [LCat]'s WORDS ARE ITS OWN (lane SH-CHILD-2's ruling).  The arm used to
   be [[]], which is the word list of NO line -- and the command loop's
   line fact says the buffer holds the bytes of a line whose words are the
   ones the process state is indexed by, so an empty list there makes the
   cat arm say the wrong thing about the buffer.  [wl_words cmd_cat_f] is
   what the line lexes to (lane SH-LEX-REDIR: the cat line is symbol-free
   and two words), and at it [file_gets_holds] holds at all three
   constructors. *)
Definition uline_ws (l : uline) : list (list (bv 8)) :=
  match l with
  | LEcho ws => ws
  (* the WHOLE body's words, as at [LPipe] below (RULING SLOT-WS, option
     B): the arm used to be [ws], which is not what the line lexes to --
     [echo a > f] is FOUR blank-separated words -- so [UkSh]'s
     [Hdsc_line] was unprovable at a redirect line.  [uline_ws_gtf] is
     the equation.  A CLEANUP IS OWED (design/app-file.md, RULING
     SLOT-WS): the better interface has the sh loop's fork assertion
     speak the PARSED line, and then this function need not mirror the
     lexer at all. *)
  | LEchoF ws => ws ++ [fd_w_gt; fname_f]
  | LCat => wl_words cmd_cat_f
  (* the WHOLE body's words, which is what [UkSh]'s [Hdsc_line] demands
     ([uline_ws lu = wl_words (rest_of I)]); [PipeDisc.pline_ws] is the
     LEFT command's alone and cannot be reused here.  The two words are
     the bar and [cat]; [uline_ws_pipe] below is the equation. *)
  | LPipe p fs => prod_words p ++ w_filts fs
  end.

(* THE BODY the console cut keeps, and the LINE the user typed: the body
   and the newline [gets] stops at.  [line_bytes (LEcho ws)] is
   [LineWords.wl_line ws] on the nose. *)
Definition line_body (l : uline) : list (bv 8) :=
  match l with
  | LEcho ws => wl_body ws
  | LEchoF ws => wl_body ws ++ suf_gtf
  | LCat => cmd_cat_f
  | LPipe p fs => prod_body p ++ suf_filts fs
  end.

Definition line_bytes (l : uline) : list (bv 8) := line_body l ++ [wl_nl].

Lemma line_bytes_echo ws : line_bytes (LEcho ws) = wl_line ws.
Proof using. reflexivity. Qed.

Lemma line_bytes_body l : line_bytes l = line_body l ++ [wl_nl].
Proof using. reflexivity. Qed.

Definition uline_ok (l : uline) : Prop :=
  match l with
  | LEcho ws => line_ok ws
  | LEchoF ws => line_ok ws /\ (length (line_bytes (LEchoF ws)) < line_max)%nat
  | LCat => True
  | LPipe p fs =>
      prod_ok p /\ fs <> [] /\ Forall filt_ok fs
      /\ (length (line_bytes (LPipe p fs)) < line_max)%nat
  end.

Global Instance uline_ok_dec l : Decision (uline_ok l).
Proof using. destruct l; rewrite /uline_ok; apply _. Defined.

(* ---- THE PIPE LINE'S WORDS ARE ITS BODY'S PARSE ---------------------- *)
(* [uline_ws (LPipe ws)] is spelled as the left command's words plus the
   two the suffix adds, and this is the equation that makes that spelling
   the one [UkSh]'s [Hdsc_line] needs.  [wl_words_body] cannot be used:
   the bar is not [wl_alnum], so [ws ++ [fd_w_bar; fd_w_cat]] is not
   [wl_wf] and the round trip is not available.  What IS true is that a
   well-formed body absorbs any tail that starts a fresh word. *)
Lemma fd_wl_words_body_app (ws : list (list (bv 8))) (L : list (bv 8))
    (rest : list (list (bv 8))) :
  wl_wf ws -> ws <> [] -> wl_words L = [] :: rest ->
  wl_words (wl_body ws ++ L) = ws ++ rest.
Proof using.
  revert L rest.
  induction ws as [| w r IH]; intros L rest Hwf Hne HL; [by destruct (Hne eq_refl) |].
  destruct (wl_wf_cons w r Hwf) as [[Hw0 Ha] Hr].
  destruct r as [| w1 r1].
  - cbn [wl_body wl_tail]. rewrite app_nil_r.
    rewrite (wl_words_prepend w L [] rest Ha HL) app_nil_r. reflexivity.
  - assert (Hne1 : (w1 :: r1) <> []) by discriminate.
    rewrite wl_body_cons wl_tail_cons.
    rewrite <- (app_assoc w (wl_sp :: wl_body (w1 :: r1)) L).
    cbn [app].
    rewrite (wl_words_prepend w (wl_sp :: (wl_body (w1 :: r1) ++ L))
               [] ((w1 :: r1) ++ rest) Ha
               ltac:(rewrite wl_words_cons_sp (IH L rest Hr Hne1 HL);
                     reflexivity)).
    rewrite app_nil_r. reflexivity.
Qed.

Lemma wl_words_barcat : wl_words suf_barcat = [] :: [fd_w_bar; fd_w_cat].
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma suf_barcats_S (n : nat) : suf_barcats (S n) = suf_barcat ++ suf_barcats n.
Proof using. reflexivity. Qed.

Lemma w_barcats_S (n : nat) : w_barcats (S n) = [fd_w_bar; fd_w_cat] ++ w_barcats n.
Proof using. reflexivity. Qed.

Lemma w_barcats_comm (n : nat) :
  w_barcats n ++ [fd_w_bar; fd_w_cat] = [fd_w_bar; fd_w_cat] ++ w_barcats n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite w_barcats_S -app_assoc IH. reflexivity.
Qed.

Lemma w_barcats_S_r (n : nat) : w_barcats (S n) = w_barcats n ++ [fd_w_bar; fd_w_cat].
Proof using. rewrite w_barcats_S w_barcats_comm. reflexivity. Qed.

Lemma suf_barcat_eq : suf_barcat = wl_sp :: fd_bar :: wl_sp :: fd_w_cat.
Proof using. by vm_compute. Qed.

Lemma fd_w_bar_eq : fd_w_bar = [fd_bar].
Proof using. by vm_compute. Qed.

Lemma fd_bar_ne_sp : fd_bar <> wl_sp.
Proof using. by vm_compute. Qed.

Lemma fd_w_cat_alnum : Forall wl_alnum fd_w_cat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* the suffix in front of a tail that starts a fresh word *)
Lemma wl_words_barcat_app (L : list (bv 8)) (R : list (list (bv 8))) :
  wl_words L = [] :: R ->
  wl_words (suf_barcat ++ L) = [] :: fd_w_bar :: fd_w_cat :: R.
Proof using.
  intros HL. rewrite suf_barcat_eq. cbn [app].
  rewrite wl_words_cons_sp.
  rewrite (wl_words_cons_other_cons fd_bar (wl_sp :: fd_w_cat ++ L) [] (fd_w_cat :: R)
             fd_bar_ne_sp); [by rewrite fd_w_bar_eq |].
  rewrite wl_words_cons_sp.
  rewrite (wl_words_prepend fd_w_cat L [] R fd_w_cat_alnum HL) app_nil_r.
  reflexivity.
Qed.

Lemma wl_words_barcats (n : nat) :
  wl_words (suf_barcats (S n)) = [] :: w_barcats (S n).
Proof using.
  induction n as [| n IH].
  - rewrite (_ : suf_barcats 1 = suf_barcat);
      [| by unfold suf_barcats; cbn [replicate concat]; apply app_nil_r].
    rewrite (_ : w_barcats 1 = [fd_w_bar; fd_w_cat]);
      [| by unfold w_barcats; cbn [replicate concat app]].
    exact wl_words_barcat.
  - rewrite suf_barcats_S (wl_words_barcat_app _ _ IH). reflexivity.
Qed.

Lemma w_barcats_length (n : nat) : length (w_barcats n) = (2 * n)%nat.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite w_barcats_S length_app IH. cbn [length]. lia.
Qed.

(* ...and at a stage list of filters (cut G3): one stage in front of a
   tail that starts a fresh word, and the last stage alone *)
Lemma suf_filt_bar (F : filt) : fd_bar ∈ suf_filt F.
Proof using. rewrite /suf_filt. apply elem_of_list_further, elem_of_list_here. Qed.

Lemma wl_words_filt_app (F : filt) (L : list (bv 8)) (R : list (list (bv 8))) :
  filt_ok F -> wl_words L = [] :: R ->
  wl_words (suf_filt F ++ L) = [] :: fd_w_bar :: filt_words F ++ R.
Proof using.
  intros HF HL. rewrite /suf_filt. cbn [app].
  rewrite wl_words_cons_sp.
  rewrite (wl_words_cons_other_cons fd_bar (wl_sp :: wl_body (filt_words F) ++ L) []
             (filt_words F ++ R) fd_bar_ne_sp); [by rewrite fd_w_bar_eq |].
  rewrite wl_words_cons_sp.
  rewrite (fd_wl_words_body_app (filt_words F) L R (filt_wf F HF) (filt_words_ne F) HL).
  reflexivity.
Qed.

Lemma wl_words_filt_last (F : filt) :
  filt_ok F -> wl_words (suf_filt F) = [] :: fd_w_bar :: filt_words F.
Proof using.
  intros HF. rewrite /suf_filt wl_words_cons_sp.
  rewrite (wl_words_cons_other_cons fd_bar (wl_sp :: wl_body (filt_words F)) []
             (filt_words F) fd_bar_ne_sp); [by rewrite fd_w_bar_eq |].
  rewrite wl_words_cons_sp (wl_words_body _ (filt_wf F HF)). reflexivity.
Qed.

Lemma wl_words_filts (fs : list filt) :
  fs <> [] -> Forall filt_ok fs -> wl_words (suf_filts fs) = [] :: w_filts fs.
Proof using.
  induction fs as [| F fs IH]; intros Hne Hok; [by destruct (Hne eq_refl) |].
  apply Forall_cons_1 in Hok as [HF Hok].
  destruct fs as [| F' fs'].
  - change (suf_filts [F]) with (suf_filt F ++ []). rewrite app_nil_r (wl_words_filt_last F HF).
    change (w_filts [F]) with ((fd_w_bar :: filt_words F) ++ []). rewrite app_nil_r. reflexivity.
  - rewrite suf_filts_cons (wl_words_filt_app F _ (w_filts (F' :: fs')) HF
                               (IH ltac:(discriminate) Hok)).
    reflexivity.
Qed.

Lemma w_filts_app (a b : list filt) : w_filts (a ++ b) = w_filts a ++ w_filts b.
Proof using. rewrite /w_filts map_app concat_app //. Qed.

Lemma w_filts_length_ge (fs : list filt) : fs <> [] -> (2 <= length (w_filts fs))%nat.
Proof using.
  destruct fs as [| F fs]; [by intros H; destruct (H eq_refl) |]. intros _.
  rewrite w_filts_cons length_app. destruct F; cbn [length filt_words]; lia.
Qed.

Lemma filts_last (fs : list filt) : fs <> [] -> exists fs0 F, fs = fs0 ++ [F].
Proof using.
  revert fs. intros fs. induction fs as [| F0 fs IH] using rev_ind; intros H;
    [by destruct (H eq_refl) | by exists fs, F0].
Qed.

(* [n] cats are the landed suffix *)
Lemma suf_filt_cat : suf_filt FCat = suf_barcat.
Proof using. by vm_compute. Qed.

Lemma suf_filts_cats (n : nat) : suf_filts (cats n) = suf_barcats n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite cats_S suf_filts_cons IH suf_filt_cat suf_barcats_S. reflexivity.
Qed.

Lemma w_filts_cats (n : nat) : w_filts (cats n) = w_barcats n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite cats_S w_filts_cons IH w_barcats_S. reflexivity.
Qed.

Lemma uline_ws_pipe (p : producer) (fs : list filt) :
  prod_ok p -> Forall filt_ok fs ->
  wl_words (line_body (LPipe p fs)) = uline_ws (LPipe p fs).
Proof using.
  intros Hok HF. pose proof (prod_words_ne p Hok) as Hne.
  destruct fs as [| F fs].
  - cbn [line_body uline_ws].
    change (suf_filts []) with (@nil (bv 8)). change (w_filts []) with (@nil (list (bv 8))).
    rewrite !app_nil_r. exact (wl_words_body _ (prod_wf p Hok)).
  - exact (fd_wl_words_body_app (prod_words p) (suf_filts (F :: fs)) (w_filts (F :: fs))
             (prod_wf p Hok) Hne (wl_words_filts (F :: fs) ltac:(discriminate) HF)).
Qed.

(* ...and the redirect line's, the same way (RULING SLOT-WS, option B) *)
Lemma wl_words_gtf : wl_words suf_gtf = [] :: [fd_w_gt; fname_f].
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma uline_ws_gtf (ws : list (list (bv 8))) :
  line_ok ws -> wl_words (line_body (LEchoF ws)) = uline_ws (LEchoF ws).
Proof using.
  intro Hok.
  assert (Hne : ws <> []).
  { pose proof (line_ok_pos ws Hok) as Hp.
    destruct ws as [| w r]; [cbn [length] in Hp; lia | discriminate]. }
  exact (fd_wl_words_body_app ws suf_gtf [fd_w_gt; fname_f]
           (line_ok_wf _ Hok) Hne wl_words_gtf).
Qed.

(* ---- the redirect suffix, and the bytes a line body may carry -------- *)

Definition wl_gt : bv 8 := Z_to_bv 8 62%Z.

(* the partial line the user is in the middle of.  '>' is not a
   [wl_body_byte] and the line [echo hi > f] passes through the input
   [echo hi >], so the file application's D3 admits it. *)
Definition fbody_byte (b : bv 8) : Prop := wl_body_byte b \/ b = wl_gt.

Global Instance fbody_byte_dec b : Decision (fbody_byte b).
Proof using. rewrite /fbody_byte. apply _. Defined.

Lemma fbody_byte_of_body b : wl_body_byte b -> fbody_byte b.
Proof using. by left. Qed.

Lemma suf_gtf_len : length suf_gtf = 4%nat.
Proof using. by vm_compute. Qed.

Lemma suf_gtf_bytes : Forall fbody_byte suf_gtf.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_gt_not_body : ~ wl_body_byte wl_gt.
Proof using.
  rewrite /wl_body_byte /wl_alnum /wl_gt. intros [H | H].
  - assert (Hv : bv_unsigned (Z_to_bv 8 62%Z) = 62%Z) by (by vm_compute). lia.
  - apply (f_equal bv_unsigned) in H. rewrite wl_sp_val in H.
    assert (Hv : bv_unsigned (Z_to_bv 8 62%Z) = 62%Z) by (by vm_compute). lia.
Qed.

Lemma suf_gtf_gt : wl_gt ∈ suf_gtf.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ...and the bar's mirrors, which is how a pipe body is refuted where a
   redirect body is refuted by the '>' *)
Lemma fd_bar_not_body : ~ wl_body_byte fd_bar.
Proof using.
  rewrite /wl_body_byte /wl_alnum /fd_bar. intros [H | H].
  - assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
  - apply (f_equal bv_unsigned) in H. rewrite wl_sp_val in H.
    assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
Qed.

Lemma suf_barcat_bar : fd_bar ∈ suf_barcat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- THE PARSER ------------------------------------------------------ *)

Definition strip_gtf (b : list (bv 8)) : option (list (bv 8)) :=
  if decide (suf_gtf `suffix_of` b)
  then Some (take (length b - length suf_gtf) b) else None.

Lemma strip_gtf_app c : strip_gtf (c ++ suf_gtf) = Some c.
Proof using.
  rewrite /strip_gtf decide_True; [| by exists c].
  rewrite length_app.
  replace (length c + length suf_gtf - length suf_gtf)%nat with (length c)
    by lia.
  by rewrite take_app_length.
Qed.

Lemma strip_gtf_Some b c : strip_gtf b = Some c -> b = c ++ suf_gtf.
Proof using.
  intros Hc. destruct (decide (suf_gtf `suffix_of` b)) as [[k ->] | Hn].
  - rewrite (strip_gtf_app k) in Hc. by injection Hc as <-.
  - rewrite /strip_gtf decide_False in Hc; [discriminate | exact Hn].
Qed.

Lemma strip_gtf_None b c : strip_gtf b = None -> b <> c ++ suf_gtf.
Proof using. intros H ->. by rewrite strip_gtf_app in H. Qed.

(* THE PARSE of one body.  It answers [Some] only for an ADMISSIBLE line,
   so [is_Some (parse_line b)] IS the content half of the discipline at
   that body; and what it answers determines the body
   ([line_body_parse]). *)
Definition parse_line (b : list (bv 8)) : option uline :=
  if decide (b = cmd_cat_f) then Some LCat
  else match strip_gtf b with
       | Some c =>
           if decide (body_ok c /\ (S (length b) < line_max)%nat)
           then Some (LEchoF (wl_words c)) else None
       | None => if decide (body_ok b) then Some (LEcho (wl_words b)) else None
       end.

Definition uline_of (b : list (bv 8)) : uline := default inhabitant (parse_line b).

(* the word lists of a body list, in order *)
Definition lines_of (I : list (bv 8)) : list uline := uline_of <$> bodies_of I.

(* ---- [LPipe] IS OUT OF THE PARSER'S RANGE ---------------------------- *)
(* The whole point of adding the constructor additively: [parse_line] is
   untouched, so no input the FILE application quantifies over ever files
   an [LPipe] line, [lines_of]'s range is the three constructors it was,
   and [alts_ok], the determinacy theorem and [AppFile]'s conclusion mean
   what they meant.  This is the fact that makes every [LPipe] arm added
   below a DEAD arm, and it is the guard the three round-trip lemmas
   carry. *)
Definition uline_nopipe (l : uline) : Prop := forall ws n, l <> LPipe ws n.

Lemma uline_nopipe_echo ws : uline_nopipe (LEcho ws).
Proof using. intros ws' n H. discriminate H. Qed.
Lemma uline_nopipe_echof ws : uline_nopipe (LEchoF ws).
Proof using. intros ws' n H. discriminate H. Qed.
Lemma uline_nopipe_cat : uline_nopipe LCat.
Proof using. intros ws' n H. discriminate H. Qed.

Lemma parse_line_not_pipe b ws n : parse_line b <> Some (LPipe ws n).
Proof using.
  rewrite /parse_line. case_decide as Hc; [discriminate |].
  destruct (strip_gtf b) as [c |]; case_decide; discriminate.
Qed.

Lemma uline_of_nopipe b : uline_nopipe (uline_of b).
Proof using.
  intros ws n Heq.
  destruct (parse_line b) as [l |] eqn:Hp; rewrite /uline_of Hp in Heq;
    cbn in Heq; [| discriminate Heq].
  rewrite Heq in Hp. exact (parse_line_not_pipe b ws n Hp).
Qed.

Lemma lines_of_nopipe I l : l ∈ lines_of I -> uline_nopipe l.
Proof using.
  rewrite /lines_of. intro Hl.
  apply elem_of_list_fmap in Hl as (b & -> & _).
  exact (uline_of_nopipe b).
Qed.

Lemma parse_line_ok b l : parse_line b = Some l -> uline_ok l.
Proof using.
  rewrite /parse_line. case_decide as Hc.
  { intros [= <-]. exact I. }
  destruct (strip_gtf b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody Hok] Hlen]. rewrite /uline_ok. split.
    + exact Hok.
    + pose proof (strip_gtf_Some b c Hs) as Hbc.
      rewrite Hbc length_app in Hlen.
      rewrite /line_bytes /line_body !length_app Hbody.
      cbn [length] in Hlen |- *. lia.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody Hok]. exact Hok.
Qed.

Lemma line_body_parse b l : parse_line b = Some l -> b = line_body l.
Proof using.
  rewrite /parse_line. case_decide as Hc.
  { intros [= <-]. exact Hc. }
  destruct (strip_gtf b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody _] _]. rewrite /line_body Hbody.
    exact (strip_gtf_Some b c Hs).
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody _]. by rewrite /line_body Hbody.
Qed.

(* ---- ...AND ITS INVERSE ---------------------------------------------- *)

Lemma line_ok_body_len ws : line_ok ws -> (4 <= length (wl_body ws))%nat.
Proof using.
  intro Hok. pose proof (line_ok_head ws Hok) as Hh.
  destruct ws as [| w r]; [discriminate |].
  cbn in Hh. injection Hh as Hw.
  rewrite wl_body_cons length_app Hw.
  cbn [length]. lia.
Qed.

Lemma cat_words : wl_words cmd_cat_f = [sb "cat"%string; sb "f"%string].
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma cat_not_echo : wl_words cmd_cat_f !! 0%nat <> Some cmd_echo.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma cmd_cat_f_len : length cmd_cat_f = 5%nat.
Proof using. by vm_compute. Qed.

Lemma body_no_gtf ws (c : list (bv 8)) :
  line_ok ws -> wl_body ws <> c ++ suf_gtf.
Proof using.
  intros Hok Heq.
  pose proof (wl_body_bytes ws (line_ok_wf _ Hok)) as Hfb.
  rewrite Heq in Hfb. apply Forall_app in Hfb as [_ Hsuf].
  exact (wl_gt_not_body
           (proj1 (Forall_forall _ _) Hsuf wl_gt suf_gtf_gt)).
Qed.

(* ---- THE ROUND TRIP, at the parser's own range ------------------------ *)
(* THE GUARD [uline_nopipe] IS THE WHOLE PRICE OF THE CONSTRUCTOR.  These
   three say "the model's lines ARE [parse_line]'s range", so they are
   false at a constructor deliberately left out of it: [parse_line (wl_body
   ws ++ suf_barcat)] is [None] (the bar is not [wl_body_byte], so
   [body_ok] fails).  Every caller has the guard for free -- its line came
   out of [uline_of] ([uline_of_nopipe]) or is a literal. *)
Lemma parse_line_body l :
  uline_nopipe l -> uline_ok l -> parse_line (line_body l) = Some l.
Proof using.
  intro Hnp. destruct l as [ws | ws | | ws npc]; [| | | by destruct (Hnp ws npc eq_refl)].
  - (* LEcho *)
    intro Hok. rewrite /line_body /parse_line.
    rewrite decide_False; last first.
    { intro Heq. apply cat_not_echo.
      rewrite -Heq (wl_words_body ws (line_ok_wf _ Hok)).
      exact (line_ok_head ws Hok). }
    destruct (strip_gtf (wl_body ws)) as [c |] eqn:Hs.
    { exfalso. exact (body_no_gtf ws c Hok (strip_gtf_Some _ _ Hs)). }
    rewrite decide_True; last first.
    { rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
      split; [reflexivity | exact Hok]. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
  - (* LEchoF *)
    intros [Hok Hlen]. rewrite /line_body /parse_line.
    rewrite decide_False; last first.
    { intro Heq. pose proof (line_ok_body_len ws Hok) as Hb.
      apply (f_equal length) in Heq.
      rewrite length_app suf_gtf_len cmd_cat_f_len in Heq. lia. }
    rewrite strip_gtf_app decide_True; last first.
    { split.
      - rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
        split; [reflexivity | exact Hok].
      - rewrite /line_bytes /line_body !length_app in Hlen.
        cbn [length] in Hlen. rewrite length_app. lia. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
  - intros _. rewrite /parse_line /line_body.
    destruct (decide (cmd_cat_f = cmd_cat_f)) as [_ | Hne]; [reflexivity |].
    by destruct (Hne eq_refl).
Qed.

Lemma uline_of_body l : uline_nopipe l -> uline_ok l -> uline_of (line_body l) = l.
Proof using. intros Hnp H. by rewrite /uline_of (parse_line_body l Hnp H). Qed.

(* ---- D3 FOR THE FILE APPLICATION ------------------------------------- *)

Definition fbody_ok (b : list (bv 8)) : Prop := is_Some (parse_line b).

Global Instance fbody_ok_dec b : Decision (fbody_ok b).
Proof using. rewrite /fbody_ok. apply _. Defined.

Lemma fbody_ok_line b : fbody_ok b -> uline_ok (uline_of b) /\ b = line_body (uline_of b).
Proof using.
  intros [l Hl]. rewrite /uline_of Hl /=.
  split; [exact (parse_line_ok b l Hl) | exact (line_body_parse b l Hl)].
Qed.

(* THE TYPED LINE'S WORDS ARE THE BODY'S PARSE, at every constructor
   (RULING SLOT-WS, option B).  This is the equation [UkSh]'s [Hdsc_line]
   asks of an era's line read; it was a PREMISE of
   [FileReadInst.file_disc_line] while [uline_ws (LEchoF ws)] was [ws],
   and false there. *)
Lemma uline_ws_words (b : list (bv 8)) :
  fbody_ok b -> uline_ws (uline_of b) = wl_words b.
Proof using.
  intro Hfb. destruct (fbody_ok_line b Hfb) as [Hok Hb].
  transitivity (wl_words (line_body (uline_of b)));
    [ | exact (f_equal wl_words (eq_sym Hb)) ].
  revert Hok. generalize (uline_of b). intros [ws | ws | | ws npc] Hok.
  - cbn [uline_ws line_body]. symmetry.
    exact (wl_words_body ws (line_ok_wf _ Hok)).
  - symmetry. exact (uline_ws_gtf ws (proj1 Hok)).
  - reflexivity.
  - symmetry. exact (uline_ws_pipe ws npc (proj1 Hok) (proj1 (proj2 (proj2 Hok)))).
Qed.

Lemma fbody_ok_of l : uline_nopipe l -> uline_ok l -> fbody_ok (line_body l).
Proof using. intros Hnp H. exists l. exact (parse_line_body l Hnp H). Qed.

(* ---- ...AND THE READING THAT SURVIVES THE FOURTH CONSTRUCTOR ---------- *)
(* [fbody_ok b] is "[b] is in [parse_line]'s range".  Its ONE consumer
   above the pure model is [UkSh.ush_posw]'s third conjunct -- the slot the
   sh loop leaves, which says the input's last body is the body of the LINE
   the era filed, so that a child law can tell WHICH constructor it was
   ([fbody_ok_echo]).  Read that way the conjunct never needed the parser:
   what it needs is that the body IS some admissible line's body, and that
   is [fline_ok], which every era can supply -- including one whose lines
   are outside [parse_line]'s range.  [fline_ok_echo] is [fbody_ok_echo] at
   it, so nothing downstream loses anything. *)
Definition fline_ok (b : list (bv 8)) : Prop :=
  exists l : uline, uline_ok l /\ b = line_body l.

Lemma fline_ok_of l : uline_ok l -> fline_ok (line_body l).
Proof using. intro H. by exists l. Qed.

(* ...AND WHICH LINE THE [cat f] WORD LIST IS: the fork's words at a cat
   round are [uline_ws LCat], and no other constructor has them -- an echo
   line's first word is [echo], a redirect's and a pipeline's word lists are
   two longer than a command's, which has at least two. *)
Lemma fline_ok_cat_words (b : list (bv 8)) :
  fline_ok b -> wl_words b = uline_ws LCat -> uline_of b = LCat.
Proof using.
  intros (l & Hok & ->) Hw.
  destruct l as [ws' | ws' | | ws' npc'].
  - exfalso. cbn [line_body] in Hw.
    rewrite (wl_words_body ws' (line_ok_wf _ Hok)) in Hw.
    pose proof (line_ok_head ws' Hok) as Hh. rewrite Hw in Hh.
    revert Hh. cbn [uline_ws]. vm_compute. discriminate.
  - exfalso. destruct Hok as [Hok' _].
    rewrite (uline_ws_gtf ws' Hok') in Hw.
    apply (f_equal length) in Hw. revert Hw.
    cbn [uline_ws]. rewrite length_app.
    pose proof (line_ok_ge2 ws' Hok') as H2.
    vm_compute (length (wl_words cmd_cat_f)). cbn [length]. lia.
  - apply uline_of_body; [ intros w ? Hp; discriminate Hp | exact Hok ].
  - exfalso. destruct Hok as (Hok' & Hn1 & Hf1 & _).
    rewrite (uline_ws_pipe ws' npc' Hok' Hf1) in Hw.
    apply (f_equal length) in Hw. revert Hw.
    cbn [uline_ws]. rewrite length_app.
    pose proof (prod_words_ge2 ws' Hok') as H2.
    pose proof (w_filts_length_ge npc' Hn1) as H3.
    vm_compute (length (wl_words cmd_cat_f)). lia.
Qed.

(* WHICH LINE A REDIRECT WORD LIST IS (RULING SLOT-WS, option B): an
   admissible body whose words are a command's, then `>', then a file name,
   is THE redirect line of that command, and the file is `f`.  This is what
   the forked child reads off the sh loop's fork assertion ([last_ws I]):
   the other three constructors are refuted by their words -- an echo
   line's are all alphanumeric, [cat f] has two, a pipeline's last but one
   is the bar. *)
Lemma fline_ok_redir_words (b : list (bv 8)) (ws : list (list (bv 8)))
    (file : list (bv 8)) :
  fline_ok b -> line_ok ws -> wl_words b = ws ++ [fd_w_gt; file] ->
  uline_of b = LEchoF ws /\ file = fname_f.
Proof using.
  intros (l & Hok & ->) Hws Hw.
  destruct l as [ws' | ws' | | ws' npc'].
  - (* LEcho: its words are alphanumeric, and `>' is not *)
    exfalso. cbn [line_body] in Hw.
    rewrite (wl_words_body ws' (line_ok_wf _ Hok)) in Hw.
    pose proof (line_ok_wf _ Hok) as Hwf. rewrite Hw in Hwf.
    apply Forall_app in Hwf as [_ Hwf].
    apply Forall_cons_1 in Hwf as [[_ Hgt] _].
    apply Forall_cons_1 in Hgt as [Hgt _].
    revert Hgt. rewrite /wl_alnum. vm_compute. intros [H | [H | H]];
      destruct H as [H1 H2]; first [ by apply H1 | by apply H2 ].
  - (* LEchoF: the two suffixes line up *)
    destruct Hok as [Hok' Hlen].
    rewrite (uline_ws_gtf ws' Hok') in Hw. cbn [uline_ws] in Hw.
    replace (ws' ++ [fd_w_gt; fname_f])
      with ((ws' ++ [fd_w_gt]) ++ [fname_f]) in Hw
      by (rewrite -app_assoc; reflexivity).
    replace (ws ++ [fd_w_gt; file])
      with ((ws ++ [fd_w_gt]) ++ [file]) in Hw
      by (rewrite -app_assoc; reflexivity).
    apply app_inj_tail in Hw as [Hw ->].
    apply app_inj_tail in Hw as [-> _].
    split; [ | reflexivity ].
    apply uline_of_body; [ intros w ? Hp; discriminate Hp | by split ].
  - (* LCat: two words, so the command would have none *)
    exfalso. cbn [line_body] in Hw.
    apply (f_equal length) in Hw. rewrite length_app in Hw.
    pose proof (line_ok_pos ws Hws) as Hp.
    revert Hw. vm_compute (length (wl_words cmd_cat_f)). cbn [length]. lia.
  - (* LPipe: the word before the last is the bar, or [grep] *)
    exfalso. destruct Hok as (Hok' & Hn1 & Hf1 & _).
    rewrite (uline_ws_pipe ws' npc' Hok' Hf1) in Hw. cbn [uline_ws] in Hw.
    destruct (filts_last npc' Hn1) as (fs0 & F & ->).
    rewrite w_filts_app in Hw.
    replace (ws ++ [fd_w_gt; file])
      with ((ws ++ [fd_w_gt]) ++ [file]) in Hw
      by (rewrite -app_assoc; reflexivity).
    destruct F as [| w].
    + change (w_filts [FCat]) with [fd_w_bar; fd_w_cat] in Hw.
      replace (prod_words ws' ++ w_filts fs0 ++ [fd_w_bar; fd_w_cat])
        with (((prod_words ws' ++ w_filts fs0) ++ [fd_w_bar]) ++ [fd_w_cat]) in Hw
        by (rewrite -!app_assoc; reflexivity).
      apply app_inj_tail in Hw as [Hw _].
      apply app_inj_tail in Hw as [_ Hbar]. discriminate Hbar.
    + change (w_filts [FGrep w]) with [fd_w_bar; fd_w_grep; w] in Hw.
      replace (prod_words ws' ++ w_filts fs0 ++ [fd_w_bar; fd_w_grep; w])
        with ((((prod_words ws' ++ w_filts fs0) ++ [fd_w_bar]) ++ [fd_w_grep]) ++ [w]) in Hw
        by (rewrite -!app_assoc; reflexivity).
      apply app_inj_tail in Hw as [Hw _].
      apply app_inj_tail in Hw as [_ Hg]. discriminate Hg.
Qed.

Lemma fline_ok_of_body b : fbody_ok b -> fline_ok b.
Proof using.
  intro Hb. destruct (fbody_ok_line b Hb) as [Hok Heq]. by exists (uline_of b).
Qed.

(* an admissible body is made of body bytes and fits [getcmd]'s buffer --
   the two facts the snoc law needs when a newline closes a line *)
Lemma fbody_ok_bytes b : fbody_ok b -> Forall fbody_byte b.
Proof using.
  intro Hb. destruct (fbody_ok_line b Hb) as [Hok Heq].
  pose proof (uline_of_nopipe b) as Hnp. rewrite Heq.
  destruct (uline_of b) as [ws | ws | | ws npc]; rewrite /line_body;
    [| | | by destruct (Hnp ws npc eq_refl)].
  - apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact fbody_byte_of_body].
  - apply Forall_app. split; [| exact suf_gtf_bytes].
    destruct Hok as [Hok _].
    apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact fbody_byte_of_body].
  - apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma fbody_ok_short b : fbody_ok b -> (S (length b) < line_max)%nat.
Proof using.
  intro Hb. destruct (fbody_ok_line b Hb) as [Hok Heq].
  pose proof (uline_of_nopipe b) as Hnp. rewrite Heq.
  destruct (uline_of b) as [ws | ws | | ws npc]; [| | | by destruct (Hnp ws npc eq_refl)].
  - pose proof (line_ok_len ws Hok) as Hl.
    rewrite wl_line_length in Hl. rewrite /line_body. lia.
  - destruct Hok as [_ Hl].
    rewrite /line_bytes /line_body length_app in Hl. cbn [length] in Hl.
    rewrite /line_body. lia.
  - rewrite /line_body cmd_cat_f_len /line_max. lia.
Qed.

(* ---- EVERY BYTE OF AN ADMISSIBLE LINE, AT EVERY CONSTRUCTOR ---------- *)
(* [fbody_ok_bytes] is this fact one level down and only for a body in the
   PARSER's range.  This one holds at [LPipe] too, and the price is the
   bar, which is NOT an [fbody_byte] -- so a consumer that enumerates the
   byte values of a line ([UkSh.ush_uline_body_val]) has to name it. *)
Lemma suf_barcat_bytes :
  Forall (fun b => fbody_byte b \/ b = fd_bar) suf_barcat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma suf_barcats_bytes (n : nat) :
  Forall (fun b => fbody_byte b \/ b = fd_bar) (suf_barcats n).
Proof using.
  induction n as [| n IH]; [constructor |].
  rewrite suf_barcats_S. apply Forall_app. split; [exact suf_barcat_bytes | exact IH].
Qed.

Lemma suf_filts_bytes (fs : list filt) :
  Forall filt_ok fs -> Forall (fun b => fbody_byte b \/ b = fd_bar) (suf_filts fs).
Proof using.
  induction fs as [| F fs IH]; intros Hok; [constructor |].
  apply Forall_cons_1 in Hok as [HF Hok].
  rewrite suf_filts_cons. apply Forall_app. split; [| exact (IH Hok)].
  rewrite /suf_filt.
  constructor; [left; left; right; reflexivity |].
  constructor; [right; reflexivity |].
  constructor; [left; left; right; reflexivity |].
  eapply Forall_impl; [exact (wl_body_bytes _ (filt_wf F HF)) |].
  intros b Hb. left. exact (fbody_byte_of_body b Hb).
Qed.

Lemma line_bytes_bytes l :
  uline_ok l ->
  Forall (fun b => fbody_byte b \/ b = fd_bar \/ b = wl_nl) (line_bytes l).
Proof using.
  intro Hok.
  rewrite line_bytes_body. apply Forall_app. split;
    [| apply Forall_singleton; by right; right].
  destruct l as [ws | ws | | ws npc]; rewrite /line_body.
  - apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) |].
    intros b Hb. left. exact (fbody_byte_of_body b Hb).
  - apply Forall_app. split.
    + apply Forall_impl with (P := wl_body_byte);
        [exact (wl_body_bytes ws (line_ok_wf _ (proj1 Hok))) |].
      intros b Hb. left. exact (fbody_byte_of_body b Hb).
    + apply Forall_impl with (P := fbody_byte); [exact suf_gtf_bytes |].
      intros b Hb. by left.
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - apply Forall_app. split.
    + apply Forall_impl with (P := wl_body_byte);
        [exact (prod_body_bytes ws (proj1 Hok)) |].
      intros b Hb. left. exact (fbody_byte_of_body b Hb).
    + apply Forall_impl with (P := fun b => fbody_byte b \/ b = fd_bar);
        [exact (suf_filts_bytes npc (proj1 (proj2 (proj2 Hok)))) |].
      intros b [Hb | Hb]; [by left | by right; left].
Qed.

(* D3: every COMPLETE body parses to an admissible line, and the partial
   line is body bytes short enough that its newline still fits. *)
Definition disc_input_f (I : list (bv 8)) : Prop :=
  Forall fbody_ok (bodies_of I)
  /\ Forall fbody_byte (rest_of I)
  /\ (S (length (rest_of I)) < line_max)%nat.

Global Instance disc_input_f_dec I : Decision (disc_input_f I).
Proof using. rewrite /disc_input_f. apply _. Defined.

Lemma disc_input_f_nil : disc_input_f [].
Proof using.
  rewrite /disc_input_f bodies_of_nil rest_of_nil /line_max.
  split; [constructor |]. split; [constructor | cbn [length]; lia].
Qed.

Lemma disc_input_f_snoc I b : disc_input_f (I ++ [b]) -> disc_input_f I.
Proof using.
  intros (Hb & Hr & Hs). destruct (decide (b = wl_nl)) as [-> | Hne].
  - rewrite bodies_of_snoc_nl in Hb.
    apply Forall_app in Hb as [Hb1 Hb2]. rewrite Forall_singleton in Hb2.
    split; [exact Hb1 |]. split; [exact (fbody_ok_bytes _ Hb2) |].
    exact (fbody_ok_short _ Hb2).
  - rewrite (bodies_of_snoc_other I b Hne) in Hb.
    rewrite (rest_of_snoc_other I b Hne) in Hr, Hs.
    apply Forall_app in Hr as [Hr1 _].
    split; [exact Hb |]. split; [exact Hr1 |].
    rewrite (length_app (rest_of I) [b]) in Hs. cbn [length] in Hs. lia.
Qed.

Lemma disc_input_f_prefix I I' :
  I `prefix_of` I' -> disc_input_f I' -> disc_input_f I.
Proof using.
  intros [k ->]. induction k as [| b k IH] using rev_ind; intro Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_input_f_snoc _ _ Hd).
Qed.

Lemma disc_input_f_body I i b :
  disc_input_f I -> bodies_of I !! i = Some b -> fbody_ok b.
Proof using. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

Lemma disc_input_f_at I i :
  disc_input_f I -> (i < nlines I)%nat ->
  uline_ok (uline_of (bodies_of I !!! i))
  /\ bodies_of I !!! i = line_body (uline_of (bodies_of I !!! i)).
Proof using.
  intros Hd Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb).
  exact (fbody_ok_line b (disc_input_f_body I i b Hd Hb)).
Qed.

(* ====================================================================== *)
(*  2.  WHAT A FILE CONTENT LOOKS LIKE                                     *)
(* ====================================================================== *)

(* '$' is the one byte the prompt opens on and NOTHING the session writes
   before a prompt carries ([LineBytes.nodollar]) -- not a word, not a
   blank, not a newline, and so not any content echo can have written. *)

(* A CONTENT IS BODY BYTES, OPTIONALLY CLOSED BY ONE NEWLINE: echo's chunks
   are its arguments and single blanks, and the newline it writes last.
   This is everything the determinacy argument reads off a file. *)
Definition fcont_ok (bs : list (bv 8)) : Prop :=
  Forall wl_body_byte bs
  \/ (exists v, Forall wl_body_byte v /\ bs = v ++ [wl_nl]).

Definition fstate_ok (s : fstate) : Prop :=
  match s with None => True | Some bs => fcont_ok bs end.

(* THE FILES THE APPLICATION DESCRIBES at a state: [f], and nothing else
   (cut C9b, moved down from [UkFileIface.fif_files], which is now this).
   It is the content function a pipeline's [cat f] producer reads at the
   round's state. *)
Definition files_of (s : fstate) : list (bv 8) -> option (list (bv 8)) :=
  fun p => if decide (p = fname_f) then s else None.

Lemma files_of_f (s : fstate) : files_of s fname_f = s.
Proof using. unfold files_of. case_decide; [reflexivity | done]. Qed.

Lemma files_of_ne (s : fstate) (p : list (bv 8)) : p <> fname_f -> files_of s p = None.
Proof using. intros Hp. unfold files_of. case_decide; [done | reflexivity]. Qed.

Lemma files_of_some (s : fstate) (p c : list (bv 8)) :
  files_of s p = Some c -> s = Some c.
Proof using. unfold files_of. case_decide; [done | discriminate]. Qed.

Lemma fcont_ok_nodollar bs : fcont_ok bs -> Forall nodollar bs.
Proof using.
  intros [HF | (v & HF & ->)].
  - apply Forall_impl with (P := wl_body_byte);
      [exact HF | exact body_byte_nodollar].
  - apply Forall_app. split.
    + apply Forall_impl with (P := wl_body_byte);
        [exact HF | exact body_byte_nodollar].
    + apply Forall_singleton, nl_nodollar.
Qed.

(* the newline, if any, is at the END -- which is what lines a content up
   against sh's panic line "fork\n" *)
Lemma fcont_ok_nl bs :
  fcont_ok bs -> wl_nl ∉ bs \/ (exists v, wl_nl ∉ v /\ bs = v ++ [wl_nl]).
Proof using.
  intros [HF | (v & HF & ->)].
  - left. exact (wl_nonl_of_body_bytes _ HF).
  - right. exists v. split; [exact (wl_nonl_of_body_bytes _ HF) | reflexivity].
Qed.

(* ---- echo's chunks, and why a content has that shape ----------------- *)

Lemma echo_args_chunks_shape (args : list (list (bv 8))) :
  Forall wl_word args -> args <> [] ->
  exists n, length (echo_args_chunks args) = S n
    /\ echo_args_chunks args !!! n = [wl_nl]
    /\ (forall i, (i < n)%nat ->
          Forall wl_body_byte (echo_args_chunks args !!! i)).
Proof using.
  induction args as [| a rest IH]; intros HF Hne; [done |].
  destruct (Forall_cons_1 _ _ _ HF) as [Ha HFr].
  destruct rest as [| b rest'].
  - exists 1%nat. cbn [echo_args_chunks length].
    split; [reflexivity |]. split; [reflexivity |].
    intros i Hi. assert (i = 0%nat) by lia. subst i. cbn.
    destruct Ha as [_ Halnum]. exact (wl_alnum_body a Halnum).
  - destruct (IH HFr ltac:(discriminate)) as (n & Hlen & Hlast & Hbody).
    exists (S (S n)). cbn [echo_args_chunks length].
    rewrite Hlen. split; [reflexivity |]. split.
    { by rewrite !(wl_lta_cons_S _ _ (S n)) !(wl_lta_cons_S _ _ n). }
    intros i Hi. destruct i as [| [| i]].
    + cbn. destruct Ha as [_ Halnum]. exact (wl_alnum_body a Halnum).
    + rewrite (wl_lta_cons_S _ _ 0%nat). cbn.
      apply (bool_decide_unpack _). vm_compute. exact I.
    + rewrite (wl_lta_cons_S _ _ (S i)) (wl_lta_cons_S _ _ i).
      apply Hbody. lia.
Qed.

Lemma subseq_shape (cs : list (list (bv 8))) (sel : list nat) (n : nat) :
  length cs = S n ->
  (forall i, (i < n)%nat -> Forall wl_body_byte (cs !!! i)) ->
  cs !!! n = [wl_nl] ->
  sel_ok cs sel -> fcont_ok (subseq cs sel).
Proof using.
  intros Hlen Hbody Hlast. revert sel.
  induction sel as [| j sel IH]; intros [Hs Hr].
  { left. rewrite subseq_nil. constructor. }
  apply StronglySorted_inv in Hs as [Hs Hj].
  apply Forall_cons_1 in Hr as [Hjr Hr].
  assert (Hsub : subseq cs (j :: sel) = cs !!! j ++ subseq cs sel).
  { by rewrite /subseq fmap_cons concat_cons. }
  destruct (decide (j = n)) as [-> | Hne].
  - (* the newline chunk is selected: it is the LAST one *)
    assert (Hnil : sel = []).
    { destruct sel as [| k sel']; [reflexivity |].
      exfalso.
      apply Forall_cons_1 in Hj as [Hnk _].
      apply Forall_cons_1 in Hr as [Hkl _].
      lia. }
    subst sel. rewrite Hsub subseq_nil app_nil_r Hlast.
    right. exists []. split; [constructor | reflexivity].
  - assert (Hjn : (j < n)%nat) by lia.
    destruct (IH (conj Hs Hr)) as [HFl | (v & HFv & Hv)]; rewrite Hsub.
    + left. apply Forall_app. split; [exact (Hbody j Hjn) | exact HFl].
    + right. exists (cs !!! j ++ v). rewrite Hv app_assoc.
      split; [| reflexivity].
      apply Forall_app. split; [exact (Hbody j Hjn) | exact HFv].
Qed.

Lemma fcont_ok_subseq ws sel :
  line_ok ws -> sel_ok (echo_chunks ws) sel ->
  fcont_ok (subseq (echo_chunks ws) sel).
Proof using.
  intros Hok Hsel.
  assert (Hne : drop 1 ws <> []).
  { pose proof (line_ok_ge2 ws Hok) as H2. intro Hz.
    apply (f_equal length) in Hz. rewrite length_drop /= in Hz. lia. }
  assert (HF : Forall wl_word (drop 1 ws))
    by (apply lb_Forall_drop, (line_ok_wf _ Hok)).
  destruct (echo_args_chunks_shape (drop 1 ws) HF Hne)
    as (n & Hlen & Hlast & Hbody).
  exact (subseq_shape (echo_chunks ws) sel n Hlen Hbody Hlast Hsel).
Qed.

(* ====================================================================== *)
(*  3.  THE ROUND'S ALTERNATIVES                                           *)
(* ====================================================================== *)

(* SH'S DIAGNOSTICS ARE WORD LINES, as [EchoDisc.dg_exec] is -- the redirect
   arm's "open %s failed" at the file name [f], and the exec diagnostic for
   /cat.  Stating them in the word vocabulary is what makes their collision
   with an echoed line a statement the parse settles. *)
Definition dg_open : list (list (bv 8)) :=
  [ sb "open"%string; sb "f"%string; sb "failed"%string ].
Definition dg_exec_cat : list (list (bv 8)) :=
  [ sb "exec"%string; sb "cat"%string; sb "failed"%string ].

Lemma dg_open_line : wl_line dg_open = sb "open f failed"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_exec_cat_line :
  wl_line dg_exec_cat = sb "exec cat failed"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* CAT'S OWN DIAGNOSTIC IS NOT A WORD LINE -- ':' is not alphanumeric -- so
   it is transcribed as bytes (user/cat.c, [fprintf(2, "cat: cannot open
   %s\n", …)]).  Nothing below needs it to be a word line; what it needs is
   that it carries no '$' and ends at its newline. *)
Definition dg_catopen : list (bv 8) := sb "cat: cannot open f"%string ++ nlb.

Definition alt_openfail : list (bv 8) := wl_line dg_open ++ u_prompt.
Definition alt_execcat  : list (bv 8) := wl_line dg_exec_cat ++ u_prompt.
Definition alt_catopen  : list (bv 8) := dg_catopen ++ u_prompt.

Lemma alt_openfail_string :
  alt_openfail = sb "open f failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_execcat_string :
  alt_execcat = sb "exec cat failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_catopen_string :
  alt_catopen = sb "cat: cannot open f"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ONE ALTERNATIVE DECIDES A ROUND: what the console shows and what becomes
   of [f].  [REcho] is the echo application's four, unchanged and with no
   f-effect; the [RF*] are the redirect line's and the [RC*] are cat's. *)
Inductive ralt :=
  | REcho (a : nat)          (* the echo application's four; f unchanged *)
  | RFRan (sel : list nat)   (* "$ ";  f := the chunks that landed         *)
  | RFExec                   (* "exec echo failed\n$ ";  f := []          *)
  | RFOpenU                  (* "open f failed\n$ ";     f unchanged      *)
  | RFOpenM                  (* "open f failed\n$ ";     f := [] (created)*)
  | RFSilent                 (* "$ ";                    f unchanged (limit 3;
                                RULING HOLD-POS: the line's silent alternative
                                leaves `f` alone, like [REcho 2] / [RCSilent]) *)
  | RFFork                   (* "fork\n";                f unchanged      *)
  | RCRan                    (* f's content, or cat's diagnostic; then "$ "*)
  | RCNoOpen                 (* "cat: cannot open f\n$ " at a PRESENT f   *)
  | RCExec                   (* "exec cat failed\n$ "                     *)
  | RCSilent                 (* "$ "                                      *)
  | RCFork.                  (* "fork\n"                                  *)

Global Instance ralt_eq_dec : EqDecision ralt.
Proof using. solve_decision. Defined.
Global Instance ralt_inhabited : Inhabited ralt := populate (REcho 0%nat).

(* THE ENCODING the stage's [cs_auth]/[cs_lb] machinery carries: an
   injective [nat] code, and the echo application's four are their own
   index, so an echo line's rounds are LITERALLY today's ([sessf_sess]). *)
Definition ralt_enc (a : ralt) : nat :=
  match a with
  | REcho k => if decide (k < 4)%nat then k else (4 + 12 * (k - 4))%nat
  | RFExec => 5%nat | RFOpenU => 6%nat | RFOpenM => 7%nat
  | RFSilent => 8%nat | RFFork => 9%nat
  | RCRan => 10%nat | RCNoOpen => 11%nat | RCExec => 12%nat
  | RCSilent => 13%nat | RCFork => 14%nat
  | RFRan sel => (15 + 12 * encode_nat sel)%nat
  end.

Definition ralt_dec (n : nat) : ralt :=
  if decide (n < 4)%nat then REcho n
  else if decide (n = 5%nat) then RFExec
  else if decide (n = 6%nat) then RFOpenU
  else if decide (n = 7%nat) then RFOpenM
  else if decide (n = 8%nat) then RFSilent
  else if decide (n = 9%nat) then RFFork
  else if decide (n = 10%nat) then RCRan
  else if decide (n = 11%nat) then RCNoOpen
  else if decide (n = 12%nat) then RCExec
  else if decide (n = 13%nat) then RCSilent
  else if decide (n = 14%nat) then RCFork
  else if decide (Nat.modulo n 12 = 3%nat)
       then RFRan (default [] (decode_nat (Nat.div (n - 15) 12)))
       else REcho (4 + Nat.div (n - 4) 12)%nat.

Lemma fd_mod12_add (a m : nat) : Nat.modulo (a + 12 * m) 12 = Nat.modulo a 12.
Proof using.
  replace (a + 12 * m)%nat with (a + m * 12)%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma fd_div12_mul (m : nat) : Nat.div (12 * m) 12 = m.
Proof using.
  replace (12 * m)%nat with (m * 12)%nat by lia.
  rewrite Nat.div_mul; [reflexivity | lia].
Qed.

Lemma ralt_dec_enc a : ralt_dec (ralt_enc a) = a.
Proof using.
  destruct a as [k | sel | | | | | | | | | |]; try (by vm_compute).
  - (* REcho: its own index below 4, and out of every other code's way
       above it *)
    rewrite /ralt_enc. case_decide as Hk.
    + rewrite /ralt_dec decide_True; [reflexivity | exact Hk].
    + assert (Hm : Nat.modulo (4 + 12 * (k - 4)) 12 = 4%nat)
        by (rewrite fd_mod12_add; by vm_compute).
      rewrite /ralt_dec.
      do 11 (case_decide; [exfalso; lia |]).
      case_decide; [exfalso; congruence |].
      replace (4 + 12 * (k - 4) - 4)%nat with (12 * (k - 4))%nat by lia.
      rewrite fd_div12_mul. f_equal. lia.
  - (* RFRan: the chunk subset through the countable encoding *)
    assert (Hm : Nat.modulo (15 + 12 * encode_nat sel) 12 = 3%nat)
      by (rewrite fd_mod12_add; by vm_compute).
    rewrite /ralt_enc /ralt_dec.
    do 11 (case_decide; [exfalso; lia |]).
    case_decide; [| exfalso; congruence].
    replace (15 + 12 * encode_nat sel - 15)%nat with (12 * encode_nat sel)%nat
      by lia.
    rewrite fd_div12_mul decode_encode_nat. reflexivity.
Qed.

Lemma ralt_dec_lt4 n : (n < 4)%nat -> ralt_dec n = REcho n.
Proof using. intro H. rewrite /ralt_dec decide_True; [reflexivity | exact H]. Qed.

(* the panic alternatives: sh's [fork1] panicked, init reaped the shell and
   its outer loop opened a NEW prologue round -- [EchoDisc]'s alternative 3
   at an echo line, and its twins at the two new line shapes *)
Definition ralt_panic (a : ralt) : bool :=
  match a with
  | REcho k => bool_decide (k = 3%nat)
  | RFFork => true
  | RCFork => true
  | _ => false
  end.

(* WHICH ALTERNATIVES A LINE SHAPE ADMITS, and [sel]'s shape *)
Definition ralt_ok (l : uline) (a : ralt) : Prop :=
  match l with
  | LEcho _ => match a with REcho k => (k < 4)%nat | _ => False end
  | LEchoF ws =>
      match a with
      | RFRan sel => sel_ok (echo_chunks ws) sel
      | RFExec | RFOpenU | RFOpenM | RFSilent | RFFork => True
      | _ => False
      end
  | LCat =>
      match a with
      | RCRan | RCNoOpen | RCExec | RCSilent | RCFork => True
      | _ => False
      end
  (* THE DEAD ARM.  [lines_of] never yields [LPipe] ([uline_of_nopipe]),
     so which alternatives this line admits is unobservable to every FILE
     statement; it is [LCat]'s five because that makes [fsm], [cont] and
     every per-line choice ([FileOutPure.ralt_def],
     [FileHooks.fpan_of]/[fexf_of]/[fnoc_of]) agree with [LCat]'s arm
     verbatim, and so costs each landed proof one copied line.  The PIPE
     application reads its own [PipeDisc.palt_ok]/[pcont], never these. *)
  | LPipe _ _ =>
      match a with
      | RCRan | RCNoOpen | RCExec | RCSilent | RCFork => True
      | _ => False
      end
  end.

Global Instance ralt_ok_dec l a : Decision (ralt_ok l a).
Proof using. destruct l, a; rewrite /ralt_ok; apply _. Defined.

(* THE F-EFFECT.  [RFOpenM] is guarded at an ABSENT f (design section 1):
   xv6's [sys_open] truncates only after [filealloc] has succeeded, so at a
   present f the failed open leaves the file alone and this alternative is
   [RFOpenU].  [RFSilent]'s effect is IDENTITY (RULING HOLD-POS, 2026-09-18):
   it is sh's [argv[0] == 0] exit, unreachable under the discipline, and
   every line shape then has one silent alternative that leaves `f` alone
   ([REcho 2] / [RFSilent] / [RCSilent]) -- which is what the round's
   credential files at the fork's relayed failure row. *)
Definition fsm (s : fstate) (l : uline) (a : ralt) : fstate :=
  match l with
  | LEchoF ws =>
      match a with
      | RFRan sel => Some (subseq (echo_chunks ws) sel)
      | RFExec => Some []
      | RFSilent => s
      | RFOpenM => match s with None => Some [] | Some _ => s end
      | _ => s
      end
  | _ => s
  end.

(* THE CONSOLE CONTINUATION of a round, at the state the file is in when it
   starts.  At [REcho] it is [EchoDisc.line_alts_of] verbatim. *)
Definition cont (s : fstate) (l : uline) (a : ralt) : list (bv 8) :=
  match a with
  | REcho k => line_alts_of (uline_ws l) !!! k
  | RFRan _ => u_prompt
  | RFExec => alt_execfail
  | RFOpenU => alt_openfail
  | RFOpenM => alt_openfail
  | RFSilent => u_prompt
  | RFFork => alt_panic
  | RCRan => match s with Some bs => bs ++ u_prompt | None => alt_catopen end
  | RCNoOpen => alt_catopen
  | RCExec => alt_execcat
  | RCSilent => u_prompt
  | RCFork => alt_panic
  end.

Lemma fstate_ok_fsm s l a : fstate_ok s -> uline_ok l -> ralt_ok l a -> fstate_ok (fsm s l a).
Proof using.
  intros Hs Hl Ha. destruct l as [ws | ws | | ws npc]; [exact Hs | | exact Hs | exact Hs].
  destruct a; try exact Hs; try (by left; constructor).
  - destruct Hl as [Hok _]. exact (fcont_ok_subseq ws sel Hok Ha).
  - destruct s as [bs |]; [exact Hs | by left; constructor].
Qed.

(* ---- EVERY ALTERNATIVE'S OWN OUTPUT, IN ONE SHAPE -------------------- *)

(* '$' is not a byte of any word line, and a word line's ONE newline is its
   last byte.  Both readings come off [LineWords] at once. *)
Lemma wl_line_shape ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl].
Proof using.
  intro Hwf. split.
  - apply Forall_forall. intros b Hb.
    pose proof (wl_line_byte_val ws b Hwf Hb) as Hv. rewrite /nodollar. lia.
  - exists (wl_body ws). split; [exact (wl_body_nonl ws Hwf) | reflexivity].
Qed.

Lemma wl_line_shape' ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ (wl_nl ∉ wl_line ws
      \/ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl]).
Proof using.
  intro H. destruct (wl_line_shape ws H) as [H1 H2].
  split; [exact H1 | by right].
Qed.

(* THE ENGINE OF THE DETERMINACY ARGUMENT: a non-panic alternative prints a
   '$'-free run -- whose only newline, if any, is its last byte -- and then
   sh's prompt.  A panic alternative prints sh's panic line and the
   prologue init then opens.  There is no third shape, at any line, at any
   file state: which is why no table of alternatives appears below. *)
Lemma cont_panic s l a : ralt_panic a = true -> cont s l a = alt_panic.
Proof using.
  destruct a; try discriminate; [| reflexivity | reflexivity].
  rewrite /ralt_panic. intro Hk. apply bool_decide_eq_true in Hk as ->.
  exact (line_alts_of_3 (uline_ws l)).
Qed.

Lemma cont_shape s l a :
  uline_ok l -> fstate_ok s -> ralt_ok l a -> ralt_panic a = false ->
  exists u, cont s l a = u ++ u_prompt
            /\ Forall nodollar u
            /\ (wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl]).
Proof using.
  intros Hl Hs Ha Hp.
  assert (Hex : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hop : wl_wf dg_open)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hec : wl_wf dg_exec_cat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpr : exists u : list (bv 8), u_prompt = u ++ u_prompt
                  /\ Forall nodollar u
                  /\ (wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl])).
  { exists []. split; [reflexivity |]. split; [constructor |].
    left. apply not_elem_of_nil. }
  destruct a; rewrite /cont.
  - (* REcho: the echo application's four, minus the panic one *)
    rewrite /ralt_panic in Hp. apply bool_decide_eq_false in Hp.
    rewrite /ralt_ok in Ha. destruct l as [ws | ws | | ws npc]; [| done | done | done].
    destruct a as [| [| [| [| a]]]]; [| | | done | exfalso; lia].
    + exists (wl_line (drop 1 ws)). rewrite line_alts_of_0.
      split; [reflexivity |].
      apply (wl_line_shape' (drop 1 ws)).
      apply lb_Forall_drop, (line_ok_wf _ Hl).
    + exists (wl_line dg_exec). rewrite line_alts_of_1 /alt_execfail.
      split; [reflexivity |]. exact (wl_line_shape' dg_exec Hex).
    + rewrite line_alts_of_2 /alt_prompt. exact Hpr.
  - exact Hpr.
  - exists (wl_line dg_exec). rewrite /alt_execfail.
    split; [reflexivity |]. exact (wl_line_shape' dg_exec Hex).
  - exists (wl_line dg_open). rewrite /alt_openfail.
    split; [reflexivity |]. exact (wl_line_shape' dg_open Hop).
  - exists (wl_line dg_open). rewrite /alt_openfail.
    split; [reflexivity |]. exact (wl_line_shape' dg_open Hop).
  - exact Hpr.
  - discriminate.
  - (* cat ran: the content, or its own diagnostic *)
    destruct s as [bs |].
    + exists bs. split; [reflexivity |].
      split; [exact (fcont_ok_nodollar bs Hs) | exact (fcont_ok_nl bs Hs)].
    + exists dg_catopen. rewrite /alt_catopen. split; [reflexivity |].
      split.
      * apply (bool_decide_unpack _). vm_compute. exact I.
      * right. exists (sb "cat: cannot open f"%string). split; [| reflexivity].
        apply (bool_decide_unpack _). vm_compute. exact I.
  - exists dg_catopen. rewrite /alt_catopen. split; [reflexivity |].
    split.
    + apply (bool_decide_unpack _). vm_compute. exact I.
    + right. exists (sb "cat: cannot open f"%string). split; [| reflexivity].
      apply (bool_decide_unpack _). vm_compute. exact I.
  - exists (wl_line dg_exec_cat). rewrite /alt_execcat.
    split; [reflexivity |]. exact (wl_line_shape' dg_exec_cat Hec).
  - exact Hpr.
  - discriminate.
Qed.

(* ====================================================================== *)
(*  4.  THE SESSION, WITH THE FILE STATE THREADED                          *)
(* ====================================================================== *)

(* the alternative round [i] took, decoded; out of range it reads the
   inhabitant, which keeps every function below TOTAL exactly as
   [EchoDisc]'s do -- the choices are pinned by the wire wherever the
   discipline actually looks at them *)
Definition ralt_at (cs : list nat) (i : nat) : ralt := ralt_dec (cs !!! i).

(* how many shells have died on their own fork panic BEFORE line [i] --
   [EchoDisc.pro_idx] at the three panic alternatives instead of the one *)
Fixpoint pro_idx_f (cs : list nat) (i : nat) : nat :=
  match i with
  | 0%nat => 0%nat
  | S i' => (pro_idx_f cs i' + if ralt_panic (ralt_at cs i') then 1 else 0)%nat
  end.

(* THE FILE STATE BEFORE ROUND [q]: the boot state, moved by every round
   before it.  This is the whole of what the file adds to the session. *)
Fixpoint fstate_upto (cs : list nat) (s : fstate) (bs : list (list (bv 8)))
    (q : nat) : fstate :=
  match q with
  | 0%nat => s
  | S q' => fsm (fstate_upto cs s bs q') (uline_of (bs !!! q')) (ralt_at cs q')
  end.

Definition alt_cont_f (ps cs : list nat) (s : fstate)
    (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
  cont (fstate_upto cs s bs i) (uline_of (bs !!! i)) (ralt_at cs i)
  ++ (if ralt_panic (ralt_at cs i)
      then pro_of (pro_from (S (pro_idx_f cs i)) ps) else []).

Definition alt_blk_f (ps cs : list nat) (s : fstate)
    (bs : list (list (bv 8))) (i : nat) : list (bv 8) :=
  bs !!! i ++ wl_nl :: alt_cont_f ps cs s bs i.

Definition alt_seq_f (ps cs : list nat) (s : fstate)
    (bs : list (list (bv 8))) (q : nat) : list (bv 8) :=
  concat (alt_blk_f ps cs s bs <$> List.seq 0 q).

(* THE EXPECTED SESSION TRANSCRIPT for the era's input [I] at boot state
   [s]: [EchoDisc.sess] with the file threaded through the blocks. *)
Definition sessf (ps cs : list nat) (s : fstate) (I : list (bv 8))
  : list (bv 8) :=
  pro_of ps ++ alt_seq_f ps cs s (bodies_of I) (nlines I) ++ rest_of I.

(* the state after the last COMPLETE line of [I] *)
Definition fstate_after (cs : list nat) (s : fstate) (I : list (bv 8)) : fstate :=
  fstate_upto cs s (bodies_of I) (nlines I).

(* ---- the round pointer ----------------------------------------------- *)

Lemma pro_idx_f_S cs i :
  pro_idx_f cs (S i)
  = (pro_idx_f cs i + if ralt_panic (ralt_at cs i) then 1 else 0)%nat.
Proof using. reflexivity. Qed.

Lemma pro_idx_f_Sp cs i :
  ralt_panic (ralt_at cs i) = true -> pro_idx_f cs (S i) = S (pro_idx_f cs i).
Proof using. intro H. rewrite pro_idx_f_S H. lia. Qed.

Lemma pro_idx_f_Sn cs i :
  ralt_panic (ralt_at cs i) = false -> pro_idx_f cs (S i) = pro_idx_f cs i.
Proof using. intro H. rewrite pro_idx_f_S H. lia. Qed.

Lemma pro_idx_f_mono cs i j :
  (i <= j)%nat -> (pro_idx_f cs i <= pro_idx_f cs j)%nat.
Proof using.
  intros Hij. induction j as [| j IH].
  - assert (i = 0%nat) by lia. by subst i.
  - destruct (decide (i = S j)) as [-> | Hne]; [done |].
    rewrite pro_idx_f_S.
    assert (pro_idx_f cs i <= pro_idx_f cs j)%nat by (apply IH; lia).
    destruct (ralt_panic (ralt_at cs j)); lia.
Qed.

Lemma pro_idx_f_le cs i : (pro_idx_f cs i <= i)%nat.
Proof using.
  induction i as [| i IH]; [cbn; lia |].
  rewrite pro_idx_f_S. destruct (ralt_panic (ralt_at cs i)); lia.
Qed.

Lemma pro_idx_f_S_le cs i : (pro_idx_f cs (S i) <= S (pro_idx_f cs i))%nat.
Proof using. rewrite pro_idx_f_S. destruct (ralt_panic (ralt_at cs i)); lia. Qed.

Lemma pro_idx_f_ext cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  forall j, (j <= q)%nat -> pro_idx_f cs1 j = pro_idx_f cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_f_S IH; [| lia].
  by rewrite /ralt_at (Hj j ltac:(lia)).
Qed.

Lemma pro_idx_f_add cs n i :
  pro_idx_f cs (n + i) = (pro_idx_f cs n + pro_idx_f (drop n cs) i)%nat.
Proof using.
  induction i as [| i IH]; [rewrite Nat.add_0_r; cbn [pro_idx_f]; lia |].
  rewrite Nat.add_succ_r !pro_idx_f_S IH /ralt_at lb_lookup_total_drop.
  destruct (ralt_panic (ralt_dec (cs !!! (n + i)))); lia.
Qed.

(* ---- the state, and the two ways to read it -------------------------- *)

Lemma fstate_upto_ext cs1 cs2 s bs1 bs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  fstate_upto cs1 s bs1 q = fstate_upto cs2 s bs2 q.
Proof using.
  intros Hc Hb. induction q as [| q IH]; [reflexivity |].
  cbn [fstate_upto]. rewrite IH; [| intros j Hj; apply Hc; lia
                              | intros j Hj; apply Hb; lia].
  by rewrite /ralt_at (Hc q ltac:(lia)) (Hb q ltac:(lia)).
Qed.

Lemma fstate_upto_drop cs s bs n i :
  fstate_upto (drop n cs) (fstate_upto cs s bs n) (drop n bs) i
  = fstate_upto cs s bs (n + i).
Proof using.
  induction i as [| i IH]; [by rewrite Nat.add_0_r |].
  rewrite Nat.add_succ_r. cbn [fstate_upto]. rewrite IH.
  by rewrite /ralt_at !lb_lookup_total_drop.
Qed.

(* ---- the block sequence ---------------------------------------------- *)

Lemma alt_seq_f_0 ps cs s bs : alt_seq_f ps cs s bs 0 = [].
Proof using. reflexivity. Qed.

Lemma alt_seq_f_S ps cs s bs q :
  alt_seq_f ps cs s bs (S q) = alt_seq_f ps cs s bs q ++ alt_blk_f ps cs s bs q.
Proof using.
  rewrite /alt_seq_f List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

Lemma alt_blk_f_ext ps1 ps2 cs1 cs2 s bs1 bs2 q :
  (forall j, (j <= q)%nat -> cs1 !!! j = cs2 !!! j) ->
  (forall j, (j <= q)%nat -> bs1 !!! j = bs2 !!! j) ->
  (forall r, (r <= pro_idx_f cs1 (S q))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_blk_f ps1 cs1 s bs1 q = alt_blk_f ps2 cs2 s bs2 q.
Proof using.
  intros Hc Hb Hr. rewrite /alt_blk_f /alt_cont_f.
  rewrite (Hb q ltac:(lia)) /ralt_at (Hc q ltac:(lia)).
  rewrite (fstate_upto_ext cs1 cs2 s bs1 bs2 q
             ltac:(intros j Hj; apply Hc; lia)
             ltac:(intros j Hj; apply Hb; lia)).
  destruct (ralt_panic (ralt_dec (cs2 !!! q))) eqn:Hpa; [| reflexivity].
  rewrite (pro_idx_f_ext cs1 cs2 q ltac:(intros j Hj; apply Hc; lia) q
             ltac:(lia)).
  rewrite (Hr (S (pro_idx_f cs2 q))); [reflexivity |].
  rewrite pro_idx_f_S -(pro_idx_f_ext cs1 cs2 q
            ltac:(intros j Hj; apply Hc; lia) q ltac:(lia)).
  rewrite /ralt_at -(Hc q ltac:(lia)) in Hpa. rewrite Hpa. lia.
Qed.

Lemma alt_seq_f_ext ps1 ps2 cs1 cs2 s bs1 bs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  (forall r, (r <= pro_idx_f cs1 q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq_f ps1 cs1 s bs1 q = alt_seq_f ps2 cs2 s bs2 q.
Proof using.
  induction q as [| q IH]; intros Hc Hb Hr; [reflexivity |].
  rewrite !alt_seq_f_S.
  rewrite (IH ltac:(intros j Hj; apply Hc; lia)
              ltac:(intros j Hj; apply Hb; lia)
              ltac:(intros r Hr'; apply Hr;
                    pose proof (pro_idx_f_mono cs1 q (S q) ltac:(lia)); lia)).
  by rewrite (alt_blk_f_ext ps1 ps2 cs1 cs2 s bs1 bs2 q
                ltac:(intros j Hj; apply Hc; lia)
                ltac:(intros j Hj; apply Hb; lia) Hr).
Qed.

(* two body lists that agree below [q] give the same sequence -- which is
   what makes a completed line's block independent of the lines after it *)
Lemma alt_seq_f_bs_ext ps cs s bs1 bs2 q :
  (forall j, (j < q)%nat -> bs1 !!! j = bs2 !!! j) ->
  alt_seq_f ps cs s bs1 q = alt_seq_f ps cs s bs2 q.
Proof using.
  intro Hb. by apply (alt_seq_f_ext ps ps cs cs s bs1 bs2 q).
Qed.

Lemma alt_seq_f_bs_app ps cs s bs bs' q :
  (q <= length bs)%nat ->
  alt_seq_f ps cs s (bs ++ bs') q = alt_seq_f ps cs s bs q.
Proof using.
  intro Hq. apply alt_seq_f_bs_ext. intros j Hj.
  rewrite !list_lookup_total_alt lookup_app_l; [reflexivity | lia].
Qed.

Lemma alt_seq_f_cs_ext ps cs1 cs2 s bs q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  alt_seq_f ps cs1 s bs q = alt_seq_f ps cs2 s bs q.
Proof using.
  intro Hc. by apply (alt_seq_f_ext ps ps cs1 cs2 s bs bs q).
Qed.

Lemma alt_seq_f_ps_ext ps1 ps2 cs s bs q :
  (forall r, (r <= pro_idx_f cs q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq_f ps1 cs s bs q = alt_seq_f ps2 cs s bs q.
Proof using.
  intro Hr. by apply (alt_seq_f_ext ps1 ps2 cs cs s bs bs q).
Qed.

(* ---- dropping the first block, which is what the induction consumes -- *)

Lemma alt_cont_f_drop ps cs s bs n i :
  alt_cont_f (pro_from (pro_idx_f cs n) ps) (drop n cs) (fstate_upto cs s bs n)
    (drop n bs) i
  = alt_cont_f ps cs s bs (n + i).
Proof using.
  rewrite /alt_cont_f !lb_lookup_total_drop /ralt_at !lb_lookup_total_drop.
  rewrite fstate_upto_drop. f_equal.
  destruct (ralt_panic (ralt_dec (cs !!! (n + i)))); [| reflexivity].
  rewrite pro_from_add pro_idx_f_add. f_equal. f_equal. lia.
Qed.

Lemma alt_blk_f_drop ps cs s bs n i :
  alt_blk_f (pro_from (pro_idx_f cs n) ps) (drop n cs) (fstate_upto cs s bs n)
    (drop n bs) i
  = alt_blk_f ps cs s bs (n + i).
Proof using.
  by rewrite /alt_blk_f lb_lookup_total_drop alt_cont_f_drop.
Qed.

Lemma alt_seq_f_cons ps cs s bs q :
  alt_seq_f ps cs s bs (S q)
  = alt_blk_f ps cs s bs 0%nat
    ++ alt_seq_f (pro_from (pro_idx_f cs 1%nat) ps) (drop 1 cs)
         (fstate_upto cs s bs 1%nat) (drop 1 bs) q.
Proof using.
  rewrite /alt_seq_f.
  replace (List.seq 0 (S q)) with (0%nat :: List.seq 1 q) by reflexivity.
  rewrite fmap_cons concat_cons. f_equal.
  rewrite -List.seq_shift -list_fmap_compose.
  f_equal. apply list_fmap_ext.
  intros i x Hx. rewrite /compose. by rewrite (alt_blk_f_drop ps cs s bs 1 x).
Qed.

Lemma alt_seq_f_cons_assoc ps cs s bs q (t : list (bv 8)) :
  alt_seq_f ps cs s bs (S q) ++ t
  = bs !!! 0%nat
    ++ wl_nl :: (alt_cont_f ps cs s bs 0%nat
                 ++ (alt_seq_f (pro_from (pro_idx_f cs 1%nat) ps) (drop 1 cs)
                       (fstate_upto cs s bs 1%nat) (drop 1 bs) q ++ t)).
Proof using. rewrite alt_seq_f_cons /alt_blk_f. apply lb_app4. Qed.

(* ---- THE SESSION'S LAWS, at [EchoDisc.sess]'s statements ------------- *)

Lemma sessf_nil ps cs s : sessf ps cs s [] = pro_of ps.
Proof using.
  rewrite /sessf rest_of_nil nlines_nil alt_seq_f_0. by rewrite !app_nil_r.
Qed.

Lemma sessf_snoc_other ps cs s I b :
  b <> wl_nl -> sessf ps cs s (I ++ [b]) = sessf ps cs s I ++ [b].
Proof using.
  intro Hb. rewrite /sessf (bodies_of_snoc_other I b Hb)
    (nlines_snoc_other I b Hb) (rest_of_snoc_other I b Hb).
  by rewrite !app_assoc.
Qed.

Lemma sessf_snoc_nl ps cs s I :
  sessf ps cs s (I ++ [wl_nl])
  = sessf ps cs s I
    ++ wl_nl :: alt_cont_f ps cs s (bodies_of I ++ [rest_of I]) (nlines I).
Proof using.
  assert (Hidx : (bodies_of I ++ [rest_of I]) !!! (nlines I) = rest_of I).
  { rewrite list_lookup_total_alt
      (lookup_app_r (bodies_of I) [rest_of I] (nlines I)
         ltac:(rewrite /nlines; lia)).
    rewrite /nlines Nat.sub_diag. reflexivity. }
  rewrite {1}/sessf bodies_of_snoc_nl nlines_snoc_nl rest_of_snoc_nl.
  rewrite alt_seq_f_S (alt_seq_f_bs_app ps cs s (bodies_of I) [rest_of I]
                         (nlines I) ltac:(rewrite /nlines; lia)).
  rewrite /alt_blk_f Hidx app_nil_r /sessf.
  by rewrite !app_assoc.
Qed.

Lemma sessf_step ps cs s I b :
  sessf ps cs s I `prefix_of` sessf ps cs s (I ++ [b]).
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sessf_snoc_nl. by eexists.
  - rewrite (sessf_snoc_other ps cs s I b Hb). by eexists.
Qed.

Lemma sessf_mono ps cs s I I' :
  I `prefix_of` I' -> sessf ps cs s I `prefix_of` sessf ps cs s I'.
Proof using.
  intros [k ->]. induction k as [| b k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply sessf_step].
Qed.

Lemma sessf_take ps cs s I q :
  (nlines I <= q)%nat -> sessf ps (take q cs) s I = sessf ps cs s I.
Proof using.
  intros Hq. rewrite /sessf. do 2 f_equal.
  apply alt_seq_f_cs_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma sessf_ps_ext ps1 ps2 cs s I :
  (forall r, (r <= pro_idx_f cs (nlines I))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  sessf ps1 cs s I = sessf ps2 cs s I.
Proof using.
  intros Hr. rewrite /sessf (Hr 0%nat ltac:(lia)).
  by rewrite (alt_seq_f_ps_ext ps1 ps2 cs s (bodies_of I) (nlines I) Hr).
Qed.

(* the side condition [EchoDisc.pro_ok]/[pro_pin] state, at the panic
   alternatives of all three line shapes *)
Definition pro_ok_f (ps cs : list nat) (q : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx_f cs q < pro_rounds ps)%nat.

Global Instance pro_ok_f_dec ps cs q : Decision (pro_ok_f ps cs q).
Proof using. rewrite /pro_ok_f. apply _. Defined.

Lemma pro_ok_f_mono ps cs q q' :
  (q' <= q)%nat -> pro_ok_f ps cs q -> pro_ok_f ps cs q'.
Proof using.
  intros Hq [HF Hlt]. split; [exact HF |].
  pose proof (pro_idx_f_mono cs q' q Hq). lia.
Qed.

Definition pro_pin_f (ps cs : list nat) (I : list (bv 8)) : Prop :=
  forall q, (q < nstarted I)%nat -> (pro_idx_f cs q < pro_rounds ps)%nat.

Lemma pro_pin_f_of_ok ps cs I :
  pro_ok_f ps cs (nlines I) -> pro_pin_f ps cs I.
Proof using.
  intros [_ Hlt] q Hq.
  pose proof (nstarted_le_S I) as H1.
  pose proof (pro_idx_f_mono cs q (nlines I)) as H2.
  destruct (decide (q <= nlines I)%nat) as [Hle | Hgt]; [lia |].
  (* [q] is the line in progress: [nstarted] is [nlines + 1] *)
  assert (Hq' : q = nlines I) by lia. lia.
Qed.

(* ====================================================================== *)
(*  5.  THE DISCIPLINE, THE CLAIM, AND THE HISTORY                         *)
(* ====================================================================== *)

(* D3 over one power cycle's input *)
Definition disc_seg_f (seg : list mobs) : Prop := disc_input_f (ins seg).

Global Instance disc_seg_f_dec seg : Decision (disc_seg_f seg).
Proof using. rewrite /disc_seg_f. apply _. Defined.

Lemma disc_seg_f_nil : disc_seg_f [].
Proof using. exact disc_input_f_nil. Qed.

Lemma disc_seg_f_out (seg : list mobs) (b : bv 8) :
  disc_seg_f (seg ++ [ObsUartOut Uart0 b]) <-> disc_seg_f seg.
Proof using. rewrite /disc_seg_f ins_app ins_out app_nil_r. done. Qed.

Lemma disc_seg_f_prefix (seg' seg : list mobs) :
  seg' `prefix_of` seg -> disc_seg_f seg -> disc_seg_f seg'.
Proof using.
  intros [k ->] Hd. rewrite /disc_seg_f ins_app in Hd.
  apply (disc_input_f_prefix _ _ ltac:(by eexists) Hd).
Qed.

(* D1/D2 AT ONE INPUT POSITION, at [EchoDisc.disc_pt]'s statement with
   [sessf] in place of [sess]: the expected transcript for the COMPLETE
   LINES typed so far ([LineWords.done_of]) -- read at the era's boot
   state -- is already on the wire.  The rule is the RELAXED per-line one
   echo's is (ruled 2026-09-23): a user may type a line as a burst, and only
   the previous line's block has to have ended before the next line's first
   byte.  The rest of the wire's account -- that every typed byte is echoed
   before the next is filed -- is the kernel's FIFO discipline, read off
   [ConsLog.cons_ev_ok] at the arm's open ([FileOut.fecl_pure_open]). *)
Definition disc_pt_f (ps cs : list nat) (s : fstate) (p : list mobs) : Prop :=
  sessf ps cs s (done_of (ins p)) `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_f_dec ps cs s p : Decision (disc_pt_f ps cs s p).
Proof using. rewrite /disc_pt_f. apply _. Defined.

(* THE STRICT RULE IMPLIES THE RELAXED ONE, [EchoDisc.disc_pt_of_strict]'s
   twin: a session that waited for every byte's echo is disciplined here. *)
Lemma disc_pt_f_of_strict (ps cs : list nat) (s : fstate) (p : list mobs) :
  sessf ps cs s (ins p) `prefix_of` obs_wire Uart0 p -> disc_pt_f ps cs s p.
Proof using.
  intro H. rewrite /disc_pt_f. etrans; [| exact H].
  apply sessf_mono, done_of_prefix.
Qed.

(* the resolution's range condition, where [EchoDisc]'s was [c < 4]: every
   line's alternative is one ITS SHAPE admits.  [Forall2] also pins the
   length, which [EchoDisc.disc_seg'] states separately. *)
Definition alts_ok (I : list (bv 8)) (cs : list nat) : Prop :=
  Forall2 (fun l c => ralt_ok l (ralt_dec c)) (lines_of I) cs.

Global Instance alts_ok_dec I cs : Decision (alts_ok I cs).
Proof using. rewrite /alts_ok. apply _. Defined.

Lemma alts_ok_length I cs : alts_ok I cs -> length cs = nlines I.
Proof using.
  intro H. apply Forall2_length in H.
  by rewrite /lines_of length_fmap in H.
Qed.

Lemma alts_ok_at I cs i :
  alts_ok I cs -> (i < nlines I)%nat ->
  ralt_ok (uline_of (bodies_of I !!! i)) (ralt_at cs i).
Proof using.
  intros H Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
  assert (Hl : lines_of I !! i = Some (uline_of b))
    by (rewrite /lines_of list_lookup_fmap Hb; reflexivity).
  destruct (Forall2_lookup_l _ _ _ _ _ H Hl) as (c & Hc & Hok).
  rewrite /ralt_at (list_lookup_total_correct cs i c Hc).
  by rewrite (list_lookup_total_correct _ _ _ Hb).
Qed.

(* THE PER-CYCLE DISCIPLINE, at [EchoDisc.disc_seg']'s shape, with the
   era's BOOT STATE a parameter: what the user must do does not depend on
   the file, but what the wire shows does, so the state the era started in
   is what the transcript is read at. *)
Definition disc_seg_f' (s : fstate) (seg : list mobs) : Prop :=
  disc_seg_f seg
  /\ exists ps cs : list nat,
       alts_ok (ins seg) cs
       /\ forall p : list mobs, p ∈ in_pres seg ->
            pro_ok_f ps cs (nlines (ins p)) /\ disc_pt_f ps cs s p.

(* the constructor the literals below spend, [EchoDisc.disc_seg'_intro]'s
   twin.  ([disc_seg_f'] is NOT claimed decidable: the search over the
   resolutions that [EchoDisc] can run needs a bound on [sel], and no
   consumer asks for it.) *)
Definition disc_pt_all_f (ps cs : list nat) (s : fstate) (seg : list mobs) : Prop :=
  Forall (fun p => pro_ok_f ps cs (nlines (ins p)) /\ disc_pt_f ps cs s p)
    (in_pres seg).

Global Instance disc_pt_all_f_dec ps cs s seg : Decision (disc_pt_all_f ps cs s seg).
Proof using. rewrite /disc_pt_all_f. apply _. Defined.

Lemma disc_seg_f'_intro (s : fstate) (seg : list mobs) (ps cs : list nat) :
  disc_seg_f seg -> alts_ok (ins seg) cs -> disc_pt_all_f ps cs s seg ->
  disc_seg_f' s seg.
Proof using.
  intros Hd Hl Hall. split; [exact Hd |]. exists ps, cs.
  split; [exact Hl |].
  intros p Hp. exact (proj1 (Forall_forall _ _) Hall p Hp).
Qed.

Lemma disc_seg_f'_nil s : disc_seg_f' s [].
Proof using.
  split; [exact disc_seg_f_nil |]. exists [], [].
  split; [rewrite /alts_ok; constructor |].
  intros p Hp. by apply elem_of_nil in Hp.
Qed.

(* THE DISCIPLINE OVER THE WHOLE HISTORY.  Each cycle is read at SOME boot
   state: the theorem's conclusion ([file_phi]) is what ties those states
   to what earlier cycles typed. *)
Definition disc_f (h : list mobs) : Prop :=
  Forall (fun seg => exists s : fstate, fstate_ok s /\ disc_seg_f' s seg) (cycles_of h).

Lemma disc_f_nil : disc_f [].
Proof using. constructor. Qed.

Lemma disc_f_seg h seg : disc_f h -> seg ∈ cycles_of h -> disc_seg_f seg.
Proof using.
  intros Hd Hin. apply elem_of_list_lookup in Hin as [i Hi].
  destruct (Forall_lookup_1 _ _ _ _ Hd Hi) as (s & _ & Hs & _). exact Hs.
Qed.

(* THE OUTPUT CLAIM for one power cycle, at a boot state: everything on the
   console wire is a prefix of the transcript this cycle's input calls for,
   under some resolution.  [EchoDisc.good_out] with [sessf]. *)
Definition good_out_f (s : fstate) (seg : list mobs) : Prop :=
  exists ps cs : list nat,
    pro_ok_f ps cs (nlines (ins seg))
    /\ alts_ok (ins seg) cs
    /\ obs_wire Uart0 seg `prefix_of` sessf ps cs s (ins seg).

Lemma good_out_f_nil s : good_out_f s [].
Proof using.
  exists [0%nat], []. split.
  { split.
    - apply Forall_singleton. rewrite pro_alts_length. lia.
    - vm_compute. lia. }
  split; [rewrite /alts_ok; constructor |].
  apply prefix_nil.
Qed.

(* ---- THE LINES THE FILE MAY HOLD ------------------------------------- *)

Definition echof_ws (l : uline) : option (list (list (bv 8))) :=
  match l with LEchoF ws => Some ws | _ => None end.

(* the word lists of the [LEchoF] lines of one input, in order *)
Definition echof_lines_in (I : list (bv 8)) : list (list (list (bv 8))) :=
  omap echof_ws (lines_of I).

Definition echof_cyc (seg : list mobs) : list (list (list (bv 8))) :=
  echof_lines_in (ins seg).

Definition echof_lines_of (h : list mobs) : list (list (list (bv 8))) :=
  concat (echof_cyc <$> cycles_of h).

(* ...and the ones typed in cycles STRICTLY BEFORE cycle [k], which is the
   set a boot state at cycle [k] may have come from *)
Definition echof_lines_before (h : list mobs) (k : nat)
  : list (list (list (bv 8))) :=
  concat (echof_cyc <$> take k (cycles_of h)).

Lemma echof_lines_before_all h :
  echof_lines_before h (length (cycles_of h)) = echof_lines_of h.
Proof using. by rewrite /echof_lines_before take_ge. Qed.

Lemma echof_lines_in_app I k :
  echof_lines_in I `prefix_of` echof_lines_in (I ++ k).
Proof using.
  destruct (bodies_of_app I k) as [z Hz].
  rewrite /echof_lines_in /lines_of Hz fmap_app omap_app. by eexists.
Qed.

Lemma echof_lines_in_prefix I I' :
  I `prefix_of` I' -> echof_lines_in I `prefix_of` echof_lines_in I'.
Proof using. intros [k ->]. apply echof_lines_in_app. Qed.

Lemma echof_cyc_app seg k :
  echof_cyc seg `prefix_of` echof_cyc (seg ++ k).
Proof using.
  rewrite /echof_cyc ins_app. apply echof_lines_in_app.
Qed.

Lemma echof_lines_of_snoc h e :
  echof_lines_of h `prefix_of` echof_lines_of (h ++ [e]).
Proof using.
  rewrite /echof_lines_of /cycles_of cycles_rev_app /=.
  destruct e as [i b | i b | |]; cbn [cyc_step].
  - destruct (cycles_rev h) as [| c cs].
    + rewrite /=. apply prefix_nil.
    + cbn [rev]. rewrite !fmap_app !concat_app /=.
      rewrite !app_nil_r. apply prefix_app, echof_cyc_app.
  - destruct (cycles_rev h) as [| c cs].
    + rewrite /=. apply prefix_nil.
    + cbn [rev]. rewrite !fmap_app !concat_app /=.
      rewrite !app_nil_r. apply prefix_app, echof_cyc_app.
  - cbn [rev]. rewrite fmap_app concat_app.
    apply prefix_app_r. reflexivity.
  - reflexivity.
Qed.

Lemma echof_lines_of_prefix h' h :
  h' `prefix_of` h -> echof_lines_of h' `prefix_of` echof_lines_of h.
Proof using.
  intros [k ->]. induction k as [| e k IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply echof_lines_of_snoc].
Qed.

(* every line the file may hold is an ADMISSIBLE echo line -- which is what
   makes a boot state's content a content ([fstate_ok]) *)
Lemma echof_lines_in_ok I :
  disc_input_f I -> Forall line_ok (echof_lines_in I).
Proof using.
  intro Hd. apply Forall_forall. intros ws Hws.
  apply elem_of_list_omap in Hws as (l & Hl & Hws).
  apply elem_of_list_lookup in Hl as [i Hi].
  rewrite /lines_of list_lookup_fmap in Hi.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hi. injection Hi as <-.
  destruct (fbody_ok_line b (disc_input_f_body I i b Hd Hb)) as [Hok _].
  destruct (uline_of b) as [ws' | ws' | | ws' npc']; try discriminate.
  injection Hws as <-. exact (proj1 Hok).
Qed.

(* the boot state of an era: absent, or a chunk subsequence of a line
   typed in an EARLIER cycle (design section 1) *)
Definition fadm_boot (Ls : list (list (list (bv 8)))) (s : fstate) : Prop :=
  s = None
  \/ exists ws sel, ws ∈ Ls /\ sel_ok (echo_chunks ws) sel
                    /\ s = Some (subseq (echo_chunks ws) sel).

Lemma fadm_boot_fst_ok Ls s :
  Forall line_ok Ls -> fadm_boot Ls s -> fstate_ok s.
Proof using.
  intros HF [-> | (ws & sel & Hws & Hsel & ->)]; [exact I |].
  exact (fcont_ok_subseq ws sel (proj1 (Forall_forall _ _) HF ws Hws) Hsel).
Qed.

(* THE THEOREM'S CONCLUSION.  The file persists, so the statement is over
   the whole history, cycle by cycle, with each era's boot state chosen
   inside the admissible set -- and the FIRST era's boot state absent,
   because the mkfs image has no [f].

   THE FIRST CLAUSE IS GUARDED.  [cycles_of [] = []], so an unguarded
   [s0s !! 0 = Some None] would make [file_phi []] false while
   [disc_f []] holds; the guarded form says the same thing at every
   history that has a cycle. *)
Definition file_phi (h : list mobs) : Prop :=
  disc_f h ->
  exists s0s : list fstate,
    length s0s = length (cycles_of h)
    /\ (forall s, s0s !! 0%nat = Some s -> s = None)
    /\ (forall k s, s0s !! S k = Some s ->
          fadm_boot (echof_lines_before h (S k)) s)
    /\ Forall2 good_out_f s0s (cycles_of h).

(* ====================================================================== *)
(*  6.  THE LINE MODEL INSTANCE, AND DETERMINACY AS ITS COROLLARY          *)
(*                                                                        *)
(*  [sessf] is [LineModel.lm_sess] at the instance below, by conversion    *)
(*  ([alt_seq_f_lm] is [reflexivity]); the byte shape the determinacy      *)
(*  argument reads off this model is [cont_panic] and [cont_shape], and    *)
(*  no arm ends coverage.  [sessf_prefix_det] (two witnesses put the same  *)
(*  bytes on the wire) is then [LineModel.lm_sess_prefix_det] read back    *)
(*  through the equations.  It concludes an equality of BYTES and never    *)
(*  of indices or of file states, and it cannot conclude more: [RFOpenU]   *)
(*  and [RFOpenM] print the same bytes and leave different files, and      *)
(*  [RCRan] at an absent f prints exactly what [RCNoOpen] prints at a       *)
(*  present one.  The two-state form [sessf_prefix_det2] is what the       *)
(*  claim spends: the discipline's witness at the state the trace          *)
(*  predicate chose, the claim's own at the state filed off the deed.      *)
(* ====================================================================== *)
Definition file_lm : lmodel :=
  MkLM fstate uline uline_of ralt ralt_dec ralt_panic cont fsm
       (fun _ => ralt_ok) fbody_ok fbody_byte uline_ok fstate_ok
       (fun _ => false) (fun _ => False).

Lemma pro_idx_f_lm cs i : pro_idx_f cs i = lm_pro_idx file_lm cs i.
Proof using. induction i as [| i IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma fstate_upto_lm cs s bs q :
  fstate_upto cs s bs q = lm_upto file_lm cs s bs q.
Proof using. induction q as [| q IH]; [reflexivity |]. cbn. by rewrite IH. Qed.

Lemma alt_cont_f_lm ps cs s bs i :
  alt_cont_f ps cs s bs i = lm_cont_at file_lm ps cs s bs i.
Proof using.
  rewrite /alt_cont_f /lm_cont_at fstate_upto_lm pro_idx_f_lm. reflexivity.
Qed.

Lemma alt_seq_f_lm ps cs s bs q :
  alt_seq_f ps cs s bs q = lm_seq file_lm ps cs s bs q.
Proof using. reflexivity. Qed.

Lemma sessf_lm ps cs s I : sessf ps cs s I = lm_sess file_lm ps cs s I.
Proof using. rewrite /sessf /lm_sess. by rewrite alt_seq_f_lm. Qed.

Lemma alts_ok_lm s I cs : alts_ok I cs <-> lm_alts_ok file_lm s I cs.
Proof using.
  rewrite (lm_alts_ok_nostate file_lm s I cs (fun _ _ _ _ H => H)). reflexivity.
Qed.

Lemma disc_input_f_lm I : disc_input_f I = lm_disc_input file_lm I.
Proof using. reflexivity. Qed.

Lemma fstate_after_lm cs s I : fstate_after cs s I = lm_after file_lm cs s I.
Proof using. rewrite /fstate_after /lm_after. apply fstate_upto_lm. Qed.

Lemma pro_ok_f_lm ps cs q : pro_ok_f ps cs q <-> lm_pro_ok file_lm ps cs q.
Proof using. rewrite /pro_ok_f /lm_pro_ok pro_idx_f_lm. reflexivity. Qed.

(* ---- the discipline and the claim, as the model's ---- *)
Lemma disc_pt_f_lm ps cs s p : disc_pt_f ps cs s p <-> lm_disc_pt file_lm ps cs s p.
Proof using. rewrite /disc_pt_f /lm_disc_pt sessf_lm. done. Qed.

Lemma disc_seg_f'_lm s seg : disc_seg_f' s seg <-> lm_disc_seg' file_lm s seg.
Proof using.
  rewrite /disc_seg_f' /lm_disc_seg' /disc_seg_f disc_input_f_lm. split.
  - intros [Hd (ps & cs & Hao & Hall)]. split; [exact Hd |]. exists ps, cs.
    split; [by apply (alts_ok_lm s) |].
    split; [apply lm_d4_noterm; intro a; reflexivity |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_f_lm | by apply disc_pt_f_lm].
  - intros [Hd (ps & cs & Hao & _ & Hall)]. split; [exact Hd |]. exists ps, cs.
    split; [by apply (alts_ok_lm s) |].
    intros p Hp. destruct (Hall p Hp) as [Hok Hpt].
    split; [by apply pro_ok_f_lm | by apply disc_pt_f_lm].
Qed.

Lemma disc_f_lm h : disc_f h <-> lm_disc file_lm h.
Proof using.
  rewrite /disc_f /lm_disc. split; intros H.
  - eapply Forall_impl; [exact H |]. intros seg (s & Hs & Hd).
    exists s. split; [exact Hs | by apply disc_seg_f'_lm].
  - eapply Forall_impl; [exact H |]. intros seg (s & Hs & Hd).
    exists s. split; [exact Hs | by apply disc_seg_f'_lm].
Qed.

Lemma expected_rel_f_lm s I out :
  (exists ps cs : list nat,
     pro_ok_f ps cs (nlines I) /\ alts_ok I cs /\ out `prefix_of` sessf ps cs s I)
  <-> lm_expected_rel file_lm s I out.
Proof using.
  rewrite /lm_expected_rel. split.
  - intros (ps & cs & Hok & Hao & Hw). exists ps, cs.
    split; [by apply pro_ok_f_lm |]. split; [by apply (alts_ok_lm s) |].
    by rewrite -sessf_lm.
  - intros (ps & cs & Hok & Hao & Hw). exists ps, cs.
    split; [by apply pro_ok_f_lm |]. split; [by apply (alts_ok_lm s) |].
    by rewrite sessf_lm.
Qed.

Lemma good_out_f_lm s seg : good_out_f s seg <-> lm_good_out file_lm s seg.
Proof using. rewrite /good_out_f /lm_good_out. apply expected_rel_f_lm. Qed.

Lemma pro_pin_f_lm ps cs I : pro_pin_f ps cs I <-> lm_pro_pin file_lm ps cs I.
Proof using.
  rewrite /pro_pin_f /lm_pro_pin. split; intros H q Hq; specialize (H q Hq);
    by rewrite -?pro_idx_f_lm ?pro_idx_f_lm in H |- *.
Qed.

(* the byte shape: what section 3 proved of the alternatives *)
Lemma file_lm_laws : lm_laws file_lm.
Proof using.
  constructor.
  - intros b Hb. exact (proj1 (fbody_ok_line b Hb)).
  - intros s l a Hs Hl Ha. exact (fstate_ok_fsm s l a Hs Hl Ha).
  - intros s l a H. exact (cont_panic s l a H).
  - intros a H. cbn in H. discriminate H.
  - intros s l a _ _ H. cbn in H. discriminate H.
  - intros u' u _ H. exact H.
  - intros s l a Hs Hl Ha Hp _.
    destruct (cont_shape s l a Hl Hs Ha Hp) as (u & Hu & Hnd & Hnl).
    exists u. split; [exact Hu |]. split; [exact Hnd |].
    intros Y ps W _ Hcmp. exact (lb_out_eq_panic u Y _ Hnd Hnl (lm_below_panic_any u Y ps W Hcmp)).
  - intros s l c _ H. cbn in H. discriminate H.
Qed.

Lemma file_lm_byte_laws : lm_byte_laws file_lm.
Proof using.
  constructor.
  - intros l Hl. exact (fbody_ok_bytes l Hl).
  - intros l Hl. exact (fbody_ok_short l Hl).
  - intros b Hb. destruct Hb as [[Ha | ->] | ->].
    + destruct Ha as [H | [H | H]]; lia.
    + rewrite wl_sp_val. lia.
    + rewrite (_ : bv_unsigned wl_gt = 62%Z); [lia | by vm_compute].
  - change (ralt_panic (ralt_dec 0) = false).
    rewrite (ralt_dec_lt4 0 ltac:(lia)). by vm_compute.
Qed.

Lemma sessf_prefix_det2 (ps ps' cs cs' : list nat) (s s' : fstate)
    (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok_f ps' cs' (nlines I') ->
  alts_ok I cs -> alts_ok I' cs' ->
  pro_pin_f ps cs I -> disc_input_f I -> disc_input_f I' ->
  fstate_ok s -> fstate_ok s' ->
  sessf ps' cs' s' I' `prefix_of` sessf ps cs s I ->
  I' `prefix_of` I /\ pro_ok_f ps cs (nlines I')
  /\ sessf ps' cs' s' I' = sessf ps cs s I'.
Proof using.
  intros Hps Hok Hcs Hcs' Hpin Hd Hd' Hs Hs' Hpre.
  rewrite !sessf_lm in Hpre |- *.
  destruct (lm_sess_prefix_det file_lm file_lm_laws ps ps' cs cs' s s' I' I Hps
              (proj1 (pro_ok_f_lm _ _ _) Hok)
              (proj1 (alts_ok_lm s _ _) Hcs) (proj1 (alts_ok_lm s' _ _) Hcs')
              (proj1 (pro_pin_f_lm _ _ _) Hpin) Hd Hd' Hs Hs'
              ltac:(intros i _ H; cbn in H; discriminate H)
              ltac:(intros i _ (c & _ & H); cbn in H; discriminate H) Hpre)
    as (H1 & H2 & H3 & _).
  split; [exact H1 |]. split; [by apply pro_ok_f_lm | exact H3].
Qed.

Lemma sessf_prefix_det (ps ps' cs cs' : list nat) (s : fstate)
    (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok_f ps' cs' (nlines I') ->
  alts_ok I cs -> alts_ok I' cs' ->
  pro_pin_f ps cs I -> disc_input_f I -> disc_input_f I' -> fstate_ok s ->
  sessf ps' cs' s I' `prefix_of` sessf ps cs s I ->
  I' `prefix_of` I /\ pro_ok_f ps cs (nlines I')
  /\ sessf ps' cs' s I' = sessf ps cs s I'.
Proof using.
  intros Hps Hok Hcs Hcs' Hpin Hd Hd' Hs Hpre.
  exact (sessf_prefix_det2 ps ps' cs cs' s s I' I Hps Hok Hcs Hcs' Hpin Hd Hd'
           Hs Hs Hpre).
Qed.

(* ====================================================================== *)
(*  7.  THE ECHO APPLICATION IS THIS ONE AT ITS ECHO LINES                 *)
(*                                                                        *)
(*  Nothing in [EchoDisc] is re-stated or weakened: at a history whose     *)
(*  every complete line is an echo line, [sessf] IS [sess] and [disc_f]    *)
(*  IS [disc] -- the file's rounds are literally today's, which is why     *)
(*  the [REcho] alternatives had to encode as their own index.            *)
(* ====================================================================== *)

Definition echo_only (I : list (bv 8)) : Prop := Forall body_ok (bodies_of I).

Lemma echo_only_prefix I I' :
  I `prefix_of` I' -> echo_only I' -> echo_only I.
Proof using.
  intros Hp HF. rewrite /echo_only in HF |- *.
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite Hz in HF. by apply Forall_app in HF as [? _].
Qed.

Lemma parse_line_echo b : body_ok b -> parse_line b = Some (LEcho (wl_words b)).
Proof using.
  intro Hb. pose proof Hb as [Hbody Hok]. rewrite /parse_line.
  rewrite decide_False; last first.
  { intro Heq. apply cat_not_echo. rewrite -Heq -{1}Hbody.
    rewrite (wl_words_body (wl_words b) (line_ok_wf _ Hok)).
    exact (line_ok_head _ Hok). }
  destruct (strip_gtf b) as [c |] eqn:Hs.
  { exfalso. pose proof (strip_gtf_Some b c Hs) as Hbc.
    pose proof (body_ok_bytes b Hb) as Hfb.
    rewrite Hbc in Hfb. apply Forall_app in Hfb as [_ Hsuf].
    exact (wl_gt_not_body
             (proj1 (Forall_forall _ _) Hsuf wl_gt suf_gtf_gt)). }
  rewrite decide_True; [reflexivity | exact Hb].
Qed.

Lemma uline_of_echo b : body_ok b -> uline_of b = LEcho (wl_words b).
Proof using. intro H. by rewrite /uline_of (parse_line_echo b H). Qed.

(* ===================================================================== *)
(*  THE LINE AN ADMISSIBLE BODY IS, WHEN ITS WORDS ARE AN ECHO LINE        *)
(*  (the PROGRAM STREAM).                                                  *)
(*                                                                        *)
(*  [fbody_ok b] says the body parses, and the parse is one of THREE       *)
(*  constructors; [EchoDisc.line_ok (wl_words b)] picks the first, and it  *)
(*  picks it WITHOUT the round trip [wl_body (wl_words b) = b]:            *)
(*                                                                        *)
(*    [LCat]    -- its words are "cat f", whose head is not "echo"         *)
(*                 ([cat_not_echo]);                                       *)
(*    [LEchoF]  -- its body ends in " > f", so the '>' is one of its       *)
(*                 bytes, and [LineWords.wl_words_alnum_body] says every   *)
(*                 byte of a body whose words are alphanumeric is          *)
(*                 alphanumeric or a blank ([wl_gt_not_body]).             *)
(*                                                                        *)
(*  This is what lets a consumer that knows only the LINE it read (sh's    *)
(*  child law: [UkSh.ush_line_is], hence [line_ok]) conclude what the ERA  *)
(*  filed, which is the premise the file era's stage record asks for       *)
(*  ([FileLinkInst.file_lineok]).                                          *)
(* ===================================================================== *)
Lemma fbody_ok_echo (b : list (bv 8)) :
  fbody_ok b -> line_ok (wl_words b) -> uline_of b = LEcho (wl_words b).
Proof using.
  intros Hfb Hok.
  pose proof (fbody_ok_line b Hfb) as [Hlok Hbody].
  destruct (uline_of b) as [ws | ws | | ws npc] eqn:Hu;
    [| | | by destruct (uline_of_nopipe b ws npc Hu)].
  - (* LEcho: the body IS [wl_body ws], so the words are [ws] *)
    rewrite /uline_ok in Hlok. rewrite /line_body in Hbody.
    rewrite Hbody (wl_words_body ws (line_ok_wf _ Hlok)). reflexivity.
  - (* LEchoF: the '>' is a byte of the body *)
    exfalso.
    pose proof (wl_words_alnum_body b (wl_wf_alnum _ (line_ok_wf _ Hok)))
      as Hbb.
    rewrite /line_body in Hbody. rewrite Hbody in Hbb.
    apply Forall_app in Hbb as [_ Hsuf].
    exact (wl_gt_not_body
             (proj1 (Forall_forall _ _) Hsuf wl_gt suf_gtf_gt)).
  - (* LCat: the words are "cat f" *)
    exfalso. rewrite /line_body in Hbody. rewrite Hbody in Hok.
    exact (cat_not_echo (line_ok_head _ Hok)).
Qed.

(* ...AND THE SAME READING AT [fline_ok] (lane ULINE-LPIPE).  Note which
   constructor each [exfalso] kills: the redirect body by its '>', the cat
   line by its head word, and the PIPE body by its bar -- the same
   argument as the redirect's, one byte over. *)
Lemma fline_ok_echo (b : list (bv 8)) :
  fline_ok b -> line_ok (wl_words b) -> uline_of b = LEcho (wl_words b).
Proof using.
  intros [l [Hlok ->]] Hok.
  destruct l as [ws | ws | | ws npc].
  - rewrite /line_body in Hok |- *.
    rewrite (wl_words_body ws (line_ok_wf _ Hlok)).
    exact (uline_of_body (LEcho ws) (uline_nopipe_echo ws) Hlok).
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok)))
      as Hbb.
    rewrite /line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    exact (wl_gt_not_body
             (proj1 (Forall_forall _ _) Hsuf wl_gt suf_gtf_gt)).
  - exfalso. rewrite /line_body in Hok. exact (cat_not_echo (line_ok_head _ Hok)).
  - exfalso.
    pose proof (wl_words_alnum_body _ (wl_wf_alnum _ (line_ok_wf _ Hok)))
      as Hbb.
    rewrite /line_body in Hbb. apply Forall_app in Hbb as [_ Hsuf].
    destruct Hlok as (_ & Hn1 & _). destruct npc as [| F fs]; [exact (Hn1 eq_refl) |].
    rewrite suf_filts_cons in Hsuf. apply Forall_app in Hsuf as [Hsuf _].
    exact (fd_bar_not_body
             (proj1 (Forall_forall _ _) Hsuf fd_bar (suf_filt_bar F))).
Qed.

Lemma ralt_ok_echo_lt4 ws c : ralt_ok (LEcho ws) (ralt_dec c) -> (c < 4)%nat.
Proof using.
  rewrite /ralt_dec. case_decide as H4; [by intros _ |].
  do 10 (case_decide; [by intros [] |]).
  case_decide; [by intros [] |]. rewrite /ralt_ok. lia.
Qed.

Lemma ralt_panic_echo c :
  (c < 4)%nat -> ralt_panic (ralt_dec c) = bool_decide (c = 3%nat).
Proof using. intro H. by rewrite (ralt_dec_lt4 c H). Qed.

Lemma pro_idx_f_echo cs i :
  (forall j, (j < i)%nat -> (cs !!! j < 4)%nat) ->
  pro_idx_f cs i = pro_idx cs i.
Proof using.
  induction i as [| i IH]; intro Hb; [reflexivity |].
  rewrite pro_idx_f_S pro_idx_S IH; [| intros j Hj; apply Hb; lia].
  rewrite /ralt_at (ralt_panic_echo _ (Hb i ltac:(lia))).
  case_bool_decide as H3; case_decide as H3'; [done | done | done | done].
Qed.

Lemma alt_seq_f_sess ps cs s bs q :
  (forall j, (j < q)%nat -> (cs !!! j < 4)%nat) ->
  (forall j, (j < q)%nat -> body_ok (bs !!! j)) ->
  alt_seq_f ps cs s bs q = alt_seq ps cs bs q.
Proof using.
  induction q as [| q IH]; intros Hc Hb; [reflexivity |].
  rewrite alt_seq_f_S alt_seq_S IH;
    [| intros j Hj; apply Hc; lia | intros j Hj; apply Hb; lia].
  f_equal. rewrite /alt_blk_f /alt_blk /alt_cont_f /alt_cont.
  rewrite /ralt_at (ralt_dec_lt4 _ (Hc q ltac:(lia)))
          (uline_of_echo _ (Hb q ltac:(lia))).
  rewrite (pro_idx_f_echo cs q ltac:(intros j Hj; apply Hc; lia)).
  change (ralt_panic (REcho (cs !!! q))) with (bool_decide (cs !!! q = 3%nat)).
  assert (Hif : (if bool_decide (cs !!! q = 3%nat)
                 then pro_of (pro_from (S (pro_idx cs q)) ps) else [])
                = (if decide (cs !!! q = 3%nat)
                   then pro_of (pro_from (S (pro_idx cs q)) ps) else []))
    by (case_bool_decide as H3; case_decide as H3'; done).
  rewrite Hif. reflexivity.
Qed.

Lemma sessf_sess ps cs s I :
  echo_only I -> (forall j, (j < nlines I)%nat -> (cs !!! j < 4)%nat) ->
  sessf ps cs s I = sess ps cs I.
Proof using.
  intros He Hc. rewrite /sessf /sess.
  rewrite (alt_seq_f_sess ps cs s (bodies_of I) (nlines I) Hc); [reflexivity |].
  intros j Hj. rewrite /nlines in Hj.
  destruct (lookup_lt_is_Some_2 (bodies_of I) j Hj) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb).
  exact (Forall_lookup_1 _ _ _ _ He Hb).
Qed.

Lemma pro_ok_f_ok ps cs q :
  (forall j, (j < q)%nat -> (cs !!! j < 4)%nat) ->
  (pro_ok_f ps cs q <-> pro_ok ps cs q).
Proof using.
  intro Hc. rewrite /pro_ok_f /pro_ok (pro_idx_f_echo cs q Hc). done.
Qed.

Lemma alts_ok_lt4 I cs :
  echo_only I -> alts_ok I cs -> Forall (fun c => (c < 4)%nat) cs.
Proof using.
  intros He Ha. apply Forall_lookup. intros i c Hc.
  destruct (Forall2_lookup_r _ _ _ _ _ Ha Hc) as (l & Hl & Hok).
  rewrite /lines_of list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hl. injection Hl as <-.
  rewrite (uline_of_echo b (Forall_lookup_1 _ _ _ _ He Hb)) in Hok.
  exact (ralt_ok_echo_lt4 _ c Hok).
Qed.

Lemma alts_ok_of_lt4 I cs :
  echo_only I -> length cs = nlines I ->
  Forall (fun c => (c < 4)%nat) cs -> alts_ok I cs.
Proof using.
  intros He Hl HF. rewrite /alts_ok.
  apply Forall2_same_length_lookup_2;
    [rewrite /lines_of length_fmap; by rewrite Hl |].
  intros i l c Hli Hci.
  rewrite /lines_of list_lookup_fmap in Hli.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hli. injection Hli as <-.
  rewrite (uline_of_echo b (Forall_lookup_1 _ _ _ _ He Hb)).
  rewrite (ralt_dec_lt4 c (Forall_lookup_1 _ _ _ _ HF Hci)).
  rewrite /ralt_ok. exact (Forall_lookup_1 _ _ _ _ HF Hci).
Qed.

Lemma disc_input_f_of_echo I : echo_only I -> disc_input I -> disc_input_f I.
Proof using.
  intros He (Hb & Hr & Hs). split.
  { apply Forall_impl with (P := body_ok); [exact Hb |].
    intros b Hbo. exists (LEcho (wl_words b)). exact (parse_line_echo b Hbo). }
  split; [| exact Hs].
  apply Forall_impl with (P := wl_body_byte); [exact Hr | exact fbody_byte_of_body].
Qed.

(* THE COMPATIBILITY, at the whole history: a file session that is
   echo-only is disciplined for the echo application too.  Both rules are
   at the input's COMPLETE LINES, so the per-point step is [sessf_sess] at
   [done_of] (which [echo_only] and the range condition both survive, being
   prefix-closed and at [nlines_done]). *)
Lemma disc_f_disc h :
  Forall disc_seg (cycles_of h) -> disc_f h -> disc h.
Proof using.
  intros HD Hf.
  - (* the file model's discipline is the echo model's *)
    apply Forall_lookup. intros i seg Hi.
    assert (Hds : disc_seg seg) by (exact (Forall_lookup_1 _ _ _ _ HD Hi)).
    assert (He : echo_only (ins seg)) by (by destruct Hds as (? & _ & _)).
    destruct (Forall_lookup_1 _ _ _ _ Hf Hi)
      as (s & _ & _ & (ps & cs & Hao & Hall)).
    assert (Hlt4 : Forall (fun c => (c < 4)%nat) cs)
      by (exact (alts_ok_lt4 _ _ He Hao)).
    pose proof (alts_ok_length _ _ Hao) as Hlen.
    split; [exact Hds |]. exists ps, cs.
    split; [exact Hlen |]. split; [exact Hlt4 |].
    intros p Hp.
    assert (Hple : ins p `prefix_of` ins seg)
      by (apply ins_prefix;
          exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp)).
    assert (Hep : echo_only (ins p)) by (exact (echo_only_prefix _ _ Hple He)).
    assert (Hnl : (nlines (ins p) <= nlines (ins seg))%nat)
      by (by apply nlines_prefix).
    assert (Hc4 : forall j, (j < nlines (ins p))%nat -> (cs !!! j < 4)%nat).
    { intros j Hj.
      destruct (lookup_lt_is_Some_2 cs j ltac:(lia)) as [c Hc].
      rewrite (list_lookup_total_correct _ _ _ Hc).
      exact (Forall_lookup_1 _ _ _ _ Hlt4 Hc). }
    destruct (Hall p Hp) as [Hok Hpt].
    split.
    + by apply (pro_ok_f_ok ps cs (nlines (ins p)) Hc4).
    + rewrite /disc_pt.
      rewrite -(sessf_sess ps cs s (done_of (ins p))
                  (echo_only_prefix _ _ (done_of_prefix _) Hep)
                  ltac:(rewrite nlines_done; exact Hc4)).
      exact Hpt.
Qed.

(* ====================================================================== *)
(*  8.  ANTI-VACUITY: SIX MACHINE TRANSCRIPTS, FIVE GOOD AND ONE BAD       *)
(*                                                                        *)
(*  Everything here is CLOSED, so [vm_compute] answers it through the      *)
(*  parser, the chunk arithmetic and the encoding.  The five good ones     *)
(*  say the model admits what the machine does; the bad one says it does   *)
(*  not admit what the machine cannot do -- a [cat f] that prints bytes    *)
(*  nobody echoed into [f].                                                *)
(* ====================================================================== *)

Definition fd_ws : list (list (bv 8)) :=
  [sb "echo"%string; sb "hello"%string; sb "world"%string].
Definition fd_sel_all : list nat := sel_all (echo_chunks fd_ws).
Definition fd_content : list (bv 8) := subseq (echo_chunks fd_ws) fd_sel_all.
Definition fd_content1 : list (bv 8) := subseq (echo_chunks fd_ws) [0%nat].
Definition fd_b0 : list (bv 8) := line_body (LEchoF fd_ws).

(* what a completed [echo hello world > f] round leaves in the file, and
   what a round cut after the first chunk leaves *)
Lemma fd_content_val : fd_content = sb "hello world"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma fd_content1_val : fd_content1 = sb "hello"%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* (1) ONE CYCLE: [echo hello world > f], then [cat f] prints it *)
Definition fd_cs1 : list nat := [ralt_enc (RFRan fd_sel_all); ralt_enc RCRan].

Definition fd_seg1 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes (LEchoF fd_ws))
  ++ demo_out u_prompt
  ++ demo_typed (line_bytes LCat)
  ++ demo_out (fd_content ++ u_prompt).

Lemma demo_f1 : good_out_f None fd_seg1.
Proof using.
  exists [3%nat; 0%nat], fd_cs1.
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_f1_file :
  fstate_after fd_cs1 None (ins fd_seg1) = Some (sb "hello world"%string ++ nlb).
(* [vm_cast_no_check], not [vm_compute]: the decision runs the round's whole
   output segment through the model, and a [vm_compute] closing the goal is
   RE-CHECKED by the kernel's lazy conversion at [Qed] -- so the bill is paid
   twice (4.2s + 4.1s here, 13.3s + 14.8s at [demo_f1_disc]).  The cast asks
   the kernel to use the VM once and skips the tactic-time run.  The price is
   that a disagreement now surfaces at [Qed] with no goal in view, which is
   why this is done at the heavy segments only and not swept. *)
Proof using. apply (bool_decide_unpack _). vm_cast_no_check I. Qed.

(* ...and the user typed it under the rate discipline, byte by byte *)
Lemma demo_f1_disc : disc_seg_f' None fd_seg1.
Proof using.
  eapply (disc_seg_f'_intro None fd_seg1 [3%nat; 0%nat] fd_cs1);
    apply (bool_decide_unpack _); vm_cast_no_check I.
Qed.

(* (2) THE SAME ACROSS A POWER CYCLE: the era boots at the file the
   earlier era left, and [cat f] prints it again *)
Definition fd_seg2 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes LCat)
  ++ demo_out (fd_content ++ u_prompt).

Lemma demo_f2 : good_out_f (Some fd_content) fd_seg2.
Proof using.
  exists [3%nat; 0%nat], [ralt_enc RCRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_f2_adm : fadm_boot [fd_ws] (Some fd_content).
Proof using.
  right. exists fd_ws, fd_sel_all.
  split; [apply elem_of_list_here |]. split; [| reflexivity].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* (3) THE ROUND IN FLIGHT AT THE CUT: the power went off after the echo
   line's newline and before the last write, so the era boots at the
   SUBSEQUENCE that landed, and [cat f] prints [hello] *)
Definition fd_seg3 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes LCat)
  ++ demo_out (fd_content1 ++ u_prompt).

Lemma demo_f3 : good_out_f (Some fd_content1) fd_seg3.
Proof using.
  exists [3%nat; 0%nat], [ralt_enc RCRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_f3_adm : fadm_boot [fd_ws] (Some fd_content1).
Proof using.
  right. exists fd_ws, [0%nat].
  split; [apply elem_of_list_here |]. split; [| reflexivity].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* (4) [cat f] BEFORE ANY ECHO: cat's own diagnostic *)
Definition fd_seg4 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes LCat)
  ++ demo_out alt_catopen.

Lemma demo_f4 : good_out_f None fd_seg4.
Proof using.
  exists [3%nat; 0%nat], [ralt_enc RCRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* (5) THE EXEC-FAILED ROUND: sh's child could not exec /echo AFTER the
   open truncated [f], so [cat f] prints nothing but the prompt *)
Definition fd_seg5 : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes (LEchoF fd_ws))
  ++ demo_out alt_execfail
  ++ demo_typed (line_bytes LCat)
  ++ demo_out u_prompt.

Lemma demo_f5 : good_out_f None fd_seg5.
Proof using.
  exists [3%nat; 0%nat], [ralt_enc RFExec; ralt_enc RCRan].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ---- THE NEGATIVE WITNESS -------------------------------------------- *)

(* the head byte of a concatenation is the head byte of its first part *)
Lemma fd_head_app (C Z : list (bv 8)) (b c : bv 8) :
  C !! 0%nat = Some c -> (C ++ Z) !! 0%nat = Some b -> b = c.
Proof using.
  intros Hc Hb. rewrite (lookup_app_l C Z 0%nat) in Hb.
  - rewrite Hc in Hb. by injection Hb.
  - apply lookup_lt_Some in Hc. lia.
Qed.

(* a subsequence's first byte is some selected chunk's first byte *)
Lemma subseq_head (cs : list (list (bv 8))) (sel : list nat) (b : bv 8) :
  sel_ok cs sel -> subseq cs sel !! 0%nat = Some b ->
  exists i, (i < length cs)%nat /\ cs !!! i !! 0%nat = Some b.
Proof using.
  intros [Hs Hr]. revert Hs Hr.
  induction sel as [| j sel IH]; intros Hs Hr H; [discriminate |].
  apply StronglySorted_inv in Hs as [Hs _].
  apply Forall_cons_1 in Hr as [Hj Hr].
  rewrite /subseq fmap_cons concat_cons in H.
  destruct (cs !!! j) as [| x xs] eqn:Hx.
  - rewrite app_nil_l in H. destruct (IH Hs Hr H) as (i & Hi & Hb).
    by exists i.
  - exists j. split; [exact Hj |]. rewrite Hx. cbn in H |- *. exact H.
Qed.

(* WHAT A [cat f] ROUND CAN PUT ON THE WIRE FIRST, at a file that only
   [echo hello world > f] ever wrote: '$', 'c', 'e', 'f', or one of
   [hello world\n]'s own bytes.  Never 'g'. *)
Lemma fd_cat_head (s : fstate) (a : ralt) (Z : list (bv 8)) (b : bv 8) :
  ralt_ok LCat a ->
  (s = None \/ exists sel, sel_ok (echo_chunks fd_ws) sel
                           /\ s = Some (subseq (echo_chunks fd_ws) sel)) ->
  (cont s LCat a ++ Z) !! 0%nat = Some b -> bv_unsigned b <> 103%Z.
Proof using.
  intros Ha Hs Hb.
  assert (Hco : alt_catopen !! 0%nat = Some (Z_to_bv 8 99%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hce : alt_execcat !! 0%nat = Some (Z_to_bv 8 101%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hcf : alt_panic !! 0%nat = Some (Z_to_bv 8 102%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  destruct a; try (by destruct Ha); rewrite /cont in Hb.
  - (* cat ran *)
    destruct Hs as [-> | (sel & Hsel & ->)].
    + rewrite (fd_head_app _ _ _ _ Hco Hb). by vm_compute.
    + destruct (subseq (echo_chunks fd_ws) sel) as [| x xs] eqn:Hsub.
      * rewrite -(app_assoc [] u_prompt Z) app_nil_l in Hb.
        rewrite (fd_head_app _ _ _ _ u_prompt_head Hb). by vm_compute.
      * rewrite -(app_assoc (x :: xs) u_prompt Z) in Hb.
        cbn in Hb. injection Hb as Hxb.
        destruct (subseq_head (echo_chunks fd_ws) sel x Hsel
                    ltac:(rewrite Hsub; reflexivity)) as (i & Hi & Hx).
        vm_compute in Hi.
        destruct i as [| [| [| [| i]]]]; [| | | | exfalso; lia];
          vm_compute in Hx; injection Hx as <-; rewrite -Hxb; by vm_compute.
  - rewrite (fd_head_app _ _ _ _ Hco Hb). by vm_compute.
  - rewrite (fd_head_app _ _ _ _ Hce Hb). by vm_compute.
  - rewrite (fd_head_app _ _ _ _ u_prompt_head Hb). by vm_compute.
  - rewrite (fd_head_app _ _ _ _ Hcf Hb). by vm_compute.
Qed.

(* the file [echo hello world > f] leaves, whichever way its round went *)
Lemma fd_fsm_shape (a : ralt) :
  ralt_ok (LEchoF fd_ws) a ->
  fsm None (LEchoF fd_ws) a = None
  \/ exists sel, sel_ok (echo_chunks fd_ws) sel
                 /\ fsm None (LEchoF fd_ws) a = Some (subseq (echo_chunks fd_ws) sel).
Proof using.
  intro Ha. destruct a; try (by destruct Ha); cbn [fsm].
  - right. exists sel. split; [exact Ha | reflexivity].
  - right. exists []. split; [apply sel_ok_nil | reflexivity].
  - by left.
  - right. exists []. split; [apply sel_ok_nil | reflexivity].
  - (* RFSilent: identity (RULING HOLD-POS) *) by left.
  - by left.
Qed.

(* the three appends the cancellation goes through *)
Lemma fd_cancel3 (A B Cc G C : list (bv 8)) :
  ((A ++ B ++ Cc) ++ (wl_nl :: G))
    `prefix_of` (A ++ ((B ++ (Cc ++ wl_nl :: C)) ++ [])) ->
  G `prefix_of` C.
Proof using.
  rewrite app_nil_r -!app_assoc. intro Hp.
  apply wl_prefix_app_cancel in Hp.
  apply wl_prefix_app_cancel in Hp.
  apply wl_prefix_app_cancel in Hp.
  exact (prefix_cons_inv_2 _ _ _ _ Hp).
Qed.

(* THE WIRE THAT IS NOT ADMITTED: [echo hello world > f] was typed, and
   then [cat f] printed [goodbye].  Nothing the model admits prints a byte
   the user never echoed into the file, and the refutation is the
   determinacy theorem plus one head byte. *)
Definition fd_bad_J : list (bv 8) := line_bytes (LEchoF fd_ws) ++ cmd_cat_f.
Definition fd_bad_cs : list nat := [ralt_enc (RFRan fd_sel_all)].

Definition fd_seg_bad : list mobs :=
  demo_out u_prologue
  ++ demo_typed (line_bytes (LEchoF fd_ws))
  ++ demo_out u_prompt
  ++ demo_typed (line_bytes LCat)
  ++ demo_out (sb "goodbye"%string ++ nlb ++ u_prompt).

Lemma demo_f_bad : ~ good_out_f None fd_seg_bad.
Proof using.
  intros (ps & cs & Hok & Hcs & Hpre).
  (* the honest transcript through the OPEN [cat f] line is on the wire *)
  assert (Hw : obs_wire Uart0 fd_seg_bad
               = sessf [3%nat; 0%nat] fd_bad_cs None fd_bad_J
                 ++ wl_nl :: (sb "goodbye"%string ++ nlb ++ u_prompt))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HT : sessf [3%nat; 0%nat] fd_bad_cs None fd_bad_J
                 `prefix_of` sessf ps cs None (ins fd_seg_bad)).
  { etrans; [| exact Hpre]. rewrite Hw. by eexists. }
  (* so the adversary's resolution agrees with it through that line *)
  destruct (sessf_prefix_det ps [3%nat; 0%nat] cs fd_bad_cs None
              fd_bad_J (ins fd_seg_bad) (proj1 Hok)
              ltac:(apply (bool_decide_unpack _); vm_compute; exact I)
              Hcs
              ltac:(apply (bool_decide_unpack _); vm_compute; exact I)
              (pro_pin_f_of_ok ps cs (ins fd_seg_bad) Hok)
              ltac:(apply (bool_decide_unpack _); vm_compute; exact I)
              ltac:(apply (bool_decide_unpack _); vm_compute; exact I)
              I HT)
    as (_ & _ & Heq).
  rewrite Hw Heq in Hpre.
  (* the two inputs, cut *)
  assert (HbJ : bodies_of fd_bad_J = [fd_b0])
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HnJ : nlines fd_bad_J = 1%nat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HrJ : rest_of fd_bad_J = cmd_cat_f)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HbI : bodies_of (ins fd_seg_bad) = [fd_b0; cmd_cat_f])
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HnI : nlines (ins fd_seg_bad) = 2%nat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HrI : rest_of (ins fd_seg_bad) = [])
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  rewrite /sessf HbJ HnJ HrJ HbI HnI HrI in Hpre.
  rewrite (alt_seq_f_bs_ext ps cs None [fd_b0] [fd_b0; cmd_cat_f] 1
             ltac:(intros j Hj; assert (Hj0 : j = 0%nat) by lia;
                   by rewrite Hj0)) in Hpre.
  rewrite (alt_seq_f_S ps cs None [fd_b0; cmd_cat_f] 1) /alt_blk_f in Hpre.
  rewrite (_ : [fd_b0; cmd_cat_f] !!! 1%nat = cmd_cat_f) in Hpre;
    [| reflexivity].
  apply fd_cancel3 in Hpre.
  (* the cat round's first byte would have to be 'g' *)
  assert (Hg : (sb "goodbye"%string ++ nlb ++ u_prompt) !! 0%nat
               = Some (Z_to_bv 8 103%Z))
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (HC : alt_cont_f ps cs None [fd_b0; cmd_cat_f] 1%nat !! 0%nat
               = Some (Z_to_bv 8 103%Z))
    by (eapply lb_prefix_lookup; [exact Hpre | exact Hg]).
  assert (Hu1 : uline_of ([fd_b0; cmd_cat_f] !!! 1%nat) = LCat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hu0 : uline_of ([fd_b0; cmd_cat_f] !!! 0%nat) = LEchoF fd_ws)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hs1 : fstate_upto cs None [fd_b0; cmd_cat_f] 1%nat
                = fsm None (LEchoF fd_ws) (ralt_at cs 0%nat))
    by (cbn [fstate_upto]; by rewrite Hu0).
  rewrite /alt_cont_f Hu1 Hs1 in HC.
  (* both rounds' alternatives are ones their line shapes admit *)
  pose proof (alts_ok_at (ins fd_seg_bad) cs 0%nat Hcs ltac:(rewrite HnI; lia))
    as Ha0.
  pose proof (alts_ok_at (ins fd_seg_bad) cs 1%nat Hcs ltac:(rewrite HnI; lia))
    as Ha1.
  rewrite HbI Hu0 in Ha0. rewrite HbI Hu1 in Ha1.
  pose proof (fd_cat_head _ _ _ _ Ha1 (fd_fsm_shape _ Ha0) HC) as Hne.
  apply Hne. by vm_compute.
Qed.
